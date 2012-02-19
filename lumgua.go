package main

import (
	"bufio"
	"bytes"
	"container/vector"
	"exec"
	"flag"
	"fmt"
	"http"
	"io"
	"io/ioutil"
	"log"
	"math"
	"os"
	//	"runtime/debug"
	"strconv"
	"strings"
	"time"
	"url"
)

/// command-line arguments

var address *string = flag.String("a", ":8082", "address")

/// global state

var definedGlobals *SymbolSet        // XXX kludge!
var bindingsKludge map[*Symbol]Value // XXX kludge!

var globals map[string]Value

var symbolTable map[string]*Symbol

var readTable map[byte]func(io.ByteScanner) Literal

/// lisp types

type Value interface {
	literal() (Literal, os.Error)
}

type NonLiteral struct{}

type Symbol struct {
	name string
}

type Number float64

type String string

type Bool bool

type List struct {
	head Value
	tail *List
}

var emptyList = &List{Number(5), nil}

type Template struct {
	NonLiteral
	name     string
	nvars    int
	freeRefs []FreeRef
	code     []Instr
	globals  []Value
}

type Func struct {
	NonLiteral
	temp *Template
	env  []Value
}

type Cont struct {
	NonLiteral
	stack Stack
}

type Cell struct {
	NonLiteral
	value Value
}

type Array struct {
	NonLiteral
	vector.Vector
}

func newTemplate(name string, nvars int, freeRefs []FreeRef, code []Instr, globals []Value) *Template {
	return &Template{
		name:     name,
		nvars:    nvars,
		freeRefs: freeRefs,
		code:     code,
		globals:  globals,
	}
}

func newFunc(temp *Template, env []Value) *Func {
	return &Func{
		temp: temp,
		env:  env,
	}
}

func newCont(stack Stack) *Cont {
	return &Cont{
		stack: stack,
	}
}

func newCell(x Value) *Cell {
	return &Cell{
		value: x,
	}
}

func newArray(v vector.Vector) *Array {
	return &Array{
		Vector: v,
	}
}

func symbolp(x Value) (ok bool) {
	_, ok = x.(*Symbol)
	return
}

func numberp(x Value) (ok bool) {
	_, ok = x.(Number)
	return
}

func nilp(x Value) (ok bool) {
	ok = (x == Value(emptyList))
	return
}

func stringp(x Value) (ok bool) {
	_, ok = x.(String)
	return
}

func boolp(x Value) (ok bool) {
	_, ok = x.(Bool)
	return
}

func consp(x Value) bool {
	list, ok := x.(*List)
	return ok && (list != emptyList)
}

func templatep(x Value) (ok bool) {
	_, ok = x.(*Template)
	return
}

func funcp(x Value) (ok bool) {
	_, ok = x.(*Func)
	return
}

func contp(x Value) (ok bool) {
	_, ok = x.(*Cont)
	return
}

func cellp(x Value) (ok bool) {
	_, ok = x.(*Cell)
	return
}

func arrayp(x Value) (ok bool) {
	_, ok = x.(*Array)
	return
}

func listp(x Value) (ok bool) {
	ok = nilp(x) || consp(x)
	return
}

func anyp(x Value) (ok bool) {
	ok = true
	return
}

func intern(name string) *Symbol {
	sym, ok := symbolTable[name]
	if !ok {
		sym = &Symbol{name}
		symbolTable[name] = sym
	}
	return sym
}

func (list *List) len() int {
	n := 0
	for x := list; x != emptyList; x = x.tail {
		n++
	}
	return n
}

/// conversion

func list(elements ...Value) Value {
	x := emptyList
	for i := len(elements) - 1; i >= 0; i-- {
		x = &List{elements[i], x}
	}
	return x
}

func array(x Value) (*Array, os.Error) {
	a := new(Array)
	err := forEach(x, func(elt Value) os.Error {
		a.Push(elt)
		return nil
	})
	if err != nil {
		return nil, os.NewError("array: bad argument")
	}
	return a, nil
}

func tuple(x Value, preds ...func(Value) bool) (*Array, os.Error) {
	a, err := array(x)
	if err != nil {
		return nil, os.NewError("tuple: bad argument")
	}
	if a.Len() != len(preds) {
		return nil, os.NewError("tuple: bad argument")
	}
	for i, pred := range preds {
		if !pred(a.At(i).(Value)) {
			return nil, os.NewError("tuple: bad argument")
		}
	}
	return a, nil
}

/// combinators

func forEach(x Value, f func(Value) os.Error) os.Error {
	list, ok := x.(*List)
	if !ok {
		return os.NewError("forEach: type error")
	}
	for list != emptyList {
		err := f(list.head)
		if err != nil {
			return err
		}
		list = list.tail
	}
	return nil
}

func listMap(x Value, f func(Value) *List) *List {
	list, ok := x.(*List)
	if !ok {
		panic("listMap: type error")
	}
	if list == emptyList {
		return emptyList
	}
	return &List{f(list.head), listMap(list.tail, f)}
}

/// interpreter

const (
	HALTED = iota
	RUNNING
)

const (
	LOCAL = iota
	FREE
)

type FreeRef struct {
	kind int
	i    int
}

type Instr interface {
	Exec(m *Machine)
	Sexp() Value
}

type continuationInstr struct{}

func newContinuationInstr() Instr {
	return &continuationInstr{}
}

func (*continuationInstr) Exec(m *Machine) {
	stack := m.stack.Slice(0, m.stack.Len()-1)
	m.a = newCont(
		Stack{*stack},
	)
}

func (instr *continuationInstr) Sexp() Value {
	return list(intern("continuation"))
}

type closeInstr struct {
	temp *Template
}

func newCloseInstr(arg Value) Instr {
	return &closeInstr{arg.(*Template)}
}

func (instr *closeInstr) Exec(m *Machine) {
	freeRefs := instr.temp.freeRefs
	n := len(freeRefs)
	if n == 0 {
		m.a = newFunc(instr.temp, nil)
		return
	}
	env := make([]Value, n)
	for i := 0; i < n; i++ {
		domain := freeRefs[i].kind
		j := freeRefs[i].i
		switch domain {
		case LOCAL:
			env[i] = m.stack.At(m.fp + j).(Value)
		case FREE:
			env[i] = m.f.env[j]
		default:
			m.throw("unknown variable domain")
			return
		}
	}
	m.a = newFunc(instr.temp, env)
}

func (instr *closeInstr) Sexp() Value {
	return list(intern("close"), instr.temp)
}

type frameInstr struct {
	pc int
}

func newFrameInstr(arg Value) Instr {
	return &frameInstr{int(arg.(Number))}
}

func (instr *frameInstr) Exec(m *Machine) {
	m.stack.Push(m.f)
	m.stack.Push(m.fp)
	m.stack.Push(instr.pc)
}

func (instr *frameInstr) Sexp() Value {
	return list(intern("frame"), Number(instr.pc))
}

type shiftInstr struct{}

func newShiftInstr() Instr {
	return &shiftInstr{}
}

func (*shiftInstr) Exec(m *Machine) {
	nremove := m.f.temp.nvars
	nkeep := m.stack.Len() - nremove - m.fp
	for i, j := m.fp, 0; j < nkeep; j++ {
		m.stack.Set(i, m.stack.At(i+nremove))
		i++
	}
	m.stack.Resize(m.stack.Len()-nremove, 0)
}

func (*shiftInstr) Sexp() Value {
	return list(intern("shift"))
}

type applyInstr struct {
	nargs int
}

func newApplyInstr(arg interface{}) Instr {
	nargs := int(arg.(Number))
	return &applyInstr{nargs}
}

func (m *Machine) prepareApplyArgs(nvars int) {
	rest, ok := m.stack.Pop().(*List)
	if !ok {
		m.throw("apply: type error")
		return
	}
	for i := 0; i < nvars; i++ {
		if rest == emptyList {
			m.throw("apply: too few arguments")
			return
		}
		m.stack.Push(rest.head)
		rest = rest.tail
	}
	if rest != emptyList {
		m.throw("apply: too many arguments")
		return
	}
}

func (m *Machine) prepareArgs(nargs, nvars int) {
	if nargs == -1 {
		m.prepareApplyArgs(nvars)
		return
	}
	if nargs < nvars {
		m.throw("too few arguments")
	}
	if nargs > nvars {
		m.throw("too many arguments")
	}
}

func (m *Machine) applyFunc(f *Func, nargs int) {
	temp := f.temp
	m.f = f
	if nargs == -1 {
		m.fp = m.stack.Len() - 1
	} else {
		m.fp = m.stack.Len() - nargs
	}
	m.pc = 0
	m.code = temp.code
	m.env = f.env
	m.prepareArgs(nargs, temp.nvars)
}

func (m *Machine) applyCont(c *Cont) {
	ret := returnInstr{}
	m.a = m.stack.At(m.stack.Len() - 1).(Value)
	m.stack = Stack{c.stack.Copy()}
	m.fp = m.stack.Len()
	ret.Exec(m)
}

func (instr *applyInstr) Exec(m *Machine) {
	switch x := m.a.(type) {
	case *Func:
		m.applyFunc(x, instr.nargs)
	case *Cont:
		if instr.nargs != 1 {
			m.throw("wrong number of arguments")
			return
		}
		m.applyCont(x)
	default:
		m.throw("attempt to call nonfunction")
		return
	}
}

func (instr *applyInstr) Sexp() Value {
	return list(intern("apply"), Number(instr.nargs))
}

type returnInstr struct{}

func newReturnInstr() Instr {
	return &returnInstr{}
}

func (*returnInstr) Exec(m *Machine) {
	fp := m.fp
	m.pc = m.stack.At(fp - 1).(int)
	m.fp = m.stack.At(fp - 2).(int)
	m.f = m.stack.At(fp - 3).(*Func)
	m.stack.Resize(fp-3, 0)
	m.code = m.f.temp.code
	m.env = m.f.env
}

func (*returnInstr) Sexp() Value {
	return list(intern("return"))
}

type constInstr struct {
	val Value
}

func newConstInstr(arg Value) Instr {
	return &constInstr{arg}
}

func (instr *constInstr) Exec(m *Machine) {
	m.a = instr.val
}

func (instr *constInstr) Sexp() Value {
	return list(intern("const"), instr.val)
}

type globalInstr struct {
	n int
}

func newGlobalInstr(arg Value) Instr {
	return &globalInstr{int(arg.(Number))}
}

func (instr *globalInstr) Exec(m *Machine) {
	m.a = m.f.temp.globals[instr.n]
}

func (instr *globalInstr) Sexp() Value {
	return list(intern("global"), Number(instr.n))
}

type localInstr struct {
	n int
}

func newLocalInstr(arg Value) Instr {
	return &localInstr{int(arg.(Number))}
}

func (instr *localInstr) Exec(m *Machine) {
	m.a = m.stack.At(m.fp + instr.n).(Value)
}

func (instr *localInstr) Sexp() Value {
	return list(intern("local"), Number(instr.n))
}

type freeInstr struct {
	n int
}

func newFreeInstr(arg Value) Instr {
	return &freeInstr{int(arg.(Number))}
}

func (instr *freeInstr) Exec(m *Machine) {
	m.a = m.f.env[instr.n]
}

func (instr *freeInstr) Sexp() Value {
	return list(intern("free"), Number(instr.n))
}

type pushInstr struct{}

func newPushInstr() Instr {
	return &pushInstr{}
}

func (*pushInstr) Exec(m *Machine) {
	m.stack.Push(m.a)
}

func (*pushInstr) Sexp() Value {
	return list(intern("push"))
}

type fjumpInstr struct {
	pc int
}

func newFjumpInstr(arg Value) Instr {
	return &fjumpInstr{int(arg.(Number))}
}

func (instr *fjumpInstr) Exec(m *Machine) {
	if b, ok := m.a.(Bool); ok && !bool(b) {
		m.pc = instr.pc
	}
}

func (instr *fjumpInstr) Sexp() Value {
	return list(intern("fjump"), Number(instr.pc))
}

type jumpInstr struct {
	pc int
}

func newJumpInstr(arg Value) Instr {
	return &jumpInstr{int(arg.(Number))}
}

func (instr *jumpInstr) Exec(m *Machine) {
	m.pc = instr.pc
}

func (instr *jumpInstr) Sexp() Value {
	return list(intern("jump"), Number(instr.pc))
}

type haltInstr struct{}

func newHaltInstr() Instr {
	return &haltInstr{}
}

func (*haltInstr) Exec(m *Machine) {
	m.status = HALTED
}

func (*haltInstr) Sexp() Value {
	return list(intern("halt"))
}

type primInstr struct {
	name string
	prim Prim
}

var sharedPrimStack []Value

func (instr *primInstr) Exec(m *Machine) {
	nvars := m.f.temp.nvars
	n := nvars
	if n > cap(sharedPrimStack) {
		m.throw("too many arguments to prim")
		return
	}
	sharedPrimStack = sharedPrimStack[0:n]
	for i := 0; i < n; i++ {
		sharedPrimStack[i] = m.stack.At(m.fp + i).(Value)
	}
	a, err := instr.prim(sharedPrimStack...)
	if err != nil {
		m.throw(err.String())
		return
	}
	m.a = a
}

func (instr *primInstr) Sexp() Value {
	return list(intern("prim"), intern(instr.name))
}

type Stack struct {
	vector.Vector
}

type Machine struct {
	status int
	f      *Func
	fp     int
	pc     int
	stack  Stack
	a      Value
	code   []Instr
	env    []Value
}

func (m *Machine) throw(s string) {
	code := []Instr{
		&frameInstr{m.pc - 1},
		&constInstr{String(s)},
		&pushInstr{},
		&constInstr{globals["throw"]}, // XXX
		&applyInstr{1},
	}
	for _, instr := range code {
		instr.Exec(m)
	}
}

func freshStack() Stack {
	var s Stack
	s.Push(
		newFunc(
			newTemplate(
				"halt", 0, nil,
				[]Instr{
					&constInstr{intern("normal")},
					&haltInstr{},
				},
				[]Value{},
			),
			nil,
		),
	)
	s.Push(0)
	s.Push(0)
	return s
}

func newMachine(f *Func) *Machine {
	return &Machine{
		RUNNING, f, 3, 0,
		freshStack(), emptyList,
		f.temp.code, f.env,
	}
}

func (m *Machine) run() {
	for m.status == RUNNING {
		m.pc++
		m.code[m.pc-1].Exec(m)
	}
}

/// primitives

type Prim func(...Value) (Value, os.Error)

func truth(x bool) Value {
	return Bool(x)
}

func primSymbolp(args ...Value) (Value, os.Error) {
	return truth(symbolp(args[0])), nil
}

func primNumberp(args ...Value) (Value, os.Error) {
	return truth(numberp(args[0])), nil
}

func primStringp(args ...Value) (Value, os.Error) {
	return truth(stringp(args[0])), nil
}

func primBoolp(args ...Value) (Value, os.Error) {
	return truth(boolp(args[0])), nil
}

func primConsp(args ...Value) (Value, os.Error) {
	return truth(consp(args[0])), nil
}

func primTemplatep(args ...Value) (Value, os.Error) {
	return truth(templatep(args[0])), nil
}

func primFuncp(args ...Value) (Value, os.Error) {
	return truth(funcp(args[0])), nil
}

func primContp(args ...Value) (Value, os.Error) {
	return truth(contp(args[0])), nil
}

func primCellp(args ...Value) (Value, os.Error) {
	return truth(cellp(args[0])), nil
}

func primArrayp(args ...Value) (Value, os.Error) {
	return truth(arrayp(args[0])), nil
}

func primSymbolName(args ...Value) (Value, os.Error) {
	if sym, ok := args[0].(*Symbol); ok {
		return String(sym.name), nil
	}
	return nil, os.NewError("symbolname: type error")
}

func primCons(args ...Value) (Value, os.Error) {
	if len(args) != 2 {
		return nil, os.NewError("cons: wrong number of arguments")
	}
	tail, ok := args[1].(*List)
	if !ok {
		return nil, os.NewError("cons: type error")
	}
	return &List{args[0], tail}, nil
}

func primCar(args ...Value) (Value, os.Error) {
	if list, ok := args[0].(*List); ok {
		if list == emptyList {
			return nil, os.NewError("car: nil")
		}
		return list.head, nil
	}
	return nil, os.NewError("car: type error")
}

func primCdr(args ...Value) (Value, os.Error) {
	if list, ok := args[0].(*List); ok {
		if list == emptyList {
			return nil, os.NewError("cdr: nil")
		}
		return list.tail, nil
	}
	return nil, os.NewError("cdr: type error")
}

func makeFreeRef(kind *Symbol, i Number) (r FreeRef, err os.Error) {
	switch kind.name {
	case "local":
		r.kind = LOCAL
	case "free":
		r.kind = FREE
	default:
		err = os.NewError(
			"makeFreeRef: unknown kind of free reference",
		)
	}
	r.i = int(i)
	return
}

func packFreeRefs(src Value) ([]FreeRef, os.Error) {
	specs, err := array(src)
	if err != nil {
		return nil, os.NewError("packFreeRefs: bad argument")
	}
	n := specs.Len()
	freeRefs := make([]FreeRef, n)
	for i := 0; i < n; i++ {
		spec, err := tuple(specs.At(i).(Value), symbolp, numberp)
		if err != nil {
			return nil, os.NewError(
				"packFreeRefs: bad argument",
			)
		}
		freeRefs[i], err = makeFreeRef(
			spec.At(0).(*Symbol),
			spec.At(1).(Number),
		)
		if err != nil {
			return nil, os.NewError(
				"packFreeRefs: bad argument",
			)
		}
	}
	return freeRefs, nil
}

func makeInstr(opcode string, args *List) Instr {
	arg := Value(emptyList)
	if args != emptyList {
		arg = args.head
	}
	switch opcode {
	case "continuation":
		return newContinuationInstr()
	case "close":
		return newCloseInstr(arg)
	case "frame":
		return newFrameInstr(arg)
	case "shift":
		return newShiftInstr()
	case "apply":
		return newApplyInstr(arg)
	case "return":
		return newReturnInstr()
	case "const":
		return newConstInstr(arg)
	case "global":
		return newGlobalInstr(arg)
	case "local":
		return newLocalInstr(arg)
	case "free":
		return newFreeInstr(arg)
	case "push":
		return newPushInstr()
	case "fjump":
		return newFjumpInstr(arg)
	case "jump":
		return newJumpInstr(arg)
	case "halt":
		return newHaltInstr()
	default:
		panic("makeInstr: unknown opcode: \"" + opcode + "\"")
	}
	return nil
}

func packCode(src Value) ([]Instr, os.Error) {
	a, err := array(src)
	if err != nil {
		return nil, os.NewError("packCode: bad argument")
	}
	n := a.Len()
	code := make([]Instr, n)
	for i := 0; i < n; i++ {
		switch x := a.At(i).(type) {
		case *List:
			opcode, ok := x.head.(*Symbol)
			if !ok {
				return nil, os.NewError(
					"packCode: non-symbol opcode",
				)
			}
			code[i] = makeInstr(opcode.name, x.tail)
		default:
			return nil, os.NewError("packCode: bad argument")
		}
	}
	return code, nil
}

func primTemplateNew(args ...Value) (Value, os.Error) {
	// var nvars int
	// if n, ok := args[0].(Number); ok {
	// 	nvars = int(n)
	// } else {
	// 	return nil, os.NewError("templatenew: type error")
	// }
	// freeRefs, err := packFreeRefs(args[1])
	// if err != nil {
	// 	return nil, os.NewError("templatenew: invalid free references")
	// }
	// code, err := packCode(args[2])
	// if err != nil {
	// 	return nil, os.NewError("templatenew: invalid code")
	// }
	// temp := newTemplate(
	// 	"",
	// 	nvars,
	// 	freeRefs,
	// 	code,
	// )
	// return temp, nil
	return nil, os.NewError("templatenew: not implemented")
}

func unpackFreeRef(ref FreeRef) Value {
	switch ref.kind {
	case LOCAL:
		return list(String("local"), Number(ref.i))
	case FREE:
		return list(String("free"), Number(ref.i))
	}
	panic("unpackFreeRef: unexpected free reference kind")
}

func unpackInstr(instr Instr) Value {
	return instr.Sexp()
}

func primTemplateOpen(args ...Value) (Value, os.Error) {
	temp, ok := args[0].(*Template)
	if !ok {
		return nil, os.NewError("templateopen: type error")
	}
	n := len(temp.freeRefs)
	freeRefs := emptyList
	for i := n - 1; i >= 0; i-- {
		freeRefs = &List{unpackFreeRef(temp.freeRefs[i]), freeRefs}
	}
	code := emptyList
	n = len(temp.code)
	for i := n - 1; i >= 0; i-- {
		code = &List{unpackInstr(temp.code[i]), code}
	}
	sexp := list(
		intern("template"),
		String(temp.name),
		Number(temp.nvars),
		freeRefs,
		code,
	)
	return sexp, nil
}

func primFuncNew(args ...Value) (Value, os.Error) {
	temp, ok := args[0].(*Template)
	if !ok {
		return nil, os.NewError("funcnew: type error")
	}
	envArray, ok := args[1].(*Array)
	if !ok {
		return nil, os.NewError("funcnew: type error")
	}
	env := make([]Value, envArray.Len())
	n := len(env)
	for i := 0; i < n; i++ {
		env[i] = envArray.At(i).(Value)
	}
	return newFunc(temp, env), nil
}

func primFuncOpen(args ...Value) (Value, os.Error) {
	f, ok := args[0].(*Func)
	if !ok {
		return nil, os.NewError("funcopen: type error")
	}
	envArray := new(Array)
	for _, elt := range f.env {
		envArray.Push(elt)
	}
	sexp := list(
		intern("func"),
		f.temp,
		envArray,
	)
	return sexp, nil
}

func primContOpen(args ...Value) (Value, os.Error) {
	c, ok := args[0].(*Cont)
	if !ok {
		return nil, os.NewError("contopen: type error")
	}
	stack := newArray(c.stack.Copy())
	n := stack.Len()
	for i := 0; i < n; i++ {
		if n, ok := stack.At(i).(int); ok {
			stack.Set(i, Number(n))
		}
	}
	return list(intern("cont"), stack), nil
}

func primArrayNew(args ...Value) (Value, os.Error) {
	m, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("arraynew: type error")
	}
	n := int(m)
	a := new(Array)
	for i := 0; i < n; i++ {
		a.Push(Value(emptyList))
	}
	return a, nil
}

func primArrayGet(args ...Value) (Value, os.Error) {
	a, ok := args[0].(*Array)
	if !ok {
		return nil, os.NewError("arrayget: type error")
	}
	i, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("arrayget: type error")
	}
	return a.At(int(i)).(Value), nil
}

func primArrayPut(args ...Value) (Value, os.Error) {
	a, ok := args[0].(*Array)
	if !ok {
		return nil, os.NewError("arrayput: type error")
	}
	i, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("arrayput: type error")
	}
	x := args[2]
	a.Set(int(i), x)
	return emptyList, nil
}

func primArrayLength(args ...Value) (Value, os.Error) {
	a, ok := args[0].(*Array)
	if !ok {
		return nil, os.NewError("arraylength: type error")
	}
	return Number(a.Len()), nil
}

func primCellNew(args ...Value) (Value, os.Error) {
	return newCell(args[0]), nil
}

func primCellGet(args ...Value) (Value, os.Error) {
	c, ok := args[0].(*Cell)
	if !ok {
		return nil, os.NewError("cellget: type error")
	}
	return c.value, nil
}

func primCellPut(args ...Value) (Value, os.Error) {
	c, ok := args[0].(*Cell)
	if !ok {
		return nil, os.NewError("cellput: type error")
	}
	x := args[1]
	c.value = x
	return c, nil
}

func primStrGet(args ...Value) (Value, os.Error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, os.NewError("strget: type error")
	}
	i, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("strget: type error")
	}
	return String(string(s)[int(i)]), nil
}

func primStrCat(args ...Value) (Value, os.Error) {
	s := ""
	err := forEach(args[0], func(elt Value) os.Error {
		str, ok := elt.(String)
		if !ok {
			return os.NewError("strcat: type error")
		}
		s += string(str)
		return nil
	})
	if err != nil {
		return nil, err
	}
	return String(s), nil
}

func primStrLength(args ...Value) (Value, os.Error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, os.NewError("strlength: type error")
	}
	return Number(len(string(s))), nil
}

func primSubstringp(args ...Value) (Value, os.Error) {
	sub, ok := args[0].(String)
	if !ok {
		return nil, os.NewError("substringp: type error")
	}
	str, ok := args[1].(String)
	if !ok {
		return nil, os.NewError("substringp: type error")
	}
	return truth(strings.Index(string(str), string(sub)) != -1), nil
}

func primAtoi(args ...Value) (Value, os.Error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, os.NewError("atoi: type error")
	}
	var n float64
	if _, err := fmt.Sscan(string(s), &n); err != nil {
		return emptyList, nil
	}
	return Number(n), nil
}

func primItoa(args ...Value) (Value, os.Error) {
	n, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("itoa: type error")
	}
	s := fmt.Sprint(float64(n))
	return String(s), nil
}

func primIntern(args ...Value) (Value, os.Error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, os.NewError("intern: type error")
	}
	return intern(string(s)), nil
}

func primAdd(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("+: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("+: type error")
	}
	return Number(float64(a) + float64(b)), nil
}

func primSub(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("-: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("-: type error")
	}
	return Number(float64(a) - float64(b)), nil
}

func primMul(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("*: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("*: type error")
	}
	return Number(float64(a) * float64(b)), nil
}

func primDiv(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("/: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("/: type error")
	}
	return Number(float64(a) / float64(b)), nil
}

func primPow(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("pow: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("pow: type error")
	}
	return Number(math.Pow(float64(a), float64(b))), nil
}

func primEq(args ...Value) (Value, os.Error) {
	return truth(args[0] == args[1]), nil
}

func primNeq(args ...Value) (Value, os.Error) {
	return truth(args[0] != args[1]), nil
}

func primLt(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("<: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("<: type error")
	}
	return truth(float64(a) < float64(b)), nil
}

func primGt(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError(">: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError(">: type error")
	}
	return truth(float64(a) > float64(b)), nil
}

func primLe(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError("<=: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError("<=: type error")
	}
	return truth(float64(a) <= float64(b)), nil
}

func primGe(args ...Value) (Value, os.Error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, os.NewError(">=: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, os.NewError(">=: type error")
	}
	return truth(float64(a) >= float64(b)), nil
}

func primLog(args ...Value) (Value, os.Error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, os.NewError("log: type error")
	}
	fmt.Println(string(s))
	return emptyList, nil
}

type stringBody struct {
	*strings.Reader
}

func (b stringBody) Close() os.Error {
	return nil
}

func httpPut(rawURL string, body string) os.Error {
	bakedURL, err := url.Parse(rawURL)
	if err != nil {
		return os.NewError("http: parse url fail: " + err.String())
	}
	request := &http.Request{
		URL:    bakedURL,
		RawURL: rawURL,
		Method: "PUT",
		Header: http.Header(
			map[string][]string{
				"Content-Type": []string{
					"text/plain; charset=utf-8",
				},
			},
		),
		Host: bakedURL.Host,
		Body: stringBody{
			strings.NewReader(body),
		},
		ContentLength: int64(len(body)),
	}
	response, err := http.DefaultClient.Do(request)
	if err != nil || response.StatusCode != 200 {
		return os.NewError("http: put fail: " + err.String())
	}
	return nil
}

func primHttp(args ...Value) (Value, os.Error) {
	method, ok := args[0].(*Symbol)
	if !ok {
		return nil, os.NewError("http: type error")
	}
	url, ok := args[1].(String)
	if !ok {
		return nil, os.NewError("http: type error")
	}
	switch method.name {
	case "get":
		response, err := http.Get(string(url))
		if err != nil {
			return nil, os.NewError(
				"http: get fail: " + err.String(),
			)
		}
		defer response.Body.Close()
		if response.StatusCode != 200 {
			return nil, os.NewError(
				"http: get fail: status: " + response.Status,
			)
		}
		text, err := ioutil.ReadAll(response.Body)
		if err != nil {
			return nil, os.NewError(
				"http: get fail: " + err.String(),
			)
		}
		return String(text), nil
	case "put":
		list, ok := args[2].(*List)
		if !ok || list == emptyList {
			return nil, os.NewError("http: bad argument")
		}
		bodyString, ok := list.head.(String)
		if !ok {
			return nil, os.NewError("http: bod argument")
		}
		httpPut(string(url), string(bodyString))
		return emptyList, nil
	}
	return nil, os.NewError("http: unsupported method: " + method.name)
}

func primNow(args ...Value) (Value, os.Error) {
	ns := time.Nanoseconds()
	return Number(float64(ns / 1000000)), nil
}

func primExec(args ...Value) (Value, os.Error) {
	var s String
	var ok bool
	var err os.Error
	if len(args) != 2 {
		return nil, os.NewError("exec: wrong number of arguments")
	}
	s, ok = args[0].(String)
	if !ok {
		return nil, os.NewError("exec: bad program name")
	}
	cmdname := string(s)
	cmdargs := make([]string, 0)
	err = forEach(args[1], func(arg Value) os.Error {
		s, ok = arg.(String)
		if !ok {
			return os.NewError("exec: bad argument")
		}
		cmdargs = append(cmdargs, string(s))
		return nil
	})
	if err != nil {
		return nil, err
	}
	cmd := exec.Command(cmdname, cmdargs...)
	p, err := cmd.StdoutPipe()
	if err != nil {
		return nil, os.NewError("exec: pipe fail")
	}
	go io.Copy(os.Stdout, p)
	err = cmd.Run()
	if err != nil {
		return nil, err
	}
	return emptyList, nil
}

func primExit(args ...Value) (Value, os.Error) {
	if len(args) != 1 || !numberp(args[0]) {
		return nil, os.NewError("exit: bad argument list")
	}
	os.Exit(int(args[0].(Number)))
	return nil, os.NewError("exit: failed to exit!")
}

func primReadAll(args ...Value) (val Value, err os.Error) {
	if len(args) != 1 || !stringp(args[0]) {
		return nil, os.NewError("readall: bad argument list")
	}
	defer func() {
		x := recover()
		if x == nil {
			return
		}
		if s, ok := x.(string); ok {
			err = os.NewError(s)
			return
		}
		panic(x)
	}()
	buf := bytes.NewBufferString(string(args[0].(String)))
	lits, err := readAll(buf)
	if err != nil {
		return
	}
	acc := emptyList
	for i := len(lits) - 1; i >= 0; i-- {
		acc = &List{lits[i].value(), acc}
	}
	return acc, nil
}

func primCompile(args ...Value) (val Value, err os.Error) {
	if len(args) != 1 {
		return nil, os.NewError("compile: wrong number of arguments")
	}
	defer func() {
		x := recover()
		if x == nil {
			return
		}
		if s, ok := x.(string); ok {
			err = os.NewError(s)
			return
		}
		panic(x)
	}()
	lit, err := args[0].literal()
	if err != nil {
		err = os.NewError("compile: type error")
	}
	return compile(parseExpr(lit))
}

var primDecls = [][]interface{}{
	{"symbolp x", primSymbolp},
	{"numberp x", primNumberp},
	{"stringp x", primStringp},
	{"boolp x", primBoolp},
	{"consp x", primConsp},
	{"templatep x", primTemplatep},
	{"funcp x", primFuncp},
	{"contp x", primContp},
	{"cellp x", primCellp},
	{"arrayp x", primArrayp},
	{"symbolname sym", primSymbolName},
	{"cons a d", primCons},
	{"car c", primCar},
	{"cdr c", primCdr},
	{"templatenew nvars freerefs code", primTemplateNew},
	{"templateopen temp", primTemplateOpen},
	{"funcnew temp env", primFuncNew},
	{"funcopen f", primFuncOpen},
	{"contopen c", primContOpen},
	{"arraynew size", primArrayNew},
	{"arrayget a i", primArrayGet},
	{"arrayput a i x", primArrayPut},
	{"arraylength a", primArrayLength},
	{"cellnew x", primCellNew},
	{"cellget c", primCellGet},
	{"cellput c x", primCellPut},
	{"strget s i", primStrGet},
	{"strcat args", primStrCat},
	{"strlength s", primStrLength},
	{"substringp sub str", primSubstringp},
	{"atoi s", primAtoi},
	{"itoa n", primItoa},
	{"intern name", primIntern},
	{"+ a b", primAdd},
	{"- a b", primSub},
	{"* a b", primMul},
	{"/ a b", primDiv},
	{"pow base expt", primPow},
	{"= a b", primEq},
	{"!= a b", primNeq},
	{"< a b", primLt},
	{"> a b", primGt},
	{"<= a b", primLe},
	{">= a b", primGe},
	{"log text", primLog},
	{"http method url args", primHttp},
	{"now", primNow},
	{"exec cmd args", primExec},
	{"exit code", primExit},
	{"readall str", primReadAll},
	{"compile expr", primCompile},
}

func define(name string, value Value) {
	globals[name] = value
}

func makePrim(decl []interface{}) *Template {
	protocol := decl[0].(string)
	parts := strings.Split(protocol, " ")
	name := parts[0]
	nargs := len(parts) - 1
	prim := decl[1].(func(...Value) (Value, os.Error))
	return newTemplate(
		name, nargs, nil,
		[]Instr{
			&primInstr{name, prim},
			&returnInstr{},
		},
		[]Value{},
	)
}

func loadPrims() {
	for _, decl := range primDecls {
		temp := makePrim(decl)
		define(temp.name, newFunc(temp, nil))
	}
	define("apply", newFunc(
		newTemplate(
			"apply", 2, nil,
			[]Instr{
				&localInstr{1},
				&pushInstr{},
				&localInstr{0},
				&shiftInstr{},
				&applyInstr{-1},
			},
			[]Value{},
		),
		nil,
	))
	define("call/cc", newFunc(
		newTemplate(
			"call/cc", 1, nil,
			[]Instr{
				&continuationInstr{},
				&pushInstr{},
				&localInstr{0},
				&shiftInstr{},
				&applyInstr{1},
			},
			[]Value{},
		),
		nil,
	))
	define("T", Bool(true))
	define("F", Bool(false))
}

/// reader

func nextLine(buf io.ByteScanner) {
	for {
		b, err := buf.ReadByte()
		if err != nil || b == '\n' {
			break
		}
	}
}

func skipws(buf io.ByteScanner) {
	for {
		b, err := buf.ReadByte()
		if err != nil {
			break
		}
		switch b {
		case ' ', '\t', '\n':
			continue
		case ';':
			nextLine(buf)
			continue
		}
		buf.UnreadByte()
		break
	}
}

func readAtom(buf io.ByteScanner) Literal {
	atomBuf := []byte{}
loop:
	for {
		b, err := buf.ReadByte()
		if err != nil {
			break
		}
		switch b {
		case '(', ')', '\'', '"', ' ', '\t', '\n':
			buf.UnreadByte()
			break loop
		}
		atomBuf = append(atomBuf, b)
	}
	if len(atomBuf) == 0 {
		panic("read: empty atom")
	}
	atom := string(atomBuf)
	n, err := strconv.Atof64(atom)
	if err == nil {
		return Number(n)
	}
	return intern(atom)
}

func readQuote(buf io.ByteScanner) Literal {
	x := read(buf)
	return newListLiteral(intern("quote"), x)
}

func readQuasi(buf io.ByteScanner) Literal {
	x := read(buf)
	return newListLiteral(intern("quasiquote"), x)
}

func readComma(buf io.ByteScanner) Literal {
	b, err := buf.ReadByte()
	if err != nil {
		panic("read: incomplete comma")
	}
	tag := intern("unquote")
	if b == '@' {
		tag = intern("unquotesplicing")
	} else {
		buf.UnreadByte()
	}
	x := read(buf)
	return newListLiteral(tag, x)
}

func readAmpersand(buf io.ByteScanner) Literal {
	skipws(buf)
	b, err := buf.ReadByte()
	if err != nil {
		panic("read: incomplete input")
	}
	if b != '(' {
		panic("read: ill-formed ampersand")
	}
	x := readList(buf)
	return newListLiteral(intern("ampersand"), x)
}

func readString(buf io.ByteScanner) Literal {
	strbuf := []byte{}
loop:
	for {
		b, err := buf.ReadByte()
		if err != nil {
			break
		}
		switch b {
		case '"':
			return String(string(strbuf))
		case '\\':
			b, err := buf.ReadByte()
			if err != nil {
				break loop
			}
			switch b {
			case 't':
				strbuf = append(strbuf, '\t')
			case 'n':
				strbuf = append(strbuf, '\n')
			case '\\':
				strbuf = append(strbuf, '\\')
			case '"':
				strbuf = append(strbuf, '"')
			default:
				panic("read: unknown escape")
			}
		default:
			strbuf = append(strbuf, b)
		}
	}
	panic("read: unterminated string")
	return String("")
}

func readList(buf io.ByteScanner) Literal {
	skipws(buf)
	items := []Literal{}
	for {
		b, err := buf.ReadByte()
		if err != nil {
			panic("read: premature end of file")
		}
		if b == ')' {
			break
		}
		buf.UnreadByte()
		items = append(items, read(buf))
		skipws(buf)
	}
	return newListLiteral(items...)
}

func read(buf io.ByteScanner) Literal {
	skipws(buf)
	b, err := buf.ReadByte()
	if err != nil {
		panic("read: premature end of file")
	}
	if b == ')' {
		panic("read: unmatched close-parenthesis")
	}
	if reader, ok := readTable[b]; ok {
		return reader(buf)
	}
	buf.UnreadByte()
	return readAtom(buf)
}

func readAll(r io.Reader) (lits []Literal, err os.Error) {
	defer func() {
		x := recover()
		if s, ok := x.(string); ok {
			err = os.NewError(s)
			return
		}
		if x != nil {
			panic(x)
		}
	}()
	buf := bufio.NewReader(r)
	lits = []Literal{}
	for {
		skipws(buf)
		if _, err := buf.ReadByte(); err != nil {
			break
		}
		_ = buf.UnreadByte()
		item := read(buf)
		lits = append(lits, item)
	}
	return lits, nil
}

type Literal interface {
	value() Value
	literalVariant()
}

type ListLiteral struct {
	items []Literal
}

func newListLiteral(items ...Literal) *ListLiteral {
	return &ListLiteral{items}
}

func (list *ListLiteral) empty() bool {
	return (len(list.items) == 0)
}

func (list *ListLiteral) head() Literal {
	return list.items[0]
}

func (list *ListLiteral) tail() Literal {
	return &ListLiteral{list.items[1:]}
}

func (list *ListLiteral) at(i int) Literal {
	return list.items[i]
}

func (list *ListLiteral) len() int {
	return len(list.items)
}

func (_ Number) literalVariant()       {}
func (_ String) literalVariant()       {}
func (_ *Symbol) literalVariant()      {}
func (_ *ListLiteral) literalVariant() {}

func (n Number) literal() (Literal, os.Error) {
	return n, nil
}

func (s String) literal() (Literal, os.Error) {
	return s, nil
}

func (s *Symbol) literal() (Literal, os.Error) {
	return s, nil
}

func (b Bool) literal() (Literal, os.Error) {
	return nil, os.NewError("not a literal")
}

func (list *List) literal() (Literal, os.Error) {
	items := make([]Literal, list.len())
	rest := list
	for i := 0; i < len(items); i++ {
		var err os.Error
		items[i], err = rest.head.literal()
		if err != nil {
			return nil, err
		}
		rest = rest.tail
	}
	return &ListLiteral{items}, nil
}

func (_ NonLiteral) literal() (Literal, os.Error) {
	return nil, os.NewError("not a literal")
}

func (n Number) value() Value {
	return n
}

func (s String) value() Value {
	return s
}

func (s *Symbol) value() Value {
	return s
}

func (x *ListLiteral) value() Value {
	tail := emptyList
	for i := x.len() - 1; i >= 0; i-- {
		tail = &List{x.at(i).value(), tail}
	}
	return tail
}

func parseCallExpr(form *ListLiteral) Expr {
	if form.empty() {
		panic("parseExpr: empty call")
	}
	funcExpr := parseExpr(form.head())
	argExprs := parseEach(form.items[1:])
	return CallExpr{funcExpr, argExprs}
}

func parseParams(lit Literal) []*Symbol {
	x, ok := lit.(*ListLiteral)
	if !ok {
		panic("parseExpr: ill-formed parameter list")
	}
	params := make([]*Symbol, x.len())
	for i, item := range x.items {
		params[i], ok = item.(*Symbol)
		if !ok {
			panic("parseExpr: bad parameter")
		}
	}
	return params
}

func parseInits(lit Literal) []InitPair {
	list, ok := lit.(*ListLiteral)
	if !ok || list.empty() {
		panic("parseExpr: ill-formed init list")
	}
	inits := make([]InitPair, list.len())
	for i, item := range list.items {
		pair, ok := item.(*ListLiteral)
		if !ok || pair.len() != 2 {
			panic("parseExpr: ill-formed init list")
		}
		inits[i].name, ok = pair.head().(*Symbol)
		inits[i].expr = parseExpr(pair.at(1))
	}
	return inits
}

func parseEach(forms []Literal) []Expr {
	exprs := make([]Expr, len(forms))
	for i, form := range forms {
		exprs[i] = parseExpr(form)
	}
	return exprs
}

func parseCondClause(form Literal) CondClause {
	list, ok := form.(*ListLiteral)
	if !ok || list.len() < 2 {
		panic("parseExpr: ill-formed cond clause")
	}
	head := list.head()
	if head == intern("else") {
		return CondClause{
			QuoteExpr{Bool(true)},
			parseEach(list.items[1:]),
		}
	}
	return CondClause{
		parseExpr(head),
		parseEach(list.items[1:]),
	}
}

func analyzeUnquotesplicing(lit Literal) (Literal, bool) {
	form, ok := lit.(*ListLiteral)
	if !ok || form.len() != 2 {
		return nil, false
	}
	if form.head() == Literal(intern("unquotesplicing")) {
		return form.at(1), true
	}
	return nil, false
}

func expandQuasi(lit Literal) Literal {
	switch lit.(type) {
	case Number:
		return lit
	case String:
		return lit
	case *Symbol:
		return newListLiteral(intern("quote"), lit)
	}
	x := lit.(*ListLiteral)
	if x.empty() {
		return newListLiteral(intern("quote"), lit)
	}
	head := x.head()
	if head == intern("unquote") {
		if x.len() != 2 {
			panic("expandQuasi: ill-formed unquote")
		}
		return x.at(1)
	}
	if head == intern("quasiquote") {
		if x.len() != 2 {
			panic("expandQuasi: ill-formed quasiquote")
		}
		return expandQuasi(expandQuasi(x.at(1)))
	}
	if subLit, ok := analyzeUnquotesplicing(head); ok {
		return newListLiteral(
			intern("append"),
			subLit,
			expandQuasi(x.tail()),
		)
	}
	return newListLiteral(
		intern("cons"),
		expandQuasi(head),
		expandQuasi(x.tail()),
	)
}

func parseMatchClause(lit Literal) MatchClause {
	var clause MatchClause
	x, ok := lit.(*ListLiteral)
	if !ok || x.len() < 2 {
		panic("parseExpr: ill-formed match clause")
	}
	sym, ok := x.head().(*Symbol)
	if ok && sym == intern("else") {
		// TODO - this is awkward
		clause.tag = sym
		clause.params = []*Symbol{}
		clause.body = parseEach(x.items[1:])
		return clause
	}
	pattern, ok := x.head().(*ListLiteral)
	if !ok || pattern.empty() {
		panic("parseExpr: ill-formed match clause")
	}
	clause.tag, ok = pattern.head().(*Symbol)
	if !ok {
		panic("parseExpr: ill-formed match clause")
	}
	clause.params = make([]*Symbol, pattern.len()-1)
	for i, item := range pattern.items[1:] {
		clause.params[i], ok = item.(*Symbol)
		if !ok {
			panic("parseExpr: ill-formed match clause")
		}
	}
	clause.body = parseEach(x.items[1:])
	return clause
}

func parseExpr(lit Literal) Expr {
	switch x := lit.(type) {
	case Number:
		return QuoteExpr{x}
	case String:
		return QuoteExpr{x}
	case *Symbol:
		return RefExpr{x}
	}
	x, ok := lit.(*ListLiteral)
	if !ok {
		panic("parseExpr: nonliteral")
	}
	if x.empty() {
		panic("parseExpr: empty expression")
	}
	head, ok := x.head().(*Symbol)
	if !ok {
		return parseCallExpr(x)
	}
	if head == intern("quasiquote") {
		if x.len() != 2 {
			panic("parseExpr: ill-formed quasiquote")
		}
		return parseExpr(expandQuasi(x.at(1)))
	}
	if head == intern("ampersand") {
		if x.len() != 2 {
			panic("parseExpr: ill-formed ampersand")
		}
		list, ok := x.at(1).(*ListLiteral)
		if !ok {
			panic("parseExpr: ill-formed ampersand")
		}
		return AmpersandExpr{parseEach(list.items)}
	}
	if head == intern("quote") {
		if x.len() != 2 {
			panic("parseExpr: ill-formed quote")
		}
		return QuoteExpr{x.at(1).value()}
	}
	if head == intern("if") {
		if x.len() != 4 {
			panic("parseExpr: ill-formed if")
		}
		return IfExpr{
			parseExpr(x.at(1)),
			parseExpr(x.at(2)),
			parseExpr(x.at(3)),
		}
	}
	if head == intern("begin") {
		if x.len() < 2 {
			panic("parseExpr: ill-formed begin")
		}
		body := parseEach(x.items[1:])
		return BeginExpr{body}
	}
	if head == intern("jmp") {
		if x.len() != 2 {
			panic("parseExpr: ill-formed jmp")
		}
		return JmpExpr{parseExpr(x.at(1))}
	}
	if head == intern("func") {
		if x.len() < 3 {
			panic("parseExpr: ill-formed func")
		}
		params := parseParams(x.at(1))
		body := parseEach(x.items[2:])
		return FuncExpr{params, body}
	}
	if head == intern("let") {
		if x.len() < 3 {
			panic("parseExpr: ill-formed let")
		}
		inits := parseInits(x.at(1))
		body := parseEach(x.items[2:])
		return LetExpr{inits, body}
	}
	if head == intern("define") {
		if x.len() < 3 {
			panic("parseExpr: ill-formed define")
		}
		switch pattern := x.at(1).(type) {
		case *Symbol:
			return DefineExpr{pattern, parseExpr(x.at(2))}
		case *ListLiteral:
			if pattern.empty() {
				panic("parseExpr: ill-formed define")
			}
			name, ok := pattern.head().(*Symbol)
			if !ok {
				panic("parseExpr: ill-formed define")
			}
			funcExpr := FuncExpr{
				parseParams(pattern.tail()),
				parseEach(x.items[2:]),
			}
			return DefineExpr{name, funcExpr}
		}
		panic("parseExpr: ill-formed define")
	}
	if head == intern("cond") {
		if x.len() < 2 {
			panic("parseExpr: ill-formed cond")
		}
		clauses := make([]CondClause, x.len()-1)
		for i, item := range x.items[1:] {
			clauses[i] = parseCondClause(item)
		}
		return CondExpr{clauses}
	}
	if head == intern("and") {
		return AndExpr{parseEach(x.items[1:])}
	}
	if head == intern("or") {
		return OrExpr{parseEach(x.items[1:])}
	}
	if head == intern("match") {
		if x.len() < 3 {
			panic("parseExpr: ill-formed match")
		}
		clauses := make([]MatchClause, x.len()-2)
		for i, item := range x.items[2:] {
			clauses[i] = parseMatchClause(item)
		}
		return MatchExpr{
			parseExpr(x.at(1)),
			clauses,
		}
	}
	return parseCallExpr(x)
}

func parse(lit Literal) (_ Expr, err os.Error) {
	defer func() {
		x := recover()
		if s, ok := x.(string); ok {
			err = os.NewError(s)
			return
		}
		if x != nil {
			panic(x)
		}
	}()
	return parseExpr(lit), nil
}

type Expr interface {
	exprVariant()
}

type RefExpr struct {
	name *Symbol
}

type QuoteExpr struct {
	x Value
}

type AmpersandExpr struct {
	exprs []Expr
}

type IfExpr struct {
	condExpr Expr
	thenExpr Expr
	elseExpr Expr
}

type BeginExpr struct {
	body []Expr
}

type JmpExpr struct {
	expr Expr
}

type FuncExpr struct {
	params []*Symbol
	body   []Expr
}

type CallExpr struct {
	funcExpr Expr
	argExprs []Expr
}

type InitPair struct {
	name *Symbol
	expr Expr
}

type LetExpr struct {
	inits []InitPair
	body  []Expr
}

type DefineExpr struct {
	name *Symbol
	expr Expr
}

type CondClause struct {
	condExpr Expr
	thenBody []Expr
}

type CondExpr struct {
	clauses []CondClause
}

type AndExpr struct {
	exprs []Expr
}

type OrExpr struct {
	exprs []Expr
}

type MatchClause struct {
	tag    *Symbol
	params []*Symbol
	body   []Expr
}

type MatcherExpr struct {
	clauses []MatchClause
}

type MatchExpr struct {
	x       Expr
	clauses []MatchClause
}

type QuasiExpr struct {
	expr Expr
}

func (_ AmpersandExpr) exprVariant() {}
func (_ LetExpr) exprVariant()       {}
func (_ DefineExpr) exprVariant()    {}
func (_ CondExpr) exprVariant()      {}
func (_ AndExpr) exprVariant()       {}
func (_ OrExpr) exprVariant()        {}
func (_ MatcherExpr) exprVariant()   {}
func (_ MatchExpr) exprVariant()     {}
func (_ QuasiExpr) exprVariant()     {}
func (_ RefExpr) exprVariant()       {}
func (_ QuoteExpr) exprVariant()     {}
func (_ IfExpr) exprVariant()        {}
func (_ BeginExpr) exprVariant()     {}
func (_ JmpExpr) exprVariant()       {}
func (_ FuncExpr) exprVariant()      {}
func (_ CallExpr) exprVariant()      {}

type MacroExpr interface {
	expand() Expr
	macroExprVariant()
}

func (_ AmpersandExpr) macroExprVariant() {}
func (_ LetExpr) macroExprVariant()       {}
func (_ CondExpr) macroExprVariant()      {}
func (_ AndExpr) macroExprVariant()       {}
func (_ OrExpr) macroExprVariant()        {}
func (_ MatcherExpr) macroExprVariant()   {}
func (_ MatchExpr) macroExprVariant()     {}
func (_ QuasiExpr) macroExprVariant()     {}

func (expr AmpersandExpr) expand() Expr {
	acc := Expr(QuoteExpr{emptyList})
	for i := len(expr.exprs) - 1; i >= 0; i-- {
		acc = CallExpr{
			RefExpr{intern("cons")},
			[]Expr{
				expr.exprs[i],
				acc,
			},
		}
	}
	return acc
}

func (expr LetExpr) expand() Expr {
	params := make([]*Symbol, len(expr.inits))
	argExprs := make([]Expr, len(expr.inits))
	for i, init := range expr.inits {
		params[i] = init.name
		argExprs[i] = init.expr
	}
	return CallExpr{
		FuncExpr{params, expr.body},
		argExprs,
	}
}

func (expr CondExpr) expand() Expr {
	acc := Expr(QuoteExpr{emptyList})
	clauses := expr.clauses
	for i := len(clauses) - 1; i >= 0; i-- {
		acc = IfExpr{
			clauses[i].condExpr,
			BeginExpr{clauses[i].thenBody},
			acc,
		}
	}
	return acc
}

func (expr AndExpr) expand() Expr {
	acc := Expr(QuoteExpr{Bool(true)})
	for i := len(expr.exprs) - 1; i >= 0; i-- {
		acc = IfExpr{
			expr.exprs[i],
			acc,
			QuoteExpr{emptyList},
		}
	}
	return acc
}

func (expr OrExpr) expand() Expr {
	acc := Expr(QuoteExpr{emptyList})
	for i := len(expr.exprs) - 1; i >= 0; i-- {
		acc = IfExpr{
			expr.exprs[i],
			QuoteExpr{Bool(true)},
			acc,
		}
	}
	return acc
}

func (expr MatchExpr) expand() Expr {
	i := len(expr.clauses) - 1
	clause := expr.clauses[i]
	var acc Expr
	var defaultExpr Expr // XXX - code gets duplicated in the expansion
	if clause.tag == intern("else") {
		funcExpr := FuncExpr{
			[]*Symbol{intern("tag"), intern("args")},
			[]Expr{CallExpr{RefExpr{intern("f")}, []Expr{}}},
		}
		acc = LetExpr{
			[]InitPair{{
				intern("f"),
				FuncExpr{
					[]*Symbol{},
					clause.body,
				},
			}},
			[]Expr{funcExpr},
		}
		defaultExpr = BeginExpr{clause.body}
		i--
	} else {
		acc = FuncExpr{
			[]*Symbol{intern("tag"), intern("args")},
			[]Expr{CallExpr{
				RefExpr{intern("throw")},
				[]Expr{QuoteExpr{String("match: no match")}},
			}},
		}
		defaultExpr = CallExpr{
			RefExpr{intern("throw")},
			[]Expr{QuoteExpr{String("match: no match")}},
		}
	}
	for i >= 0 {
		funcExpr := FuncExpr{
			[]*Symbol{intern("tag"), intern("args")},
			[]Expr{IfExpr{
				CallExpr{
					RefExpr{intern("=")},
					[]Expr{
						RefExpr{intern("tag")},
						QuoteExpr{expr.clauses[i].tag},
					},
				},
				CallExpr{
					RefExpr{intern("apply")},
					[]Expr{
						RefExpr{intern("f")},
						RefExpr{intern("args")},
					},
				},
				CallExpr{
					RefExpr{intern("g")},
					[]Expr{
						RefExpr{intern("tag")},
						RefExpr{intern("args")},
					},
				},
			}},
		}
		acc = LetExpr{
			[]InitPair{{
				intern("f"),
				FuncExpr{
					expr.clauses[i].params,
					expr.clauses[i].body,
				},
			}, {
				intern("g"),
				acc,
			}},
			[]Expr{funcExpr},
		}
		i--
	}
	return LetExpr{
		[]InitPair{{intern("x"), expr.x}},
		[]Expr{IfExpr{
			CallExpr{
				RefExpr{intern("consp")},
				[]Expr{RefExpr{intern("x")}},
			},
			CallExpr{
				acc,
				[]Expr{
					CallExpr{
						RefExpr{intern("car")},
						[]Expr{RefExpr{intern("x")}},
					},
					CallExpr{
						RefExpr{intern("cdr")},
						[]Expr{RefExpr{intern("x")}},
					},
				},
			},
			defaultExpr,
		}},
	}
}

/// compiler

type Asm interface {
	asmVariant()
}

type AsmLabel struct {
	// Pointer identity is all that matters.
}

type AsmInstr struct {
	instr Instr
	label *AsmLabel // May be nil.
}

func (asm *AsmLabel) asmVariant() {}
func (asm *AsmInstr) asmVariant() {}

func (asm *AsmInstr) link(labels map[*AsmLabel]int) Instr {
	switch instr := asm.instr.(type) {
	case *frameInstr:
		instr.pc = labels[asm.label]
	case *fjumpInstr:
		instr.pc = labels[asm.label]
	case *jumpInstr:
		instr.pc = labels[asm.label]
	}
	return asm.instr
}

func assemble(asmCode []Asm) []Instr {
	labels := make(map[*AsmLabel]int)
	i := 0
	for _, asm := range asmCode {
		switch asm := asm.(type) {
		case *AsmLabel:
			labels[asm] = i
		case *AsmInstr:
			i++
		}
	}
	code := make([]Instr, i)
	i = 0
	for _, asm := range asmCode {
		switch asm := asm.(type) {
		case *AsmInstr:
			code[i] = asm.link(labels)
			i++
		}
	}
	return code
}

func newLabel() *AsmLabel {
	return new(AsmLabel)
}

func newPushAsm() Asm {
	return &AsmInstr{&pushInstr{}, nil}
}

func newReturnAsm() Asm {
	return &AsmInstr{&returnInstr{}, nil}
}

func newGlobalAsm(n int) Asm {
	return &AsmInstr{&globalInstr{n}, nil}
}

func newConstAsm(x Value) Asm {
	return &AsmInstr{&constInstr{x}, nil}
}

func newFrameAsm(label *AsmLabel) Asm {
	return &AsmInstr{&frameInstr{-1}, label}
}

func newShiftAsm() Asm {
	return &AsmInstr{&shiftInstr{}, nil}
}

func newApplyAsm(nargs int) Asm {
	return &AsmInstr{&applyInstr{nargs}, nil}
}

func newJumpAsm(label *AsmLabel) Asm {
	return &AsmInstr{&jumpInstr{-1}, label}
}

func newFjumpAsm(label *AsmLabel) Asm {
	return &AsmInstr{&fjumpInstr{-1}, label}
}

func newCloseAsm(temp *Template) Asm {
	return &AsmInstr{&closeInstr{temp}, nil}
}

func newLocalAsm(i int) Asm {
	return &AsmInstr{&localInstr{i}, nil}
}

func newFreeAsm(i int) Asm {
	return &AsmInstr{&freeInstr{i}, nil}
}

func seq(seqs ...[]Asm) []Asm {
	code := []Asm{}
	for _, seq := range seqs {
		code = append(code, seq...)
	}
	return code
}

func gen(code ...Asm) []Asm {
	return code
}

const (
	NONTAIL = iota
	TAIL
	JMP
)

// Only for use when the tail expression is not a call.
func genReturn(argp bool, tailp int) []Asm {
	code := make([]Asm, 0, 2)
	if argp {
		code = append(code, newPushAsm())
	}
	if tailp != NONTAIL {
		code = append(code, newReturnAsm())
	}
	return code
}

type CompEnv struct {
	local, free, global map[*Symbol]int
}

func newEmptyEnv() *CompEnv {
	return &CompEnv{
		local:  make(map[*Symbol]int),
		free:   make(map[*Symbol]int),
		global: make(map[*Symbol]int),
	}
}

func (env *CompEnv) symbolSet() *SymbolSet {
	local := make([]*Symbol, len(env.local))
	free := make([]*Symbol, len(env.free))
	for sym, i := range env.local {
		local[i] = sym
	}
	for sym, i := range env.free {
		free[i] = sym
	}
	return newSymbolSet(local, free)
}

func (env *CompEnv) globals() []Value {
	g := make([]Value, len(env.global))
	for sym, i := range env.global {
		g[i] = sym
	}
	return g
}

type SymbolSet struct {
	table map[*Symbol]bool
}

func newSymbolSet(lists ...[]*Symbol) *SymbolSet {
	table := make(map[*Symbol]bool)
	for _, list := range lists {
		for _, sym := range list {
			table[sym] = true
		}
	}
	return &SymbolSet{table}
}

func (set *SymbolSet) contains(sym *Symbol) bool {
	_, ok := set.table[sym]
	return ok
}

func (set *SymbolSet) include(sym *Symbol) {
	set.table[sym] = true
}

func (set1 *SymbolSet) union(set2 *SymbolSet) *SymbolSet {
	u := newSymbolSet()
	for sym, _ := range set1.table {
		u.include(sym)
	}
	for sym, _ := range set2.table {
		u.include(sym)
	}
	return u
}

func (set *SymbolSet) remove(sym *Symbol) {
	set.table[sym] = false, false
}

func (set1 *SymbolSet) minus(set2 *SymbolSet) *SymbolSet {
	acc := newSymbolSet()
	for sym, _ := range set1.table {
		if !set2.contains(sym) {
			acc.include(sym)
		}
	}
	return acc
}

func collectFree(exprs []Expr, b, p *SymbolSet) *SymbolSet {
	refs := newSymbolSet()
	for _, expr := range exprs {
		refs = refs.union(findFree(expr, b, p))
	}
	return refs
}

func findFree(expr Expr, b, p *SymbolSet) *SymbolSet {
	refs := newSymbolSet()
	switch expr := expr.(type) {
	case RefExpr:
		if b.contains(expr.name) && !p.contains(expr.name) {
			refs.include(expr.name)
		}
	case IfExpr:
		refs = findFree(expr.condExpr, b, p)
		refs = refs.union(findFree(expr.thenExpr, b, p))
		refs = refs.union(findFree(expr.elseExpr, b, p))
	case BeginExpr:
		refs = collectFree(expr.body, b, p)
	case JmpExpr:
		refs = findFree(expr.expr, b, p)
	case FuncExpr:
		refs = collectFree(expr.body, b, newSymbolSet(expr.params))
		refs = refs.minus(p)
	case CallExpr:
		refs = findFree(expr.funcExpr, b, p)
		refs = refs.union(collectFree(expr.argExprs, b, p))
	}
	return refs
}

func collectGlobals(globals map[*Symbol]int, nonglobals *SymbolSet, exprs []Expr) {
	for _, expr := range exprs {
		findGlobals(globals, nonglobals, expr)
	}
}

func findGlobals(globals map[*Symbol]int, nonglobals *SymbolSet, expr Expr) {
	switch expr := expr.(type) {
	case RefExpr:
		sym := expr.name
		if nonglobals.contains(sym) {
			return
		}
		_, ok := globals[sym]
		if !ok {
			if !definedGlobals.contains(sym) {
				panic("findGlobals: undefined global " +
					sym.name)
			}
			globals[sym] = len(globals)
		}
	case IfExpr:
		findGlobals(globals, nonglobals, expr.condExpr)
		findGlobals(globals, nonglobals, expr.thenExpr)
		findGlobals(globals, nonglobals, expr.elseExpr)
	case BeginExpr:
		collectGlobals(globals, nonglobals, expr.body)
	case JmpExpr:
		findGlobals(globals, nonglobals, expr.expr)
	case CallExpr:
		findGlobals(globals, nonglobals, expr.funcExpr)
		collectGlobals(globals, nonglobals, expr.argExprs)
	}
}

func analyzeRefs(env *CompEnv, locals []*Symbol, body []Expr) (*CompEnv, []FreeRef) {
	freshEnv := newEmptyEnv()
	freeRefs := []FreeRef{}
	refs := collectFree(body, env.symbolSet(), newSymbolSet(locals))
	nonglobals := newSymbolSet(locals).union(refs)
	collectGlobals(freshEnv.global, nonglobals, body)
	nfree := 0
	for i, sym := range locals {
		freshEnv.local[sym] = i
	}
	for ref, _ := range refs.table {
		if i, ok := env.local[ref]; ok {
			freeRefs = append(freeRefs, FreeRef{LOCAL, i})
			freshEnv.free[ref] = nfree
			nfree++
			continue
		}
		if i, ok := env.free[ref]; ok {
			freeRefs = append(freeRefs, FreeRef{FREE, i})
			freshEnv.free[ref] = nfree
			nfree++
			continue
		}
	}
	return freshEnv, freeRefs
}

func newRefAsm(env *CompEnv, sym *Symbol) Asm {
	if i, ok := env.local[sym]; ok {
		return newLocalAsm(i)
	}
	if i, ok := env.free[sym]; ok {
		return newFreeAsm(i)
	}
	if i, ok := env.global[sym]; ok {
		return newGlobalAsm(i)
	}
	panic("newRefAsm: cannot locate variable " + sym.name)
	return nil
}

func compFuncExpr(expr FuncExpr, env *CompEnv) *Template {
	body := BeginExpr{expr.body}
	nvars := len(expr.params)
	funcEnv, freeRefs := analyzeRefs(env, expr.params, expr.body)
	code := assemble(compExpr(body, funcEnv, false, TAIL))
	return newTemplate("", nvars, freeRefs, code, funcEnv.globals())
}

func compExpr(expr Expr, env *CompEnv, argp bool, tailp int) []Asm {
	switch expr := expr.(type) {
	case QuoteExpr:
		return seq(
			gen(newConstAsm(expr.x)),
			genReturn(argp, tailp),
		)
	case RefExpr:
		return seq(
			gen(newRefAsm(env, expr.name)),
			genReturn(argp, tailp),
		)
	case IfExpr:
		label0 := newLabel()
		label1 := newLabel()
		var jump1Seq, label1Seq, pushSeq []Asm
		if tailp == NONTAIL {
			jump1Seq = gen(newJumpAsm(label1))
			label1Seq = gen(label1)
		}
		if argp {
			pushSeq = gen(newPushAsm())
		}
		return seq(
			compExpr(expr.condExpr, env, false, NONTAIL),
			gen(newFjumpAsm(label0)),
			compExpr(expr.thenExpr, env, false, tailp),
			jump1Seq,
			gen(label0),
			compExpr(expr.elseExpr, env, false, tailp),
			label1Seq,
			pushSeq,
		)
	case BeginExpr:
		body := expr.body
		asms := seq()
		n := len(body)
		for i := 0; i < n-1; i++ {
			asms = seq(
				asms,
				compExpr(body[i], env, false, NONTAIL),
			)
		}
		return seq(asms, compExpr(body[n-1], env, argp, tailp))
	case JmpExpr:
		return compExpr(expr.expr, env, argp, JMP)
	case FuncExpr:
		temp := compFuncExpr(expr, env)
		return seq(
			gen(newCloseAsm(temp)),
			genReturn(argp, tailp),
		)
	case CallExpr:
		label := newLabel()
		frameSeq := gen(newFrameAsm(label))
		argsSeq := gen()
		funcSeq := compExpr(expr.funcExpr, env, false, NONTAIL)
		shiftSeq := gen()
		applySeq := gen(newApplyAsm(len(expr.argExprs)))
		labelSeq := gen(label)
		tailSeq := gen()
		for _, argExpr := range expr.argExprs {
			argsSeq = seq(
				argsSeq,
				compExpr(argExpr, env, true, NONTAIL),
			)
		}
		if tailp == JMP {
			frameSeq = gen()
			shiftSeq = gen(newShiftAsm())
			labelSeq = gen()
		} else if tailp == TAIL {
			tailSeq = gen(newReturnAsm())
		} else if argp {
			tailSeq = gen(newPushAsm())
		}
		return seq(
			frameSeq,
			argsSeq,
			funcSeq,
			shiftSeq,
			applySeq,
			labelSeq,
			tailSeq,
		)
	}
	panic("compile: unexpected expression")
	return []Asm{}
}

func compile(expr Expr) (temp *Template, err os.Error) {
	defer func() {
		x := recover()
		if s, ok := x.(string); ok {
			err = os.NewError(s)
			return
		}
		if x != nil {
			panic(x)
		}
	}()
	temp = compFuncExpr(
		FuncExpr{[]*Symbol{}, []Expr{macroexpandall(expr)}},
		newEmptyEnv(),
	)
	temps := findTemplates(temp)
	for _, temp := range temps {
		linkTemplate(temp, bindingsKludge)
	}
	return
}

func macroexpandall(expr Expr) Expr {
	for {
		macro, ok := expr.(MacroExpr)
		if !ok {
			break
		}
		expr = macro.expand()
	}
	switch core := expr.(type) {
	case QuoteExpr:
		return core
	case RefExpr:
		return core
	case IfExpr:
		return IfExpr{
			condExpr: macroexpandall(core.condExpr),
			thenExpr: macroexpandall(core.thenExpr),
			elseExpr: macroexpandall(core.elseExpr),
		}
	case BeginExpr:
		body := make([]Expr, len(core.body))
		for i, subexpr := range core.body {
			body[i] = macroexpandall(subexpr)
		}
		return BeginExpr{body}
	case JmpExpr:
		return JmpExpr{macroexpandall(core.expr)}
	case FuncExpr:
		body := make([]Expr, len(core.body))
		for i, subexpr := range core.body {
			body[i] = macroexpandall(subexpr)
		}
		return FuncExpr{
			core.params,
			body,
		}
	case CallExpr:
		argExprs := make([]Expr, len(core.argExprs))
		for i, argExpr := range core.argExprs {
			argExprs[i] = macroexpandall(argExpr)
		}
		return CallExpr{
			macroexpandall(core.funcExpr),
			argExprs,
		}
	}
	panic("macroexpandall: unexpected expression")
	return QuoteExpr{emptyList}
}

/// loading

func fetchSourceForms(name, address string) ([]Literal, os.Error) {
	url := "http://" + address + "/" + name + ".lisp"
	response, err := http.Get(url)
	if err != nil {
		return nil, os.NewError("fetchSourceModule: HTTP fail")
	}
	defer response.Body.Close()
	return readAll(response.Body)
}

func parseToplevel(forms []Literal) ([]DefineExpr, os.Error) {
	defs := make([]DefineExpr, len(forms))
	for i, form := range forms {
		expr, err := parse(form)
		if err != nil {
			return nil, err
		}
		def, ok := expr.(DefineExpr)
		if !ok {
			err = os.NewError("parseToplevel: form is not define")
			return nil, err
		}
		defs[i] = def
	}
	return defs, nil
}

func checkBindingUniqueness(defs []DefineExpr) (*SymbolSet, os.Error) {
	set := newSymbolSet()
	for _, def := range defs {
		if set.contains(def.name) {
			return nil, os.NewError("multiple definitions for: " +
				def.name.name)
		}
		set.include(def.name)
	}
	return set, nil
}

func analyzeCellLiteral(expr CallExpr) (Expr, os.Error) {
	ref, ok := expr.funcExpr.(RefExpr)
	if !ok || ref.name != intern("cellnew") {
		return nil, os.NewError("bad cell literal")
	}
	if len(expr.argExprs) != 1 {
		s := "fetchSourceModule: bad cell literal"
		return nil, os.NewError(s)
	}
	initExpr := expr.argExprs[0]
	return initExpr, nil
}

func findTemplates(temp *Template) []*Template {
	temps := []*Template{temp}
	for _, instr := range temp.code {
		if c, ok := instr.(*closeInstr); ok {
			temps = append(temps, findTemplates(c.temp)...)
		}
	}
	return temps
}

func linkTemplate(temp *Template, bindings map[*Symbol]Value) {
	globals := temp.globals
	for i, g := range globals {
		globals[i] = bindings[g.(*Symbol)]
	}
}

func build(forms []Literal) (map[*Symbol]Value, os.Error) {
	defs, err := parseToplevel(forms)
	if err != nil {
		return nil, err
	}
	bindings := make(map[*Symbol]Value)
	deps := make(map[*Symbol][]*Symbol)
	thunks := make(map[*Symbol]func())
	aliasThunk := func(alias, original *Symbol) func() {
		return func() {
			bindings[alias] = bindings[original]
		}
	}
	definedGlobals, err = checkBindingUniqueness(defs)
	if err != nil {
		return nil, err
	}
	for name, val := range globals {
		definedGlobals.include(intern(name))
		bindings[intern(name)] = val
	}
	for _, def := range defs {
		switch expr := def.expr.(type) {
		case FuncExpr:
			f := newFunc(
				compFuncExpr(
					macroexpandall(expr).(FuncExpr),
					newEmptyEnv(),
				),
				[]Value{},
			)
			bindings[def.name] = f
			f.temp.name = def.name.name
		case RefExpr:
			deps[def.name] = []*Symbol{expr.name}
			thunks[def.name] = aliasThunk(def.name, expr.name)
		case CallExpr:
			initExpr, err := analyzeCellLiteral(expr)
			if err != nil {
				return nil, err
			}
			cell := new(Cell)
			bindings[def.name] = cell
			switch arg := initExpr.(type) {
			case RefExpr:
				deps[def.name] = []*Symbol{arg.name}
				thunks[def.name] = func() {
					cell.value = bindings[arg.name]
				}
			case QuoteExpr:
				cell.value = arg.x
			default:
				return nil, os.NewError("bad cell literal")
			}
		}
	}
	// XXX this only works when dependencies never have dependencies
	updated := newSymbolSet()
	for _, def := range defs {
		for _, name := range append(deps[def.name], def.name) {
			thunk, ok := thunks[name]
			if !ok || updated.contains(name) {
				continue
			}
			thunk()
			updated.include(name)
		}
	}
	linked := make(map[*Template]bool)
	for _, val := range bindings {
		f, ok := val.(*Func)
		if !ok {
			continue
		}
		temps := findTemplates(f.temp)
		for _, temp := range temps {
			if _, ok := linked[temp]; ok {
				continue
			}
			linkTemplate(temp, bindings)
			linked[temp] = true
		}
	}
	bindingsKludge = bindings
	return bindings, nil
}

func loadSourceFile(name string) os.Error {
	forms, err := fetchSourceForms(name, *address)
	if err != nil {
		return err
	}
	bindings, err := build(forms)
	if err != nil {
		return err
	}
	for sym, value := range bindings {
		globals[sym.name] = value // TODO remove this
	}
	x, ok := bindings[intern("main")]
	if !ok {
		return nil
	}
	mainFunc, ok := x.(*Func)
	if !ok {
		return os.NewError("loadSourceFile: main is not a function")
	}
	m := newMachine(mainFunc)
	m.run()
	return nil
}

func initReader() {
	readTable = map[byte]func(io.ByteScanner) Literal{
		'"':  readString,
		'\'': readQuote,
		'`':  readQuasi,
		',':  readComma,
		'&':  readAmpersand,
		'(':  readList,
	}
}

func initInterpreter() {
	sharedPrimStack = make([]Value, 8)
	globals = make(map[string]Value)
	symbolTable = make(map[string]*Symbol)
	loadPrims()
}

func init() {
	initReader()
	initInterpreter()
}

func main() {
	flag.Parse()
	for _, name := range flag.Args() {
		err := loadSourceFile(name)
		if err != nil {
			log.Fatalln(err)
		}
	}
}
