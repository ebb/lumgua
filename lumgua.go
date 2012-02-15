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
	"reflect"
	//	"runtime/debug"
	"strconv"
	"strings"
	"time"
	"url"
)

/// command-line arguments

var address *string = flag.String("a", ":8082", "address")

/// global state

var globals map[string]*Binding

var symbolTable map[string]*Symbol

var readTable map[byte]func(io.ByteScanner) Literal

/// lisp types

type Value interface{}

type Symbol struct {
	name string
}

type Number float64

type String string

type Cons struct {
	car, cdr Value
}

type Nil struct{}

type Template struct {
	name     string
	nvars    int
	dottedp  bool
	freeRefs []FreeRef
	code     []Instr
}

type Func struct {
	temp *Template
	env  []Value
}

type Cont struct {
	stack Stack
}

type Cell struct {
	value Value
}

type Array struct {
	vector.Vector
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
	_, ok = x.(Nil)
	return
}

func stringp(x Value) (ok bool) {
	_, ok = x.(String)
	return
}

func consp(x Value) (ok bool) { _, ok = x.(*Cons); return }

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

/// lisp data accessors

func car(x Value) (Value, os.Error) {
	c, ok := x.(*Cons)
	if !ok {
		return nil, os.NewError("car: type error")
	}
	return c.car, nil
}

func cdr(x Value) (Value, os.Error) {
	c, ok := x.(*Cons)
	if !ok {
		return nil, os.NewError("cdr: type error")
	}
	return c.cdr, nil
}

/// conversion

func list(elements ...Value) Value {
	x := Value(Nil{})
	for i := len(elements) - 1; i >= 0; i-- {
		x = &Cons{elements[i], x}
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
		if !pred(a.At(i)) {
			return nil, os.NewError("tuple: bad argument")
		}
	}
	return a, nil
}

/// combinators

func forEach(x Value, f func(Value) os.Error) os.Error {
	for {
		switch z := x.(type) {
		case Nil:
			return nil
		case *Cons:
			err := f(z.car)
			if err != nil {
				return err
			}
			x = z.cdr
		default:
			return os.NewError("bad list")
		}
	}
	return nil
}

func listMap(x Value, f func(Value) Value) Value {
	switch z := x.(type) {
	case Nil:
		return Nil{}
	case *Cons:
		return &Cons{f(z.car), listMap(z.cdr, f)}
	}
	panic("listMap: unexpected non-list argument")
	return Nil{}
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
	m.a = &Cont{
		Stack{*stack},
	}
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
		m.a = &Func{instr.temp, nil}
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
	m.a = &Func{instr.temp, env}
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
	if m.f.temp.dottedp {
		nremove++
	}
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

func (m *Machine) prepareApplyArgs(nvars int, dottedp bool) {
	rest := m.stack.Pop().(Value)
	for i := 0; i < nvars; i++ {
		switch x := rest.(type) {
		case Nil:
			m.throw("too few arguments")
			return
		case *Cons:
			m.stack.Push(x.car)
			rest = x.cdr
		default:
			m.throw("bad argument list")
			return
		}
	}
	if dottedp {
		m.stack.Push(rest)
	} else if !nilp(rest) {
		m.throw("too many arguments")
	}
}

func (m *Machine) prepareArgs(nargs, nvars int, dottedp bool) {
	if nargs == -1 {
		m.prepareApplyArgs(nvars, dottedp)
		return
	}
	if nargs < nvars {
		m.throw("too few arguments")
	}
	if nargs > nvars && !dottedp {
		m.throw("too many arguments")
	}
	if dottedp {
		rest := Value(Nil{})
		for i := nargs; i > nvars; i-- {
			arg := m.stack.Pop().(Value)
			rest = &Cons{arg, rest}
		}
		m.stack.Push(rest)
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
	m.prepareArgs(nargs, temp.nvars, temp.dottedp)
}

func (m *Machine) applyCont(c *Cont) {
	ret := returnInstr{}
	m.a = m.stack.At(m.stack.Len() - 1)
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

type Binding struct {
	value Value
}

var unboundGlobalValue Value

type globalInstr struct {
	name string
}

func newGlobalInstr(arg Value) Instr {
	return &globalInstr{arg.(*Symbol).name}
}

func (instr *globalInstr) Exec(m *Machine) {
	binding, ok := globals[instr.name]
	if !ok {
		m.throw("unbound global: " + instr.name)
		return
	}
	m.a = binding.value
}

func (instr *globalInstr) Sexp() Value {
	return list(intern("global"), intern(instr.name))
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
	if nilp(m.a) {
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
	dottedp := m.f.temp.dottedp
	n := nvars
	if dottedp {
		n++
	}
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
		&globalInstr{"throw"},
		&applyInstr{1},
	}
	for _, instr := range code {
		instr.Exec(m)
	}
}

func freshStack() Stack {
	var s Stack
	s.Push(
		&Func{
			&Template{
				"halt", 0, false, nil,
				[]Instr{
					&constInstr{intern("normal")},
					&haltInstr{},
				},
			},
			nil,
		},
	)
	s.Push(0)
	s.Push(0)
	return s
}

func newMachine(f *Func) *Machine {
	return &Machine{
		RUNNING, f, 3, 0,
		freshStack(), Nil{},
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
	if x {
		return intern("t")
	}
	return Nil{}
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
	return &Cons{args[0], args[1]}, nil
}

func primCar(args ...Value) (Value, os.Error) {
	if c, ok := args[0].(*Cons); ok {
		return c.car, nil
	}
	return nil, os.NewError("car: type error")
}

func primCdr(args ...Value) (Value, os.Error) {
	if c, ok := args[0].(*Cons); ok {
		return c.cdr, nil
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
		spec, err := tuple(specs.At(i), symbolp, numberp)
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

func makeInstr(opcode string, args Value) Instr {
	arg := Value(Nil{})
	if !nilp(args) {
		var err os.Error
		arg, err = car(args)
		if err != nil {
			panic("makeInstr: bad argument")
		}
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
		case *Cons:
			opcode, ok := x.car.(*Symbol)
			if !ok {
				return nil, os.NewError(
					"packCode: non-symbol opcode",
				)
			}
			code[i] = makeInstr(opcode.name, x.cdr)
		default:
			return nil, os.NewError("packCode: bad argument")
		}
	}
	return code, nil
}

func primTemplateNew(args ...Value) (Value, os.Error) {
	var nvars int
	if n, ok := args[0].(Number); ok {
		nvars = int(n)
	} else {
		return nil, os.NewError("templatenew: type error")
	}
	dottedp := !nilp(args[1])
	freeRefs, err := packFreeRefs(args[2])
	if err != nil {
		return nil, os.NewError("templatenew: invalid free references")
	}
	code, err := packCode(args[3])
	if err != nil {
		return nil, os.NewError("templatenew: invalid code")
	}
	temp := &Template{
		"",
		nvars,
		dottedp,
		freeRefs,
		code,
	}
	return temp, nil
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
	freeRefs := Value(Nil{})
	for i := n - 1; i >= 0; i-- {
		freeRefs = &Cons{unpackFreeRef(temp.freeRefs[i]), freeRefs}
	}
	code := Value(Nil{})
	n = len(temp.code)
	for i := n - 1; i >= 0; i-- {
		code = &Cons{unpackInstr(temp.code[i]), code}
	}
	sexp := list(
		intern("template"),
		String(temp.name),
		Number(temp.nvars),
		truth(temp.dottedp),
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
	return &Func{temp, env}, nil
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
	stack := &Array{c.stack.Copy()}
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
		a.Push(Value(Nil{}))
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
	return Nil{}, nil
}

func primArrayLength(args ...Value) (Value, os.Error) {
	a, ok := args[0].(*Array)
	if !ok {
		return nil, os.NewError("arraylength: type error")
	}
	return Number(a.Len()), nil
}

func primCellNew(args ...Value) (Value, os.Error) {
	return &Cell{args[0]}, nil
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
		return Nil{}, nil
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
	switch args[0].(type) {
	case Nil:
		return truth(nilp(args[1])), nil
	}
	if reflect.TypeOf(args[0]) != reflect.TypeOf(args[1]) {
		return Nil{}, nil
	}
	return truth(args[0] == args[1]), nil
}

func primNeq(args ...Value) (Value, os.Error) {
	switch args[0].(type) {
	case Nil:
		return truth(!nilp(args[1])), nil
	}
	if reflect.TypeOf(args[0]) != reflect.TypeOf(args[1]) {
		return truth(true), nil
	}
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

func primDef(args ...Value) (Value, os.Error) {
	sym, ok := args[0].(*Symbol)
	if !ok {
		return nil, os.NewError("def: type error")
	}
	name := sym.name
	_, ok = globals[name]
	if ok {
		return nil, os.NewError(
			"def: multiple definitions for " +
				name,
		)
	}
	globals[name] = &Binding{args[1]}
	switch f := args[1].(type) {
	case *Func:
		f.temp.name = name
	}
	return args[0], nil
}

func primGlobal(args ...Value) (Value, os.Error) {
	sym, ok := args[0].(*Symbol)
	if !ok {
		return nil, os.NewError("global: type error")
	}
	if binding, ok := globals[sym.name]; ok {
		if binding.value != unboundGlobalValue {
			return binding.value, nil
		}
	}
	return nil, os.NewError("global: unbound")
}

func primLog(args ...Value) (Value, os.Error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, os.NewError("log: type error")
	}
	fmt.Println(string(s))
	return Nil{}, nil
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
		body, err := car(args[2])
		if err != nil {
			return nil, os.NewError("http: bad argument")
		}
		bodyString, ok := body.(String)
		if !ok {
			return nil, os.NewError("http: bod argument")
		}
		httpPut(string(url), string(bodyString))
		return Nil{}, nil
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
	return Nil{}, nil
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
	lits := newReadAll(buf)
	acc := Value(Nil{})
	for i := len(lits) - 1; i >= 0; i-- {
		acc = &Cons{valueOfLiteral(lits[i]), acc}
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
	return compile(parseExpr(literalOfValue(args[0])))
}

var primDecls = [][]interface{}{
	{"symbolp x", primSymbolp},
	{"numberp x", primNumberp},
	{"stringp x", primStringp},
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
	{"templatenew nvars dottedp freerefs code", primTemplateNew},
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
	{"strcat . args", primStrCat},
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
	{"def var val", primDef},
	{"global name", primGlobal},
	{"log text", primLog},
	{"http method url . args", primHttp},
	{"now", primNow},
	{"exec cmd . args", primExec},
	{"exit code", primExit},
	{"readall str", primReadAll},
	{"compile expr", primCompile},
}

func define(name string, value Value) {
	globals[name] = &Binding{value}
}

func makePrim(decl []interface{}) *Template {
	protocol := decl[0].(string)
	parts := strings.Split(protocol, " ")
	name := parts[0]
	nargs := len(parts) - 1
	dottedp := false
	if len(parts) >= 3 {
		if parts[len(parts)-2] == "." {
			dottedp = true
			nargs -= 2
		}
	}
	prim := decl[1].(func(...Value) (Value, os.Error))
	return &Template{
		name, nargs, dottedp, nil,
		[]Instr{
			&primInstr{name, prim},
			&returnInstr{},
		},
	}
}

func loadPrims() {
	for _, decl := range primDecls {
		temp := makePrim(decl)
		define(temp.name, &Func{temp, nil})
	}
	define("apply", &Func{
		&Template{
			"apply", 2, false, nil,
			[]Instr{
				&localInstr{1},
				&pushInstr{},
				&localInstr{0},
				&shiftInstr{},
				&applyInstr{-1},
			},
		},
		nil,
	})
	define("call/cc", &Func{
		&Template{
			"call/cc", 1, false, nil,
			[]Instr{
				&continuationInstr{},
				&pushInstr{},
				&localInstr{0},
				&shiftInstr{},
				&applyInstr{1},
			},
		},
		nil,
	})
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
	if atom == "nil" {
		return Nil{}
	}
	n, err := strconv.Atof64(atom)
	if err == nil {
		return Number(n)
	}
	return intern(atom)
}

func readQuote(buf io.ByteScanner) Literal {
	x := read(buf)
	return newListLiteral(false, intern("quote"), x)
}

func readQuasi(buf io.ByteScanner) Literal {
	x := read(buf)
	return newListLiteral(false, intern("quasiquote"), x)
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
	return newListLiteral(false, tag, x)
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
	return newListLiteral(false, intern("ampersand"), x)
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
	dotted := false
	items := []Literal{}
	for {
		b, err := buf.ReadByte()
		if err != nil {
			panic("read: premature end of file")
		}
		if b == ')' {
			break
		}
		if b == '.' {
			if len(items) == 0 {
				panic("read: ill-formed list")
			}
			dotted = true
			skipws(buf)
			items = append(items, read(buf))
			skipws(buf)
			b, err = buf.ReadByte()
			if err != nil {
				panic("read: premature end of file")
			}
			if b != ')' {
				panic("read: ill-formed list")
			}
			break
		}
		buf.UnreadByte()
		items = append(items, read(buf))
		skipws(buf)
	}
	if len(items) == 0 {
		return Nil{}
	}
	return newListLiteral(dotted, items...)
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

func newReadAll(r io.Reader) []Literal {
	buf := bufio.NewReader(r)
	items := []Literal{}
	for {
		skipws(buf)
		if _, err := buf.ReadByte(); err != nil {
			break
		}
		_ = buf.UnreadByte()
		item := read(buf)
		items = append(items, item)
	}
	return items
}

func valueOfLiteral(lit Literal) Value {
	if x, ok := lit.(*ListLiteral); ok {
		z := Value(Nil{})
		i := len(x.items)
		if x.dotted {
			i--
			z = valueOfLiteral(x.items[i])
		}
		for i > 0 {
			i--
			z = &Cons{valueOfLiteral(x.items[i]), z}
		}
		return z
	}
	return lit
}

func literalOfValue(val Value) Literal {
	switch x := val.(type) {
	case Nil:
		return x
	case Number:
		return x
	case String:
		return x
	case *Symbol:
		return x
	}
	cons, ok := val.(*Cons)
	if !ok {
		panic("literalOfValue: nonliteral value")
	}
	items := []Literal{}
	for {
		items = append(items, literalOfValue(cons.car))
		if nilp(cons.cdr) {
			break
		}
		if !consp(cons.cdr) {
			items = append(items, literalOfValue(cons.cdr))
			return &ListLiteral{true, items}
		}
		cons, _ = cons.cdr.(*Cons)
	}
	return &ListLiteral{false, items}
}

type Literal interface {
	literalVariant()
}

// Invariants:
//   len(items) > 0
type ListLiteral struct {
	dotted bool
	items  []Literal
}

func newListLiteral(dotted bool, items ...Literal) *ListLiteral {
	return &ListLiteral{dotted, items}
}

func (_ Nil) literalVariant()          {}
func (_ Number) literalVariant()       {}
func (_ String) literalVariant()       {}
func (_ *Symbol) literalVariant()      {}
func (_ *ListLiteral) literalVariant() {}

func parseCallExpr(form *ListLiteral) Expr {
	if form.dotted {
		panic("parseExpr: ill-formed call")
	}
	forms := form.items
	if len(forms) < 1 {
		panic("parseExpr: empty call")
	}
	funcExpr := parseExpr(forms[0])
	argExprs := parseEach(forms[1:])
	return CallExpr{funcExpr, argExprs}
}

func parseParams(lit Literal) ([]*Symbol, bool) {
	switch x := lit.(type) {
	case Nil:
		return []*Symbol{}, false
	case *Symbol:
		return []*Symbol{x}, true
	case *ListLiteral:
		params := make([]*Symbol, len(x.items))
		for i, item := range x.items {
			var ok bool
			params[i], ok = item.(*Symbol)
			if !ok {
				panic("parseExpr: bad parameter")
			}
		}
		return params, x.dotted
	}
	panic("parseExpr: ill-formed parameter list")
	return []*Symbol{}, false
}

func parseInits(lit Literal) []InitPair {
	list, ok := lit.(*ListLiteral)
	if !ok || list.dotted || len(list.items) == 0 {
		panic("parseExpr: ill-formed init list")
	}
	inits := make([]InitPair, len(list.items))
	for i, item := range list.items {
		pair, ok := item.(*ListLiteral)
		if !ok || pair.dotted || len(pair.items) != 2 {
			panic("parseExpr: ill-formed init list")
		}
		inits[i].name, ok = pair.items[0].(*Symbol)
		if !ok {
			panic("parseExpr: ill-formed init list")
		}
		inits[i].expr = parseExpr(pair.items[1])
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
	if !ok || list.dotted || len(list.items) < 2 {
		panic("parseExpr: ill-formed cond clause")
	}
	return CondClause{
		parseExpr(list.items[0]),
		parseEach(list.items[1:]),
	}
}

func analyzeUnquotesplicing(lit Literal) (Literal, bool) {
	var head *Symbol
	x, ok := lit.(*ListLiteral)
	if !ok {
		goto nomatch
	}
	if x.dotted || len(x.items) != 2 {
		goto nomatch
	}
	head, ok = x.items[0].(*Symbol)
	if !ok {
		goto nomatch
	}
	if head == intern("unquotesplicing") {
		return x.items[1], true
	}
nomatch:
	return Nil{}, false
}

func expandQuasi(lit Literal) Literal {
	switch x := lit.(type) {
	case Nil:
		return x
	case Number:
		return x
	case String:
		return x
	case *Symbol:
		return newListLiteral(false, intern("quote"), x)
	}
	x, ok := lit.(*ListLiteral)
	if !ok {
		panic("expandQuasi: unexpected literal type")
	}
	if head, ok := x.items[0].(*Symbol); ok {
		if head == intern("unquote") {
			if len(x.items) != 2 || x.dotted {
				panic("expandQuasi: ill-formed unquote")
			}
			return x.items[1]
		}
		if head == intern("quasiquote") {
			if len(x.items) != 2 || x.dotted {
				panic("expandQuasi: ill-formed quasiquote")
			}
			return expandQuasi(expandQuasi(x.items[1]))
		}
	}
	var acc Literal
	item := x.items[len(x.items) - 1]
	if subLit, ok := analyzeUnquotesplicing(item); ok {
		acc = subLit
	} else {
		acc = newListLiteral(
			false,
			intern("cons"),
			expandQuasi(item),
			Nil{},
		)
	}
	for i := len(x.items) - 2; i >= 0; i-- {
		item = x.items[i]
		subLit, ok := analyzeUnquotesplicing(item)
		if ok {
			acc = newListLiteral(
				false,
				intern("append"),
				subLit,
				acc,
			)
			continue
		}
		acc = newListLiteral(
			false,
			intern("cons"),
			expandQuasi(item),
			acc,
		)
	}
	return acc
}

func parseMatchClause(lit Literal) MatchClause {
	var clause MatchClause
	x, ok := lit.(*ListLiteral)
	if !ok || x.dotted || len(x.items) < 2 {
		panic("parseExpr: ill-formed match clause")
	}
	sym, ok := x.items[0].(*Symbol)
	if ok && sym == intern("t") {
		// TODO - this is awkward
		clause.tag = sym
		clause.params = []*Symbol{}
		clause.dotted = false
		clause.body = parseEach(x.items[1:])
		return clause
	}
	pattern, ok := x.items[0].(*ListLiteral)
	if !ok || len(pattern.items) < 1 {
		panic("parseExpr: ill-formed match clause")
	}
	clause.tag, ok = pattern.items[0].(*Symbol)
	if !ok {
		panic("parseExpr: ill-formed match clause")
	}
	clause.dotted = pattern.dotted
	clause.params = make([]*Symbol, len(pattern.items[1:]))
	for i, item := range pattern.items[1:] {
		sym, ok := item.(*Symbol)
		if !ok {
			panic("parseExpr: ill-formed match clause")
		}
		clause.params[i] = sym
	}
	clause.body = parseEach(x.items[1:])
	return clause
}

func parseExpr(lit Literal) Expr {
	switch x := lit.(type) {
	case Nil:
		return QuoteExpr{x}
	case Number:
		return QuoteExpr{x}
	case String:
		return QuoteExpr{x}
	case *Symbol:
		return RefExpr{x}
	case *ListLiteral:
		if x.dotted {
			panic("parseExpr: dotted list fail")
		}
		if len(x.items) == 0 {
			panic("parseExpr: empty expression")
		}
		head, ok := x.items[0].(*Symbol)
		if !ok {
			return parseCallExpr(x)
		}
		if head == intern("quasiquote") {
			if len(x.items) != 2 {
				panic("parseExpr: ill-formed quasiquote")
			}
			return parseExpr(expandQuasi(x.items[1]))
		}
		if head == intern("ampersand") {
			if len(x.items) != 2 {
				panic("parseExpr: ill-formed ampersand")
			}
			switch list := x.items[1].(type) {
			case Nil:
				return AmpersandExpr{[]Expr{}}
			case *ListLiteral:
				return AmpersandExpr{parseEach(list.items)}
			}
			panic("parseExpr: ill-formed ampersand")
		}
		if head == intern("quote") {
			if len(x.items) != 2 {
				panic("parseExpr: ill-formed quote")
			}
			return QuoteExpr{valueOfLiteral(x.items[1])}
		}
		if head == intern("if") {
			if len(x.items) != 4 {
				panic("parseExpr: ill-formed if")
			}
			return IfExpr{
				parseExpr(x.items[1]),
				parseExpr(x.items[2]),
				parseExpr(x.items[3]),
			}
		}
		if head == intern("begin") {
			if len(x.items) < 2 {
				panic("parseExpr: ill-formed begin")
			}
			body := parseEach(x.items[1:])
			return BeginExpr{body}
		}
		if head == intern("jmp") {
			if len(x.items) != 2 {
				panic("parseExpr: ill-formed jmp")
			}
			return JmpExpr{parseExpr(x.items[1])}
		}
		if head == intern("func") {
			if len(x.items) < 3 {
				panic("parseExpr: ill-formed func")
			}
			params, dotted := parseParams(x.items[1])
			body := parseEach(x.items[2:])
			return FuncExpr{params, dotted, body}
		}
		if head == intern("let") {
			if len(x.items) < 3 {
				panic("parseExpr: ill-formed let")
			}
			inits := parseInits(x.items[1])
			body := parseEach(x.items[2:])
			return LetExpr{inits, body}
		}
		if head == intern("define") {
			if len(x.items) != 3 {
				panic("parseExpr: ill-formed define")
			}
			sym, ok := x.items[1].(*Symbol)
			if !ok {
				panic("parseExpr: ill-formed define")
			}
			return DefineExpr{sym, parseExpr(x.items[2])}
		}
		if head == intern("cond") {
			clauses := make([]CondClause, len(x.items[1:]))
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
			if len(x.items) < 3 {
				panic("parseExpr: ill-formed match")
			}
			clauses := make([]MatchClause, len(x.items[2:]))
			for i, item := range x.items[2:] {
				clauses[i] = parseMatchClause(item)
			}
			return MatchExpr{
				parseExpr(x.items[1]),
				clauses,
			}
		}
		return parseCallExpr(x)
	}
	panic("parseExpr: unmatched literal")
	return QuoteExpr{Nil{}}
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
	dotted bool
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
	tag *Symbol
	params []*Symbol
	dotted bool
	body []Expr
}

type MatcherExpr struct {
	clauses []MatchClause
}

type MatchExpr struct {
	x Expr
	clauses []MatchClause
}

type QuasiExpr struct {
	expr Expr
}

func (_ AmpersandExpr) exprVariant() {}
func (_ LetExpr) exprVariant()   {}
func (_ DefineExpr) exprVariant() {}
func (_ CondExpr) exprVariant() {}
func (_ AndExpr) exprVariant() {}
func (_ OrExpr) exprVariant() {}
func (_ MatcherExpr) exprVariant() {}
func (_ MatchExpr) exprVariant() {}
func (_ QuasiExpr) exprVariant() {}
func (_ RefExpr) exprVariant()   {}
func (_ QuoteExpr) exprVariant() {}
func (_ IfExpr) exprVariant()    {}
func (_ BeginExpr) exprVariant() {}
func (_ JmpExpr) exprVariant()   {}
func (_ FuncExpr) exprVariant()  {}
func (_ CallExpr) exprVariant()  {}

type MacroExpr interface {
	expand() Expr
	macroExprVariant()
}

func (_ AmpersandExpr) macroExprVariant() {}
func (_ LetExpr) macroExprVariant() {}
func (_ DefineExpr) macroExprVariant() {}
func (_ CondExpr) macroExprVariant() {}
func (_ AndExpr) macroExprVariant() {}
func (_ OrExpr) macroExprVariant() {}
func (_ MatcherExpr) macroExprVariant() {}
func (_ MatchExpr) macroExprVariant() {}
func (_ QuasiExpr) macroExprVariant() {}

func (expr AmpersandExpr) expand() Expr {
	acc := Expr(QuoteExpr{Nil{}})
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
		FuncExpr{params, false, expr.body},
		argExprs,
	}
}

func (expr DefineExpr) expand() Expr {
	return CallExpr{
		RefExpr{intern("def")},
		[]Expr{QuoteExpr{expr.name}, expr.expr},
	}
}

func (expr CondExpr) expand() Expr {
	acc := Expr(QuoteExpr{Nil{}})
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
	acc := Expr(RefExpr{intern("t")})
	for i := len(expr.exprs) - 1; i >= 0; i-- {
		acc = IfExpr{
			expr.exprs[i],
			acc,
			QuoteExpr{Nil{}},
		}
	}
	return acc
}

func (expr OrExpr) expand() Expr {
	acc := Expr(QuoteExpr{Nil{}})
	for i := len(expr.exprs) - 1; i >= 0; i-- {
		acc = IfExpr{
			expr.exprs[i],
			RefExpr{intern("t")},
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
	if clause.tag == intern("t") {
		funcExpr := FuncExpr{
			[]*Symbol{intern("tag"), intern("args")},
			false,
			[]Expr{CallExpr{RefExpr{intern("f")}, []Expr{}}},
		}
		acc = LetExpr{
			[]InitPair{{
				intern("f"),
				FuncExpr{
					[]*Symbol{},
					false,
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
			false,
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
			false,
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
					expr.clauses[i].dotted,
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

// Either an AsmLabel or an AsmInstr.
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

func newGlobalAsm(name string) Asm {
	return &AsmInstr{&globalInstr{name}, nil}
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
	local, free map[*Symbol]int
}

func newEmptyEnv() *CompEnv {
	return &CompEnv{
		local: make(map[*Symbol]int),
		free:  make(map[*Symbol]int),
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

func analyzeRefs(env *CompEnv, locals []*Symbol, body []Expr) (*CompEnv, []FreeRef) {
	freshEnv := newEmptyEnv()
	freeRefs := []FreeRef{}
	refs := collectFree(body, env.symbolSet(), newSymbolSet(locals))
	nfree := 0
	for i, sym := range locals {
		freshEnv.local[sym] = i
	}
	for ref, _ := range refs.table {
		if _, ok := freshEnv.local[ref]; ok {
			continue
		}
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
	return newGlobalAsm(sym.name)
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
		for i := 0; i < n - 1; i++ {
			asms = seq(
				asms,
				compExpr(body[i], env, false, NONTAIL),
			)
		}
		return seq(asms, compExpr(body[n-1], env, argp, tailp))
	case JmpExpr:
		return compExpr(expr.expr, env, argp, JMP)
	case FuncExpr:
		body := BeginExpr{expr.body}
		nvars := len(expr.params)
		if expr.dotted {
			nvars--
		}
		funcEnv, freeRefs := analyzeRefs(env, expr.params, expr.body)
		code := assemble(compExpr(body, funcEnv, false, TAIL))
		temp := &Template{
			name:     "",
			nvars:    nvars,
			dottedp:  expr.dotted,
			freeRefs: freeRefs,
			code:     code,
		}
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
	core := macroexpandall(expr)
	code := assemble(compExpr(core, newEmptyEnv(), false, TAIL))
	temp = &Template{
		name:     "",
		nvars:    0,
		dottedp:  false,
		freeRefs: []FreeRef{},
		code:     code,
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
			core.dotted,
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
	return QuoteExpr{Nil{}}
}

/// loading

type Module struct {
	f *Func
}

func topFunc(temps []*Template) *Func {
	n := len(temps)
	code := make([]Instr, 3*n+1)
	for i := 0; i < 3*n; i += 3 {
		code[i+0] = &frameInstr{i + 3}
		code[i+1] = &closeInstr{temps[i/3]}
		code[i+2] = &applyInstr{0}
	}
	code[3*n] = &returnInstr{}
	return &Func{
		&Template{"", 0, false, nil, code},
		nil,
	}
}

func fetchSourceModule(name, address string) (mod *Module, err os.Error) {
	url := "http://" + address + "/" + name + ".lisp"
	response, err := http.Get(url)
	if err != nil {
		err = os.NewError("fetchSourceModule: HTTP fail")
		return
	}
	defer response.Body.Close()
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
	exprs := newReadAll(response.Body)
	temps := make([]*Template, len(exprs))
	for i, expr := range exprs {
		temps[i], err = compile(parseExpr(expr))
		if err != nil {
			return
		}
	}
	mod = &Module{topFunc(temps)}
	return
}

func loadSourceFile(name string) {
	mod, err := fetchSourceModule(name, *address)
	if err != nil {
		log.Fatalln(err)
	}
	m := newMachine(mod.f)
	m.run()
}

func initReader() {
	readTable = map[byte]func(io.ByteScanner) Literal{
		'"': readString,
		'\'': readQuote,
		'`': readQuasi,
		',': readComma,
		'&': readAmpersand,
		'(': readList,
	}
}
func initInterpreter() {
	unboundGlobalValue = &Cons{Nil{}, Nil{}}
	sharedPrimStack = make([]Value, 8)
	globals = make(map[string]*Binding)
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
		loadSourceFile(name)
	}
}
