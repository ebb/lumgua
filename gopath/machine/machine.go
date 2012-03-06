package machine

import (
	"errors"
)

var symbolTable map[string]*Symbol

var Globals map[string]Value

const (
	stateHalted = iota
	stateRunning
)

const (
	ScopeLocal = iota
	ScopeFree
)

const (
	OpContinuation = iota
	OpPush
	OpReturn
	OpGlobal
	OpConst
	OpFrame
	OpShift
	OpApply
	OpFjump
	OpJump
	OpClose
	OpLocal
	OpFree
	OpHalt
	OpPrim
)

type FreeRef struct {
	Scope int
	I     int
}

type Instr interface {
	Exec(m *Machine)
	Sexp() Value
}

type Value interface {
}

type Symbol struct {
	Name string
}

type Number float64

type String string

type Bool bool

type List struct {
	Head Value
	Tail *List
}

var EmptyList = &List{nil, nil}

type Template struct {
	Name     string
	Nvars    int
	FreeRefs []FreeRef
	Code     []Instr
	Globals  []Value
}

type Func struct {
	Temp *Template
	Env  []Value
}

type Cont struct {
	Stack []Value
}

type Cell struct {
	Value Value
}

type Array []Value

func NewTemplate(name string, nvars int, freeRefs []FreeRef, code []Instr, globals []Value) *Template {
	return &Template{
		Name:     name,
		Nvars:    nvars,
		FreeRefs: freeRefs,
		Code:     code,
		Globals:  globals,
	}
}

func NewFunc(temp *Template, env []Value) *Func {
	return &Func{
		Temp: temp,
		Env:  env,
	}
}

func NewCont(stack []Value) *Cont {
	return &Cont{stack}
}

func NewCell(x Value) *Cell {
	return &Cell{
		Value: x,
	}
}

func NewArray(contents []Value) Array {
	return contents
}

func NewList(elements ...Value) *List {
	x := EmptyList
	for i := len(elements) - 1; i >= 0; i-- {
		x = &List{elements[i], x}
	}
	return x
}

func Intern(name string) *Symbol {
	sym, ok := symbolTable[name]
	if !ok {
		sym = &Symbol{name}
		symbolTable[name] = sym
	}
	return sym
}

func (a Array) Slice() []Value {
	return ([]Value)(a)
}

func (list *List) Len() int {
	n := 0
	for x := list; x != EmptyList; x = x.Tail {
		n++
	}
	return n
}

func ForEach(x Value, f func(Value) error) error {
	list, ok := x.(*List)
	if !ok {
		return errors.New("ForEach: type error")
	}
	for list != EmptyList {
		err := f(list.Head)
		if err != nil {
			return err
		}
		list = list.Tail
	}
	return nil
}

func FindTemplates(temp *Template) []*Template {
	temps := []*Template{temp}
	for _, instr := range temp.Code {
		if c, ok := instr.(*closeInstr); ok {
			temps = append(temps, FindTemplates(c.temp)...)
		}
	}
	return temps
}

func InstrOp(instr Instr) int {
	switch instr.(type) {
	case *continuationInstr:
		return OpContinuation
	case *closeInstr:
		return OpClose
	case *frameInstr:
		return OpFrame
	case *shiftInstr:
		return OpShift
	case *applyInstr:
		return OpApply
	case *returnInstr:
		return OpReturn
	case *constInstr:
		return OpConst
	case *globalInstr:
		return OpGlobal
	case *localInstr:
		return OpLocal
	case *freeInstr:
		return OpFree
	case *pushInstr:
		return OpPush
	case *fjumpInstr:
		return OpFjump
	case *jumpInstr:
		return OpJump
	case *haltInstr:
		return OpHalt
	case *primInstr:
		return OpPrim
	}
	panic("InstrOp: unexpected instruction")
	return -1
}

type continuationInstr struct{}

func (*continuationInstr) Exec(m *Machine) {
	n := len(m.stack)-1
	s := make([]Value, n)
	copy(s, m.stack[:n])
	m.a = NewCont(s)
}

func NewContinuationInstr() Instr {
	return &continuationInstr{}
}

func (instr *continuationInstr) Sexp() Value {
	return NewList(Intern("continuation"))
}

type closeInstr struct {
	temp *Template
}

func (instr *closeInstr) Exec(m *Machine) {
	freeRefs := instr.temp.FreeRefs
	n := len(freeRefs)
	if n == 0 {
		m.a = NewFunc(instr.temp, nil)
		return
	}
	env := make([]Value, n)
	for i := 0; i < n; i++ {
		domain := freeRefs[i].Scope
		j := freeRefs[i].I
		switch domain {
		case ScopeLocal:
			env[i] = m.stack[m.fp + j]
		case ScopeFree:
			env[i] = m.f.Env[j]
		default:
			m.throw("unknown variable domain")
			return
		}
	}
	m.a = NewFunc(instr.temp, env)
}

func NewCloseInstr(temp *Template) Instr {
	return &closeInstr{temp}
}

func (instr *closeInstr) Sexp() Value {
	return NewList(Intern("close"), instr.temp)
}

type frameInstr struct {
	pc int
}

func (instr *frameInstr) Exec(m *Machine) {
	m.rstack = append(m.rstack, Return{m.f, m.fp, instr.pc})
}

func NewFrameInstr(pc int) Instr {
	return &frameInstr{pc}
}

func (instr *frameInstr) Sexp() Value {
	return NewList(Intern("frame"), Number(instr.pc))
}

type shiftInstr struct{}

func (*shiftInstr) Exec(m *Machine) {
	nremove := m.f.Temp.Nvars
	nkeep := len(m.stack) - nremove - m.fp
	for i, j := m.fp, 0; j < nkeep; j++ {
		m.stack[i] = m.stack[i+nremove]
		i++
	}
	m.stack = m.stack[0:len(m.stack)-nremove]
}

func NewShiftInstr() Instr {
	return &shiftInstr{}
}

func (*shiftInstr) Sexp() Value {
	return NewList(Intern("shift"))
}

type applyInstr struct {
	nargs int
}

func (m *Machine) prepareApplyArgs(nvars int) {
	rest, ok := m.stack[len(m.stack)-1].(*List)
	if !ok {
		m.throw("apply: type error")
		return
	}
	m.stack = m.stack[:len(m.stack)-1]
	for i := 0; i < nvars; i++ {
		if rest == EmptyList {
			m.throw("apply: too few arguments")
			return
		}
		m.stack = append(m.stack, rest.Head)
		rest = rest.Tail
	}
	if rest != EmptyList {
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
	temp := f.Temp
	m.f = f
	if nargs == -1 {
		m.fp = len(m.stack) - 1
	} else {
		m.fp = len(m.stack) - nargs
	}
	m.pc = 0
	m.code = temp.Code
	m.env = f.Env
	m.prepareArgs(nargs, temp.Nvars)
}

func (m *Machine) applyCont(c *Cont) {
	ret := returnInstr{}
	m.a = m.stack[len(m.stack)-1]
	n := len(c.Stack)
	if n <= cap(m.stack) {
		m.stack = m.stack[:n]
	} else {
		m.stack = make([]Value, n)
	}
	copy(m.stack, c.Stack)
	m.fp = n
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

func NewApplyInstr(nargs int) Instr {
	return &applyInstr{nargs}
}

func (instr *applyInstr) Sexp() Value {
	return NewList(Intern("apply"), Number(instr.nargs))
}

type returnInstr struct{}

func (*returnInstr) Exec(m *Machine) {
	ret := m.rstack[len(m.rstack)-1]
	m.rstack = m.rstack[:len(m.rstack)-1]
	m.f = ret.f
	m.fp = ret.fp
	m.pc = ret.pc
	m.code = m.f.Temp.Code
	m.env = m.f.Env
}

func NewReturnInstr() Instr {
	return &returnInstr{}
}

func (*returnInstr) Sexp() Value {
	return NewList(Intern("return"))
}

type constInstr struct {
	val Value
}

func (instr *constInstr) Exec(m *Machine) {
	m.a = instr.val
}

func NewConstInstr(val Value) Instr {
	return &constInstr{val}
}

func (instr *constInstr) Sexp() Value {
	return NewList(Intern("const"), instr.val)
}

type globalInstr struct {
	n int
}

func (instr *globalInstr) Exec(m *Machine) {
	m.a = m.f.Temp.Globals[instr.n]
}

func NewGlobalInstr(n int) Instr {
	return &globalInstr{n}
}

func (instr *globalInstr) Sexp() Value {
	return NewList(Intern("global"), Number(instr.n))
}

type localInstr struct {
	n int
}

func (instr *localInstr) Exec(m *Machine) {
	m.a = m.stack[m.fp+instr.n]
}

func NewLocalInstr(n int) Instr {
	return &localInstr{n}
}

func (instr *localInstr) Sexp() Value {
	return NewList(Intern("local"), Number(instr.n))
}

type freeInstr struct {
	n int
}

func (instr *freeInstr) Exec(m *Machine) {
	m.a = m.f.Env[instr.n]
}

func NewFreeInstr(n int) Instr {
	return &freeInstr{n}
}

func (instr *freeInstr) Sexp() Value {
	return NewList(Intern("free"), Number(instr.n))
}

type pushInstr struct{}

func (*pushInstr) Exec(m *Machine) {
	m.stack = append(m.stack, m.a)
}

func NewPushInstr() Instr {
	return &pushInstr{}
}

func (*pushInstr) Sexp() Value {
	return NewList(Intern("push"))
}

type fjumpInstr struct {
	pc int
}

func (instr *fjumpInstr) Exec(m *Machine) {
	if b, ok := m.a.(Bool); ok && !bool(b) {
		m.pc = instr.pc
	}
}

func NewFjumpInstr(pc int) Instr {
	return &fjumpInstr{pc}
}

func (instr *fjumpInstr) Sexp() Value {
	return NewList(Intern("fjump"), Number(instr.pc))
}

type jumpInstr struct {
	pc int
}

func (instr *jumpInstr) Exec(m *Machine) {
	m.pc = instr.pc
}

func NewJumpInstr(pc int) Instr {
	return &jumpInstr{pc}
}

func (instr *jumpInstr) Sexp() Value {
	return NewList(Intern("jump"), Number(instr.pc))
}

type haltInstr struct{}

func (*haltInstr) Exec(m *Machine) {
	m.status = stateHalted
}

func NewHaltInstr() Instr {
	return &haltInstr{}
}

func (*haltInstr) Sexp() Value {
	return NewList(Intern("halt"))
}

type Prim func(...Value) (Value, error)

type primInstr struct {
	name string
	prim Prim
}

var sharedPrimStack []Value

func (instr *primInstr) Exec(m *Machine) {
	nvars := m.f.Temp.Nvars
	if nvars > cap(sharedPrimStack) {
		m.throw("too many arguments to prim")
		return
	}
	sharedPrimStack = sharedPrimStack[0:nvars]
	for i := 0; i < nvars; i++ {
		sharedPrimStack[i] = m.stack[m.fp+i]
	}
	a, err := instr.prim(sharedPrimStack...)
	if err != nil {
		m.throw(err.Error())
		return
	}
	m.a = a
}

func NewPrimInstr(name string, prim Prim) Instr {
	return &primInstr{name, prim}
}

func (instr *primInstr) Sexp() Value {
	return NewList(Intern("prim"), Intern(instr.name))
}

func NewPrimTemplate(name string, nargs int, prim Prim) *Template {
	return NewTemplate(
		name, nargs, nil,
		[]Instr{
			&primInstr{name, prim},
			&returnInstr{},
		},
		[]Value{},
	)
}

var ApplyFunc *Func
var CallccFunc *Func

type Return struct {
	f  *Func
	fp int
	pc int
}

type Machine struct {
	status int
	f      *Func
	fp     int
	pc     int
	rstack []Return
	stack  []Value
	a      Value
	code   []Instr
	env    []Value
}

func (m *Machine) throw(s string) {
	code := []Instr{
		&frameInstr{m.pc - 1},
		&constInstr{String(s)},
		&pushInstr{},
		&constInstr{Globals["throw"]}, // XXX
		&applyInstr{1},
	}
	for _, instr := range code {
		instr.Exec(m)
	}
}

func freshRstack() []Return {
	s := make([]Return, 1)
	s[0].f = NewFunc(
		NewTemplate(
			"halt", 0, nil,
			[]Instr{
				&constInstr{Intern("normal")},
				&haltInstr{},
			},
			[]Value{},
		),
		nil,
	)
	s[0].fp = 0
	s[0].pc = 0
	return s
}

func NewMachine(f *Func) *Machine {
	return &Machine{
		stateRunning, f, 3, 0,
		freshRstack(), []Value{}, EmptyList,
		f.Temp.Code, f.Env,
	}
}

func (m *Machine) Run() {
	for m.status == stateRunning {
		m.pc++
		m.code[m.pc-1].Exec(m)
	}
}

func init() {
	symbolTable = make(map[string]*Symbol)
	sharedPrimStack = make([]Value, 8)
	Globals = make(map[string]Value)
	ApplyFunc = NewFunc(
		NewTemplate(
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
	)
	CallccFunc = NewFunc(
		NewTemplate(
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
	)
}
