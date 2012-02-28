package compiler

import (
	"errors"
	. "norstrulde/lumgua/assembler"
	. "norstrulde/lumgua/machine"
	. "norstrulde/lumgua/syntax"
)

var DefinedGlobals *SymbolSet        // XXX kludge!
var BindingsKludge map[*Symbol]Value // XXX kludge!

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
		code = append(code, NewPushAsm())
	}
	if tailp != NONTAIL {
		code = append(code, NewReturnAsm())
	}
	return code
}

type CompEnv struct {
	local, free, global map[*Symbol]int
}

func NewEmptyEnv() *CompEnv {
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
	return NewSymbolSet(local, free)
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

func NewSymbolSet(lists ...[]*Symbol) *SymbolSet {
	table := make(map[*Symbol]bool)
	for _, list := range lists {
		for _, sym := range list {
			table[sym] = true
		}
	}
	return &SymbolSet{table}
}

func (set *SymbolSet) Contains(sym *Symbol) bool {
	_, ok := set.table[sym]
	return ok
}

func (set *SymbolSet) Include(sym *Symbol) {
	set.table[sym] = true
}

func (set1 *SymbolSet) Union(set2 *SymbolSet) *SymbolSet {
	u := NewSymbolSet()
	for sym, _ := range set1.table {
		u.Include(sym)
	}
	for sym, _ := range set2.table {
		u.Include(sym)
	}
	return u
}

func (set *SymbolSet) Remove(sym *Symbol) {
	delete(set.table, sym)
}

func (set1 *SymbolSet) Minus(set2 *SymbolSet) *SymbolSet {
	acc := NewSymbolSet()
	for sym, _ := range set1.table {
		if !set2.Contains(sym) {
			acc.Include(sym)
		}
	}
	return acc
}

func collectFree(exprs []Expr, b, p *SymbolSet) *SymbolSet {
	refs := NewSymbolSet()
	for _, expr := range exprs {
		refs = refs.Union(findFree(expr, b, p))
	}
	return refs
}

func findFree(expr Expr, b, p *SymbolSet) *SymbolSet {
	refs := NewSymbolSet()
	switch expr := expr.(type) {
	case RefExpr:
		if b.Contains(expr.Name) && !p.Contains(expr.Name) {
			refs.Include(expr.Name)
		}
	case IfExpr:
		refs = findFree(expr.CondExpr, b, p)
		refs = refs.Union(findFree(expr.ThenExpr, b, p))
		refs = refs.Union(findFree(expr.ElseExpr, b, p))
	case BeginExpr:
		refs = collectFree(expr.Body, b, p)
	case JmpExpr:
		refs = findFree(expr.Expr, b, p)
	case FuncExpr:
		refs = collectFree(expr.Body, b, NewSymbolSet(expr.Params))
		refs = refs.Minus(p)
	case CallExpr:
		refs = findFree(expr.FuncExpr, b, p)
		refs = refs.Union(collectFree(expr.ArgExprs, b, p))
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
		sym := expr.Name
		if nonglobals.Contains(sym) {
			return
		}
		_, ok := globals[sym]
		if !ok {
			if !DefinedGlobals.Contains(sym) {
				panic("findGlobals: undefined global " +
					sym.Name)
			}
			globals[sym] = len(globals)
		}
	case IfExpr:
		findGlobals(globals, nonglobals, expr.CondExpr)
		findGlobals(globals, nonglobals, expr.ThenExpr)
		findGlobals(globals, nonglobals, expr.ElseExpr)
	case BeginExpr:
		collectGlobals(globals, nonglobals, expr.Body)
	case JmpExpr:
		findGlobals(globals, nonglobals, expr.Expr)
	case CallExpr:
		findGlobals(globals, nonglobals, expr.FuncExpr)
		collectGlobals(globals, nonglobals, expr.ArgExprs)
	}
}

func analyzeRefs(env *CompEnv, locals []*Symbol, body []Expr) (*CompEnv, []FreeRef) {
	freshEnv := NewEmptyEnv()
	freeRefs := []FreeRef{}
	refs := collectFree(body, env.symbolSet(), NewSymbolSet(locals))
	nonglobals := NewSymbolSet(locals).Union(refs)
	collectGlobals(freshEnv.global, nonglobals, body)
	nfree := 0
	for i, sym := range locals {
		freshEnv.local[sym] = i
	}
	for ref, _ := range refs.table {
		if i, ok := env.local[ref]; ok {
			freeRefs = append(freeRefs, FreeRef{ScopeLocal, i})
			freshEnv.free[ref] = nfree
			nfree++
			continue
		}
		if i, ok := env.free[ref]; ok {
			freeRefs = append(freeRefs, FreeRef{ScopeFree, i})
			freshEnv.free[ref] = nfree
			nfree++
			continue
		}
	}
	return freshEnv, freeRefs
}

func newRefAsm(env *CompEnv, sym *Symbol) Asm {
	if i, ok := env.local[sym]; ok {
		return NewLocalAsm(i)
	}
	if i, ok := env.free[sym]; ok {
		return NewFreeAsm(i)
	}
	if i, ok := env.global[sym]; ok {
		return NewGlobalAsm(i)
	}
	panic("newRefAsm: cannot locate variable " + sym.Name)
	return nil
}

func CompFuncExpr(expr FuncExpr, env *CompEnv) *Template {
	body := BeginExpr{expr.Body}
	nvars := len(expr.Params)
	funcEnv, freeRefs := analyzeRefs(env, expr.Params, expr.Body)
	code := Assemble(compExpr(body, funcEnv, false, TAIL))
	return NewTemplate("", nvars, freeRefs, code, funcEnv.globals())
}

func compExpr(expr Expr, env *CompEnv, argp bool, tailp int) []Asm {
	switch expr := expr.(type) {
	case QuoteExpr:
		return seq(
			gen(NewConstAsm(expr.X)),
			genReturn(argp, tailp),
		)
	case RefExpr:
		return seq(
			gen(newRefAsm(env, expr.Name)),
			genReturn(argp, tailp),
		)
	case IfExpr:
		label0 := NewLabel()
		label1 := NewLabel()
		var jump1Seq, label1Seq, pushSeq []Asm
		if tailp == NONTAIL {
			jump1Seq = gen(NewJumpAsm(label1))
			label1Seq = gen(label1)
		}
		if argp {
			pushSeq = gen(NewPushAsm())
		}
		return seq(
			compExpr(expr.CondExpr, env, false, NONTAIL),
			gen(NewFjumpAsm(label0)),
			compExpr(expr.ThenExpr, env, false, tailp),
			jump1Seq,
			gen(label0),
			compExpr(expr.ElseExpr, env, false, tailp),
			label1Seq,
			pushSeq,
		)
	case BeginExpr:
		body := expr.Body
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
		return compExpr(expr.Expr, env, argp, JMP)
	case FuncExpr:
		temp := CompFuncExpr(expr, env)
		return seq(
			gen(NewCloseAsm(temp)),
			genReturn(argp, tailp),
		)
	case CallExpr:
		label := NewLabel()
		frameSeq := gen(NewFrameAsm(label))
		argsSeq := gen()
		funcSeq := compExpr(expr.FuncExpr, env, false, NONTAIL)
		shiftSeq := gen()
		applySeq := gen(NewApplyAsm(len(expr.ArgExprs)))
		labelSeq := gen(label)
		tailSeq := gen()
		for _, argExpr := range expr.ArgExprs {
			argsSeq = seq(
				argsSeq,
				compExpr(argExpr, env, true, NONTAIL),
			)
		}
		if tailp == JMP {
			frameSeq = gen()
			shiftSeq = gen(NewShiftAsm())
			labelSeq = gen()
		} else if tailp == TAIL {
			tailSeq = gen(NewReturnAsm())
		} else if argp {
			tailSeq = gen(NewPushAsm())
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
	panic("Compile: unexpected expression")
	return []Asm{}
}

func Compile(expr Expr) (temp *Template, err error) {
	defer func() {
		x := recover()
		if s, ok := x.(string); ok {
			err = errors.New(s)
			return
		}
		if x != nil {
			panic(x)
		}
	}()
	temp = CompFuncExpr(
		FuncExpr{[]*Symbol{}, []Expr{Macroexpandall(expr)}},
		NewEmptyEnv(),
	)
	temps := FindTemplates(temp)
	for _, temp := range temps {
		LinkTemplate(temp, BindingsKludge)
	}
	return
}

func Macroexpandall(expr Expr) Expr {
	for {
		macro, ok := expr.(MacroExpr)
		if !ok {
			break
		}
		expr = macro.Expand()
	}
	switch core := expr.(type) {
	case QuoteExpr:
		return core
	case RefExpr:
		return core
	case IfExpr:
		return IfExpr{
			CondExpr: Macroexpandall(core.CondExpr),
			ThenExpr: Macroexpandall(core.ThenExpr),
			ElseExpr: Macroexpandall(core.ElseExpr),
		}
	case BeginExpr:
		body := make([]Expr, len(core.Body))
		for i, subexpr := range core.Body {
			body[i] = Macroexpandall(subexpr)
		}
		return BeginExpr{body}
	case JmpExpr:
		return JmpExpr{Macroexpandall(core.Expr)}
	case FuncExpr:
		body := make([]Expr, len(core.Body))
		for i, subexpr := range core.Body {
			body[i] = Macroexpandall(subexpr)
		}
		return FuncExpr{
			core.Params,
			body,
		}
	case CallExpr:
		argExprs := make([]Expr, len(core.ArgExprs))
		for i, argExpr := range core.ArgExprs {
			argExprs[i] = Macroexpandall(argExpr)
		}
		return CallExpr{
			Macroexpandall(core.FuncExpr),
			argExprs,
		}
	}
	panic("Macroexpandall: unexpected expression")
	return QuoteExpr{EmptyList}
}

func LinkTemplate(temp *Template, bindings map[*Symbol]Value) {
	globals := temp.Globals
	for i, g := range globals {
		globals[i] = bindings[g.(*Symbol)]
	}
}
