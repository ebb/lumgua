package loader

import (
	"errors"
	"net/http"
	. "norstrulde/lumgua/compiler"
	. "norstrulde/lumgua/machine"
	_ "norstrulde/lumgua/primitives"
	. "norstrulde/lumgua/syntax"
	"norstrulde/tsort"
)

/// loading

func fetchSourceForms(address, name string) ([]Literal, error) {
	url := "http://" + address + "/" + name + ".lisp"
	response, err := http.Get(url)
	if err != nil {
		return nil, errors.New("fetchSourceModule: HTTP fail")
	}
	defer response.Body.Close()
	return ReadAll(response.Body)
}

func parseToplevel(forms []Literal) ([]DefineExpr, error) {
	defs := make([]DefineExpr, len(forms))
	for i, form := range forms {
		expr, err := ParseToplevel(form)
		if err != nil {
			return nil, err
		}
		def, ok := expr.(DefineExpr)
		if !ok {
			err = errors.New("parseToplevel: form is not define")
			return nil, err
		}
		defs[i] = def
	}
	return defs, nil
}

func checkBindingUniqueness(defs []DefineExpr) (*SymbolSet, error) {
	set := NewSymbolSet()
	for _, def := range defs {
		if set.Contains(def.Name) {
			return nil, errors.New("multiple definitions for: " +
				def.Name.Name)
		}
		set.Include(def.Name)
	}
	return set, nil
}

func analyzeCellLiteral(expr CallExpr) (Expr, error) {
	ref, ok := expr.FuncExpr.(RefExpr)
	if !ok || ref.Name != Intern("cellnew") {
		return nil, errors.New("bad cell literal")
	}
	if len(expr.ArgExprs) != 1 {
		s := "fetchSourceModule: bad cell literal"
		return nil, errors.New(s)
	}
	initExpr := expr.ArgExprs[0]
	return initExpr, nil
}

func build(forms []Literal) (map[*Symbol]Value, error) {
	defs, err := parseToplevel(forms)
	if err != nil {
		return nil, err
	}
	bindings := make(map[*Symbol]Value)
	deps := tsort.NewStringDepGraph()
	thunks := make(map[*Symbol]func())
	aliasThunk := func(alias, original *Symbol) func() {
		return func() {
			bindings[alias] = bindings[original]
		}
	}
	DefinedGlobals, err = checkBindingUniqueness(defs)
	if err != nil {
		return nil, err
	}
	for name, val := range Globals {
		DefinedGlobals.Include(Intern(name))
		bindings[Intern(name)] = val
	}
	for _, def := range defs {
		switch expr := def.Expr.(type) {
		case FuncExpr:
			f := NewFunc(
				CompFuncExpr(
					Macroexpandall(expr).(FuncExpr),
					NewEmptyEnv(),
				),
				[]Value{},
			)
			bindings[def.Name] = f
			f.Temp.Name = def.Name.Name
		case RefExpr:
			deps.AddDep(expr.Name.Name, def.Name.Name)
			thunks[def.Name] = aliasThunk(def.Name, expr.Name)
		case CallExpr:
			initExpr, err := analyzeCellLiteral(expr)
			if err != nil {
				return nil, err
			}
			cell := new(Cell)
			bindings[def.Name] = cell
			switch arg := initExpr.(type) {
			case RefExpr:
				deps.AddDep(arg.Name.Name, def.Name.Name)
				thunks[def.Name] = func() {
					cell.Value = bindings[arg.Name]
				}
			case QuoteExpr:
				cell.Value = arg.X
			default:
				return nil, errors.New("bad cell literal")
			}
		}
	}
	sortedNames, hasCycle := deps.Tsort()
	if hasCycle {
		return nil, errors.New("build: cyclic value dependencies")
	}
	for _, name := range sortedNames {
		thunk, ok := thunks[Intern(name)]
		if !ok {
			continue
		}
		thunk()
	}
	linked := make(map[*Template]bool)
	for _, val := range bindings {
		f, ok := val.(*Func)
		if !ok {
			continue
		}
		temps := FindTemplates(f.Temp)
		for _, temp := range temps {
			if _, ok := linked[temp]; ok {
				continue
			}
			LinkTemplate(temp, bindings)
			linked[temp] = true
		}
	}
	BindingsKludge = bindings
	return bindings, nil
}

func LoadSourceFile(address, name string) error {
	forms, err := fetchSourceForms(address, name)
	if err != nil {
		return err
	}
	bindings, err := build(forms)
	if err != nil {
		return err
	}
	for sym, value := range bindings {
		Globals[sym.Name] = value // TODO remove this
	}
	x, ok := bindings[Intern("main")]
	if !ok {
		return nil
	}
	mainFunc, ok := x.(*Func)
	if !ok {
		return errors.New("LoadSourceFile: main is not a function")
	}
	m := NewMachine(mainFunc)
	m.Run()
	return nil
}
