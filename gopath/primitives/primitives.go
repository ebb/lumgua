package primitives

import "bytes"
import "errors"
import "fmt"
import "io"
import "io/ioutil"
import "math"
import "net/http"
import . "norstrulde/lumgua/compiler"
import . "norstrulde/lumgua/machine"
import . "norstrulde/lumgua/syntax"
import "os"
import "os/exec"
import "strings"
import "time"
import "net/url"

func truth(x bool) Value {
	return Bool(x)
}

func primTypeof(args ...Value) (Value, error) {
	var name string
	switch args[0].(type) {
	case Bool:
		name = "bool"
	case Number:
		name = "number"
	case *Symbol:
		name = "symbol"
	case String:
		name = "string"
	case *List:
		name = "list"
	case *Template:
		name = "template"
	case *Func:
		name = "func"
	case *Cont:
		name = "cont"
	case *Cell:
		name = "cell"
	case Array:
		name = "array"
	default:
		return nil, errors.New("typeof: unknown type")
	}
	return Intern(name), nil
}

func primSymbolName(args ...Value) (Value, error) {
	if sym, ok := args[0].(*Symbol); ok {
		return String(sym.Name), nil
	}
	return nil, errors.New("symbolname: type error")
}

func primCons(args ...Value) (Value, error) {
	tail, ok := args[1].(*List)
	if !ok {
		return nil, errors.New("cons: type error")
	}
	return &List{args[0], tail}, nil
}

func primCar(args ...Value) (Value, error) {
	if list, ok := args[0].(*List); ok {
		if list == EmptyList {
			return nil, errors.New("car: nil")
		}
		return list.Head, nil
	}
	return nil, errors.New("car: type error")
}

func primCdr(args ...Value) (Value, error) {
	if list, ok := args[0].(*List); ok {
		if list == EmptyList {
			return nil, errors.New("cdr: nil")
		}
		return list.Tail, nil
	}
	return nil, errors.New("cdr: type error")
}

func unpackFreeRef(ref FreeRef) Value {
	switch ref.Scope {
	case ScopeLocal:
		return NewList(Intern("local"), Number(ref.I))
	case ScopeFree:
		return NewList(Intern("free"), Number(ref.I))
	}
	panic("UnpackFreeRef: unexpected free reference scope")
}

func unpackInstr(instr Instr) Value {
	return instr.Sexp()
}

func primTemplateOpen(args ...Value) (Value, error) {
	temp, ok := args[0].(*Template)
	if !ok {
		return nil, errors.New("templateopen: type error")
	}
	n := len(temp.FreeRefs)
	freeRefs := EmptyList
	for i := n - 1; i >= 0; i-- {
		freeRefs = &List{unpackFreeRef(temp.FreeRefs[i]), freeRefs}
	}
	code := EmptyList
	n = len(temp.Code)
	for i := n - 1; i >= 0; i-- {
		code = &List{unpackInstr(temp.Code[i]), code}
	}
	sexp := NewList(
		Intern("template"),
		String(temp.Name),
		Number(temp.Nvars),
		freeRefs,
		code,
	)
	return sexp, nil
}

func primFuncNew(args ...Value) (Value, error) {
	temp, ok := args[0].(*Template)
	if !ok {
		return nil, errors.New("funcnew: type error")
	}
	envArray, ok := args[1].(Array)
	if !ok {
		return nil, errors.New("funcnew: type error")
	}
	envSlice := envArray.Slice()
	envCopy := make([]Value, len(envSlice))
	copy(envCopy, envSlice)
	return NewFunc(temp, envCopy), nil
}

func primFuncOpen(args ...Value) (Value, error) {
	f, ok := args[0].(*Func)
	if !ok {
		return nil, errors.New("funcopen: type error")
	}
	env := make([]Value, len(f.Env))
	copy(env, f.Env)
	sexp := NewList(
		Intern("func"),
		f.Temp,
		env,
	)
	return sexp, nil
}

func primContOpen(args ...Value) (Value, error) {
	c, ok := args[0].(*Cont)
	if !ok {
		return nil, errors.New("contopen: type error")
	}
	return c.Open(), nil
}

func primArrayNew(args ...Value) (Value, error) {
	m, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("arraynew: type error")
	}
	n := int(m)
	contents := make([]Value, n)
	for i, _ := range(contents) {
		contents[i] = EmptyList
	}
	return NewArray(contents), nil
}

func primArrayGet(args ...Value) (Value, error) {
	a, ok := args[0].(Array)
	if !ok {
		return nil, errors.New("arrayget: type error")
	}
	i, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("arrayget: type error")
	}
	return a.Slice()[int(i)], nil
}

func primArrayPut(args ...Value) (Value, error) {
	a, ok := args[0].(Array)
	if !ok {
		return nil, errors.New("arrayput: type error")
	}
	i, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("arrayput: type error")
	}
	x := args[2]
	a.Slice()[int(i)] = x
	return EmptyList, nil
}

func primArrayLength(args ...Value) (Value, error) {
	a, ok := args[0].(Array)
	if !ok {
		return nil, errors.New("arraylength: type error")
	}
	return Number(len(a.Slice())), nil
}

func primCellNew(args ...Value) (Value, error) {
	return NewCell(args[0]), nil
}

func primCellGet(args ...Value) (Value, error) {
	c, ok := args[0].(*Cell)
	if !ok {
		return nil, errors.New("cellget: type error")
	}
	return c.Value, nil
}

func primCellPut(args ...Value) (Value, error) {
	c, ok := args[0].(*Cell)
	if !ok {
		return nil, errors.New("cellput: type error")
	}
	x := args[1]
	c.Value = x
	return c, nil
}

func primStrGet(args ...Value) (Value, error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, errors.New("strget: type error")
	}
	i, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("strget: type error")
	}
	return String(string(s)[int(i)]), nil
}

func primStrCat(args ...Value) (Value, error) {
	s := ""
	err := ForEach(args[0], func(elt Value) error {
		str, ok := elt.(String)
		if !ok {
			return errors.New("strcat: type error")
		}
		s += string(str)
		return nil
	})
	if err != nil {
		return nil, err
	}
	return String(s), nil
}

func primStrLength(args ...Value) (Value, error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, errors.New("strlength: type error")
	}
	return Number(len(string(s))), nil
}

func primSubstringp(args ...Value) (Value, error) {
	sub, ok := args[0].(String)
	if !ok {
		return nil, errors.New("substringp: type error")
	}
	str, ok := args[1].(String)
	if !ok {
		return nil, errors.New("substringp: type error")
	}
	return truth(strings.Index(string(str), string(sub)) != -1), nil
}

func primAtoi(args ...Value) (Value, error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, errors.New("atoi: type error")
	}
	var n float64
	if _, err := fmt.Sscan(string(s), &n); err != nil {
		return Bool(false), nil
	}
	return Number(n), nil
}

func primItoa(args ...Value) (Value, error) {
	n, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("itoa: type error")
	}
	s := fmt.Sprint(float64(n))
	return String(s), nil
}

func primIntern(args ...Value) (Value, error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, errors.New("intern: type error")
	}
	return Intern(string(s)), nil
}

func primAdd(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("+: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("+: type error")
	}
	return Number(float64(a) + float64(b)), nil
}

func primSub(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("-: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("-: type error")
	}
	return Number(float64(a) - float64(b)), nil
}

func primMul(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("*: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("*: type error")
	}
	return Number(float64(a) * float64(b)), nil
}

func primDiv(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("/: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("/: type error")
	}
	return Number(float64(a) / float64(b)), nil
}

func primPow(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("pow: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("pow: type error")
	}
	return Number(math.Pow(float64(a), float64(b))), nil
}

func primEq(args ...Value) (Value, error) {
	return truth(args[0] == args[1]), nil
}

func primNeq(args ...Value) (Value, error) {
	return truth(args[0] != args[1]), nil
}

func primLt(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("<: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("<: type error")
	}
	return truth(float64(a) < float64(b)), nil
}

func primGt(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New(">: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New(">: type error")
	}
	return truth(float64(a) > float64(b)), nil
}

func primLe(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New("<=: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New("<=: type error")
	}
	return truth(float64(a) <= float64(b)), nil
}

func primGe(args ...Value) (Value, error) {
	a, ok := args[0].(Number)
	if !ok {
		return nil, errors.New(">=: type error")
	}
	b, ok := args[1].(Number)
	if !ok {
		return nil, errors.New(">=: type error")
	}
	return truth(float64(a) >= float64(b)), nil
}

func primLog(args ...Value) (Value, error) {
	s, ok := args[0].(String)
	if !ok {
		return nil, errors.New("log: type error")
	}
	fmt.Println(string(s))
	return EmptyList, nil
}

func httpPut(rawURL string, body string) error {
	bakedURL, err := url.Parse(rawURL)
	if err != nil {
		return errors.New("http: parse url fail: " + err.Error())
	}
/*
	header := http.Header(
		map[string][]string{
			"Content-Type": []string{
				"text/plain; charset=utf-8",
			},
		},
	)
*/
	reader := ioutil.NopCloser(strings.NewReader(body))
	request, err := http.NewRequest("PUT", rawURL, reader)
	if err != nil {
		return errors.New(
			"http: error creating request: " + err.Error())
	}
	request.Header.Add("Content-Type", "text/plain; charset=utf-8")
	request.ContentLength = int64(len(body))
	request.Host = bakedURL.Host
/*
	request := &http.Request{
		URL:           bakedURL,
		RawURL:        rawURL,
		Method:        "PUT",
		Header:        header,
		Host:          bakedURL.Host,
		Body:          ioutil.NopCloser(strings.NewReader(body)),
		ContentLength: int64(len(body)),
	}
*/
	response, err := http.DefaultClient.Do(request)
	if err != nil || response.StatusCode != 200 {
		return errors.New("http: put fail: " + err.Error())
	}
	return nil
}

func primHttp(args ...Value) (Value, error) {
	method, ok := args[0].(*Symbol)
	if !ok {
		return nil, errors.New("http: type error")
	}
	url, ok := args[1].(String)
	if !ok {
		return nil, errors.New("http: type error")
	}
	switch method.Name {
	case "get":
		response, err := http.Get(string(url))
		if err != nil {
			return nil, errors.New(
				"http: get fail: " + err.Error(),
			)
		}
		defer response.Body.Close()
		if response.StatusCode != 200 {
			return nil, errors.New(
				"http: get fail: status: " + response.Status,
			)
		}
		text, err := ioutil.ReadAll(response.Body)
		if err != nil {
			return nil, errors.New(
				"http: get fail: " + err.Error(),
			)
		}
		return String(text), nil
	case "put":
		list, ok := args[2].(*List)
		if !ok || list == EmptyList {
			return nil, errors.New("http: bad argument")
		}
		bodyString, ok := list.Head.(String)
		if !ok {
			return nil, errors.New("http: bod argument")
		}
		httpPut(string(url), string(bodyString))
		return EmptyList, nil
	}
	return nil, errors.New("http: unsupported method: " + method.Name)
}

func primNow(args ...Value) (Value, error) {
	ns := time.Now().Nanosecond()
	return Number(float64(ns / 1000000)), nil
}

func primExec(args ...Value) (Value, error) {
	var s String
	var ok bool
	var err error
	s, ok = args[0].(String)
	if !ok {
		return nil, errors.New("exec: bad program name")
	}
	cmdname := string(s)
	cmdargs := make([]string, 0)
	err = ForEach(args[1], func(arg Value) error {
		s, ok = arg.(String)
		if !ok {
			return errors.New("exec: bad argument")
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
		return nil, errors.New("exec: pipe fail")
	}
	go io.Copy(os.Stdout, p)
	err = cmd.Run()
	if err != nil {
		return nil, err
	}
	return EmptyList, nil
}

func primExit(args ...Value) (Value, error) {
	os.Exit(int(args[0].(Number)))
	return nil, errors.New("exit: failed to exit!")
}

func primReadAll(args ...Value) (val Value, err error) {
	defer func() {
		x := recover()
		if x == nil {
			return
		}
		if s, ok := x.(string); ok {
			err = errors.New(s)
			return
		}
		panic(x)
	}()
	buf := bytes.NewBufferString(string(args[0].(String)))
	lits, err := ReadAll(buf)
	if err != nil {
		return
	}
	acc := EmptyList
	for i := len(lits) - 1; i >= 0; i-- {
		acc = &List{LiteralValue(lits[i]), acc}
	}
	return acc, nil
}

func primCompile(args ...Value) (val Value, err error) {
	defer func() {
		x := recover()
		if x == nil {
			return
		}
		if s, ok := x.(string); ok {
			err = errors.New(s)
			return
		}
		panic(x)
	}()
	lit, err := EnsureLiteral(args[0])
	if err != nil {
		err = errors.New("compile: type error")
	}
	return Compile(ParseExpr(lit))
}

var primDecls = [][]interface{}{
	{"typeof x", primTypeof},
	{"symbolname sym", primSymbolName},
	{"cons a d", primCons},
	{"car c", primCar},
	{"cdr c", primCdr},
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
	Globals[name] = value
}

func makePrim(decl []interface{}) *Template {
	protocol := decl[0].(string)
	parts := strings.Split(protocol, " ")
	name := parts[0]
	nargs := len(parts) - 1
	prim := decl[1].(func(...Value) (Value, error))
	return NewPrimTemplate(name, nargs, prim)
}

func init() {
	for _, decl := range primDecls {
		temp := makePrim(decl)
		define(temp.Name, NewFunc(temp, nil))
	}
	define("apply", ApplyFunc)
	define("call/cc", CallccFunc)
	define("T", Bool(true))
	define("F", Bool(false))
}
