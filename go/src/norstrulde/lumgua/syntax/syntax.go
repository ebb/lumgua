package syntax

import (
	"bufio"
	"errors"
	"io"
	. "norstrulde/lumgua/machine"
	"strconv"
)

var readTable map[byte]func(io.ByteScanner) Literal

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
	n, err := strconv.ParseFloat(atom, 64)
	if err == nil {
		return Number(n)
	}
	return Intern(atom)
}

func readQuote(buf io.ByteScanner) Literal {
	x := read(buf)
	return newListLiteral(Intern("quote"), x)
}

func readQuasi(buf io.ByteScanner) Literal {
	x := read(buf)
	return newListLiteral(Intern("quasiquote"), x)
}

func readComma(buf io.ByteScanner) Literal {
	b, err := buf.ReadByte()
	if err != nil {
		panic("read: incomplete comma")
	}
	tag := Intern("unquote")
	if b == '@' {
		tag = Intern("unquotesplicing")
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
	return newListLiteral(Intern("ampersand"), x)
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

func ReadAll(r io.Reader) (lits []Literal, err error) {
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
}

type ListLiteral struct {
	items []Literal
}

func newListLiteral(items ...Literal) *ListLiteral {
	return &ListLiteral{items}
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

func EnsureLiteral(x Value) (Literal, error) {
	switch x := x.(type) {
	case Number, *Symbol, String:
		return x, nil
	case *List:
		items := make([]Literal, x.Len())
		rest := x
		for i := 0; i < len(items); i++ {
			var err error
			items[i], err = EnsureLiteral(rest.Head)
			if err != nil {
				return nil, err
			}
			rest = rest.Tail
		}
		return &ListLiteral{items}, nil
	}
	return nil, errors.New("EnsureLiteral: value is not a literal")
}

func LiteralValue(lit Literal) Value {
	switch x := lit.(type) {
	case *ListLiteral:
		tail := EmptyList
		for i := x.len() - 1; i >= 0; i-- {
			tail = &List{LiteralValue(x.at(i)), tail}
		}
		return tail
	}
	return lit
}

func parseParams(lit Literal) []*Symbol {
	x, ok := lit.(*ListLiteral)
	if !ok {
		panic("ParseExpr: ill-formed parameter list")
	}
	params := make([]*Symbol, x.len())
	for i, item := range x.items {
		params[i], ok = item.(*Symbol)
		if !ok {
			panic("ParseExpr: bad parameter")
		}
	}
	return params
}

func parseInits(lit Literal) []InitPair {
	list, ok := lit.(*ListLiteral)
	if !ok || list.len() == 0 {
		panic("ParseExpr: ill-formed init list")
	}
	inits := make([]InitPair, list.len())
	for i, item := range list.items {
		pair, ok := item.(*ListLiteral)
		if !ok || pair.len() != 2 {
			panic("ParseExpr: ill-formed init list")
		}
		inits[i].name, ok = pair.head().(*Symbol)
		inits[i].expr = ParseExpr(pair.at(1))
	}
	return inits
}

func parseEach(forms []Literal) []Expr {
	exprs := make([]Expr, len(forms))
	for i, form := range forms {
		exprs[i] = ParseExpr(form)
	}
	return exprs
}

func parseCondClause(form Literal) CondClause {
	list, ok := form.(*ListLiteral)
	if !ok || list.len() < 2 {
		panic("ParseExpr: ill-formed cond clause")
	}
	head := list.head()
	if head == Intern("else") {
		return CondClause{
			QuoteExpr{Bool(true)},
			parseEach(list.items[1:]),
		}
	}
	return CondClause{
		ParseExpr(head),
		parseEach(list.items[1:]),
	}
}

func analyzeUnquotesplicing(lit Literal) (Literal, bool) {
	form, ok := lit.(*ListLiteral)
	if !ok || form.len() != 2 {
		return nil, false
	}
	if form.head() == Literal(Intern("unquotesplicing")) {
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
		return newListLiteral(Intern("quote"), lit)
	}
	x := lit.(*ListLiteral)
	if x.len() == 0 {
		return newListLiteral(Intern("quote"), lit)
	}
	head := x.head()
	if head == Intern("unquote") {
		if x.len() != 2 {
			panic("expandQuasi: ill-formed unquote")
		}
		return x.at(1)
	}
	if head == Intern("quasiquote") {
		if x.len() != 2 {
			panic("expandQuasi: ill-formed quasiquote")
		}
		return expandQuasi(expandQuasi(x.at(1)))
	}
	if subLit, ok := analyzeUnquotesplicing(head); ok {
		return newListLiteral(
			Intern("append"),
			subLit,
			expandQuasi(x.tail()),
		)
	}
	return newListLiteral(
		Intern("cons"),
		expandQuasi(head),
		expandQuasi(x.tail()),
	)
}

func parseMatchClause(lit Literal) MatchClause {
	var clause MatchClause
	x, ok := lit.(*ListLiteral)
	if !ok || x.len() < 2 {
		panic("ParseExpr: ill-formed match clause")
	}
	sym, ok := x.head().(*Symbol)
	if ok && sym == Intern("else") {
		// TODO - this is awkward
		clause.tag = sym
		clause.params = []*Symbol{}
		clause.body = parseEach(x.items[1:])
		return clause
	}
	pattern, ok := x.head().(*ListLiteral)
	if !ok || pattern.len() == 0 {
		panic("ParseExpr: ill-formed match clause")
	}
	clause.tag, ok = pattern.head().(*Symbol)
	if !ok {
		panic("ParseExpr: ill-formed match clause")
	}
	clause.params = make([]*Symbol, pattern.len()-1)
	for i, item := range pattern.items[1:] {
		clause.params[i], ok = item.(*Symbol)
		if !ok {
			panic("ParseExpr: ill-formed match clause")
		}
	}
	clause.body = parseEach(x.items[1:])
	return clause
}

func ParseExpr(lit Literal) Expr {
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
		panic("ParseExpr: nonliteral")
	}
	if x.len() == 0 {
		panic("ParseExpr: empty expression")
	}
	head, ok := x.head().(*Symbol)
	if !ok {
		panic("ParseExpr: compound form does not start with a symbol")
	}
	if head == Intern("quasiquote") {
		if x.len() != 2 {
			panic("ParseExpr: ill-formed quasiquote")
		}
		return ParseExpr(expandQuasi(x.at(1)))
	}
	if head == Intern("ampersand") {
		if x.len() != 2 {
			panic("ParseExpr: ill-formed ampersand")
		}
		list, ok := x.at(1).(*ListLiteral)
		if !ok {
			panic("ParseExpr: ill-formed ampersand")
		}
		return AmpersandExpr{parseEach(list.items)}
	}
	if head == Intern("quote") {
		if x.len() != 2 {
			panic("ParseExpr: ill-formed quote")
		}
		return QuoteExpr{LiteralValue(x.at(1))}
	}
/*
	if head == Intern("if") {
		if x.len() != 4 {
			panic("ParseExpr: ill-formed if")
		}
		return IfExpr{
			ParseExpr(x.at(1)),
			ParseExpr(x.at(2)),
			ParseExpr(x.at(3)),
		}
	}
*/
	if head == Intern("begin") {
		if x.len() < 2 {
			panic("ParseExpr: ill-formed begin")
		}
		body := parseEach(x.items[1:])
		return BeginExpr{body}
	}
	if head == Intern("goto") {
		if x.len() != 2 {
			panic("ParseExpr: ill-formed goto")
		}
		return GotoExpr{ParseExpr(x.at(1))}
	}
	if head == Intern("func") {
		if x.len() < 3 {
			panic("ParseExpr: ill-formed func")
		}
		params := parseParams(x.at(1))
		body := parseEach(x.items[2:])
		return FuncExpr{params, body}
	}
	if head == Intern("let") {
		if x.len() < 3 {
			panic("ParseExpr: ill-formed let")
		}
		inits := parseInits(x.at(1))
		body := parseEach(x.items[2:])
		return LetExpr{inits, body}
	}
	if head == Intern("define") {
		if x.len() < 3 {
			panic("ParseExpr: ill-formed define")
		}
		switch pattern := x.at(1).(type) {
		case *Symbol:
			return DefineExpr{pattern, ParseExpr(x.at(2))}
		case *ListLiteral:
			if pattern.len() == 0 {
				panic("ParseExpr: ill-formed define")
			}
			name, ok := pattern.head().(*Symbol)
			if !ok {
				panic("ParseExpr: ill-formed define")
			}
			funcExpr := FuncExpr{
				parseParams(pattern.tail()),
				parseEach(x.items[2:]),
			}
			return DefineExpr{name, funcExpr}
		}
		panic("ParseExpr: ill-formed define")
	}
	if head == Intern("if") {
		if x.len() < 2 {
			panic("ParseExpr: ill-formed if")
		}
		clauses := make([]CondClause, x.len()-1)
		for i, item := range x.items[1:] {
			clauses[i] = parseCondClause(item)
		}
		return CondExpr{clauses}
	}
	if head == Intern("and") {
		return AndExpr{parseEach(x.items[1:])}
	}
	if head == Intern("or") {
		return OrExpr{parseEach(x.items[1:])}
	}
	if head == Intern("match") {
		if x.len() < 3 {
			panic("ParseExpr: ill-formed match")
		}
		clauses := make([]MatchClause, x.len()-2)
		for i, item := range x.items[2:] {
			clauses[i] = parseMatchClause(item)
		}
		return MatchExpr{
			ParseExpr(x.at(1)),
			clauses,
		}
	}
	items := x.items
	if head == Intern("call") {
		if len(items) == 1 {
			panic("ParseExpr: empty call")
		}
		items = items[1:]
		// fall through
	}
	funcExpr := ParseExpr(items[0])
	argExprs := parseEach(items[1:])
	return CallExpr{funcExpr, argExprs}
}

func Parse(lit Literal) (_ Expr, err error) {
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
	return ParseExpr(lit), nil
}

type Expr interface {
	exprVariant()
}

type RefExpr struct {
	Name *Symbol
}

type QuoteExpr struct {
	X Value
}

type IfExpr struct {
	CondExpr Expr
	ThenExpr Expr
	ElseExpr Expr
}

type BeginExpr struct {
	Body []Expr
}

type GotoExpr struct {
	Expr Expr
}

type FuncExpr struct {
	Params []*Symbol
	Body   []Expr
}

type CallExpr struct {
	FuncExpr Expr
	ArgExprs []Expr
}

type AmpersandExpr struct {
	exprs []Expr
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
	Name *Symbol
	Expr Expr
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
func (_ GotoExpr) exprVariant()      {}
func (_ FuncExpr) exprVariant()      {}
func (_ CallExpr) exprVariant()      {}

type MacroExpr interface {
	Expand() Expr
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

func (expr AmpersandExpr) Expand() Expr {
	acc := Expr(QuoteExpr{EmptyList})
	for i := len(expr.exprs) - 1; i >= 0; i-- {
		acc = CallExpr{
			RefExpr{Intern("cons")},
			[]Expr{
				expr.exprs[i],
				acc,
			},
		}
	}
	return acc
}

func (expr LetExpr) Expand() Expr {
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

func (expr CondExpr) Expand() Expr {
	acc := Expr(QuoteExpr{EmptyList})
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

func (expr AndExpr) Expand() Expr {
	acc := Expr(QuoteExpr{Bool(true)})
	for i := len(expr.exprs) - 1; i >= 0; i-- {
		acc = IfExpr{
			expr.exprs[i],
			acc,
			QuoteExpr{Bool(false)},
		}
	}
	return acc
}

func (expr OrExpr) Expand() Expr {
	acc := Expr(QuoteExpr{Bool(false)})
	for i := len(expr.exprs) - 1; i >= 0; i-- {
		acc = IfExpr{
			expr.exprs[i],
			QuoteExpr{Bool(true)},
			acc,
		}
	}
	return acc
}

func (expr MatchExpr) Expand() Expr {
	i := len(expr.clauses) - 1
	clause := expr.clauses[i]
	var acc Expr
	var defaultExpr Expr // XXX - code gets duplicated in the expansion
	if clause.tag == Intern("else") {
		funcExpr := FuncExpr{
			[]*Symbol{Intern("tag"), Intern("args")},
			[]Expr{CallExpr{RefExpr{Intern("f")}, []Expr{}}},
		}
		acc = LetExpr{
			[]InitPair{{
				Intern("f"),
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
			[]*Symbol{Intern("tag"), Intern("args")},
			[]Expr{CallExpr{
				RefExpr{Intern("throw")},
				[]Expr{QuoteExpr{String("match: no match")}},
			}},
		}
		defaultExpr = CallExpr{
			RefExpr{Intern("throw")},
			[]Expr{QuoteExpr{String("match: no match")}},
		}
	}
	for i >= 0 {
		funcExpr := FuncExpr{
			[]*Symbol{Intern("tag"), Intern("args")},
			[]Expr{IfExpr{
				CallExpr{
					RefExpr{Intern("=")},
					[]Expr{
						RefExpr{Intern("tag")},
						QuoteExpr{expr.clauses[i].tag},
					},
				},
				CallExpr{
					RefExpr{Intern("apply")},
					[]Expr{
						RefExpr{Intern("f")},
						RefExpr{Intern("args")},
					},
				},
				CallExpr{
					RefExpr{Intern("g")},
					[]Expr{
						RefExpr{Intern("tag")},
						RefExpr{Intern("args")},
					},
				},
			}},
		}
		acc = LetExpr{
			[]InitPair{{
				Intern("f"),
				FuncExpr{
					expr.clauses[i].params,
					expr.clauses[i].body,
				},
			}, {
				Intern("g"),
				acc,
			}},
			[]Expr{funcExpr},
		}
		i--
	}
	return LetExpr{
		[]InitPair{
			{Intern("x"), expr.x},
			{Intern("f"), acc},
		},
		[]Expr{IfExpr{
			CallExpr{
				RefExpr{Intern("consp")},
				[]Expr{RefExpr{Intern("x")}},
			},
			CallExpr{
				RefExpr{Intern("f")},
				[]Expr{
					CallExpr{
						RefExpr{Intern("car")},
						[]Expr{RefExpr{Intern("x")}},
					},
					CallExpr{
						RefExpr{Intern("cdr")},
						[]Expr{RefExpr{Intern("x")}},
					},
				},
			},
			defaultExpr,
		}},
	}
}

func init() {
	readTable = map[byte]func(io.ByteScanner) Literal{
		'"':  readString,
		'\'': readQuote,
		'`':  readQuasi,
		',':  readComma,
		'&':  readAmpersand,
		'(':  readList,
	}
}
