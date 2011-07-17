(define list (func x x))

(defmac define
  (func (var val)
    `(begin (def ',var)
	    (set ,var ,val))))

(defmac defmac
  (func (var val)
    `(begin (define ,var ,val)
	    (mac ',var))))

(define t 't)

(define nilp
  (func (x)
    (= x nil)))

(define caar
  (func (x)
    (car (car x))))

(define cadr
  (func (x)
    (car (cdr x))))

(define cdar
  (func (x)
    (cdr (car x))))

(define cddr
  (func (x)
    (cdr (cdr x))))

(defmac cond
  (func clauses
    (foldr (func (clause exp)
	     (cond
	      ((= 't (car clause))
	       `(begin .,(cdr clause)))
	      (t
	       `(if ,(car clause)
		    (begin .,(cdr clause))
		  ,exp))))
	   'nil
	   clauses)))

(define foldl
  (func (f z x)
    (jmp (if (nilp x)
	     z
	   (foldl f (f z (car x))
		  (cdr x))))))

(define foldr
  (func (f z x)
    (if (nilp x)
	z
      (f (car x) (foldr f z (cdr x))))))

(define length
  (func (x)
    (foldl (func (n elt)
	     (+ n 1))
	   0
	   x)))

(define loop
  (func (f)
    (jmp (begin (f) (loop f)))))

(define for
  (func (i n f)
    (jmp (cond
	  ((< i n)
	   (f i)
	   (for (+ i 1) n f))))))

(define foreach
  (func (f x)
    (foldl (func (ignore elt)
	     (f elt)
	     nil)
	   nil
	   x)))

(define map
  (func (f x)
    (foldl (func (y elt)
	     (cons (f elt) y))
	   nil
	   (reverse x))))

(define filter
  (func (pred x)
    (foldl (func (y elt)
	     (cond
	      ((pred elt)
	       (cons elt y))
	      (t y)))
	   nil
	   (reverse x))))

(define compose
  (func (f g)
    (func (x)
      (f (g x)))))

(define snoc
  (func (d a)
    (cons a d)))

(define reverse
  (func (x)
    (foldl snoc nil x)))

(define append
  (func (x y)
    (cond
     ((nilp y) x)
     ((nilp x) y)
     (t (foldl snoc y (reverse x))))))

(define not
  (func (x)
    (nilp x)))

(defmac and
  (func exps
    (foldr (func (exp acc)
	     `(if ,exp ,acc nil))
	   't
	   exps)))

(defmac or
  (func exps
    (foldr (func (exp acc)
	     `(if ,exp t ,acc))
	   'nil
	   exps)))

(define startsp
  (func (x sym)
    (and (consp x) (= (car x) sym))))

(defmac matcher
  (func clauses
    (cond
     ((consp clauses)
      (let ((clause (car clauses)))
	(cond
	 ((= 't (car clause))
	  `(let ((f (func () .,(cdr clause))))
	     (func (x)
	       (f))))
	 (t
	  `(let ((f (func ,(cdar clause)
		      .,(cdr clause)))
		 (g (matcher .,(cdr clauses))))
	     (func (x)
	       (cond
		((startsp x ',(caar clause))
		 (apply f (cdr x)))
		(t
		 (g x)))))))))
     (t
      '(func (x)
	 (throw "match: no match"))))))

(defmac match
  (func (x . clauses)
    `((matcher .,clauses)
      ,x)))

(define atomp
  (func (x)
    (or (nilp x) (numberp x) (symbolp x) (stringp x))))

(define qq
  (func (exp)
    (cond
     ((symbolp exp)
      `(quote ,exp))
     ((atomp exp)
      exp)
     (t
      (match exp
	((quote exp)
	 `(list 'quote ,(qq exp)))
	((unquote exp)
	 exp)
	((quasiquote exp)
	 (qq (qq exp)))
	(t
	 (match (car exp)
	   ((unquotesplicing subexp)
	    `(append ,subexp ,(qq (cdr exp))))
	   (t
	    `(cons ,(qq (car exp))
		   ,(qq (cdr exp)))))))))))

(defmac quasiquote qq)

(define first car)

(define second cadr)

(define third
  (func (x)
    (second (cdr x))))

(define fourth
  (func (x)
    (third (cdr x))))

(define nth
  (func (n x)
    (cond
     ((= n 0) (car x))
     (t (nth (- n 1) (cdr x))))))

(define dottedp
  (func (x)
    (cond
     ((nilp x)
      nil)
     ((consp x)
      (dottedp (cdr x)))
     (t t))))

(define maketruelist
  (func (x)
    (cond
     ((nilp x)
      nil)
     ((consp x)
      (cons (car x) (maketruelist (cdr x))))
     (t
      (list x)))))

(define lookup
  (func (x key)
    (cond
     ((nilp x) nil)
     ((= key (caar x)) (cadr (car x)))
     (t (jmp (lookup (cdr x) key))))))

(define simplelet
  (func (bindings body)
    `((func ,(map car bindings)
	.,body)
      .,(map cadr bindings))))

(defmac let
  (func (head . tail)
    (cond
     ((symbolp head)
      (throw "no implementation for named let"))
     (t
      (simplelet head tail)))))

(defmac send
  (func (proc msg)
    `(sendmsg ,proc (list ',(car msg) .,(cdr msg)))))

(define macroexpand
  (func (exp)
    (apply (global (car exp)) (cdr exp))))

(define detect
  (func (pred x)
    (cond
     ((nilp x) nil)
     ((pred (car x)) t)
     (t (detect pred (cdr x))))))

(define member
  (func (x s)
    (detect (func (y) (= x y)) s)))

(define setmemberp
  (func (x s)
    (member x s)))

(define setcons
  (func (x s)
    (if (setmemberp x s)
	s
      (cons x s))))

(define setsnoc
  (func (s x)
    (setcons x s)))

(define setunion
  (func (s1 s2)
    (foldl setsnoc s1 s2)))

(define setminus
  (func (s1 s2)
    (filter (func (x)
	      (not (setmemberp x s2)))
	    s1)))

(define setintersect
  (func (s1 s2)
    (filter (func (x)
	      (setmemberp x s2))
	    s1)))

(define collectfree
  (func (x b p)
    (foldl setunion nil
	   (map (func (x)
		  (findfree x b p))
		x))))

(define findfree
  (func (x b p)
    (cond
     ((symbolp x)
      (if (and (setmemberp x b)
	       (not (setmemberp x p)))
	  (list x)
	nil))
     ((consp x)
      (match x
	((quote c)
	 nil)
	((set var val)
	 (findfree val b p))
	((if test then else)
	 (collectfree (list test then else) b p))
	((begin . body)
	 (collectfree body b p))
	((func vars . body)
	 (setminus (collectfree body b (maketruelist vars))
		       p))
	(t
	 (collectfree x b p))))
     (t nil))))

(define gen
  (func (instr)
    (list instr)))

(define seq
  (func seqs
    (foldr append nil seqs)))

(define label
  (func ()
    (list 'label)))

(define searching
  (func (var vars n)
    (jmp (cond
	  ((nilp vars) -1)
	  ((= (car vars) var) n)
	  (t (searching var (cdr vars) (+ n 1)))))))

(define find
  (func (var vars succeed fail)
    (let ((n (searching var vars 0)))
      (cond
       ((>= n 0) (succeed n))
       (t (fail))))))

(define locate
  (func (var env)
    (match env
      ((env local free)
       (find var local
		 (func (n)
		   `(local ,n))
		 (func ()
		   (find var free
			     (func (n)
			       `(free ,n))
			     (func ()
			       '(global)))))))))

(define genreturn
  (func (argp tailp)
    (seq (if argp
		 (gen '(push))
	       nil)
	     (if tailp
		 (gen '(return))
	       nil))))

(define expandrefs
  (func (vars env)
    (map (func (var)
	   (locate var env))
	 vars)))

(define compform
  (func (exp env argp tailp)
    (match exp
      ((quote val)
       (compconst val argp tailp))
      ((set var val)
       (seq (comp val env nil nil)
	    (gen `(set ,var))
	    (cond
	     (tailp (gen '(return)))
	     (argp  (gen '(push))))))
      ((if test then else)
       (let ((label0 (label))
	     (label1 (label)))
	 (seq (comp test env nil nil)
	      (gen `(fjump ,label0))
	      (comp then env nil tailp)
	      (cond
	       ((not tailp) (gen `(jump ,label1))))
	      (gen label0)
	      (comp else env nil tailp)
	      (cond
	       ((not tailp) (gen label1)))
	      (cond
	       (argp (gen '(push)))))))
      ((begin . stmts)
       (cond
	((nilp (cdr stmts))
	 (comp (car stmts) env argp tailp))
	(t
	 (seq (comp (car stmts) env nil nil)
	      (comp `(begin .,(cdr stmts)) env argp tailp)))))
      ((jmp exp)
       (cond
	(tailp (comp exp env nil 'jmp))
	(t (throw "compform: jmp in nontail position"))))
      ((func vars . body)
       (match env
	 ((env local free)
	  (let ((propervars (maketruelist vars)))
	    (let ((free (collectfree body (setunion local free)
				     propervars)))
	      (let ((code (comp `(begin .,body)
				`(env ,propervars ,free)
				nil t))
		    (freerefs (expandrefs free env)))
		(seq (gen `(close (template ,vars ,freerefs ,code)))
		     (genreturn argp tailp))))))))
      (t
       (let ((label0 (label)))
	 (seq (cond
	       ((!= tailp 'jmp) (gen `(frame ,label0)))
	       (t nil))
	      (apply seq
		     (map (func (arg)
			    (comp arg env t nil))
			  (cdr exp)))
	      (comp (car exp) env nil nil)
	      (cond
	       ((= tailp 'jmp) (gen '(shift)))
	       (t nil))
	      (gen `(apply ,(length (cdr exp))))
	      (gen label0)
	      (cond
	       ((= tailp 'jmp) nil)
	       (tailp (gen '(return)))
	       (argp  (gen '(push)))
	       (t nil))))))))

(define compconst
  (func (val argp tailp)
    (seq (gen `(const ,val))
	     (genreturn argp tailp))))

(define compref
  (func (var env argp tailp)
    (seq (match (locate var env)
	   ((local n) (gen `(local ,n)))
	   ((free n) (gen `(free ,n)))
	   ((global) (gen `(global ,var))))
	 (genreturn argp tailp))))

(define comp
  (func (exp env argp tailp)
    (cond
     ((consp exp)
      (compform exp env argp tailp))
     ((symbolp exp)
      (compref exp env argp tailp))
     (t
      (compconst exp argp tailp)))))

(define globalp
  (func (var env)
    (match env
      ((env local free)
       (not (or (member var local)
		(member var free)))))))

(define findglobals
  (func (exp env)
    (match env
      ((env local free)
       (cond
	((symbolp exp)
	 (cond
	  ((globalp exp env)
	   (list exp))))
	((atomp exp)
	 nil)
	(t
	 (match exp
	   ((quote subexp)
	    nil)
	   ((set var val)
	    (findglobals val env))
	   ((if pred conseq altern)
	    (foldl (func (acc subexp)
		     (setunion (findglobals subexp env)
			       acc))
		   nil
		   (list pred conseq altern)))
	   ((jmp subexp)
	    (findglobals subexp env))
	   ((begin . subexps)
	    (foldl (func (acc subexp)
		     (setunion (findglobals subexp env)
				   acc))
		   nil
		   subexps))
	   ((func vars . body)
	    (match env
	      ((env local free)
	       (let ((propervars (maketruelist vars)))
		 (let ((free (collectfree body (setunion local free)
					      propervars)))
		   (findglobals `(begin .,body)
				    `(env ,propervars ,free)))))))
	   (t
	    (foldl (func (acc subexp)
		     (setunion (findglobals subexp env)
				   acc))
		   nil
		   exp)))))))))

(define macroexpandall
  (func (exp)
    (cond
     ((atomp exp)
      exp)
     ((consp exp)
      (cond
       ((macrop (car exp))
	(macroexpandall (macroexpand exp)))
       (t
	(match exp
	  ((quote subexp)
	   `(quote ,subexp))
	  ((set var val)
	   `(set ,var ,(macroexpandall val)))
	  ((if pred conseq altern)
	   `(if ,(macroexpandall pred)
		,(macroexpandall conseq)
	      ,(macroexpandall altern)))
	  ((begin . body)
	   `(begin .,(map macroexpandall body)))
	  ((jmp subexp)
	   `(jmp ,(macroexpandall subexp)))
	  ((func vars . body)
	   `(func ,vars .,(map macroexpandall body)))
	  (t
	   (map macroexpandall exp)))))))))

(define labelp
  (func (instr)
    (= (car instr) 'label)))

(define useslabelp
  (func (instr)
    (let ((op (car instr)))
      (or (= op 'fjump)
	  (= op 'jump)
	  (= op 'frame)))))

(define findlabelpc
  (func (label labels)
    (cond
     ((= label (first (car labels)))
      (second (car labels)))
     (t (jmp (findlabelpc label (cdr labels)))))))

(define asm1st
  (let ((gatherlabels
	 (func (acc instr)
	   (let ((addr (car acc))
		 (labels (cdr acc)))
	     (if (labelp instr)
		 (cons addr
		       (cons (list instr addr) labels))
	       (cons (+ 1 addr) labels))))))
    (func (code)
      (cdr (foldl gatherlabels
		  (cons 0 nil)
		  code)))))

(define asm2nd
  (func (code labels)
    (map (func (instr)
	   (if (useslabelp instr)
	       (let ((pc (findlabelpc (second instr) labels)))
		 (list (car instr) pc))
	     (match instr
	       ((close template)
		`(close ,(assemble template)))
	       (t instr))))
	 (filter (compose not labelp) code))))

(define decodevars
  (func (vars f)
    (cond
     ((dottedp vars)
      (f (- (length (maketruelist vars)) 1) t))
     (t
      (f (length vars) nil)))))

(define assemble
  (func (template)
    (match template
      ((template vars freerefs code)
       (let ((labels (asm1st code)))
	 (decodevars
	  vars
	  (func (nvars dottedp)
	    (templatenew
	     nvars
	     dottedp
	     freerefs
	     (asm2nd code labels)))))))))

(define tabify
  (func (vals)
    (apply strcat
	   (cons (write (car vals))
		 (map (func (val)
			(strcat "\t" (write val)))
		      (cdr vals))))))

(define showinstr
  (func (pc instr)
    (log (tabify (cons pc instr)))))

(define showfunc
  (func (f . nesting)
    (match (funcopen f)
      ((func temp env)
       (apply showtemplate (cons temp nesting))))))

(define showtemplate
  (func (template . nesting)
    (match (templateopen template)
      ((template name nvars dottedp freerefs code)
       (cond
	((consp nesting)
	 (match (nth (car nesting) code)
	   ((close template)
	    (apply showtemplate
		   (cons template (cdr nesting))))))
	(t
	 (log (strcat "name: " name))
	 (log (strcat "nvars: " (write nvars)))
	 (log (strcat "dottedp: " (write dottedp)))
	 (log (strcat "freerefs: " (write freerefs)))
	 (foldl (func (pc instr)
		  (showinstr pc instr)
		  (+ pc 1))
		0
		code)
	 nil))))))

(define compile
  (func (exp)
    (assemble
     (match (first (comp `(func () ,(macroexpandall exp))
			     '(env nil nil)
			     nil nil))
       ((close template)
	template)))))

(define strextend
  (func (cell . strs)
    (cellput cell (apply strcat (cons (cellget cell) strs)))))

(define streamnew
  (func (s)
    (let ((i (cellnew 0))
	  (n (strlength s)))
      (func (msg)
	(let ((j (cellget i)))
	  (cond
	   ((= msg 'peek)
	    (if (< j n)
		(strget s j)
	      nil))
	   ((= msg 'advance)
	    (cond
	     ((< j n)
	      (cellput i (+ 1 j)))))
	   (t
	    (throw "unknown stream message"))))))))

(define readall
  (func (s)
    (let ((stream (streamnew s)))
      (reverse (call/cc
		(func (esc)
		  (let ((exps (cellnew nil)))
		    (loop (func ()
			    (skipws stream)
			    (cond
			     ((stream 'peek)
			      (cellput exps (cons (read stream)
						  (cellget exps))))
			     (t (esc (cellget exps)))))))))))))

(define skipws
  (func (stream)
    (let ((c (stream 'peek)))
      (cond
       (c (cond
	   ((whitespacep c)
	    (stream 'advance)
	    (skipws stream))
	   ((= c ";")
	    (nextline stream)
	    (skipws stream))))))))

(define whitespacep
  (func (c)
    (substringp c " \t\n")))

(define nextline
  (func (stream)
    (let ((c (stream 'peek)))
      (cond
       ((and c (!= c "\n"))
	(stream 'advance)
	(nextline stream))))))

(define read
  (func (stream)
    (skipws stream)
    (let ((c (stream 'peek))
	  (table (list (list "`" readquasi)
		       (list "," readcomma)
		       (list "(" readlist)
		       (list "'" readquote)
		       (list "\"" readstring))))
      (cond
       ((nilp c)
	(throw "read: incomplete input")))
      (cond
       ((= c ")")
	(throw "read: unbalanced \")\"")))
      (let ((reader (lookup table c)))
	(if reader
	    (begin (stream 'advance)
		   (reader stream))
	  (readatom stream))))))

(define readquasi
  (func (stream)
    (list 'quasiquote (read stream))))

(define readcomma
  (func (stream)
    (let ((c (stream 'peek)))
      (cond
       ((nilp c)
	(throw "read: syntax error")))
      (cond
       ((= c "@")
	(stream 'advance)
	(list 'unquotesplicing (read stream)))
       (t (list 'unquote (read stream)))))))

(define readlist
  (func (stream)
    (call/cc
     (func (esc)
       (let ((exps (cellnew nil)))
	 (loop (func ()
		 (skipws stream)
		 (cond
		  ((not (stream 'peek))
		   (throw "read: unmatched \"(\"")))
		 (let ((c (stream 'peek)))
		   (cond
		    ((= c ")")
		     (stream 'advance)
		     (esc (reverse (cellget exps))))
		    ((= c ".")
		     (stream 'advance)
		     (cond
		      ((nilp (cellget exps))
		       (throw "read: ill-formed dotted list")))
		     (let ((finalform (read stream)))
		       (skipws stream)
		       (let ((c (stream 'peek)))
			 (cond
			  ((!= c ")")
			   (throw "read: ill-formed dotted list"))
			  (t
			   (stream 'advance)
			   (esc (append (reverse (cdr (cellget exps)))
					(cons (car (cellget exps))
					      finalform))))))))
		    (t (cellput exps
				(cons (read stream)
				      (cellget exps)))))))))))))

(define readquote
  (func (stream)
    (list 'quote (read stream))))

(define readstring
  (func (stream)
    (call/cc
     (func (esc)
       (let ((content (cellnew "")))
	 (let ((pushchar
		(func (c)
		  (stream 'advance)
		  (strextend content c))))
	   (loop (func ()
		   (let ((c (stream 'peek)))
		     (cond
		      ((nilp c)
		       (throw "read: unterminated string"))
		      ((= c "\"")
		       (stream 'advance)
		       (esc (cellget content)))
		      ((= c "\\")
		       (stream 'advance)
		       (let ((c (stream 'peek)))
			 (cond
			  ((nilp c) (throw "unterminated string"))
			  ((= c "t") (pushchar "\t"))
			  ((= c "n") (pushchar "\n"))
			  ((= c "\\") (pushchar "\\"))
			  ((= c "\"") (pushchar "\""))
			  (t (throw (strcat "read: unknown escape: \\" c))))))
		      (t (pushchar c))))))))))))

(define readatom
  (func (stream)
    (let ((terminators "()'\" \t\n"))
      (let ((str (call/cc
		  (func (esc)
		    (let ((buf (cellnew "")))
		      (loop (func ()
			      (let ((c (stream 'peek)))
				(cond
				 ((and c (not (substringp c terminators)))
				  (strextend buf c)
				  (stream 'advance))
				 (t (esc (cellget buf))))))))))))
	(cond
	 ((= str "nil") nil)
	 ((atoi str) (atoi str))
	 (t (intern str)))))))

(define escape
  (func (s)
    (let ((n (strlength s))
	  (se (cellnew "")))
      (for 0 n
	   (func (i)
	     (strextend
	      se (let ((c (strget s i)))
		   (cond
		    ((= c "\\") "\\\\")
		    ((= c "\"") "\\\"")
		    ((= c "\n") "\\n")
		    ((= c "\t") "\\t")
		    (t c))))))
      (cellget se))))

(define improperfoldl
  (func (f g z x)
    (jmp (cond
	  ((consp x)
	   (improperfoldl f g (f z (car x)) (cdr x)))
	  ((nilp x)
	   z)
	  (t
	   (g z x))))))

(define writecons
  (func (x)
    (let ((inards (improperfoldl
		   (func (z e)
		     (strcat z " " (write e)))
		   (func (z e)
		     (strcat z " . " (write e)))
		   (write (car x))
		   (cdr x))))
      (strcat "(" inards ")"))))

(define write
  (func (x)
    (cond
     ((numberp x) (itoa x))
     ((symbolp x) (symbolname x))
     ((nilp x) "nil")
     ((consp x) (writecons x))
     ((templatep x) "<template>")
     ((funcp x) "<func>")
     ((contp x) "<cont>")
     ((stringp x) (strcat "\"" (escape x) "\""))
     ((cellp x) "<cell>")
     ((arrayp x) "<array>")
     (t (throw "write: unknown type")))))

(define listfromarray
  (func (a)
    (let ((len (arraylength a))
	  (x (cellnew nil)))
      (for 1 (+ len 1)
	   (func (i)
	     (cellput x (cons (arrayget a (- len i))
			      (cellget x)))))
      (cellget x))))

(define arrayfromlist
  (func (x)
    (cond
     ((nilp x)
      "[]")
     ((consp x)
      (let ((s (cellnew "[")))
	(strextend s (tojson (car x)))
	(foreach (func (elt)
		   (strextend s "," (tojson elt)))
		 (cdr x))
	(strextend s "]")
	(cellget s)))
     (t
      (throw "arrayfromlist: type error")))))

(define tojson
  (func (x)
    (cond
     ((or (nilp x) (consp x))
      (arrayfromlist x))
     ((numberp x)
      (write x))
     ((stringp x)
      (strcat "\"" (escape x) "\""))
     ((symbolp x)
      (strcat "\"" (symbolname x) "\""))
     (t
      (throw "tojson: unexpected type")))))

(define tofasl
  (func (x)
    (tojson (tofaslexp x))))

(define tofaslexp
  (func (x)
    (cond
     ((or (numberp x)
	  (symbolp x)
	  (nilp x))
      x)
     ((stringp x)
      `("string" ,x))
     ((templatep x)
      (match (templateopen x)
	((template name nvars dottedp freerefs code)
	 `("template" ,nvars ,dottedp ,freerefs
	   ,(map (func (x)
		   (map tofaslexp x))
		 code)))))
     ((consp x)
      (cond
       ((dottedp x)
	`("dotted" ,(map tofaslexp
			 (maketruelist x))))
       (t
	`("list" ,(map tofaslexp x)))))
     (t
      (throw "tofasl: unexpected type")))))

(define refreshimage
  (func ()
    (let ((text (http 'get "http://localhost:8082/lumgua.lisp")))
      (let ((exps (readall text))
	    (fasl (cellnew "[\n")))
	(cond
	 ((not (consp exps))
	  (throw "compilefile: no expressions")))
	(strextend fasl (tofasl (compile (car exps))))
	(foreach (func (exp)
		   (log (write exp))
		   (strextend fasl ",\n" (tofasl (compile exp))))
		 (cdr exps))
	(strextend fasl "\n]\n")
	(http 'put "http://localhost:8082/lumgua.fasl" (cellget fasl))
	(log "done!")))))

(define showbacktrace
  (func (c)
    (match (contopen c)
      ((cont stack)
       (call/cc
	(func (esc)
	  (let ((fp (cellnew (arraylength stack))))
	    (loop (func ()
		    (cond
		     ((= (cellget fp) 0)
		      (esc nil)))
		    (let ((f (arrayget stack (- (cellget fp) 3))))
		      (cellput fp (arrayget stack (- (cellget fp) 2)))
		      (match (funcopen f)
			((func temp env)
			 (match (templateopen temp)
			   ((template name nvars dottedp freerefs code)
			    (let ((s (cellnew "(")))
			      (cond
			       ((= name "")
				(strextend s "<anon>"))
			       (t (strextend s name)))
			      (for (cellget fp)
				   (+ (cellget fp) (+ nvars (if dottedp 1 0)))
				   (func (i)
				     (strextend s " "
						(write (arrayget stack i)))))
			      (strextend s ")")
			      (log (cellget s)))))))))))))))))

(define repl
  (func ()
    (log (call/cc (func (cc)
		    (set throw
			 (func (s)
			   (jmp (call/cc (func (xx)
					   (showbacktrace xx)
					   (cc s))))))
		    "entering REPL")))
    (loop (func ()
	    (let ((text (http 'get "http://localhost:8082/eval")))
	      (let ((exps (readall text)))
		(foreach (func (exp)
			   (log (write ((funcnew (compile exp)
						 (arraynew 0))))))
			 exps)))))))

(repl)
