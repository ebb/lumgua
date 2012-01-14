(define simplelet
  (func (bindings body)
    `((func ,(map car bindings)
	.,body)
      .,(map cadr bindings))))

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
  (flip setcons))

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
	((if test then else)
	 (collectfree (list test then else) b p))
	((begin . body)
	 (collectfree body b p))
	((func vars . body)
	 (setminus (collectfree body b (maketruelist vars)) p))
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

(define macrop
  (func (name)
    (member name
	    '(define cond and or matcher match quasiquote let send))))

(define macroexpand
  (func (exp)
    (match exp
      ((define var val)
       `(def ',var ,val))
      ((cond . clauses)
       (foldr (func (clause exp)
		(cond
		 ((= 't (car clause))
		  `(begin .,(cdr clause)))
		 (t
		  `(if ,(car clause)
		       (begin .,(cdr clause))
		     ,exp))))
	      'nil
	      clauses))
      ((and . exps)
       (foldr (func (exp acc)
		`(if ,exp ,acc nil))
	      't
	      exps))
      ((or . exps)
       (foldr (func (exp acc)
		`(if ,exp t ,acc))
	      'nil
	      exps))
      ((matcher . clauses)
       (cond
	((consp clauses)
	 (let ((clause (car clauses)))
	   (cond
	    ((= 't (car clause))
	     `(let ((f (func () .,(cdr clause))))
		(func (x)
		  (f))))
	    ((symbolp (car clause))
	     `(let ((f (func () .,(cdr clause)))
		    (g (matcher .,(cdr clauses))))
		(func (x)
		  (cond
		   ((= x ',(car clause))
		    (f))
		   (t
		    (g x))))))
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
	    (throw "match: no match")))))
      ((match x . clauses)
       `((matcher .,clauses)
	 ,x))
      ((quasiquote exp)
       (qq exp))
      ((let head . tail)
       (cond
	((symbolp head)
	 (throw "no implementation for named let"))
	(t
	 (simplelet head tail))))
      ((send proc msg)
       `(sendmsg ,proc (list ',(car msg) .,(cdr msg))))
      (t (throw (strcat "macroexpand: no match for "
			(write exp)))))))

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
    (startsp instr 'label)))

(define useslabelp
  (func (instr)
    (member (car instr) '(fjump jump frame))))

(define findlabelpc lookup)

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

(define compilefile
  (func (name)
    (let ((text (http 'get (strcat "http://localhost:8082/"
				   name ".lisp"))))
      (let ((exps (readall text))
	    (fasl (cellnew "[\n")))
	(cond
	 ((not (consp exps))
	  (throw "compilefile: no expressions")))
	(log (write (car exps)))
	(strextend fasl (tofasl (compile (car exps))))
	(foreach (func (exp)
		   (log (write exp))
		   (strextend fasl ",\n" (tofasl (compile exp))))
		 (cdr exps))
	(strextend fasl "\n]\n")
	(http 'put (strcat "http://localhost:8082/"
			   name ".fasl")
	      (cellget fasl))
	(log "done!")))))
