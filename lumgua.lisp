(define t 't)

(define nilp
  (func (x)
    (= x '())))

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

(define flip
  (func (f)
    (func (a b)
      (f b a))))

(define foldl
  (func (f z x)
    (jmp (if (nilp x)
	     z
	   (foldl f (f z (car x))
		  (cdr x))))))

(define foldr
  (func (f z x)
    (foldl (flip f) z (reverse x))))

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
	     '())
	   '()
	   x)))

(define map
  (func (f x)
    (foldr (func (elt z)
	     (cons (f elt) z))
	   '()
	   x)))

(define filter
  (func (pred x)
    (foldr (func (elt z)
	     (cond
	       ((pred elt)
		(cons elt z))
	       (t z)))
	   '()
	   x)))

(define compose
  (func (f g)
    (func (x)
      (f (g x)))))

(define snoc
  (func (d a)
    (cons a d)))

(define reverse
  (func (x)
    (foldl snoc '() x)))

(define append
  (func (x y)
    (cond
     ((nilp y) x)
     ((nilp x) y)
     (t (foldr cons y x)))))

(define not
  (func (x)
    (nilp x)))

(define atomp
  (func (x)
    (or (nilp x) (numberp x) (symbolp x) (stringp x))))

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

(define lookup
  (func (key x)
    (cond
     ((nilp x) '())
     ((= key (caar x)) (cadr (car x)))
     (t (jmp (lookup key (cdr x)))))))

(define strextend
  (func (cell str)
    (cellput cell (strcat &((cellget cell) str)))))

(define escape
  (func (s)
    (let ((n (strlength s))
	  (se (cellnew "")))
      (for 0 n
	   (func (i)
	     (strextend se (let ((c (strget s i)))
			     (cond
			      ((= c "\\") "\\\\")
			      ((= c "\"") "\\\"")
			      ((= c "\n") "\\n")
			      ((= c "\t") "\\t")
			      (t c))))))
      (cellget se))))

(define writecons
  (func (x)
    (let ((inards (foldl (func (z e)
			   (strcat &(z " " (write e))))
			 (write (car x))
			 (cdr x))))
      (strcat &("(" inards ")")))))

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
     ((stringp x) (strcat &("\"" (escape x) "\"")))
     ((cellp x) "<cell>")
     ((arrayp x) "<array>")
     (t (throw "write: unknown type")))))

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
		      (esc '())))
		    (let ((f (arrayget stack (- (cellget fp) 3))))
		      (cellput fp (arrayget stack (- (cellget fp) 2)))
		      (match (funcopen f)
			((func temp env)
			 (match (templateopen temp)
			   ((template name nvars freerefs code)
			    (let ((s (cellnew "(")))
			      (cond
			       ((= name "")
				(strextend s "<anon>"))
			       (t (strextend s name)))
			      (for (cellget fp)
				   (+ (cellget fp) nvars)
				   (func (i)
				     (strextend s " ")
				     (strextend s (write (arrayget stack i)))))
			      (strextend s ")")
			      (log (cellget s)))))))))))))))))

(define time
  (func (f)
    (- 0 (- (now)
	    (begin (f) (now))))))

(define throwfunc
  (cellnew (func (s)
	     (log s)
	     (exit 1))))

(define throw
  (func (s)
    ((cellget throwfunc) s)))

(define repl
  (func ()
    (log (call/cc (func (cc)
		    (cellput throwfunc
			     (func (s)
			       (jmp (call/cc (func (xx)
					       (showbacktrace xx)
					       (cc s))))))
		    "entering REPL")))
    (loop (func ()
	    (let ((text (http 'get "http://localhost:8082/eval" &())))
	      (let ((exps (readall text)))
		(foreach (func (exp)
			   (log (write ((funcnew (compile exp)
						 (arraynew 0))))))
			 exps)))))))

(define detect
  (func (pred x)
    (cond
     ((nilp x) '())
     ((pred (car x)) t)
     (t (detect pred (cdr x))))))

(define member
  (func (x s)
    (detect (func (y) (= x y)) s)))

(define tabify
  (func (vals)
    (strcat (cons (write (car vals))
		  (map (func (val)
			 (strcat &("\t" (write val))))
		       (cdr vals))))))

(define showinstr
  (func (pc instr)
    (log (tabify (cons pc instr)))))

(define showfunc
  (func (f nesting)
    (match (funcopen f)
      ((func temp env)
       (showtemplate temp nesting)))))

(define showtemplate
  (func (template nesting)
    (match (templateopen template)
      ((template name nvars freerefs code)
       (cond
	((consp nesting)
	 (match (nth (car nesting) code)
	   ((close template)
	    (showtemplate template (cdr nesting)))))
	(t
	 (log (strcat &("name: " name)))
	 (log (strcat &("nvars: " (write nvars))))
	 (log (strcat &("freerefs: " (write freerefs))))
	 (foldl (func (pc instr)
		  (showinstr pc instr)
		  (+ pc 1))
		0
		code)
	 '()))))))

(repl)
