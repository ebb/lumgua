(define (nilp x)
  (= x '()))

(define (caar x)
  (car (car x)))

(define (cadr x)
  (car (cdr x)))

(define (cdar x)
  (cdr (car x)))

(define (cddr x)
  (cdr (cdr x)))

(define (flip f)
  (func (a b)
    (f b a)))

(define (foldl f z x)
  (jmp (if (nilp x)
	   z
	 (foldl f (f z (car x))
		(cdr x)))))

(define (foldr f z x)
  (foldl (flip f) z (reverse x)))

(define (length x)
  (foldl (func (n elt)
	   (+ n 1))
	 0
	 x))

(define (loop f)
  (jmp (begin (f) (loop f))))

(define (for i n f)
  (jmp (cond
	((< i n)
	 (f i)
	 (for (+ i 1) n f)))))

(define (foreach f x)
  (foldl (func (ignore elt)
	   (f elt)
	   '())
	 '()
	 x))

(define (map f x)
  (foldr (func (elt z)
	   (cons (f elt) z))
	 '()
	 x))

(define (filter pred x)
  (foldr (func (elt z)
	   (cond
	    ((pred elt)
	     (cons elt z))
	    (else z)))
	 '()
	 x))

(define (compose f g)
  (func (x)
    (f (g x))))

(define (snoc d a)
  (cons a d))

(define (reverse x)
  (foldl snoc '() x))

(define (append x y)
  (cond
   ((nilp y) x)
   ((nilp x) y)
   (else (foldr cons y x))))

(define (not x)
  (if x F T))

(define (atomp x)
  (or (nilp x) (numberp x) (symbolp x) (stringp x) (boolp x)))

(define first car)

(define second cadr)

(define (third x)
  (second (cdr x)))

(define (fourth x)
  (third (cdr x)))

(define (nth n x)
  (jmp (cond
	((= n 0) (car x))
	(else (nth (- n 1) (cdr x))))))

(define (strextend cell str)
  (cellput cell (strcat &((cellget cell) str))))

(define (escape s)
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
			    (else c))))))
    (cellget se)))

(define (writecons x)
  (let ((inards (foldl (func (z e)
			 (strcat &(z " " (write e))))
		       (write (car x))
		       (cdr x))))
    (strcat &("(" inards ")"))))

(define (write x)
  (cond
   ((numberp x) (itoa x))
   ((symbolp x) (symbolname x))
   ((nilp x) "()")
   ((consp x) (writecons x))
   ((templatep x) "<template>")
   ((funcp x) "<func>")
   ((contp x) "<cont>")
   ((stringp x) (strcat &("\"" (escape x) "\"")))
   ((boolp x) (if x "<true>" "<false>"))
   ((cellp x) "<cell>")
   ((arrayp x) "<array>")
   (else (throw "write: unknown type"))))

(define (showoneframe stack f fp)
  (match (funcopen f)
    ((func temp env)
     (match (templateopen temp)
       ((template name nvars freerefs code)
	(let ((s (cellnew "(")))
	  (cond
	   ((= name "")
	    (strextend s "<anon>"))
	   (else (strextend s name)))
	  (for fp
	       (+ fp nvars)
	       (func (i)
		 (strextend s " ")
		 (strextend s (write (arrayget stack i)))))
	  (strextend s ")")
	  (log (cellget s))))))))

(define (showbacktraceloop stack fp)
  (cond
   ((!= fp 0)
    (let ((f (arrayget stack (- fp 3)))
	  (fp (arrayget stack (- fp 2))))
      (showoneframe stack f fp)
      (jmp (showbacktraceloop stack fp))))))

(define (showbacktrace c)
  (match (contopen c)
    ((cont stack)
     (showbacktraceloop stack (arraylength stack)))))

(define (time f)
  (- 0 (- (now)
	  (begin (f) (now)))))

(define (hardpanic s)
  (log s)
  (exit 1))

(define throwfunc
  (cellnew hardpanic))

(define (throw s)
  ((cellget throwfunc) s))

(define (repl)
  (log (call/cc
	(func (cc)
	  (cellput throwfunc
		   (func (s)
		     (call/cc (func (xx)
				(let ((softpanic (cellget throwfunc)))
				  (cellput throwfunc hardpanic)
				  (showbacktrace xx)
				  (cellput throwfunc softpanic))
				(cc s)))))
	  "entering REPL")))
  (loop (func ()
	  (let ((text (http 'get "http://localhost:8082/eval" '())))
	    (let ((exps (readall text)))
	      (foreach (func (exp)
			 (log (write ((funcnew (compile exp)
					       (arraynew 0))))))
		       exps))))))

(define (detect pred x)
  (cond
   ((nilp x) F)
   ((pred (car x)) T)
   (else (jmp (detect pred (cdr x))))))

(define (member x s)
  (detect (func (y) (= x y)) s))

(define (tabify vals)
  (strcat (cons (write (car vals))
		(map (func (val)
		       (strcat &("\t" (write val))))
		     (cdr vals)))))

(define (showinstr pc instr)
  (log (tabify (cons pc instr))))

(define (showfunc f nesting)
  (match (funcopen f)
    ((func temp env)
     (showtemplate temp nesting))))

(define (showtemplate template nesting)
  (match (templateopen template)
    ((template name nvars freerefs code)
     (cond
      ((consp nesting)
       (match (nth (car nesting) code)
	 ((close template)
	  (showtemplate template (cdr nesting)))))
      (else
       (log (strcat &("name: " name)))
       (log (strcat &("nvars: " (write nvars))))
       (log (strcat &("freerefs: " (write freerefs))))
       (foldl (func (pc instr)
		(showinstr pc instr)
		(+ pc 1))
	      0
	      code)
       'end)))))

(define main repl)
