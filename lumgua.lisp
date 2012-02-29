(define (consp x)
  (and (= (typeof x) 'list)
       (!= x '())))

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
  (jmp (if ((nilp x) z)
	   (else
	    (foldl f (f z (car x))
		   (cdr x))))))

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
  (jmp (if ((< i n)
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
	   (if ((pred elt)
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
  (if ((nilp y) x)
      ((nilp x) y)
      (else (foldr cons y x))))

(define (not x)
  (if (x F)
      (else T)))

(define first car)

(define second cadr)

(define (third x)
  (second (cdr x)))

(define (fourth x)
  (third (cdr x)))

(define (nth n x)
  (jmp (if ((= n 0) (car x))
	   (else (nth (- n 1) (cdr x))))))

(define (strextend cell str)
  (cellput cell (strcat &((cellget cell) str))))

(define (escape s)
  (let ((n (strlength s))
	(se (cellnew "")))
    (for 0 n
	 (func (i)
	   (strextend se (let ((c (strget s i)))
			   (if ((= c "\\") "\\\\")
			       ((= c "\"") "\\\"")
			       ((= c "\n") "\\n")
			       ((= c "\t") "\\t")
			       (else c))))))
    (cellget se)))

(define (writelist x)
  (if ((= x '())
       "()")
      (else
       (let ((inards (foldl (func (z e)
			      (strcat &(z " " (write e))))
			    (write (car x))
			    (cdr x))))
	 (strcat &("(" inards ")"))))))

(define (write x)
  (match &((typeof x))
    ((bool) (if (x "<true>") (else "<false>")))
    ((number) (itoa x))
    ((symbol) (symbolname x))
    ((string) (strcat &("\"" (escape x) "\"")))
    ((list) (writelist x))
    ((template) "<template>")
    ((func) "<func>")
    ((cont) "<cont>")
    ((cell) "<cell>")
    ((array) "<array>")
    (else (throw "write: unknown type"))))

(define (showoneframe stack f fp)
  (match (funcopen f)
    ((func temp env)
     (match (templateopen temp)
       ((template name nvars freerefs code)
	(let ((s (cellnew "(")))
	  (if ((= name "")
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
  (jmp (if ((!= fp 0)
	    (let ((f (arrayget stack (- fp 3)))
		  (fp (arrayget stack (- fp 2))))
	      (showoneframe stack f fp)
	      (showbacktraceloop stack fp))))))

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
  (jmp (if ((nilp x) F)
	   ((pred (car x)) T)
	   (else (detect pred (cdr x))))))

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
  (jmp (match (templateopen template)
	 ((template name nvars freerefs code)
	  (if ((= nesting '())
	       (log (strcat &("name: " name)))
	       (log (strcat &("nvars: " (write nvars))))
	       (log (strcat &("freerefs: " (write freerefs))))
	       (foldl (func (pc instr)
			(showinstr pc instr)
			(+ pc 1))
		      0
		      code)
	       'end)
	      (else
	       (match (nth (car nesting) code)
		 ((close template)
		  (showtemplate template (cdr nesting))))))))))

(define main repl)

; some tests
;
; (foo)
; (showfunc showfunc '())
