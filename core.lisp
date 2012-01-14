(define list (func x x))

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
	     nil)
	   nil
	   x)))

(define map
  (func (f x)
    (foldr (func (elt z)
	     (cons (f elt) z))
	   nil
	   x)))

(define filter
  (func (pred x)
    (foldr (func (elt z)
	     (cond
	       ((pred elt)
		(cons elt z))
	       (t z)))
	   nil
	   x)))

(define compose
  (func (f g)
    (func (x)
      (f (g x)))))

(define snoc
  (flip cons))

(define reverse
  (func (x)
    (foldl snoc nil x)))

(define append
  (func (x y)
    (cond
     ((nilp y) x)
     ((nilp x) y)
     (t (foldr cons y x)))))

(define not
  (func (x)
    (nilp x)))

(define startsp
  (func (x sym)
    (and (consp x) (= (car x) sym))))

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
  (func (key x)
    (cond
     ((nilp x) nil)
     ((= key (caar x)) (cadr (car x)))
     (t (jmp (lookup key (cdr x)))))))
