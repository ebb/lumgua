(let consp
   (fun (x)
      (and
         (= (typeof x) 'list)
         (!= x '()))))

(let nilp
   (fun (x)
      (= x '())))

(let caar
   (fun (x)
      (car (car x))))

(let cadr
   (fun (x)
      (car (cdr x))))

(let cdar
   (fun (x)
      (cdr (car x))))

(let cddr
   (fun (x)
      (cdr (cdr x))))

(let flip
   (fun (f)
      (fun (a b)
         (f b a))))

(let foldl
   (fun (f z x)
      (cond
         (case (nilp x) z)
         (else
            (goto (foldl f (f z (car x)) (cdr x)))))))

(let foldr
   (fun (f z x)
      (foldl (flip f) z (reverse x))))

(let length
   (fun (x)
      (foldl
         (fun (n elt)
            (+ n 1))
         0
         x)))

(let loop
   (sub (f)
      (begin
         (f)
         (goto (loop f)))))

(let for
   (sub (i n f)
      (cond
         (case (< i n)
            (begin
               (f i)
               (goto (for (+ i 1) n f)))))))

(let foreach
   (sub (f x)
      (cond
         (case (not (nilp x))
            (begin
               (f (car x))
               (goto (foreach f (cdr x))))))))

(let map
   (fun (f x)
      (foldr
         (fun (elt z)
            (cons (f elt) z))
         '()
         x)))

(let filter
   (fun (pred x)
      (foldr
         (fun (elt z)
            (if (pred elt) (cons elt z) z))
         '()
         x)))

(let compose
   (fun (f g)
      (fun (x)
         (f (g x)))))

(let snoc
   (fun (d a)
      (cons a d)))

(let reverse
   (fun (x)
      (foldl snoc '() x)))

(let append
   (fun (x y)
      (cond
         (case (nilp y) x)
         (case (nilp x) y)
         (else (foldr cons y x)))))

(let not
   (fun (x)
      (if x F T)))

(let first car)

(let second cadr)

(let third
   (fun (x)
      (second (cdr x))))

(let fourth
   (fun (x)
      (third (cdr x))))

(let nth
   (fun (n x)
      (if (= n 0)
         (car x)
         (goto (nth (- n 1) (cdr x))))))

(let strextend
   (sub (cell str)
      (cellput cell (strcat &((cellget cell) str)))))

(let escape
   (sub (s)
      (let n (strlength s))
      (let se (cellnew ""))
      (begin
         (for 0 n
            (sub (i)
               (strextend se
                  (block
                     (let c (strget s i))
                     (cond
                        (case (= c "\\") "\\\\")
                        (case (= c "\"") "\\\"")
                        (case (= c "\n") "\\n")
                        (case (= c "\t") "\\t")
                        (else c))))))
         (cellget se))))

(let writelist
   (fun (x)
      (cond
         (case (= x '())
            "()")
         (else
            (let inards
               (foldl
                  (fun (z e)
                     (strcat &(z " " (write e))))
                  (write (car x))
                  (cdr x)))
            (strcat &("(" inards ")"))))))

(let write
   (fun (x)
      (match &((typeof x))
         (case (bool) (if x "T" "F"))
         (case (number) (itoa x))
         (case (symbol) (symbolname x))
         (case (string) (strcat &("\"" (escape x) "\"")))
         (case (list) (writelist x))
         (case (template) "<template>")
         (case (func) "<func>")
         (case (cont) "<cont>")
         (case (cell) "<cell>")
         (case (array) "<array>")
         (else (throw "write: unknown type")))))

(let showoneframe
   (sub (stack f fp)
      (match (funcopen f)
         (case (func temp env)
            (match (templateopen temp)
               (case (template name nvars freerefs code)
                  (let s (cellnew "("))
                  (begin
                     (strextend s (if (= name "") "<anon>" name))
                     (for fp (+ fp nvars)
                        (sub (i)
                           (begin
                              (strextend s " ")
                              (strextend s (write (arrayget stack i))))))
                     (strextend s ")")
                     (log (cellget s)))))))))

(let showbacktrace
   (sub (c)
      (match (contopen c)
         (case (cont rstack stack)
            (let n (arraylength rstack))
            (for 1 n
               (sub (i)
                  (let j (- n i))
                  (match (arrayget rstack j)
                     (case (return f fp pc)
                        (showoneframe stack f fp)))))))))

(let time
   (sub (f)
      (- 0
         (- (now)
            (begin (f) (now))))))

(let hardpanic
   (sub (s)
      (begin
         (log s)
         (exit 1))))

(let throwfunc
   (cellnew hardpanic))

(let throw
   (sub (s)
      (call (cellget throwfunc) s)))

(let repl
   (sub ()
      (begin
         (log
            (call/cc
               (sub (cc)
                  (begin
                     (cellput throwfunc
                        (sub (s)
                           (call/cc
                              (sub (xx)
                                 (let softpanic (cellget throwfunc))
                                 (begin
                                    (cellput throwfunc hardpanic)
                                    (showbacktrace xx)
                                    (cellput throwfunc softpanic)
                                    (cc s))))))
                     "entering REPL"))))
         (loop
            (sub ()
               (let text (http 'get "http://localhost:8082/eval" '()))
               (block
                  (let exps (readall text))
                  (foreach
                     (sub (exp)
                        (log (write (call (funcnew (compile exp) (arraynew 0))))))
                     exps)))))))

(let detect
   (fun (pred x)
      (cond
         (case (nilp x) F)
         (case (pred (car x)) T)
         (else (goto (detect pred (cdr x)))))))

(let member
   (fun (x s)
      (detect (fun (y) (= x y)) s)))

(let tabify
   (fun (vals)
      (strcat
         (cons (write (car vals))
            (map
               (fun (val)
                  (strcat &("\t" (write val))))
               (cdr vals))))))

(let showinstr
   (sub (pc instr)
      (log (tabify (cons pc instr)))))

(let showfunc
   (sub (f nesting)
      (match (funcopen f)
         (case (func temp env)
            (showtemplate temp nesting)))))

(let showtemplate
   (sub (template nesting)
      (match (templateopen template)
         (case (template name nvars freerefs code)
            (cond
               (case (= nesting '())
                  (begin
                     (log (strcat &("name: " name)))
                     (log (strcat &("nvars: " (write nvars))))
                     (log (strcat &("freerefs: " (write freerefs))))
                     (foldl
                        (sub (pc instr)
                           (begin
                              (showinstr pc instr)
                              (+ pc 1)))
                        0
                        code)
                     'end))
               (else
                  (match (nth (car nesting) code)
                     (case (close template)
                        (goto (showtemplate template (cdr nesting)))))))))))

(let main repl)

; some tests
;
; (foo)
; (showfunc showfunc '())
