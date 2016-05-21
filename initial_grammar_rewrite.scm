#lang eopl

(define print eopl:pretty-print)

(define-datatype program program?
 (a-program(expl1 expression?)))

(define-datatype expression expression?
 (const-exp(num number?)) ;done
(binary-exp
       (exp1 expression?)
       (bin string?)
       (exp2 expression?))  
 (if-exp
      (exp1 expression?) 
      (body1 (list-of expression?))
      (body2 (list-of expression?)))
 (var-exp(var symbol?)) ;done
 (let-exp
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))
  (begin-exp
    (exp expression?)
    (exps (list-of expression?)))
  (minus-exp(exp1 expression?)) ;done
  (plus-exp(exp1 expression?))
  (newref-exp
   (exp expression?))
  (deref-exp
   (var expression?))
  (setref-exp
   (var expression?)
   (exp expression?))
  
  (emptylist-exp)
  
  (list-exp
   (exps (list-of expression?)))
  
  (proc-exp
   (vars (list-of identifier?))
   (body expression?))
  
  (letproc-exp
   (name identifier?)
   (vars (list-of identifier?))
   (exp expression?)
   (body expression?))
  
  (letrec-exp
   (names (list-of identifier?))
   (varss (list-of (list-of identifier?)))
   (exps (list-of expression?))
   (body expression?))
  
  (call-exp
   (rator expression?)
   (rand (list-of expression?)))

  (while-exp (cond expression?)
              (body (list-of expression?)))
  
  )

 (define-datatype expval expval?
    (num-val
      (value number?))
    (bool-val
      (boolean boolean?))
   (proc-val
    (proc proc?))
   (list-val
   (lst list?))
   (ref-val
    (ref reference?)))

  (define expval->num
    (lambda (v)
      (cases expval v
	(num-val (num) num)
	(else (expval-extractor-error 'num v)))))

  (define expval->bool
    (lambda (v)
      (cases expval v
	(bool-val (bool) bool)
	(else (expval-extractor-error 'bool v)))))

(define expval->ref
  (lambda (val)
    (cases expval val
      (ref-val (ref) ref)
      (else (expval-extractor-error 'ref val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc val)))))

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (expval-extractor-error 'list val)))))


  (define expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
	variant value)))

 (define-datatype proc proc?
   (procedure
    (vars (list-of identifier?))
    (body expression?)
    (saved-env environment?)))


(define-datatype environment environment?
  (empty-env)
  (extend-env
   (saved-var var?)
   (saved-val scheme-value?)
   (saved-env environment?))
  (extend-env-rec
   (names (list-of identifier?))
   (varss (list-of (list-of identifier?)))
   (exps (list-of expression?))
   (old-env environment?)))

(define var? symbol?)
(define scheme-value? (lambda (s) #t))

(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? search-var saved-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (names varss exps old-env)
                      (define (apply-rec names varss exps)
                        (if (null? names)
                            (apply-env old-env search-var)
                            (if (eqv? search-var (car names))
                                (proc-val (procedure (car varss) (car exps) env))
                                (apply-rec (cdr names) (cdr varss) (cdr exps)))))
                      (apply-rec names varss exps))
      )))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))


(define the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("//" (arbno (not #\newline))) skip)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      (binary-op ((or "-" "+" "*" "/" "==" "!=" ">" "<" ">=" "<=")) string)
      ))
  
  (define the-grammar
    '((program (expression) a-program)

      (expression (number) const-exp)
      
      (expression 
       ("(" expression binary-op expression ")")
       binary-exp)
      
      (expression
       ("if" "(" expression ")" "{" (arbno expression) "}" "else" "{" (arbno expression) "}")
       if-exp)

      (expression (identifier) var-exp)

      (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp) 

      (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
      (expression
       ("--" expression)
       minus-exp)

      (expression
       ("++" expression)
       plus-exp)
      
      (expression ("newref" "(" expression ")") newref-exp)
      (expression ("deref" "(" expression ")") deref-exp)
      (expression ("setref" "(" expression "," expression ")") setref-exp)

      (expression ("emptylist") emptylist-exp)
      (expression ("list" "(" (separated-list expression ",") ")") list-exp)
      (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
      (expression ("letproc" identifier "(" (arbno identifier) ")" expression "in" expression) letproc-exp)
      (expression ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression) "in" expression) letrec-exp)
      (expression ("[" expression (arbno expression) "]") call-exp)
      (expression ("while" "(" expression ")" "{" (arbno expression) "}" ) while-exp)
      ))

(define scan&parse
     (sllgen:make-string-parser the-lexical-spec the-grammar))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

 (define value-of-program 
    (lambda (pgm)
      (initialize-store!)
      (cases program pgm
        (a-program (exp1)
          (value-of exp1 (init-env))))))
 
 ;(define help-if
  ;  (lambda (exps env)
   ;   (cond
    ;    ((null? exps) '())
     ;      (else (cons (value-of (car exps) env)(help-if (cdr exps) env))))))

(define help-if
  (lambda (exps env)
                 (let ((last (value-of (car exps) env)))
                   (define (help-if-rec exps last)
                     (if (null? exps)
                         last
                         (let ((last (value-of (car exps) env)))
                           (help-if-rec (cdr exps) last))))
                   (help-if-rec exps last))))

  (define value-of
    (lambda (exp env)
      (cases expression exp
        (const-exp (num) (num-val num))
        (var-exp (var) (apply-env env var))
        (binary-exp (exp1 bin exp2)
          (let ((val1 (value-of exp1 env))
                (val2 (value-of exp2 env)))
            (let ((num1 (expval->num val1))
                  (num2 (expval->num val2)))
              (cond
                ((equal? bin "-") (num-val(- num1 num2)))
                ((equal? bin "+") (num-val(+ num1 num2)))
                ((equal? bin "*") (num-val(* num1 num2)))
                ((equal? bin "/") (num-val(/ num1 num2)))
                ((equal? bin "==")(if (eqv? num1 num2) (bool-val #t)
                   (bool-val #f)))
                ((equal? bin "!=")(if (eqv? num1 num2) (bool-val #f)
                   (bool-val #t)))
                ((equal? bin "<")(if (< num1 num2) (bool-val #t)
                   (bool-val #f)))
                ((equal? bin ">")(if (> num1 num2) (bool-val #t)
                   (bool-val #f)))
                ((equal? bin "<=")(if (<= num1 num2) (bool-val #t)
                   (bool-val #f)))
                ((equal? bin ">=")(if (>= num1 num2) (bool-val #t)
                   (bool-val #f)))
                )
              )))

        (begin-exp (exp exps)
                 (let ((last (value-of exp env)))
                   (define (begin-exp-rec exps last)
                     (if (null? exps)
                         last
                         (let ((last (value-of (car exps) env)))
                           (begin-exp-rec (cdr exps) last))))
                   (begin-exp-rec exps last)))

        (newref-exp (exp1)
                  (let ((v1 (value-of exp1 env)))
                         (ref-val (newref v1))))
        (deref-exp (exp1)
                   (let ((v1 (value-of exp1 env)))
                     (let ((ref1 (expval->ref v1)))
                       (deref ref1))))
        (setref-exp (exp1 exp2)
                    (let ((ref (expval->ref (value-of exp1 env))))
                      (let ((val2 (value-of exp2 env))) (begin
                                                          (setref! ref val2)
                                                          (num-val 23)))))

        (if-exp (exp1 body1 body2)
          (let ((val1 (value-of exp1 env)))
            (if (expval->bool val1)
              (help-if body1 env)
              (help-if body2 env))))
        
        (let-exp (vars exps body)
               (let ((vals (map (lambda (exp) (value-of exp env)) exps)))
                 (define (add-env vars vals env)
                   (if (null? vars)
                       env
                       (add-env (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env))))
                 (value-of body (add-env vars vals env))))
        
        (minus-exp (exp1)
           (let ((val1 (value-of exp1 env)))
             (let ((num1 (- (expval->num val1) 1)))
             (num-val num1))))
        (plus-exp (exp1)
           (let ((val1 (value-of exp1 env)))
             (let ((num1 (+ (expval->num val1) 1)))
             (num-val num1))))

        (emptylist-exp () (list-val '()))
      
      (list-exp (exps)
                (list-val (map (lambda (exp) (value-of exp env)) exps)))
      
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      
      (letproc-exp (proc-name proc-args proc-body let-body)
                   (let ((proc (proc-val (procedure proc-args proc-body env))))
                     (value-of let-body
                               (extend-env proc-name proc env))))
      
      (letrec-exp (p-name b-var p-body letrec-body)
                  (value-of letrec-body
                            (extend-env-rec p-name b-var p-body env)))
      
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (args (map (lambda (exp) (value-of exp env)) rand)))
                  (apply-procedure proc args)))

        

        ;(while-exp (cond body)
         ;          (if (value-of cond env)
          ;             (help-loop cond body env)
           ;            '()))

        (while-exp (cond body)
        (let loop ()
          (if (value-of cond env)
            (begin
              (help-if body env)
              (loop))
            '())))
        )))


(define help-loop
  (lambda (cond body env)
    (begin
      (help-if body env)
      (if (value-of cond env)
          (help-loop cond body env)
          '()))))

(define init-env 
    (lambda ()
      (empty-env)))

(define (empty-store)
  (make-vector 0))

(define the-store 'uninitialized)

(define (get-val value-of-result)
  (car value-of-result))

(define (get-store)
  the-store)

(define (initialize-store!)
  (set! the-store (empty-store)))

(define (reference? v)
  (integer? v))

(define (identifier? x)
  (and (symbol? x)
       (not (eqv? x 'lambda))))

(define (newref val)
  (let* ((next-ref (vector-length the-store))
         (next-store (make-vector (+ next-ref 1) val)))
    (define (newref-rec idx)
      (if (equal? idx next-ref)
          0
          (begin (vector-set! next-store idx (vector-ref the-store idx))
                 (newref-rec (+ idx 1)))))
    (newref-rec 0)
    (set! the-store next-store)
    next-ref))

(define (deref ref)
  (vector-ref the-store ref))

(define (setref! ref val)
  (vector-set! the-store ref val)
  ref)

(define apply-procedure
  (lambda (proc1 args)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (define (apply-procedure-rec vars vals env)
                   (if (null? vars)
                       (if (null? vals)
                           (value-of body env)
                           (apply-procedure (expval->proc (value-of body env)) vals))
                       (if (null? vals)
                           (procedure vars body env)
                           (apply-procedure-rec (cdr vars) (cdr vals)
                                                (extend-env (car vars) (car vals) env)))))
                 (apply-procedure-rec vars args saved-env)))))

(define program-1
  "begin
 ++5;
   begin
(5 - 4)
end;
--5 end")

(define program-2
  "let x = newref(0)
   in begin
        setref(x, 11);
        setref(x ,(deref(x) - 5));
        -- deref(x)
      end

")

(define program-3 "letrec sum(x y) = if ((x == 0)) {y} else{ [sum (x - 1) (y + 1)]} in [sum 3 2]")

(define program-4 "letrec
                             even(x) = if ((x == 0)) {1} else{ [odd (x - 1)]}
                             odd(x) = if ((x == 0)) {0} else{ [even (x - 1)]}
                           in [odd 13]")


(define program-5 "if( (5 == 6)) {(5 + 1) (1 + 2) } else{ (5 - 1) (1 + 1)} ")

(define program-6 "let x = newref(0) in begin
                              while ( (deref(x) < 1) ){ setref(x, (deref(x) + 2)) } ; deref(x) end")

(define program-7 "let x = newref(3) in begin
                              if ( (deref(x) < 5) ) {1} else {0} ; deref(x) end")

(print (run program-1))
(print (run program-2))


(print (run program-3))

(print (run program-4))

(print (run program-5))

;(print (run program-6))