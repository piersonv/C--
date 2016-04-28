#lang eopl

(define-datatype program program?
 (a-program(expl1 expression?)))

(define-datatype expression expression?
 (const-exp(num number?))
 (diff-exp
       (exp1 expression?)
       (exp2 expression?))
 (zero?-exp(exp1 expression?))
 (if-exp
      (exp1 expression?) 
      (exp2 expression?)
      (exp3 expression?))
 (var-exp(var symbol?))
 (let-exp
      (var symbol?)
      (exp1 expression?)
      (body expression?))
  (minus-exp(exp1 expression?))
  (equal?-exp
   (exp1 expression?)
   (exp2 expression?))
  (greater?-exp
   (exp1 expression?)
   (exp2 expression?))
  (less?-exp
   (exp1 expression?)
   (exp2 expression?))
  (let*-exp
   (vars (list-of symbol?))
   (exprs (list-of expression?))
   (body expression?)))

 (define-datatype expval expval?
    (num-val
      (value number?))
    (bool-val
      (boolean boolean?))
    (proc-val 
      (proc proc?)))

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

  (define expval->proc
    (lambda (v)
      (cases expval v
	(proc-val (proc) proc)
	(else (expval-extractor-error 'proc v)))))

  (define expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
	variant value)))

  (define-datatype proc proc?
    (procedure
      (bvar symbol?)
      (body expression?)
      (env environment?)))


(define-datatype environment environment?
  (empty-env)
  (extend-env
   (saved-var var?)
   (saved-val scheme-value?)
   (saved-env environment?))
  (extend-env*
   (saved-vars (list-of var?))
   (saved-vals (list-of scheme-value?))
   (saved-env environment?)))

(define var? symbol?)
(define scheme-value? (lambda (s) #t))


(define help-extend-env*
  (lambda (vars vals search-var env)
    (cond
      ((null? vars) (apply-env env search-var))
      (else (if (eqv? (car vars) search-var) (car vals)
            (help-extend-env* (cdr vars) (cdr vals) search-var env))))))
    
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? search-var saved-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env* (saved-vars saved-vals saved-env)
                   (help-extend-env* saved-vars saved-vals search-var saved-env)))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define help-has-binding?
  (lambda (vars vals search-var env)
    (cond
      ((null? vars) (has-binding? env search-var))
      (else (if (eqv? (car vars) search-var) #t
            (help-extend-env* (cdr vars) (cdr vals) search-var))))))

(define has-binding?
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 #f)
      (extend-env (saved-var saved-val saved-env)
                  (or (eqv? search-var saved-var)
                      (has-binding? saved-env search-var)))
      (extend-env* (saved-vars saved-vals saved-env)
                   (help-has-binding? saved-vars saved-vals search-var saved-env))
    )))

(define the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("%" (arbno (not #\newline))) skip)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      ))
  
  (define the-grammar
    '((program (expression) a-program)

      (expression (number) const-exp)
      (expression
        ("-" "(" expression "," expression ")")
        diff-exp)
      
      (expression
       ("zero?" "(" expression ")")
       zero?-exp)

      (expression
       ("if" expression "then" expression "else" expression)
       if-exp)

      (expression (identifier) var-exp)

      (expression
       ("let" identifier "=" expression "in" expression)
       let-exp)   

      (expression
       ("minus" "(" expression ")")
       minus-exp)
      
      (expression
       ("equal?" "(" expression "," expression ")")
       equal?-exp)
       
      (expression
       ("greater?" "(" expression "," expression ")")
       greater?-exp)
       
      (expression
       ("less?" "(" expression "," expression ")")
       less?-exp)
      
      (expression
       ("let*" (arbno identifier "=" expression) "in" expression)
       let*-exp)
      ))

(define scan&parse
     (sllgen:make-string-parser the-lexical-spec the-grammar))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

 (define value-of-program 
    (lambda (pgm)
      (cases program pgm
        (a-program (exp1)
          (value-of exp1 (init-env))))))

 (define help-let
          (lambda (exps env)
            (cond
              ((null? exps) '())
              (else (cons (value-of (car exps) env)(help-let (cdr exps) env))))))
 
  (define value-of
    (lambda (exp env)
      (cases expression exp
        (const-exp (num) (num-val num))
        (var-exp (var) (apply-env env var))
        (diff-exp (exp1 exp2)
          (let ((val1 (value-of exp1 env))
                (val2 (value-of exp2 env)))
            (let ((num1 (expval->num val1))
                  (num2 (expval->num val2)))
              (num-val
                (- num1 num2)))))
        (zero?-exp (exp1)
          (let ((val1 (value-of exp1 env)))
            (let ((num1 (expval->num val1)))
              (if (zero? num1)
                (bool-val #t)
                (bool-val #f)))))
        (if-exp (exp1 exp2 exp3)
          (let ((val1 (value-of exp1 env)))
            (if (expval->bool val1)
              (value-of exp2 env)
              (value-of exp3 env))))
        (let-exp (var exp1 body)       
          (let ((val1 (value-of exp1 env)))
            (value-of body
              (extend-env var val1 env))))
        (minus-exp (exp1)
           (let ((val1 (value-of exp1 env)))
             (let ((num1 (* (expval->num val1) -1)))
             (num-val num1))))
        (equal?-exp (exp1 exp2)
           (let ((val1 (value-of exp1 env))(val2 (value-of exp2 env)))
             (let((num1 (expval->num val1))(num2 (expval->num val2)))
               (if (eqv? num1 num2) (bool-val #t)
                   (bool-val #f)))))
        (greater?-exp (exp1 exp2)
           (let ((val1 (value-of exp1 env))(val2 (value-of exp2 env)))
             (let((num1 (expval->num val1))(num2 (expval->num val2)))
               (if (> num1 num2) (bool-val #t)
                   (bool-val #f)))))
        (less?-exp (exp1 exp2)
           (let ((val1 (value-of exp1 env))(val2 (value-of exp2 env)))
             (let((num1 (expval->num val1))(num2 (expval->num val2)))
               (if (< num1 num2) (bool-val #t)
                   (bool-val #f)))))
       
        (let*-exp (vars exps body)
           (let ((vals (help-let exps env)))
             (value-of body (extend-env* vars vals env))))
        )))

(define init-env 
    (lambda ()
      (extend-env 
       'i (num-val 1)
       (extend-env
        'v (num-val 5)
        (extend-env
         'x (num-val 10)
         (empty-env))))))