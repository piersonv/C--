#lang eopl

(define-datatype program program?
 (a-program(expl1 expression?)))

(define-datatype expression expression?
 (const-exp(num number?)) ;done
(binary-exp
       (exp1 expression?)
       (bin string?)
       (exp2 expression?))  
  
; (diff-exp
;       (exp1 expression?)
;       (exp2 expression?))
; (sum-exp
;       (exp1 expression?)
;       (exp2 expression?))
; (prod-exp
;       (exp1 expression?)
 ;      (exp2 expression?))
; (quot-exp
     ;  (exp1 expression?)
      ; (exp2 expression?))
 (if-exp
      (exp1 expression?) 
      (body1 (list-of expression?))
      (body2 (list-of expression?)))
 (var-exp(var symbol?)) ;done
 (let-exp
      (var symbol?)
      (exp1 expression?)
      (body expression?))
  (minus-exp(exp1 expression?)) ;done
 ; (equal?-exp
  ; (exp1 expression?)
  ; (exp2 expression?))
 ; (greater?-exp
 ;  (exp1 expression?)
  ; (exp2 expression?))
 ; (less?-exp
  ; (exp1 expression?)
   ;(exp2 expression?))
  )

 (define-datatype expval expval?
    (num-val
      (value number?))
    (bool-val
      (boolean boolean?)))

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

  (define expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
	variant value)))


(define-datatype environment environment?
  (empty-env)
  (extend-env
   (saved-var var?)
   (saved-val scheme-value?)
   (saved-env environment?)))

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
                      (apply-env saved-env search-var))))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define has-binding?
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 #f)
      (extend-env (saved-var saved-val saved-env)
                  (or (eqv? search-var saved-var)
                      (has-binding? saved-env search-var))))))

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
      
     ; (expression
      ;  ("-" "(" expression "," expression ")")
       ; diff-exp)
     ; (expression
      ;  ("+" "(" expression "," expression ")")
       ; sum-exp)
     ; (expression
      ;  ("*" "(" expression "," expression ")")
      ;  prod-exp)
    ;  (expression
       ; ("/" "(" expression "," expression ")")
       ; quot-exp)
      
      (expression
       ("if" "(" expression ")" "{" (arbno expression) "}" "else" "{" (arbno expression) "}")
       if-exp)

      (expression (identifier) var-exp)

      (expression
       ("let" identifier "=" expression ";" expression)
       let-exp)   

      (expression
       ("--" expression)
       minus-exp)
      
     ; (expression
      ; ("equal?" "(" expression "," expression ")")
      ; equal?-exp)
       
     ; (expression
     ;  ("greater?" "(" expression "," expression ")")
     ;  greater?-exp)
       
     ; (expression
      ; ("less?" "(" expression "," expression ")")
      ; less?-exp)
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
 
 (define help-if
    (lambda (exps env)
      (cond
        ((null? exps) '())
           (else (cons (value-of (car exps) env)(help-if (cdr exps) env))))))

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
        ;(diff-exp (exp1 exp2)
          ;(let ((val1 (value-of exp1 env))
               ; (val2 (value-of exp2 env)))
            ;(let ((num1 (expval->num val1))
                 ; (num2 (expval->num val2)))
             ; (num-val
               ; (- num1 num2)))))
        ;(sum-exp (exp1 exp2)
         ; (let ((val1 (value-of exp1 env))
             ;   (val2 (value-of exp2 env)))
           ; (let ((num1 (expval->num val1))
              ;    (num2 (expval->num val2)))
             ; (num-val
               ; (+ num1 num2)))))
       ; (prod-exp (exp1 exp2)
         ; (let ((val1 (value-of exp1 env))
             ;   (val2 (value-of exp2 env)))
           ; (let ((num1 (expval->num val1))
                ;  (num2 (expval->num val2)))
             ; (num-val
               ; (* num1 num2)))))
       ; (quot-exp (exp1 exp2)
         ; (let ((val1 (value-of exp1 env))
               ; (val2 (value-of exp2 env)))
          ;  (let ((num1 (expval->num val1))
               ;   (num2 (expval->num val2)))
             ; (num-val
               ; (/ num1 num2)))))
        (if-exp (exp1 body1 body2)
          (let ((val1 (value-of exp1 env)))
            (if (expval->bool val1)
              (help-if body1 env)
              (help-if body2 env))))
        (let-exp (var exp1 body)       
          (let ((val1 (value-of exp1 env)))
            (value-of body
              (extend-env var val1 env))))
        (minus-exp (exp1)
           (let ((val1 (value-of exp1 env)))
             (let ((num1 (- (expval->num val1) 1)))
             (num-val num1))))
       ; (equal?-exp (exp1 exp2)
          ; (let ((val1 (value-of exp1 env))(val2 (value-of exp2 env)))
            ; (let((num1 (expval->num val1))(num2 (expval->num val2)))
              ; (if (eqv? num1 num2) (bool-val #t)
                  ; (bool-val #f)))))
       ; (greater?-exp (exp1 exp2)
          ; (let ((val1 (value-of exp1 env))(val2 (value-of exp2 env)))
            ; (let((num1 (expval->num val1))(num2 (expval->num val2)))
              ; (if (> num1 num2) (bool-val #t)
                  ; (bool-val #f)))))
       ; (less?-exp (exp1 exp2)
          ; (let ((val1 (value-of exp1 env))(val2 (value-of exp2 env)))
            ; (let((num1 (expval->num val1))(num2 (expval->num val2)))
              ; (if (< num1 num2) (bool-val #t)
                  ; (bool-val #f)))))
        )))

(define init-env 
    (lambda ()
      (empty-env)))