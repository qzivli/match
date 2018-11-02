(library (edu indiana compat)
  (export add1 sub1 syntax-error
          make-parameter parameterize
          last-pair make-list
          void)
  (import (rnrs))

  (define (add1 x) (+ x 1))
  (define (sub1 x) (- x 1))

  (define syntax-error error)

  ;; Taken from:
  ;; https://cisco.github.io/ChezScheme/csug9.5/system.html#./system:h13

  (define make-parameter
    (case-lambda
     [(init guard)
      (let ([v (guard init)])
        (case-lambda
         [() v]
         [(u) (set! v (guard u))]))]
     [(init)
      (make-parameter init (lambda (x) x))]))

  (define-syntax parameterize
    (lambda (x)
      (syntax-case x ()
        [(_ () b1 b2 ...) #'(begin b1 b2 ...)]
        [(_ ((x e) ...) b1 b2 ...)
         (with-syntax ([(p ...) (generate-temporaries #'(x ...))]
                       [(y ...) (generate-temporaries #'(x ...))])
             #'(let ([p x] ... [y e] ...)
                 (let ([swap (lambda ()
                               (let ([t (p)]) (p y) (set! y t))
                               ...)])
                   (dynamic-wind swap (lambda () b1 b2 ...) swap))))])))

  (define (last-pair ls)
    (if (null? (cdr ls))
        ls
        (last-pair (cdr ls))))

  (define (void) (if #f 'not-me))

  (define make-list
    (case-lambda
     [(n)
      (make-list n (void))]
     [(n obj)
      (let loop ([n n] [ls '()])
        (if (zero? n)
            ls
            (loop (sub1 n) (cons obj ls))))]))

  ) ; end of library
