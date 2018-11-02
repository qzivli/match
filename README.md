# match

A pattern matching library for Scheme.


This program was originally designed and implemented by Dan Friedman. It was redesigned and implemented by Erik Hilsdale; some improvements were suggested by Steve Ganz. Additional modifications were made by Kent Dybvig.


## Example

```
(import (edu indiana match))

(define (tree-sum expr)
  (match expr
    [,x (guard (number? x)) x]
    [(,e1 ,e2)
     (let ([v1 (tree-sum e1)]
           [v2 (tree-sum e2)])
       (+ v1 v2))]))

(tree-sum '(1 2))
(tree-sum '(1 (2 3)))
(tree-sum '((1 2) 3))
(tree-sum '((1 2) (3 4)))
(tree-sum '((1 2) (3 (4 5))))

#;(tree-sum '((1 2) (3 (4 #\5))))  ; error

(match '(1 2 1 2 1)
  [(,a ,b ,a ,b ,a) (guard (number? a) (number? b)) (+ a b)])  ; 3

(match '((1 2 3) 5 (1 2 3))
  [((,a ...) ,b (,a ...)) `(,a ... ,b)])  ; (1 2 3 5) or ((1 2 3) ... 5) ?

(parameterize ([match-equality-test (lambda (x y) (equal? x (reverse y)))])
  (match '((1 2 3) (3 2 1))
    [(,a ,a) 'yes]
    [,oops 'no]))  ; yes

```

