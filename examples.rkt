#lang racket/base

(require redex)
(require "flow.rkt")

(test-equal (term (extend ((d 1) (e 2)) (a b c) (1 2 3))) '((d 1) (e 2) (a 1) (b 2) (c 3)))
(test-equal (term (eval-arg c ((a 1) (b 2) (c 3)) ())) 3)
(test-equal (term (eval-arg 4 ((a 1) (b 2) (c 3)) ())) 4)
(test-equal (term (eval-primop (x := (add 1 2)) () ())) '((x 3)))
(test-equal (term (eval-primop (x := (add y z)) ((y 1) (z 2)) ())) '((y 1) (z 2) (x 3)))

(define example1 (term (x := (add 1 a b c 2))))
(define example2 (term (y := (add x c d e))))

(test-equal (term (free-vars-op ,example1)) '(a b c))
(test-equal (term (assigned-vars ,example1)) '(x))


(test-equal (term (free-vars (,example1 ,example2))) '(d e a b c))

(define test-block1
  (term
    (BL ()
        ((x1 := (add 1 2))
         (jit-merge-point x1)
         (x2 := (add 4 x1))
         (x3 := (mult 2 4)))
        x3
        ((1  (LINK B1 ()))
         (8  (LINK B2 ()))
         (-1 (LINK B3 ())))
        )))

(redex-match FLOW+JIT block test-block1)

(define test-block2
  (term
    (BL ()
        ((y1 := (add 4 2))
         (y2 := (add y1 2))
         (y3 := (sub y2 2)))
        y3
        ())))
(redex-match FLOW+JIT block test-block2)

(define test-function
  (term ((B1 ,test-block1) (B2 ,test-block2))))

(define test-program
  (term (,test-block1 () ε ,test-function)))

(redex-match FLOW+JIT state test-program)

(define example-tr
  (term ((x1 := (get 1)) (x := (get 2)))))


(redex-match FLOW+JIT trace example-tr)
(test-equal (term (splice ,example-tr ,example-tr ,example-tr))
            (append example-tr example-tr example-tr))

(term (compile ,example-tr))

