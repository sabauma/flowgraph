#lang racket/base

(require redex)
(require "flow.rkt")

(test-equal (term (extend ((d 1) (e 2)) (a b c) (1 2 3))) '((d 1) (e 2) (a 1) (b 2) (c 3)))
(test-equal (term (eval-arg c ((a 1) (b 2) (c 3)))) 3)
(test-equal (term (eval-arg 4 ((a 1) (b 2) (c 3)))) 4)
(test-equal (term (eval-primop (x := (add 1 2)) ())) '((x 3)))
(test-equal (term (eval-primop (x := (add y z)) ((y 1) (z 2)))) '((y 1) (z 2) (x 3)))

(define test-block1
  (term
    (BL ()
        ((x1 := (add 1 2))
         (x2 := (add 4 x1))
         (x3 := (mult 2 4)))
        x3
        ((1 B1) (8 B2) (-1 B3))
        )))

(redex-match FLOW block test-block1)

(define test-block2
  (term
    (BL ()
        ((y1 := (add 4 2))
         (y2 := (add y1 2))
         (y3 := (sub y2 2)))
        y3
        ())))
(redex-match FLOW block test-block2)

(define test-function
  (term ((B1 ,test-block1) (B2 ,test-block2))))

(define test-program
  (term (,test-block1 () ε ,test-function ((test ,test-function)))))

(redex-match FLOW+AS state test-program)

