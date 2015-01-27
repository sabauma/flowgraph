#lang racket/base

(provide (all-defined-out))

(require redex)

(define-language FLOW
  (block    (BL (arg ...) (op ...) x L))
  (op       (x := (opname arg ...)))
  (opname   primop call)
  (primop   add sub mult div equal lt cons car cdr)
  (arg      val x)
  (val      n b funptr (val ...))
  (link     (LINK x (arg ...))) ;; Link -- contains the block id and args to pass
  (lidx     n b default)        ;; Link index
  (funptr   (FUN x))
  (n        integer)
  (b        boolean)
  (x        variable-not-otherwise-mentioned)
  (E        ((x val) ...))      ;; Evaluation env -- mapping from names to values
  (P        ((x block) ...))    ;; Program        -- mapping from names to blocks
  (L        ((lidx link) ...))  ;; Link env       -- mapping from values to names
  )

(define-metafunction FLOW
  δ : primop (val ...) -> val
  [(δ add   (val ...))         ,(apply +  (term (val ...)))]
  [(δ sub   (val ...))         ,(apply -  (term (val ...)))]
  [(δ mult  (val ...))         ,(apply *  (term (val ...)))]
  [(δ div   (val ...))         ,(apply /  (term (val ...)))]
  [(δ equal (val ...))         ,(apply =  (term (val ...)))]
  [(δ lt    (val ...))         ,(apply <  (term (val ...)))]
  [(δ gt    (val ...))         ,(apply >  (term (val ...)))]
  [(δ lte   (val ...))         ,(apply <= (term (val ...)))]
  [(δ gte   (val ...))         ,(apply >= (term (val ...)))]
  [(δ cons  (val (val_1 ...))) (val val_1 ...)]
  [(δ head  ((val _ ...)))     val]
  [(δ tail  ((_ val ...)))     (val ...)]
  )

(define-extended-language FLOW+AS FLOW
  (S ε (FR E x block S)) ;; Stack: environment and remainder of block
  ;; Interpreter state consissts of
  ;; * Current block being interpreted
  ;; * Environment
  ;; * Stack
  ;; * Current function (collection of blocks)
  ;; * Current program  (collection of functions)
  (state (DONE n) (block E S P))
  )

(define-extended-language FLOW+JIT FLOW+AS
  (op    (jit-merge-point val) (jit-can-enter val) (guard x) +)
  (trace (op ...))
  )

;; Based off of https://github.com/esilkensen/cwc/blob/master/mates-silkensen.rkt
(define-metafunction FLOW
  extend : ((x any) ...) (x ...) (any ...) -> ((x any) ...)
  [(extend ((x_1 any_1) ...) (x ..._n) (any ..._n))
   ((x_1 any_1) ... (x any) ...)]
  )

;; Looking up bindings in environments:
(define-metafunction FLOW
  lookup-env : E x -> any
  [(lookup-env ((x_1 any_1) ... (x any) (x_2 any_2) ...) x)
   (x any)
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(lookup-env ((x_1 any_1) ...) x_2) #f]
  )

(define-metafunction FLOW
  lookup-block : P x -> any
  [(lookup-block ((x_1 block_1) ... (x block) (x_2 block_2) ...) x)
    block
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(lookup-block ((x_1 block_1) ...) x_2) #f]
  )

(define-metafunction FLOW
  lookup-link : L lidx -> any
  [(lookup-link ((lidx_1 _) ... (lidx link) (lidx_2 _) ...) lidx)
   link
   (side-condition (not (member (term lidx) (term (lidx_2 ...)))))]
  [(lookup-link ((lidx link) ...) lidx_1) #f]
  )

(define-metafunction FLOW
  eval-arg : arg E P -> any
  [(eval-arg x E P) val
   (where (x_1 val) (lookup-env E x))]
  [(eval-arg val E P) val]
  [(eval-arg x E P) (FUN x)
   (side-condition (term (lookup-block P x)))]
  )

(define-metafunction FLOW
  eval-args : (arg ...) E P -> (any ...)
  [(eval-args (arg ...) E P) ((eval-arg arg E P) ...)]
  )

(define-metafunction FLOW
  eval-primop : op E P -> E
  [(eval-primop (x_2 := (primop arg ...)) E P)
   (extend E (x_2) ((δ primop (eval-args (arg ...) E P))))]
  )

(define-metafunction FLOW
  is-primop : op -> any
  [(is-primop (x := (primop arg ...))) #t]
  [(is-primop (x := (call arg ...)))   #f]
  )

(define-metafunction FLOW
  entry-block : F -> block
  [(entry-block F) (lookup-block F entry)]
  )

(define-metafunction FLOW
  setup-env : block (val ...) -> E
  [(setup-env (BL (arg ..._0) (op ...) x L) (val ..._0)) (extend () (arg ...) (val ...))]
  )

(define-metafunction FLOW
  copy-env : (arg ...) E P -> E
  [(copy-env (arg ...) E P)
   (extend () (arg ...) (eval-args (arg ...) E P))]
  )

(define reduce-flow
  (reduction-relation FLOW+AS
    ;; Execute current primop
    (--> ((BL (arg ...) (op_1 op ...) x L) E S P)
         ((BL (arg ...) (op ...) x L) (eval-primop op_1 E P) S P)
         flow-primop
         (side-condition (term (is-primop op_1))))

    ;; Perform call operation
    (--> ((BL (arg_0 ...) ((x_1 := (call arg arg_1 ...)) op ...) x L) E S P)
         (block
          (setup-env block (eval-args (arg_1 ...) E P))
          (FR E x_1 (BL (arg_0 ...) (op ...) x L) S)
          P)
         flow-call
         (where (FUN x_2) (eval-arg arg E P))
         (where block (lookup-block P x_2)))

    ;; Done with the block, see if we can find the associated link
    ;; For now, we just send along the whole environment
    (--> ((BL (_ ...) () x L) E S P)
         (block (setup-env block (eval-args (arg_1 ...) E P)) S P)
         flow-finish-block-link
         ;; Get the value for the exit switch variable
         (where val (eval-arg x E P))
         ;; Get the corresponding link
         (where (LINK x_2 (arg_1 ...)) (lookup-link L val))
         (where block (lookup-block P x_2)))

    ;; If we can't find an associated link, try the default link (-1)
    (--> ((BL (arg ...) () x L) E S P)
         ((BL (arg_1 ...) (op_1 ...) x_1 L_1)
          (copy-env (arg_1 ...) E P) S P)
         flow-finish-block-default
         (where x_1 (lookup-link L default))
         (where (BL (arg_1 ...) (op_1 ...) x_1 L_1) (lookup-block P x_1))
         (where (_ val) (lookup-env E x))
         (side-condition
           (not (term (lookup-link L val)))))

    ;; Empty set of links means we have a return block.
    ;; We return the value in the exitswitch variable.
    (--> ((BL (arg ...) () x ()) E (FR E_1 x_1 block_1 S_1) P)
         (block_1 (extend E_1 (x_1) (val)) S_1 P)
         flow-return
         (where (_ val) (lookup-env E x)))

    ;; Empty links with and empty stack means we are done
    (--> ((BL (arg ...) () x ()) E ε P)
         (DONE (lookup-env E x))
         flow-exit)
    )
  )

