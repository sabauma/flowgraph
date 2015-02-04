#lang racket

(provide (all-defined-out))

(require redex)

(define-language FLOW
  (block    (BL args (op ...) arg L))
  (op       (x := (opname arg ...)))
  (opname   primop call)
  (primop   add sub mult div equal lt cons car cdr null? get)
  (arg      val x)
  (args     (arg ...))
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
  [(δ null? (()))              #t]
  [(δ null? _)                 #f]
  [(δ get   (val))             val]
  )

(define-extended-language FLOW+AS FLOW
  ;; pblocks are partial blocks
  ;; They contain only the information necessarry for executing
  ;; the current block, which means they don't need their argument list
  (pb       (PB (op ...) arg L))
  (S        ε (FR E x pb S)) ;; Stack: environment and remainder of block
  ;; Interpreter state consissts of
  ;; * Current block being interpreted
  ;; * Environment
  ;; * Stack
  ;; * Current function (collection of blocks)
  ;; * Current program  (collection of functions)
  (state    (DONE n) (block E S P) (pb E S P))
  )

(define-extended-language FLOW+JIT FLOW+AS
  ;; We add in the JIT related operations
  ;; * jit-merge-point: declares where we are during executions (i.e. the location
  ;;   in the program being interpreted).
  ;; * jit-can-enter: flags a location in the program as a potential place to
  ;;   begin tracing
  (op          .... (guard arg val pb) (jit-merge-point arg) (jit-can-enter arg) +)
  ;; Operations which may appear in traces. These consist of the normal set of ;; operations along with a guard operation.
  ;; * guards: bail back to the saved block if the argument supplied does not
  ;;   evaluate to the value specified.
  (trace-op    op)
  (trace       (trace-op ...))
  (trace-state (pb E S P val trace))
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

(define-metafunction FLOW+JIT
  lookup-block : P x -> any
  [(lookup-block ((x_1 block_1) ... (x block) (x_2 block_2) ...) x)
    block
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(lookup-block ((x_1 block_1) ...) x_2) #f]
  )

(define-metafunction FLOW+JIT
  lookup-link : L lidx -> any
  [(lookup-link ((lidx_1 _) ... (lidx link) (lidx_2 _) ...) lidx)
   link
   (side-condition (not (member (term lidx) (term (lidx_2 ...)))))]
  [(lookup-link ((lidx link) ...) lidx_1) #f]
  )

(define-metafunction FLOW+JIT
  eval-arg : arg E P -> val
  [(eval-arg x E P) val
   (where (x_1 val) (lookup-env E x))]
  [(eval-arg val E P) val]
  [(eval-arg x E P) (FUN x)
   (side-condition (term (lookup-block P x)))]
  )

(define-metafunction FLOW+JIT
  eval-args : (arg ...) E P -> (any ...)
  [(eval-args (arg ...) E P) ((eval-arg arg E P) ...)]
  )

(define-metafunction FLOW+JIT
  eval-primop : op E P -> E
  [(eval-primop (x_2 := (primop arg ...)) E P)
   (extend E (x_2) ((δ primop (eval-args (arg ...) E P))))]
  )

(define-metafunction FLOW+JIT
  is-primop : op -> any
  [(is-primop (x := (primop arg ...))) #t]
  [(is-primop _)                       #f]
  )

(define-metafunction FLOW+JIT
  entry-block : F -> block
  [(entry-block F) (lookup-block F entry)]
  )

(define-metafunction FLOW+JIT
  setup-env : block (val ...) -> E
  [(setup-env (BL (arg ..._0) (op ...) _ L) (val ..._0)) (extend () (arg ...) (val ...))]
  )

(define-metafunction FLOW+JIT
  copy-env : (arg ...) E P -> E
  [(copy-env (arg ...) E P)
   (extend () (arg ...) (eval-args (arg ...) E P))]
  )

(define-metafunction FLOW+JIT
  make-pb : block -> pb
  [(make-pb (BL args (op ...) arg L)) (PB (op ...) arg L)])

;;(define-metafunction FLOW+JIT
;;  make-env-move : arg x

(define-metafunction FLOW+JIT
  make-env-moves : (arg ...) (x ...) -> (op ...)
  [(make-env-moves (arg ..._1) (x ..._1))
   ((x := (get arg)) ...)])

(define-metafunction FLOW+JIT
  block-args : block -> (arg ...)
  [(block-args (BL (arg ...) _ _ _)) (arg ...)])

(define reduce-flow
  (reduction-relation FLOW+AS
    ;; Program entry point: converts the entry block into a partial block for the
    ;; rest of the rules
    (--> (block E S P)
         ((make-pb block) E S P)
         enter-program)

    ;; Execute current primop
    (--> ((PB (op_1 op ...) arg L) E S P)
         ((PB (op ...) arg L) (eval-primop op_1 E P) S P)
         flow-primop
         (side-condition (term (is-primop op_1))))

    ;; Perform call operation
    (--> ((PB ((x_1 := (call arg arg_1 ...)) op ...) arg_2 L) E S P)
         ((make-pb block)
          (setup-env block (eval-args (arg_1 ...) E P))
          (FR E x_1 (PB (op ...) arg_2 L) S)
          P)
         flow-call
         (where (FUN x_2) (eval-arg arg E P))
         (where block (lookup-block P x_2)))

    ;; Done with the block, see if we can find the associated link
    ;; For now, we just send along the whole environment
    (--> ((PB () arg L) E S P)
         ((make-pb block) (setup-env block (eval-args (arg_1 ...) E P)) S P)
         flow-finish-block-link
         ;; Get the value for the exit switch variable
         (where val (eval-arg arg E P))
         ;; Get the corresponding link
         (where (LINK x_1 (arg_1 ...)) (lookup-link L val))
         (where block (lookup-block P x_1)))

    ;; Empty set of links means we have a return block.
    ;; We return the value in the exitswitch variable.
    (--> ((PB () arg ()) E (FR E_1 x_1 pb S_1) P)
         (pb (extend E_1 (x_1) (val)) S_1 P)
         flow-return
         (where val (eval-arg arg E P)))

    ;; Empty links with and empty stack means we are done
    (--> ((PB () arg ()) E ε P)
         (DONE (eval-arg arg E P))
         flow-exit)
    )
  )

(define-metafunction FLOW+JIT
  get-args : op -> (arg ...)
  [(get-args (_ := (opname arg ...))) (arg ...)]
  [(get-args (guard arg _ _))         (arg)]
  [(get-args (jit-merge-point arg))   (arg)]
  [(get-args (jit-can-enter arg))     (arg)]
  )

(define-metafunction FLOW+JIT
  free-vars-op : op -> (x ...)
  [(free-vars-op (guard arg val (PB trace _ _)))
   (free-vars trace)]
  [(free-vars-op op)
   ,(filter
      (lambda (o) (redex-match FLOW+JIT x o))
      (term (get-args op)))])

(define-metafunction FLOW+JIT
  assigned-vars : op -> (x ...)
  [(assigned-vars (x := _)) (x)]
  [(assigned-vars _       ) () ]
  )

(define-metafunction FLOW+JIT
  free-vars : trace -> (x ...)
  [(free-vars trace)
   ,(foldr
      (lambda (op acc)
        (set-union (term (free-vars-op ,op))
          (set-subtract (term (assigned-vars ,op)) acc)))
      '()
      (term trace))])

;; Not working as of yet
(define-metafunction FLOW+JIT
  compile : trace -> (block link)
  [(compile trace)
   ((BL (x_0 ...) trace #f ((#f (LINK x_1 (x_0 ...)))))
    (LINK x_1 (x_0 ...)))
   (where (x_0 ...) (free-vars trace))
   (where x_1 ,(gensym))])

;; Splice a sequence of traces into a single trace using magic
(define-metafunction FLOW+JIT
  splice : trace ... -> trace
  [(splice (trace-op ...) ...) (trace-op ... ...)])

(define reduce-jit
  (extend-reduction-relation reduce-flow FLOW+JIT
    ;; These operations will need to check the trace cache at some point
    (--> ((PB ((jit-merge-point arg) op ...) arg_1 L) E S P)
         ((PB (op ...) arg_1 L) E S P)
         jit-merge-point)

    ;; Begin tracing (no smart heuristics as of yet)
    (--> ((PB ((jit-can-enter arg) op ...) arg_1 L) E S P)
         ((PB (op ...) arg_1 L) E S P (eval-arg arg E P) ())
         begin-tracing)

    ;; Tracing operations

    ;; These operations will need to check the trace cache at some point or add
    (--> ((PB ((jit-merge-point arg) op ...) arg_1 L) E S P val trace)
         ((PB (op ...) arg_1 L) E S P)
         jit-stitch
         (side-condition (equal? (term (eval-arg arg E P val)) (term val))))

    ;; These operations will need to check the trace cache at some point or add
    (--> ((PB ((jit-merge-point arg) op ...) arg_1 L) E S P val trace)
         ((PB (op ...) arg_1 L) E S P val trace)
         jit-merge-point-tracing
         (side-condition (not (equal? (term (eval-arg arg E P val)) (term val)))))

    ;; Execute current primop and record it
    (--> ((PB (op_1 op ...) arg L) E S P val (trace-op ...))
         ((PB (op ...) arg L)
          (eval-primop op_1 E P) S P val
          (trace-op ... op_1))
         flow-primop-tracing
         (side-condition (term (is-primop op_1))))

    ;; Follow a link while tracing. This needs to insert a guard into the trace
    ;; to ensure it does not diverge from the recorded execution path.
    (--> ((PB () arg L) E S P val trace)
         ((make-pb block)
          (setup-env block (eval-args args E P))
          S P val
          (splice
            trace
            (guard arg val (PB () x L))
            (make-env-moves (block-args block) args)))
         flow-finish-block-link-tracing
         (where val (eval-arg arg E P))
         (where (LINK x_1 args) (lookup-link L val))
         (where block (lookup-block P x_1)))
    )
  )

