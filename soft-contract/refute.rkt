#lang typed/racket/base

(provide refute-files)

(require
 racket/match racket/set
 "utils/set.rkt" "utils/map.rkt" "utils/untyped-macros.rkt"
 "ast/definition.rkt" "ast/meta-functions.rkt" "parse/main.rkt"
 "runtime/val.rkt" "runtime/addr.rkt" "runtime/path-inv.rkt" "runtime/store.rkt" "runtime/simp.rkt"
 "proof-relation/main.rkt" "proof-relation/ext/z3.rkt" "proof-relation/local.rkt"
 "delta.rkt"
 "reduction/step-app.rkt" "reduction/main.rkt"
 "machine/definition.rkt" "machine/load.rkt"
 "instantiation.rkt")

(: refute-files : Path-String * → (Option (Pairof -blm (Option -e))))
;; Read in modules and try to find a counterexample
(define (refute-files . paths)
  (parameterize ([Γ⊢ₑₓₜ z3⊢]
                 [↦opq ↦opq/ce]
                 [concrete? #t])
    (with-concrete-allocation
      (run (files->modules paths)))))

(: run : (Listof -module) → (Option (Pairof -blm (Option -e))))
;; Execute module list and return first counterexample (TODO generalize)
(define (run ms)
  (define-values (ς₀ e†) (𝑰 ms init-prim))
  (cond
    [(search {set ς₀}) =>
     (match-lambda
       [(list blm Γ mappings)
        (cons blm (and mappings (instan Γ mappings e†)))])]
    [else #f]))

(define debug? #f)
(define steps : (HashTable Integer (Setof -σ)) (make-hasheq))

(: search : (Setof -ς) → (Option (List -blm -Γ (Option (HashTable -e Base)))))
;; Execute from given frontier
(define (search front)
  (cond
    [(set-empty? front) #f]
    [else
     (define front* (batch-step front))
     (when debug?
       (cond
         [(-ς? front*)
          (printf "Done:~n~a~n~n" (dbg-show front*))]
         [else
          (printf "~a. front: ~a~n" (hash-count steps) (set-count front*))
          (for ([ς* front*])
            (printf "  ~a~n" (dbg-show ς*))
            (⊔! steps (hash-count steps) (-ς-σ ς*)))
          (case (read)
            [(skip) (set! debug? #f)]
            [(done) (error "DONE")]
            [else (void)])
          (printf "~n")]))
     (cond
       [(set? front*) (search front*)]
       [else
        (match-define (-ς (? -blm? blm) Γ _ σ _ M) front*)
        (list blm Γ (get-model M σ Γ))])]))

(: batch-step : (Setof -ς) → (U -ς (Setof -ς)))
(define (batch-step front)
  (define ans
    (for/fold ([next : (U -ς (Setof -ς)) ∅]) ([ς front])
      (cond
        [(-ς? next) next] ; Should use #:break, but TR doesn't like it
        [else
         (match (↦/ς ς)
           [(? -ς? ς*) (on-new-state next ς*)]
           [(? set? ςs)
            (for/fold ([next : (U -ς (Setof -ς)) next]) ([ς* ςs])
              (if (-ς? next) next (on-new-state next ς*)))])])))
  #;(when debug?
    (printf "batch-step of (~a) :~n  ~a~nis (~a) ~n  ~a~n~n"
            (set-count front)
            (set-map front dbg-show)
            (if (set? ans) (set-count ans) 1)
            (if (set? ans) (set-map ans dbg-show) (dbg-show ans)))
    (case (read)
      [(skip) (set! debug? #f)]
      [(done) (error "DONE")]
      [else (void)]))
  ans)

(: on-new-state : (Setof -ς) -ς → (U -ς (Setof -ς)))
(define (on-new-state front ς)
  (match ς
    [(-ς (and blm (-blm l+ _ _ _)) _ _ _ _ _)
     (case l+
       [(havoc Λ †) front]
       [else #;(printf "blaming in ~a~n" (dbg-show ς)) ς])]
    ;; Harder to apply heuristic in this setting
    #;[(-ς (? -W?) _ κ _ _ _)
     ]
    [_ (set-add front ς)]))

;; See if it's ok to inline the application
(define (arg-inlinable? [e : -e])
  (or (-x? e) (-ref? e) (-prim? e)))

(define (dbg-show [ς : -ς]) : (Listof Sexp)
  (match-define (-ς E Γ κ _ _ _) ς)
  `((E: ,@(show-E E))
    (Γ: ,@(show-Γ Γ))
    (κ: ,@(show-κ κ))))
