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
(define debug-step : Natural 0)

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
          (printf "Done:~n")
          (print-ς (assert front* -ς?))]
         [else
          (printf "~a. front: ~a~n"
                  (begin0 debug-step (set! debug-step (+ 1 debug-step)))
                  (set-count (assert front* set?)))
          (define front*-list (set->list (assert front* set?)))
          (for ([(ς* i) (in-indexed front*-list)])
            (printf "~a:~n" i)
            (print-ς ς*)
            (printf "~n"))
          (match (read)
            ['skip (set! debug? #f)]
            ['done (error "DONE")]
            [(? exact-integer? i) ; explore specific branch
             (set! front* (set (list-ref front*-list i)))]
            [_ (void)])]))
     (match front*
       [(-ς (? -blm? blm) Γ _ σ _ M)
        (list blm Γ (get-model M σ Γ))]
       [(? set? s) (search s)])]))

(: batch-step : (Setof -ς) → (U -ς (Setof -ς)))
(define (batch-step front)
  (for/fold ([next : (U -ς (Setof -ς)) ∅]) ([ς front])
    (cond
      [(-ς? next) next] ; Should use #:break, but TR doesn't like it
      [else
       (match (↦/ς ς)
         [(? -ς? ς*) (on-new-state next ς*)]
         [(? set? ςs)
          (for/fold ([next : (U -ς (Setof -ς)) next]) ([ς* ςs])
            (if (-ς? next) next (on-new-state next ς*)))])])))

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

(define (print-ς [ς : -ς]) : Void
  (match-define (-ς E Γ κ _ _ _) ς)
  (printf "  E: ~a~n  Γ: ~a~n  κ: ~a~n" (show-E E) (show-Γ Γ) (show-κ κ)))
