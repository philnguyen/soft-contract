#lang racket/base

(provide
  min-entry
  make-ocm
  (prefix-out ocm- min-entry)
  (prefix-out ocm- min-index)
)

;; -----------------------------------------------------------------------------

(require
 require-typed-check
 "ocm-struct.rkt"
 (only-in racket/list argmin)
 (only-in racket/sequence sequence->list)
 (only-in racket/vector vector-drop vector-append)
 (for-syntax racket/base racket/syntax))

;; =============================================================================

(define-logger ocm)

(define (select-elements xs is)
  (map (λ(i) (list-ref xs i)) is))

(define (odd-elements xs)
  (select-elements xs (sequence->list (in-range 1 (length xs) 2))))

(define (vector-odd-elements xs)
  (for/vector ([i (in-range (vector-length xs))] #:when (odd? i))
    (vector-ref xs i)))

(define (even-elements xs)
  (select-elements xs (sequence->list (in-range 0 (length xs) 2))))


;; Wrapper for the matrix procedure
;; that automatically maintains a hash cache of previously-calculated values
;; because the minima operations tend to hit the same values.
;; Assuming here that (matrix i j) is invariant
;; and that the matrix function is more expensive than the cache lookup.


(define-syntax-rule (vector-append-entry xs value)
  (vector-append xs (vector value)))

(define-syntax-rule (vector-append-index xs value)
  (vector-append xs (vector value)))


(define (vector-set vec idx val)
  (vector-set! vec idx val)
  vec)

(define-syntax-rule (vector-cdr vec)
  (vector-drop vec 1))


(define (reduce2 row-indices col-indices matrix-proc entry->value)
  (let find-survivors ([rows row-indices][survivors '()])
    (cond
      [(= 0 (vector-length rows)) (list->vector (reverse survivors))]
      [else
       (define challenger-row (vector-ref rows 0))
       (cond
         ;; no survivors yet, so push first row and keep going
         [(eq? '() survivors) (find-survivors (vector-cdr rows) (cons challenger-row survivors))]
         [else
          (define index-of-last-survivor (sub1 (length survivors)))
          (define col-head (vector-ref col-indices index-of-last-survivor))
          (define-syntax-rule (test-function r) (entry->value (matrix-proc r col-head)))
          (cond
            ;; this is the challenge: is the head cell of challenger a new minimum?
            ;; use < not <=, so the recorded winner is the earliest row with the new minimum, not the latest row
            ;; if yes, challenger wins. pop element from stack, and let challenger try again (= leave rows alone)
            [(< (test-function challenger-row) (test-function (car survivors))) (find-survivors rows (cdr survivors))]

            ;; if not, challenger lost.
            ;; If we're in the last column, ignore the loser by recurring on the same values
            [(= col-head (vector-last col-indices)) (find-survivors (vector-cdr rows) survivors)]

            ;; otherwise challenger lost and we're not in last column,
            ;; so add challenger to survivor stack
            [else (find-survivors (vector-cdr rows) (cons challenger-row survivors))])])])))

;; define a special type so it can be reused in `interpolate`
;; it is (cons value row-idx)

(define minima-idx-key 'row-idx)
(define minima-payload-key 'entry)

;(define-type Make-Minimum-Input (Pair Any Index-Type))
(define (make-minimum value-rowidx-pair)
  (define ht ( make-hash ))
  (! ht minima-payload-key (car value-rowidx-pair))
  (! ht minima-idx-key (cdr value-rowidx-pair))
  ht)


;; Interpolate phase: in the minima hash, add results for even rows

(define-syntax-rule (vector-last v)
  (vector-ref v (sub1 (vector-length v))))

(define (interpolate2 minima row-indices col-indices matrix-proc entry->value)
  (define idx-of-last-col (sub1 (vector-length col-indices)))
  (define (smallest-value-entry col idx-of-last-row)
    (argmin (λ(x) (entry->value (car x)))
                                      (for/list ([row-idx (stop-after (in-vector row-indices) (λ(x) (= idx-of-last-row x)))])
                                        (cons (matrix-proc row-idx col) row-idx))))

  (for ([(col col-idx) (in-indexed col-indices)] #:when (even? col-idx))
    (define idx-of-last-row  (if (= col-idx idx-of-last-col)
                                      (vector-last row-indices)
                                      (hash-ref (hash-ref minima (vector-ref col-indices (add1 col-idx))) minima-idx-key)))
    (! minima col (make-minimum (smallest-value-entry col idx-of-last-row))))
  minima)


;; The return value `minima` is a hash:
;; the keys are col-indices (integers)
;; the values are pairs of (value row-index).
(define (concave-minima row-indices col-indices matrix-proc entry->value)
  ;((vector?) ((or/c #f vector?) procedure? procedure?) . ->* . hash?)
  (define reduce-proc reduce2)
  (define interpolate-proc interpolate2)
  (if (= 0 (vector-length col-indices))
      (make-hash)
      (let ([row-indices (reduce-proc row-indices col-indices matrix-proc entry->value)])
        (define odd-column-minima (concave-minima row-indices  (vector-odd-elements col-indices) matrix-proc entry->value))
        (interpolate-proc odd-column-minima row-indices col-indices matrix-proc entry->value))))


(define no-value 'none)

(define-syntax-rule (@ hashtable key)
  (hash-ref hashtable key))

(define-syntax-rule (! hashtable key value)
  (hash-set! hashtable key value))

(define (make-ocm matrix-proc entry->value [initial-entry 0.0])
  ;(log-ocm-debug "making new ocm")
  ($ocm (vector initial-entry) (vector no-value) 0 matrix-proc entry->value 0 0))

;; Return min { Matrix(i,j) | i < j }.
(define (min-entry ocm j)
  (if (< ($ocm-finished ocm)  j)
      (begin (advance! ocm) (min-entry ocm j))
      (vector-ref ($ocm-min-entrys ocm) j)))

;; ;; same as min-entry, but converts to raw value
;; (define/typed (min-value ocm j)
;;   (OCM-Type Index-Type -> Value-Type)
;;   (($ocm-entry->value ocm) (min-entry ocm j)))

;; Return argmin { Matrix(i,j) | i < j }.
(define (min-index ocm j)
  (if (< ($ocm-finished ocm) j)
      (begin (advance! ocm) (min-index ocm j))
      ( vector-ref ($ocm-min-row-indices ocm) j)))

;; Finish another value,index pair.
(define (advance! ocm)
  (define next (add1 ($ocm-finished ocm)))
  (log-ocm-debug "advance! ocm to next = ~a" (add1 ($ocm-finished ocm)))
  (cond
    ;; First case: we have already advanced past the previous tentative
    ;; value.  We make a new tentative value by applying ConcaveMinima
    ;; to the largest square submatrix that fits under the base.
    [(> next ($ocm-tentative ocm))
     (log-ocm-debug "advance: first case because next (~a) > tentative (~a)" next ($ocm-tentative ocm))
     (define rows (list->vector (sequence->list (in-range ($ocm-base ocm) next))))
          (set-$ocm-tentative! ocm (+ ($ocm-finished ocm) (vector-length rows)))
     (define cols  (list->vector (sequence->list (in-range next (add1 ($ocm-tentative ocm))))))
     (define minima (concave-minima rows cols ($ocm-matrix-proc ocm) ($ocm-entry->value ocm)))

     (for ([col (in-vector cols)])
       (cond
         [(>= col (vector-length ($ocm-min-entrys ocm)))
          (set-$ocm-min-entrys! ocm (vector-append-entry ($ocm-min-entrys ocm) (@ (@ minima col) minima-payload-key)))
          (set-$ocm-min-row-indices! ocm (vector-append-index ($ocm-min-row-indices ocm) (@ (@ minima col) minima-idx-key)))]
         [(< (($ocm-entry->value ocm) (@  (@ minima col) minima-payload-key)) (($ocm-entry->value ocm) (vector-ref ($ocm-min-entrys ocm) col)))
          (set-$ocm-min-entrys! ocm ( vector-set ($ocm-min-entrys ocm) col (@ (@ minima col) minima-payload-key)))
          (set-$ocm-min-row-indices! ocm ( vector-set ($ocm-min-row-indices ocm) col (@ (@ minima col) minima-idx-key)))]))

     (set-$ocm-finished! ocm next)]

    [else
     ;; Second case: the new column minimum is on the diagonal.
     ;; All subsequent ones will be at least as low,
     ;; so we can clear out all our work from higher rows.
     ;; As in the fourth case, the loss of tentative is
     ;; amortized against the increase in base.
     (define diag (($ocm-matrix-proc ocm) (sub1 next) next))
     (cond
       [(< (($ocm-entry->value ocm) diag) (($ocm-entry->value ocm) (vector-ref ($ocm-min-entrys ocm) next)))
        (log-ocm-debug "advance: second case because column minimum is on the diagonal")
        (set-$ocm-min-entrys! ocm (vector-set ($ocm-min-entrys ocm) next diag))
        (set-$ocm-min-row-indices! ocm (vector-set ($ocm-min-row-indices ocm) next (sub1 next)))
        (set-$ocm-base! ocm (sub1 next))
        (set-$ocm-tentative! ocm next)
        (set-$ocm-finished! ocm next)]

       ;; Third case: row i-1 does not supply a column minimum in
       ;; any column up to tentative. We simply advance finished
       ;; while maintaining the invariant.
       [(>= (($ocm-entry->value ocm) (($ocm-matrix-proc ocm) (sub1 next) ($ocm-tentative ocm)))
            (($ocm-entry->value ocm) (vector-ref ($ocm-min-entrys ocm) ($ocm-tentative ocm))))
        (log-ocm-debug "advance: third case because row i-1 does not suppply a column minimum")
        (set-$ocm-finished! ocm next)]

       ;; Fourth and final case: a new column minimum at self._tentative.
       ;; This allows us to make progress by incorporating rows
       ;; prior to finished into the base.  The base invariant holds
       ;; because these rows cannot supply any later column minima.
       ;; The work done when we last advanced tentative (and undone by
       ;; this step) can be amortized against the increase in base.
       [else
        (log-ocm-debug "advance: fourth case because new column minimum")
        (set-$ocm-base! ocm (sub1 next))
        (set-$ocm-tentative! ocm next)
        (set-$ocm-finished! ocm next)])]))
