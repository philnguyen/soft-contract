#lang racket/base

;; bg: removed XML and TxExprs from the original; this only works on strings now

(provide
 hyphenate
 unhyphenate
 )

;; -----------------------------------------------------------------------------

(require
 require-typed-check
 (only-in racket/string string-replace string-join)
 (only-in racket/list partition drop-right drop make-list filter-not take splitf-at))

;; -----------------------------------------------------------------------------
(require (only-in "exceptions.rkt" default-exceptions))

;; -----------------------------------------------------------------------------
(require (only-in "patterns-hashed.rkt" hashed-patterns))

;; =============================================================================
;; bg: utilities for working with type Index
;; maybe we could drop these and go with type Integer everywhere

(define (index? x)
  (and (<= 0 x)
       (< x 9999999999999)))

(define (max-index a b)
  (if (<= a b) b a))

(define (min-index a b)
  (if (<= a b) a b))

(define (max-indexes xs)
  (for/fold  ([init (car xs)]) ([next  (in-list (cdr xs))])
            (max-index init next)))

(define (assert-index i)
  (unless (index? i) (error (format "assert-index: ~a is not an index" i)))
  i)

;; -----------------------------------------------------------------------------

;; bg: changed default from #f
;; module data, define now but set! them later (because they're potentially big & slow)
(define patterns (make-hash))
(define pattern-cache (make-hash))

;; module default values
(define default-min-length 5)
(define default-min-left-length 2)
(define default-min-right-length 2)
(define default-joiner #\u00AD)

;; bg: from racket docs http://docs.racket-lang.org/reference/hashtables.html?q=hash-empty#%28def._%28%28lib._racket%2Fprivate%2Fbase..rkt%29._hash-empty~3f%29%29
(define-syntax-rule (hash-empty? hash)
  (zero? (hash-count hash)))

(define (add-pattern-to-cache pat)
  (hash-set! pattern-cache (car pat) (cdr pat)))

;; bg: renamed from (initialize-patterns)
(define (initialize-patterns)
  (when (hash-empty? pattern-cache)
    (for ([e default-exceptions])
      (add-exception (symbol->string e))))
  (when (hash-empty? patterns)
    (set! patterns hashed-patterns)))

;; Convert the hyphenated pattern into a point array for use later.
(define (add-exception exception)
  (define (make-key x) (format ".~a." (string-replace x "-" "")))
  (define (make-value x)
    `(0 ,@(map (λ(x)
                 (if (equal? x "-") 1 0))
               (regexp-split #px"[a-z]" x)) 0))
  (add-pattern-to-cache (cons (make-key exception) (make-value exception))))

;; An exception-word is a string of word characters or hyphens.
(define (exception-word? x)
  (if (regexp-match #px"^[\\w-]+$" x) #t #f))

(define (exception-words? xs)
  (and (list? xs) (andmap exception-word? xs)))

(define (string->hashpair pat)
  (define boundary-name ".")
  ;; first convert the pattern to a list of alternating letters and numbers.
  ;; insert zeroes where there isn't a number in the pattern.
  (define new-pat
    (let* ([pat
                (regexp-match* #rx"." pat)] ; convert to list
           [pat
                (map (λ(i)
                       (or (and (string->number i) (index? i) i)
                           i)) pat)] ; convert numbers
           [pat
                   (if (string? (car pat))
                       (cons 0 pat) pat)] ; add zeroes to front where needed
           [pat
                   (if (string? (car (reverse pat)))
                       (reverse (cons 0 (reverse pat))) pat)]) ; and back
      ;; bg: not using flatten, made all if-branches in for loop return lists
      (apply append
             (for/list
                       ([(current i) (in-indexed pat)])
                       (if (= i (sub1 (length pat)))
                           (list current)
                           (let ([next (list-ref pat (add1 i))])
                             ;; insert zeroes where there isn't a number
                             (if (and (or (equal? current boundary-name)
                                          (string? current))
                                      (string? next))
                                 (list current 0)
                                 (list current))))))))
  ;; then slice out the string & numerical parts to be a key / value pair.
  ;; bg: partition doesn't have a negative filter
  (define value (filter index? new-pat))
  (define key (filter string? new-pat))
  (cons (apply string-append key) value))

(define (apply-map-max xss)
  (if (or (eq? '() xss) (eq? '() (car xss))) '()
      (cons (max-indexes (for/list ([xs (in-list xss)]) (car xs)))
            (apply-map-max (for/list ([xs (in-list xss)]) (cdr xs))))))

(define (make-points word)
  ;; walk through all the substrings and see if there's a matching pattern.
  ;; if so, pad it out to full length (so we can (apply map max ...) later on)
  (define word-with-dots (format ".~a." (string-downcase word)))
  (define matching-patterns
    (cond
     [(hash-has-key? pattern-cache word-with-dots)
      (list (hash-ref pattern-cache word-with-dots))]
     [else
      (define word-as-list (string->list word-with-dots))
      (define hd (make-list (assert-index (add1 (length word-as-list))) 0))
      ;; bg: typed racket can't handle filtering the Void from a (U Void (Listof Index)) list
      (define tl
        (for*/fold
          ([init '()])
          ([len (in-range (length word-as-list))]
           [index (in-range (- (length word-as-list) len))])
          (define substring (list->string (take (drop word-as-list index) (add1 len))))
          (cond [(hash-has-key? patterns substring)
                 (define value (hash-ref patterns substring))
                 ;; put together head padding + value + tail padding
                 (cons (append (make-list index 0)
                               value
                               (make-list (assert-index (- (add1 (length word-as-list)) (length value) index)) 0))
                       init)]
                [else init])))
      (cons hd tl)]))
  (define max-value-pattern (apply-map-max matching-patterns))
  (add-pattern-to-cache (cons word-with-dots max-value-pattern))
  ;; for point list,
  ;; drop first two elements because they represent hyphenation weight
  ;; before the starting "." and between "." and the first letter.
  ;; drop last element because it represents hyphen after last "."
  ;; after you drop these two, then each number corresponds to
  ;; whether a hyphen goes after that letter.
  (drop-right (drop max-value-pattern 2) 1))


;; Find hyphenation points in a word. This is not quite synonymous with syllables.
(define (word->hyphenation-points word
                                  [min-l  default-min-length]
                                  [min-ll  default-min-left-length]
                                  [min-rl  default-min-right-length])
  (define (add-no-hyphen-zone points)
    ; points is a list corresponding to the letters of the word.
    ; to create a no-hyphenation zone of length n, zero out the first n-1 points
    ; and the last n points (because the last value in points is always superfluous)
    (define min-left-length
      (min-index min-ll (length points)))
    (define min-right-length
      (min-index min-rl (length points)))
    (define points-with-zeroes-on-left
      (append (make-list (sub1 min-left-length) 0)
              (drop points (sub1 min-left-length))))
    (define points-with-zeroes-on-left-and-right
      (append (drop-right points-with-zeroes-on-left min-right-length)
              (make-list min-right-length 0)))
    points-with-zeroes-on-left-and-right)
  (define (make-pieces word)
    (define tmp+word-dissected
      (for/fold
        ;; bg: Accumulator is a "temp-list" and a "final-list"
        ;;     The temp-list collects characters until we reach a syllable.
        ;;     At that point, the temp-list is cons'd to the final-list and
        ;;     we initialize a fresh temp-list.
        ([acc
                (cons '() '())])
        ([char
                (in-string word)]
         [point
                (in-list (add-no-hyphen-zone (make-points word)))])
        (if (even? point)
            (cons (cons char (car acc))
                  (cdr acc))
            (cons '()
                  (cons (reverse (cons char (car acc)))
                        (cdr acc))))))
    ;; bg: sorry about all the reverses, but that's the fold left game
    (define word-dissected
      (reverse
       (cons (reverse (car tmp+word-dissected))
             (cdr tmp+word-dissected))))
    (map list->string word-dissected))
  (if (and min-l (< (string-length word) min-l))
     (list word)
     (make-pieces word)))

;; joiner contract allows char or string; this coerces to string.
(define (joiner->string joiner)
  (if (char? joiner) (string joiner) joiner))

(define (apply-proc proc x [omit-string (λ(x) #f)])
  (let loop ([x x])
    (cond
     [(and (string? x) (not (omit-string x)))
      (proc x)]
     [else x])))

(define (hyphenate x [joiner default-joiner]
                               #:exceptions [extra-exceptions '()]
                               #:min-length [min-length default-min-length]
                               #:min-left-length [min-left-length default-min-left-length]
                               #:min-right-length [min-right-length default-min-right-length]
                               #:omit-word [omit-word? (λ(x) #f)]
                               #:omit-string [omit-string? (λ(x) #f)])
  (initialize-patterns) ; reset everything each time hyphenate is called
  (for ([sym extra-exceptions]) (add-exception sym))
  (define joiner-string (joiner->string joiner))
  ;; todo?: connect this regexp pattern to the one used in word? predicate
  (define word-pattern #px"\\w+") ;; more restrictive than exception-word
  (define (insert-hyphens text)
    (define (lam word . rest)
      ;; bg: what to do about rest?
      (if (not (omit-word? word))
          (string-join (word->hyphenation-points word min-length min-left-length min-right-length) joiner-string)
          word))
    (regexp-replace* word-pattern
                     text
                     lam))
 (apply-proc insert-hyphens x omit-string?))

(define (unhyphenate x [joiner default-joiner]
                     #:omit-word [omit-word? (λ(x) #f)]
                     #:omit-string [omit-string? (λ(x) #f)])
  (define word-pattern (pregexp (format "[\\w~a]+" joiner)))
  (define (remove-hyphens text)
    (define (lam word . rest)
      (if (not (omit-word? word))
          (string-replace word (joiner->string joiner) "")
          word))
    (regexp-replace* word-pattern text lam))
  (apply-proc remove-hyphens x omit-string?))
