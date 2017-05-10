#lang racket/base

(provide
  load-text-cache-file
  update-text-cache-file
  round-float
  measure-text
  measure-ascent
)

;; -----------------------------------------------------------------------------

(require
 (only-in racket/class new send)
 (only-in math/flonum fl)
 (only-in racket/file write-to-file file->value)
 (only-in racket/draw record-dc% font% make-font)
)
(require (only-in racket/serialize
  serialize ;(Any -> Any)]
  deserialize ;(Any -> (HashTable (List String String Symbol Symbol) Measurement-Result-Type))]
))

;; =============================================================================
;(define-type Font-Name String)
;(define-type Font-Size Positive-Flonum)

(define precision 4.0)
(define base (expt 10.0 precision))
(define max-size 1024.0)
(define dc (new record-dc%))
;(define-type Measurement-Result-Type (List Float Float Float Float))
;(define mrt? (make-predicate Measurement-Result-Type))
(define current-text-cache (make-parameter (make-hash '())))
(define current-font-cache (make-parameter (make-hash '())))

;(: round-float (Float -> Float))
(define (round-float x)
  (/ (round (* base x)) base))

;(: get-cache-file-path (-> Path))
(define (get-cache-file-path)
  (build-path "./font.cache"))

;(: update-text-cache-file (-> Void))
(define (update-text-cache-file)
  (define ctc (current-text-cache))
  (unless (not (eof-object? ctc))
    (write-to-file (serialize ctc) (get-cache-file-path) #:exists 'replace)))

;(: load-text-cache-file (-> Void))
(define (load-text-cache-file)
  (define cache-file-path (get-cache-file-path))
  (define H (make-hash '()))
  (current-text-cache (if (file-exists? cache-file-path)
                          (let ([val (file->value cache-file-path)])
                            (if (eof-object? val)
                                ;; Error deserializing!
                                H
                                (deserialize val)))
                          H)))

;(: get-cached-font (-> Font-Name Font-Weight Font-Style (Instance Font%)))
(define (get-cached-font font weight style)
  (hash-ref! (current-font-cache) (list font weight style) (λ() (make-font #:size max-size #:style style #:weight weight #:face font))))

;(: measure-max-size (->* (String Font-Name) (Font-Weight Font-Style) Measurement-Result-Type))
(define (measure-max-size text font [weight 'normal] [style 'normal])
  ;(: hash-updater (-> Measurement-Result-Type))
  (define (hash-updater)
    #;(current-text-cache-changed? #t)
    (define font-instance (get-cached-font font weight style))
    ;; 'combine' boolean only makes a difference for two or more chars, so use (>= (string-length text) 1) for speed
    (define-values (width height descent extra) (send dc get-text-extent text font-instance (>= (string-length text) 1)))
    ;; avoid `map` here because it requires a cast to ensure the type
    ;; this seems like a bug in TR: doesn't recognize (List Float Float Float Float) as subtype of (Listof Float)?
    (list (fl width) (fl height) (fl descent) (fl extra)))
  (hash-ref! (current-text-cache) (list text font weight style) hash-updater))

(define-syntax-rule (width x) (car x))
(define-syntax-rule (height x) (cadr x))
(define-syntax-rule (descent x) (caddr x))

;; works by taking max size and scaling it down. Allows caching of results.
;(: measure-text (-> String Font-Size Font-Name Font-Weight Font-Style Float))
(define (measure-text text size font weight style)
  (define raw-width (width (measure-max-size text font weight style)))
  (round-float (/ (* raw-width size) max-size)))

;; works by taking max size and scaling it down. Allows caching of results.
;(: measure-ascent (->* (String Font-Size Font-Name) (Font-Weight Font-Style) Float))
(define (measure-ascent text size font [weight 'normal] [style 'normal])
  (define result-list (measure-max-size text font weight style))
  (define raw-baseline-distance (- (height result-list) (descent result-list)))
  (round-float (/ (* raw-baseline-distance size) max-size)))
