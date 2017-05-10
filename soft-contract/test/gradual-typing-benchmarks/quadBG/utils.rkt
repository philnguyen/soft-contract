#lang racket/base

(provide
  (rename-out (quad-attr-remove* group-quad-attr-remove*))
  add-vert-positions
  attr-change
  attr-delete ;; for wrap.rkt
  compute-line-height
  flatten-quad ;; for render.rkt
  flatten-quadtree
  hyphenate-quad
  join-quads
  merge-attrs
  quad-attr-remove*
  quad-attr-set
  quad-attr-set*
  split-last
  split-quad
)

;; -----------------------------------------------------------------------------

(require
  require-typed-check
  "../base/quad-types.rkt"
  (only-in racket/list append-map empty? empty split-at-right first splitf-at)
  (only-in racket/string string-append*)
  (only-in math/flonum fl+))
(require (only-in "hyphenate.rkt"
  hyphenate ;(->* (String)
             ;     ((U Char String)
             ;      #:exceptions (Listof String)
             ;      #:min-length Index
             ;      #:min-left-length Index
             ;      #:min-right-length Index
             ;      #:omit-word (-> String Boolean)
             ;      #:omit-string (-> String Boolean))
             ;     String)))
))
(require (only-in "measure.rkt"
  round-float; (-> Float Float)]))
))
(require (only-in "quads.rkt"
  word ;(-> QuadAttrs String Quad)]
  quad-name ;(-> Quad Symbol)]
  quad-attrs ;(-> Quad (Listof Any))]
  make-quadattrs ;(-> (Listof Any) QuadAttrs))
  quad-list ;(-> Quad (Listof USQ)))
  box ;(-> (Listof Any) Quad))
  quad-attr-ref ;(->* ((U Quad QuadAttrs) Symbol) (Any) Any))
  whitespace/nbsp? ;(-> Any Boolean))
))
(require (only-in "world.rkt"
  world:font-size-key ;Symbol]
  world:font-size-default ;(Parameterof Float)]
  world:font-name-key ;Symbol]
  world:font-name-default ;(Parameterof String)]
  world:font-weight-key ;Symbol]
  world:font-weight-default ;(Parameterof Font-Weight)]
  world:font-style-key ;Symbol]
  world:font-style-default ;(Parameterof Font-Style)]
  world:mergeable-quad-types ;(Listof Symbol)]
  world:leading-key ;Symbol]
  world:leading-key-default ;(Parameterof Float)]
  world:height-key ;Symbol]
  world:split-quad-key ;Symbol]
  world:x-position-key ;Symbol]
  world:y-position-key ;Symbol]
))
;; =============================================================================

(define (assert v p)
  (unless (p v) (error 'utils "assert"))
  v)

;; =============================================================================

;; push together multiple attr sources into one list of pairs.
;; mostly a helper function for the two attr functions below.
;; does not resolve duplicates (see merge-attrs for that)
;;bg;
;(: join-attrs (-> Quad Quad (Listof Any)))
(define (join-attrs q0 q1)
  (append (quad-attrs q0) (quad-attrs q1)))


;; merge uses join-attrs to concatenate attributes,
;; but then resolves duplicates, with later ones overriding earlier.
;;bg; variable name is no longer accurate
;(: merge-attrs (-> QuadAttrs * QuadAttrs))
(define (merge-attrs . quads-or-attrs-or-lists)
  (for/fold ;: QuadAttrs
           ([acc  '()])
           ([qs   (in-list quads-or-attrs-or-lists)])
    (for/fold 
              ([acc  acc])
              ([q  (in-list qs)])
      (if (duplicate? (car q) acc)
          acc
          (cons q acc)))))

;;; flatten merges attributes, but applies special logic suitable to flattening
;;; for instance, resolving x and y coordinates.
;(define-type QuadAttrFloatPair (Pairof Symbol Float))

;;bg;
;(: duplicate? (-> Symbol QuadAttrs Boolean))
(define (duplicate? k attrs)
  (for/or ([a (in-list attrs)])
    (eq? k a)))

;;bg;
;(: flatten-attrs (-> Quad Quad QuadAttrs))
(define (flatten-attrs q0 q1)
  (define all-attrs (join-attrs q0 q1))
  (define-values (x-attrs y-attrs other-attrs-reversed)
    (for/fold ([xas null]
               [yas null]
               [oas null])
              ([attr  (in-list all-attrs)])
      (unless (and (pair? attr) (symbol? (car attr)))
        (error 'flatten-attrs "invariant"))
      (cond
        [(and (equal? (car attr) world:x-position-key) (flonum? (cdr attr)))
         (values (cons attr xas) yas oas)]
        [(and (equal? (car attr) world:y-position-key) (flonum? (cdr attr)))
         (values xas (cons attr yas) oas)]
        [else
         (values xas yas (cons attr oas))])))
  ;(: make-cartesian-attr (-> Symbol (Listof Any) QuadAttrs))
  (define (make-cartesian-attr key attrs)
    (if (null? attrs)
        '()
        (list (cons key
                    (for/fold 
                            ([acc 0.0])
                            ([a (in-list attrs)])
                      (unless (and (pair? a) (flonum? (cdr a))) (error 'cart "oops"))
                      (fl+ acc (cdr a)))))))
         ;(foldl fl+ 0.0 (map cdr attrs))
  (define x-attr (make-cartesian-attr world:x-position-key x-attrs))
  (define y-attr (make-cartesian-attr world:y-position-key y-attrs))
  (append
    x-attr
    y-attr
    (for/fold ;: QuadAttrs
      ([acc  '()])
      ([oar other-attrs-reversed])
      (if (duplicate? (car oar) acc)
        acc
        (cons oar acc)))))

;; ordinary flatten won't work because a quad is a bare list,
;; and flatten will go too far.
;; this version adds a check for quadness to the flattener.
;(define-type QEXP (U Quad (Listof QEXP)))
;(: flatten-quadtree (-> QEXP (Listof Quad)))
(define (flatten-quadtree quad-tree)
  (let loop ;: (Listof Quad)
    ([sexp  quad-tree]
     [acc  '()])
    (cond
     [(quad? sexp) (cons sexp acc)]
     [(null? sexp) acc]
     [else (loop (car sexp) (loop (cdr sexp) acc))])))

;; starting with a single nested quad,
;; pushes attributes down from parent quads to children,
;; resulting in a flat list of quads.
;(: flatten-quad (-> Quad (Listof Quad)))
(define (flatten-quad q)
  (flatten-quadtree
   (let loop 
     ([x  q]
      [parent (quad 'null '() '())])
     (cond
       [(quad? x)
        (let ([x-with-parent-attrs (quad (quad-name x)
                                         (flatten-attrs parent x) ; child positioned last so it overrides parent attributes
                                         (quad-list x))])

          (if (null? (quad-list x))
              x-with-parent-attrs ; no subelements, so stop here
              ( map (λ(xi) (loop xi x-with-parent-attrs)) (quad-list x))))] ; replace quad with its elements
       [else ;; it's a string ;;bg; not enforced
        (quad (quad-name parent) (make-quadattrs (quad-attrs parent)) (list x))]))))

;; flatten quad as above,
;; then dissolve it into individual character quads while copying attributes
;; input is often large, so macro allows us to avoid allocation
;;bg;
;(: split-quad (-> Quad (Listof Quad)))
(define (split-quad q)
  ;(: do-explode (->* (Any) (Quad) QEXP))
  (define (do-explode x [parent (box '())])
    (cond
      [(quad? x)
       (if (null? (quad-list x))
           x ; no subelements, so stop here
           (map
            (λ(xi) (do-explode xi x)) (quad-list x)))] ; replace quad with its elements, exploded
      [(string? x) ;; it's a string
       (map (λ(xc) (quad world:split-quad-key (make-quadattrs (quad-attrs parent)) (list xc))) (regexp-match* #px"." x))]
      [else (error 'split-quad "newerror got ~a" x)]))
  (flatten-quadtree (map do-explode (flatten-quad q))))


;; merge chars into words (and boxes), leave the rest
;; if two quads are mergeable types, and have the same attributes,
;; they get merged.
;; input is often large, so macro allows us to avoid allocation
;(: join-quads (-> (Listof Quad) (Listof Quad)))
(define (join-quads qs-in)
  (let ([make-matcher (λ (base-q )
                        (λ(q)
                          (and (member (quad-name q) world:mergeable-quad-types)
                               (not (whitespace/nbsp? q))
                               ;; if key doesn't exist, it is compared against the default value.
                               ;; this way, a nonexistent value will test true against a default value.
                               (andmap (λ(key default)
                                 (equal? (quad-attr-ref base-q key default) (quad-attr-ref q key default)))
                                       (list world:font-name-key
                                                  world:font-size-key
                                                  world:font-weight-key
                                                  world:font-style-key)
                                       (list (world:font-name-default)
                                                  (world:font-size-default)
                                                  (world:font-weight-default)
                                                  (world:font-style-default))))))])
    (let loop ([qs  qs-in][acc  '()])
      (if (null? qs)
          (reverse acc)
          (let* ([base-q (first qs)]
                 [mergeable-and-matches-base? (make-matcher base-q)]) ; make a new predicate function for this quad
            (cond
              [(mergeable-and-matches-base? base-q)
               ;; take as many quads that match, using the predicate function
               (define-values (matching-qs other-qs) (splitf-at (cdr qs) mergeable-and-matches-base?))
               (define new-word-strings (append-map quad-list (cons base-q matching-qs)))
               (define new-word
                 (if (andmap string? new-word-strings)
                     (word (make-quadattrs (quad-attrs base-q)) (string-append* new-word-strings))
                     (error 'join-quads "expected string")))
               (loop other-qs (cons new-word acc))]
              ;; otherwise move on to the next in line
              [else (loop (cdr qs) (cons base-q acc))]))))))

;; these helper functions isolate the generic functionality.
;; problem with quad-attr-set and other Quad->Quad functions
;; is that they strip out type.
;; whereas these "surgical" alternatives can be used when preserving type is essential
;(: attr-change (-> QuadAttrs (Listof Any) QuadAttrs))
(define (attr-change qas kvs)
  (merge-attrs qas (make-quadattrs kvs)))

;(: attr-delete (->* (QuadAttrs) #:rest Any QuadAttrs))
(define (attr-delete qas . ks)
  (filter (λ(qa) (not (ormap (λ(k) (equal? (car qa) k)) ks))) qas))


;; functionally update a quad attr. Similar to hash-set
;(: quad-attr-set (-> Quad Any Any Quad))
(define (quad-attr-set q k v)
  (quad-attr-set* q (list k v)))

;; functionally update multiple quad attrs. Similar to hash-set*
;(: quad-attr-set* (-> Quad (Listof Any) Quad))
(define (quad-attr-set* q kvs)
  (quad (quad-name q) (attr-change (make-quadattrs (quad-attrs q)) kvs) (quad-list q)))

;;; (define (group-quad-attr-set* q kvs)
;;;   (quad (quad-name q) (attr-change (quad-attrs q) kvs) (quad-list q)))
;;; 

;; functionally remove multiple quad attrs. Similar to hash-remove*
;(: quad-attr-remove* (->* (Quad) #:rest Any Quad))
(define (quad-attr-remove* q . ks)
  (if (null? (quad-attrs q))
      q
      ;; test all ks as a set so that iteration through attrs only happens once
      (quad (quad-name q) (apply attr-delete (make-quadattrs (quad-attrs q)) ks) (quad-list q))))

;; todo how to guarantee line has leading key?
;(: compute-line-height (-> Quad Quad))
(define (compute-line-height line)
  (quad-attr-set line world:height-key
    (quad-attr-ref line world:leading-key (world:leading-key-default))))

;(: quad-height (-> Quad Float))
(define (quad-height q)
  (let ([r (quad-attr-ref q world:height-key 0.0)])
    (if (flonum? r) r 0.0)))

;; use heights to compute vertical positions
;(: add-vert-positions (-> Quad Quad))
(define (add-vert-positions starting-quad)
  (define-values (new-quads final-height)
    (for/fold ([new-quads  '()]
               [height-so-far  0.0])
              ([q-any  (in-list (quad-list starting-quad))])
      (define q (assert q-any quad?))
      (values (cons (quad-attr-set q world:y-position-key height-so-far) new-quads)
              (round-float (+ height-so-far (quad-height q))))))
  (quad (quad-name starting-quad) (make-quadattrs (quad-attrs starting-quad)) (reverse new-quads)))

;(: quad-map ((USQ -> USQ) Quad -> Quad))
(define (quad-map proc q)
  (quad (quad-name q) (make-quadattrs (quad-attrs q))
     (map proc (quad-list q))))

;; recursively hyphenate strings in a quad
;(: hyphenate-quad (-> USQ USQ))
(define (hyphenate-quad x)
  (cond
    [(quad? x) (quad-map hyphenate-quad x)]
    [(string? x) (hyphenate x
                            #:min-length 6
                            #:min-left-length 3
                            #:min-right-length 3)]
    [else x]))
 
 ;; just because it comes up a lot
;(: split-last (All (A) ((Listof A) -> (values (Listof A) A))))
(define (split-last xs)
  (let-values ([(first-list last-list) (split-at-right xs 1)])
    (values first-list (car last-list))))

