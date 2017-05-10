#lang racket/base

(provide pdf-renderer%)

;; -----------------------------------------------------------------------------

(require
 require-typed-check
 (only-in racket/list filter-not)
 (only-in racket/draw font% make-font current-ps-setup pdf-dc% the-color-database)
 (only-in racket/class inherit define/override send* class new super-new send define/public object% this)
 (only-in racket/file display-to-file)
)
(require (only-in "world.rkt"
  world:font-size-key; Symbol]
  world:font-size-default; (Parameterof Float)]
  world:font-color-key; Symbol]
  world:font-color-default; (Parameterof String)]
  world:font-background-key; Symbol]
  world:font-background-default; (Parameterof String)]
  world:font-name-key; Symbol]
  world:font-name-default; (Parameterof String)]
  world:font-weight-key; Symbol]
  world:font-weight-default; (Parameterof Font-Weight)]
  world:font-style-key; Symbol]
  world:font-style-default; (Parameterof Font-Style)]
  world:paper-height-default; (Parameterof Float)]
  world:paper-width-default; (Parameterof Float)]
  world:x-position-key; Symbol]
  world:y-position-key; Symbol]
  world:ascent-key; Symbol]
  world:quality-default; (Parameterof Index)]
  world:draft-quality; Index]
  world:page-key; Symbol]
))
(require (only-in "utils.rkt"
  flatten-quad ;(-> Quad (Listof Quad)))
))
(require (only-in "quads.rkt"
  quad-attr-ref ;(->* ((U Quad QuadAttrs) Symbol) (Any) Any)])
  word ;(->* ((Listof Any)) Quad)]
  quad-name ;(-> Quad Symbol)]
  quad-car ;(-> Quad USQ))
  whitespace/nbsp? ;(-> Any Boolean)]
))

;; =============================================================================

(define (assert v p)
  (unless (p v) (error 'render (format "ohnoes ~a ~a" (object-name p) v)))
  v)

(define (natural? v)
  (and (integer? v) (<= 0 v)))

(define (nonnegative-float? v)
  (and (flonum? v) (<= 0 v)))

;; =============================================================================

(define abstract-renderer%

  (class object%
    (super-new)

    (define renderable-quads '(word box))

    ;; hash implementation
    ;(: render (-> Quad Any))
    (define/public (render doc-quad)
      (finalize
       (let ([rendering-input (flatten-quad (setup doc-quad))])
         (define page-quad-hash (make-hash))
         (for ([q (in-list rendering-input)])
           (when (member (quad-name q) renderable-quads)
             (hash-update! page-quad-hash (assert (quad-attr-ref q world:page-key) natural?) (λ(v) (cons q v)) (λ() null))))
         (map (λ(k) (render-page (hash-ref page-quad-hash k))) (sort (hash-keys page-quad-hash) <)))))

    ;(: render-element (-> Quad Any))
    (define/public (render-element q)
      (cond
        [(eq? 'word (quad-name q)) (render-word q)]
        [else q]))

    ;(: setup (-> Quad Quad))
    (define/public (setup q) q)

    ;; use in lieu of 'abstract' definition
    ;(: render-page (-> (Listof Quad) Void))
    (define/public (render-page qs) (void))

    ;; use in lieu of 'abstract' definition
    ;(: render-word (-> Quad Any))
    (define/public (render-word x) (word '()))

    ;(: finalize (-> Any Any))
    (define/public (finalize x) x)))

;; this is outside class def'n because if inside,
;; (define dc ...) can't see it and type it correctly.
;; there may be a better way, but for now this is OK
(define dc-output-port (open-output-bytes))

(define pdf-renderer%
  (class abstract-renderer%
    (super-new)

    (send* (current-ps-setup) (set-margin 0 0) (set-scaling 1.0 1.0))

    (define dc (new pdf-dc% [interactive #f][use-paper-bbox #f][as-eps #f]
                    [output dc-output-port]
                    [width (world:paper-width-default)][height (world:paper-height-default)]))


    (define/override (setup tx)
      (send* dc
        (start-doc "boing")
        (set-pen "black" 1 'solid)
        (set-brush "black" 'transparent)) ; no fill by default
      tx)

    (inherit render-element)


    (define font-cache (make-hash  '()))
    ;(: get-cached-font (String Nonnegative-Flonum Font-Style Font-Weight ->  (Instance Font%)))
    (define (get-cached-font font size style weight)
      (hash-ref! font-cache (list font size style weight) (λ () (make-font #:face font #:size size #:style style #:weight weight))))


    (define/override (render-word w)
      (define word-font (assert (quad-attr-ref w world:font-name-key (world:font-name-default)) string?))
      (define word-size (assert (quad-attr-ref w world:font-size-key (world:font-size-default)) nonnegative-float?))
      (define word-style (assert (quad-attr-ref w world:font-style-key (world:font-style-default)) symbol?))
      (define word-weight (assert (quad-attr-ref w world:font-weight-key (world:font-weight-default)) symbol?))
      (define word-color (assert (quad-attr-ref w world:font-color-key (world:font-color-default)) string?))
      (define word-background (assert (quad-attr-ref w world:font-background-key (world:font-background-default)) string?))
      (send dc set-font (get-cached-font word-font word-size word-style word-weight))
      (define foreground-color (send the-color-database find-color word-color))
      (when foreground-color
        (send dc set-text-foreground foreground-color))
      (define background-color (send the-color-database find-color word-background))
      (if background-color ; all invalid color-string values will return #f
          (send* dc (set-text-mode 'solid) (set-text-background background-color))
          (send dc set-text-mode 'transparent))

      (define word-text (assert (quad-car w) string?))
      (send dc draw-text word-text (assert (quad-attr-ref w world:x-position-key) flonum?)
            ;; we want to align by baseline rather than top of box
            ;; thus, subtract ascent from y to put baseline at the y coordinate
            (- (assert (quad-attr-ref w world:y-position-key) flonum?)
               (assert (quad-attr-ref w world:ascent-key 0) flonum?)) #t))

    (define/override (render-page elements)
      (send dc start-page)
      (for ([elem  (filter-not whitespace/nbsp? elements)])
        (render-element elem))
      (send dc end-page))

    (define/override (finalize xs)
      (send dc end-doc)
      (get-output-bytes dc-output-port))

    ;(: render-to-file (Quad Path-String -> Void))
    (define/public (render-to-file doc-quad path)
      (define result-bytes (send this render doc-quad))
      (display-to-file result-bytes path #:exists 'replace #:mode 'binary))
    ))
