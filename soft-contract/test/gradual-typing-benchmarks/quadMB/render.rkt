#lang racket/base

(provide pdf-renderer%)

;; -----------------------------------------------------------------------------

(require
 require-typed-check
 (only-in racket/list filter-not)
 (only-in racket/draw font% make-font current-ps-setup pdf-dc% the-color-database)
 (only-in racket/class inherit define/override send* class new super-new send define/public object% this)
 (only-in racket/file display-to-file)
(only-in "world.rkt"
  world:font-size-key
  world:font-size-default
  world:font-color-key
  world:font-color-default
  world:font-background-key
  world:font-background-default
  world:font-name-key
  world:font-name-default
  world:font-weight-key
  world:font-weight-default
  world:font-style-key
  world:font-style-default
  world:paper-height-default
  world:paper-width-default
  world:x-position-key
  world:y-position-key
  world:ascent-key
  world:quality-default
  world:draft-quality
  world:page-key)
(only-in "utils.rkt"
  flatten-quad)
(only-in "quads.rkt"
  quad-attr-ref
  word?
  word
  quad-car
  whitespace/nbsp?
  quad-name))

;; =============================================================================

(define abstract-renderer%

  (class object%
    (super-new)

    (define renderable-quads '(word box))

    ;; hash implementation
    (define/public (render doc-quad)
      (finalize
       (let ([rendering-input (flatten-quad (setup doc-quad))])
         (define page-quad-hash (make-hash))
         (for ([q (in-list rendering-input)])
           (when (member (quad-name q) renderable-quads)
             ( hash-update! page-quad-hash (quad-attr-ref q world:page-key) (λ(v) (cons q v)) (λ()  null))))
         (map (λ(k) (render-page (hash-ref page-quad-hash k))) (sort (hash-keys page-quad-hash) <)))))

    (define/public (render-element q)
      (cond
        [(word? q) (render-word q)]
        [else q]))

    (define/public (setup q) q)

    ;; use in lieu of 'abstract' definition
    (define/public (render-page qs) (void))

    ;; use in lieu of 'abstract' definition
    (define/public (render-word x) (word '()))

    (define/public (finalize x) x)))

(define-syntax-rule (map/send method xs)
  (map (λ(x) (method x)) xs))

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


    (define font-cache ( make-hash '()))
    (define (get-cached-font font size style weight)
      (hash-ref! font-cache (list font size style weight) (λ () (make-font #:face font #:size size #:style style #:weight weight))))


    (define/override (render-word w)
      (define word-font (quad-attr-ref w world:font-name-key (world:font-name-default)))
      (define word-size (quad-attr-ref w world:font-size-key (world:font-size-default)))
      (define word-style (quad-attr-ref w world:font-style-key (world:font-style-default)))
      (define word-weight (quad-attr-ref w world:font-weight-key (world:font-weight-default)) )
      (define word-color (quad-attr-ref w world:font-color-key (world:font-color-default)))
      (define word-background (quad-attr-ref w world:font-background-key (world:font-background-default)))
      (send dc set-font (get-cached-font word-font word-size word-style word-weight))
      (define foreground-color (send the-color-database find-color word-color))
      (when foreground-color
        (send dc set-text-foreground foreground-color))
      (define background-color (send the-color-database find-color word-background))
      (if background-color ; all invalid color-string values will return #f
          (send* dc (set-text-mode 'solid) (set-text-background background-color))
          (send dc set-text-mode 'transparent))

      (define word-text (quad-car w))
      (send dc draw-text word-text (quad-attr-ref w world:x-position-key)
            ;; we want to align by baseline rather than top of box
            ;; thus, subtract ascent from y to put baseline at the y coordinate
            (-  (quad-attr-ref w world:y-position-key)  (quad-attr-ref w world:ascent-key 0)) #t))

    (define/override (render-page elements)
      (send dc start-page)
      (map/send render-element (filter-not whitespace/nbsp? elements))
      (send dc end-page))

    (define/override (finalize xs)
      (send dc end-doc)
      (get-output-bytes dc-output-port))

    (define/public (render-to-file doc-quad path)
      (define result-bytes (send this render doc-quad))
      (display-to-file result-bytes path #:exists 'replace #:mode 'binary))
    ))
