#lang racket/base

(provide
  typeset
)

;; ----------------------------------------------------------------------------

(require
  require-typed-check
  "../base/quad-types.rkt"
  racket/class
  (only-in racket/list append* split-at drop-right)
  (only-in racket/sequence sequence->list)
  (only-in math/flonum fl+ fl fl>))
(require (only-in "quads.rkt"
  make-quadattrs ;(-> (Listof Any) QuadAttrs))
  quad-car ;(-> Quad (U String Quad)))
  line ;(->* ((Listof Any)) #:rest USQ Quad))
  quads->column ;(-> (Listof Quad) Quad))
  quads->page ;(-> (Listof Quad) Quad))
  quads->block ;(-> (Listof Quad) Quad))
  quad-has-attr? ;(-> Quad Symbol Boolean))
  quad-name ;(-> Quad Symbol))
  quad-attr-ref ;(((U Quad QuadAttrs) Symbol) (Any) . ->* . Any))
  quad-list ;(-> Quad (Listof USQ)))
  quad-attrs ;(-> Quad (Listof Any)))
  quads->doc ;(-> (Listof Quad) Quad))
  page ;(->* ((Listof Any)) #:rest USQ Quad))
  column ;(->* ((Listof Any)) #:rest USQ Quad))
))
(require (only-in "wrap.rkt"
  insert-spacers-in-line ;((Quad) ((Option Symbol)) . ->* . Quad))
  wrap-best ;(->* ((Listof Quad)) (Float) (Listof Quad)))
  fill ;(->* (Quad) ((Option Float)) Quad))
  add-horiz-positions ;(-> Quad Quad))
))
(require (only-in "world.rkt"
  world:line-looseness-key ;Symbol]
  world:allow-hyphenated-last-word-in-paragraph;; Boolean]
  world:line-looseness-tolerance; Float]
  world:line-index-key; Symbol]
  world:measure-key; Symbol]
  world:use-hyphenation?; Boolean]
  world:max-quality; Index]
  world:total-lines-key; Symbol]
  world:draft-quality; Index]
  world:quality-key; Symbol]
  world:quality-key-default; (Parameterof Index)]
  world:paper-width-default; (Parameterof Float)]
  world:column-count-key; Symbol]
  world:column-count-key-default; (Parameterof Index)]
  world:column-gutter-key; Symbol]
  world:column-gutter-key-default; (Parameterof Float)]
  world:column-index-key; Symbol]
  world:min-first-lines; Index]
  world:min-last-lines; Index]
  world:minimum-lines-per-column; Index]
  world:default-lines-per-column; Index]
))
(require (only-in "measure.rkt"
  round-float ;(-> Float Float)]
  load-text-cache-file; (-> Void)]
  update-text-cache-file; (-> Void)]
))
(require (only-in "utils.rkt"
  add-vert-positions; (-> Quad Quad))
  attr-change; (-> QuadAttrs (Listof Any) QuadAttrs))
  compute-line-height; (-> Quad Quad))
  hyphenate-quad; (USQ -> USQ))
  join-quads; ((Listof Quad) -> (Listof Quad)))
  merge-attrs; (QuadAttrs * -> QuadAttrs))
  quad-attr-set*; (Quad (Listof Any) -> Quad))
  split-last ;(All (A) ((Listof A) -> (values (Listof A) A))))
  split-quad ;(-> Quad (Listof Quad)))
))
(require (only-in "sugar-list.rkt"
 slice-at ;(All (A) (case-> ((Listof A) Positive-Integer -> (Listof (Listof A)))
           ;        ((Listof A) Positive-Integer Boolean -> (Listof (Listof A))))))
))
;; bg: should maybe import this
(require (only-in "../base/csp/csp.rkt"
  problem%  ;(Class (init-field [solver Any])
    ;(field [_solver Any])
    ;(field [_variable-domains Any])
    ;(field [_constraints Any])
    ;[reset (-> Void)]
    ;[custom-print (Output-Port Integer -> Void)]
    ;[custom-display (Output-Port -> Void)]
    ;[custom-write (Output-Port -> Void)]
    ;[add-variable (Any (Listof Any) . -> . Void)]
    ;[add-variables ((Listof Any) Any . -> . Void)]
    ;[add-constraint ((Index . -> . Boolean) (Listof Any) . -> . Void)]
    ;[get-solution (-> HashTableTop)]
    ;[get-solutions (-> (Listof (HashTable String Integer)))]
    ;[get-solution-iter (-> HashTableTop)]
    ;[set-solver (Any . -> . Void)]
    ;[get-solver (-> Any)])])
))
;; =============================================================================

(define (assert v p)
  (unless (p v) (error 'quad-main "asert"))
  v)

(define (natural? v)
  (and (integer? v) (<= 0 v)))

(define (index? v)
  (and (integer? v) (<= 0 v) (< v 9999999)))

(define (positive-integer? v)
  (and (integer? v) (positive? v)))

(define (listof-quad? qs)
  (and (list? qs) (andmap quad? qs)))

;; =============================================================================

;(define-type Block-Type (Listof Quad))
;(define-type Multicolumn-Type (Listof Block-Type))
;(define-type Multipage-Type (Listof Multicolumn-Type))

;(: typeset (-> Quad Quad))
(define (typeset x)
  (load-text-cache-file)
  (define pages (append*
                 (for/list ;: (Listof (Listof Quad))
                   ([multipage (in-list (input->nested-blocks x))])
                   (columns->pages (append*
                                    (for/list ;: (Listof (Listof Quad))
                                      ([multicolumn (in-list multipage)])
                                      (lines->columns (append*
                                                       (for/list ;: (Listof (Listof Quad))
                                                         ([block-quads (in-list multicolumn)])
                                                         (block-quads->lines block-quads))))))))))
  (define doc (pages->doc pages))
  (update-text-cache-file)
  doc)

;; -----------------------------------------------------------------------------

;(: cons-reverse (All (A B) ((Listof A) (Listof B) -> (Pairof (Listof A) (Listof B)))))
(define (cons-reverse xs ys)
  (cons (reverse xs) ys))

;(: input->nested-blocks (Quad . -> . (Listof Multipage-Type)))
(define (input->nested-blocks i)
  (define-values (mps mcs bs b)
    (for/fold ([multipages  null]
               [multicolumns   null]
               [blocks  null]
               [block-acc  null])
              ([q (in-list (split-quad i))])
      (case (quad-name q)
        [(page-break) (values (cons-reverse (cons-reverse (cons-reverse block-acc blocks) multicolumns) multipages) null null null)]
        [(column-break) (values multipages (cons-reverse (cons-reverse block-acc blocks) multicolumns) null null)]
        [(block-break) (values multipages multicolumns (cons-reverse block-acc blocks) null)]
        [else (values multipages multicolumns blocks (cons q block-acc))])))
  (reverse (cons-reverse (cons-reverse (cons-reverse b bs) mcs) mps)))

;(: merge-adjacent-within (Quad . -> . Quad))
(define (merge-adjacent-within q)
  (quad (quad-name q)
        (make-quadattrs (quad-attrs q))
        (join-quads (assert (quad-list q) listof-quad?))))

;(: hyphenate-quad-except-last-word (Quad . -> . Quad))
(define (hyphenate-quad-except-last-word q)
  ;(log-quad-debug "last word will not be hyphenated")
  (define-values (first-quads last-quad) (split-last (quad-list q)))
  (quad (quad-name q) (make-quadattrs (quad-attrs q))
    (append (for/list  ([q (in-list first-quads)])
             (hyphenate-quad q))
      (list last-quad))))

;(: average-looseness ((Listof Quad) . -> . Float))
(define (average-looseness lines)
  (if (<= (length lines) 1)
      0.0
      (let ([lines-to-measure  (drop-right lines 1)]) ; exclude last line from looseness calculation
        (round-float (/ (foldl fl+ 0.0 (map (λ(line ) (assert (quad-attr-ref line world:line-looseness-key 0.0) flonum?)) lines-to-measure)) (- (fl (length lines)) 1.0))))))

;;; todo: introduce a Quad subtype where quad-list is guaranteed to be all Quads (no strings)
;(: block->lines (Quad . -> . (Listof Quad)))
(define (block->lines b)
  ;(: wrap-quads ((Listof Quad) . -> . (Listof Quad)))
  (define (wrap-quads qs)
    (define wrap-proc wrap-best)
                    ;; (cond
                    ;;    [(>= quality world:max-quality) wrap-best]
                    ;;    [(<= quality world:draft-quality) wrap-first]
                    ;;    [else wrap-adaptive]))
    (wrap-proc qs))
  ;(log-quad-debug "wrapping lines")
  ;(log-quad-debug "quality = ~a" quality)
  ;(log-quad-debug "looseness tolerance = ~a" world:line-looseness-tolerance)
  (define wrapped-lines-without-hyphens (wrap-quads (assert (quad-list b) listof-quad?))) ; 100/150
  ;(log-quad-debug* (log-debug-lines wrapped-lines-without-hyphens))
  (define avg-looseness (average-looseness wrapped-lines-without-hyphens))
  (define gets-hyphenation? (and world:use-hyphenation?
                                 (fl> avg-looseness world:line-looseness-tolerance)))
  ;(log-quad-debug "average looseness = ~a" avg-looseness)
  ;(log-quad-debug (if gets-hyphenation? "hyphenating" "no hyphenation needed"))
  (define wrapped-lines (if gets-hyphenation?
                            (wrap-quads (split-quad ((if world:allow-hyphenated-last-word-in-paragraph
                                                               (lambda (x ) (assert (hyphenate-quad x) quad?))
                                                               hyphenate-quad-except-last-word) (merge-adjacent-within b))))
                            wrapped-lines-without-hyphens))
  ;(when gets-hyphenation? (log-quad-debug* (log-debug-lines wrapped-lines)))
  ;(log-quad-debug "final looseness = ~a" (average-looseness wrapped-lines))
  (map insert-spacers-in-line
       (for/list ;: (Listof Quad)
               ([line-idx (in-naturals)][the-line-any  (in-list wrapped-lines)])
         (define the-line (assert the-line-any quad?))
         (apply line (attr-change (make-quadattrs (quad-attrs the-line)) (list 'line-idx line-idx 'lines (length wrapped-lines))) (quad-list the-line)))))


;(: number-pages ((Listof Quad) . -> . (Listof Quad)))
(define (number-pages ps)
  (for/list ([i (in-naturals)][p (in-list ps)])
    (apply page (merge-attrs (make-quadattrs (quad-attrs p)) `((page . ,i))) (quad-list p))))

;(: pages->doc ((Listof Quad) . -> . Quad))
(define (pages->doc ps)
  ;; todo: resolve xrefs and other last-minute tasks
  ;; todo: generalize computation of widths and heights, recursively
  ;(: columns-mapper (Quad . -> . Quad))
  (define (columns-mapper page-in)
    (apply page (make-quadattrs (quad-attrs page-in))
           (map add-vert-positions (for/list  ([col-any (in-list (quad-list page-in))])
             (define col (assert col-any quad?))
             (apply column (make-quadattrs (quad-attrs col)) (map (λ(ln ) (compute-line-height (add-horiz-positions (fill (assert ln quad?))))) (quad-list col)))))))
  (define mapped-pages (map columns-mapper (number-pages ps)))
  (define doc (quads->doc mapped-pages))
  doc)

;(: lines->columns ((Listof Quad) . -> . (Listof Quad)))
(define (lines->columns lines)
  (define prob (new problem% [solver #f]))
  (define max-column-lines world:default-lines-per-column)
  (define-values (columns ignored-return-value)
    (for/fold ([columns  null]
               [lines-remaining  lines])
              ([col-idx (stop-before (in-naturals) (λ(x) (null? lines-remaining)))])
      ;bg;(log-quad-info "making column ~a" (add1 col-idx))
      ;; domain constraint is best way to simplify csp, because it limits the search space.
      ;; search from largest possible value to smallest.
      ;; largest possible is the minimum of the max column lines, or
      ;; the number of lines left (modulo minimum page lines) ...
      (define viable-column-range
        (sequence->list (in-range (min max-column-lines (max
                                      (length lines-remaining)
                                      (- (length lines-remaining) world:minimum-lines-per-column)))
               ;; ... and the smallest possible is 1, or the current minimum lines.
               ;; (sub1 insures that range is inclusive of last value.)
               (sub1 (min 1 world:minimum-lines-per-column)) -1)))
      ;bg;(log-quad-debug "viable number of lines for this column to start =\n~a" viable-column-range)
      (send prob add-variable "column-lines" viable-column-range)
      ;; greediness constraint: leave enough lines for next page, or take all
      ;(: greediness-constraint (Index . -> . Boolean))
      (define (greediness-constraint pl)
        (define leftover (- (length lines-remaining) pl))
        (or (= leftover 0) (>= leftover world:minimum-lines-per-column)))
      (send prob add-constraint greediness-constraint '("column-lines"))
      ;; last lines constraint: don't take page that will end with too few lines of last paragraph.
      ;(: last-lines-constraint (-> Index Boolean))
      (define (last-lines-constraint pl)
        (define last-line-of-page (list-ref lines-remaining (sub1 pl)))
        (define lines-in-this-paragraph (assert (quad-attr-ref last-line-of-page world:total-lines-key) integer?))
        (define line-index-of-last-line (assert (quad-attr-ref last-line-of-page world:line-index-key) integer?))
        (define (paragraph-too-short-to-meet-constraint?)
          (< lines-in-this-paragraph world:min-last-lines))
        (or (paragraph-too-short-to-meet-constraint?)
            (>= (add1 line-index-of-last-line) world:min-last-lines)))
      (send prob add-constraint last-lines-constraint '("column-lines"))
      ;(log-quad-debug "viable number of lines after last-lines constraint =\n~a" (map (λ(x) (hash-ref x "column-lines")) (send prob get-solutions)))
      ;; first lines constraint: don't take page that will leave too few lines at top of next page
      ;(: first-lines-constraint (Index (Listof Quad) . -> . Boolean))
      (define (first-lines-constraint pl lines-remaining)
        (define last-line-of-page (list-ref lines-remaining (sub1 pl)))
        (define lines-in-this-paragraph (assert (quad-attr-ref last-line-of-page world:total-lines-key) integer?))
        (define line-index-of-last-line (assert (quad-attr-ref last-line-of-page world:line-index-key) integer?))
        (define lines-that-will-remain (- lines-in-this-paragraph (add1 line-index-of-last-line)))
        (define (paragraph-too-short-to-meet-constraint?)
          (< lines-in-this-paragraph world:min-first-lines))
        (or (paragraph-too-short-to-meet-constraint?)
            (= 0 lines-that-will-remain) ; ok to use all lines ...
            (>= lines-that-will-remain world:min-first-lines))) ; but if any remain, must be minimum number.
      (send prob add-constraint (λ(x) (first-lines-constraint (assert x index?) lines-remaining)) '("column-lines"))
      (define s (send prob get-solution))
      (define how-many-lines-to-take (assert (hash-ref s "column-lines") natural?))
      (define-values (lines-to-take lines-to-leave) (split-at lines-remaining how-many-lines-to-take))
      (send prob reset)
      (define new-column (quads->column lines-to-take))
      (values (cons (apply column (attr-change (make-quadattrs (quad-attrs new-column)) (list world:column-index-key col-idx)) (quad-list new-column)) columns) lines-to-leave)))
  (reverse columns))

;(: columns->pages ((Listof Quad) . -> . (Listof Quad)))
(define (columns->pages cols)
  (define columns-per-page (assert (quad-attr-ref (car cols) world:column-count-key (world:column-count-key-default)) positive-integer?))
  (define column-gutter (assert (quad-attr-ref (car cols) world:column-gutter-key (world:column-gutter-key-default)) flonum?))
  ;; don't use default value here. If the col doesn't have a measure key,
  ;; it deserves to be an error, because that means the line was composed incorrectly.
  (when (not (quad-has-attr? (car cols) world:measure-key))
    (error 'columns->pages "column attrs contain no measure key: ~a ~a" (quad-attrs (car cols)) (quad-car (car cols))))
  (define column-width (assert (quad-attr-ref (car cols) world:measure-key) flonum?))
  (define width-of-printed-area (+ (* columns-per-page column-width) (* (sub1 columns-per-page) column-gutter)))
  (define result-pages
    (map  (λ(cols) (quads->page cols))
                                       (for/list  ([page-cols (in-list (slice-at cols columns-per-page))])
                                         (define-values (last-x cols)
                                           (for/fold ([current-x  (/ (- (world:paper-width-default) width-of-printed-area) 2.0)]
                                                      [cols  null])
                                                     ([col (in-list page-cols)][idx (in-naturals)])
                                             (values (foldl fl+ 0.0 (list current-x column-width column-gutter)) (cons (quad-attr-set* col (list 'x current-x 'y 40.0 world:column-index-key idx)) cols))))
                                         (reverse cols))))
  result-pages)

;(: block-quads->lines ((Listof Quad) . -> . (Listof Quad)))
(define (block-quads->lines qs)
  (block->lines (quads->block qs)))
