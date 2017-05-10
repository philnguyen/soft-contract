#lang racket/base

(provide
  line?
  column?
  block
  quad-name
  quad-attrs
  quad-list
  group-quad-list
  make-quadattrs
  box
  page-break? page-break
  column-break? column-break
  block-break? block-break
  page
  quad-attr-ref
  column
  quad-has-attr?
  run?
  word?
  word-break?
  word-string
  spacer?
  spacer
  line
  whitespace/nbsp?
  quads->doc
  quads->column
  quad-car
  quads->page
  piece
  word-break
  whitespace?
  optical-kern?
  optical-kern
  word
  quads->line
  quad->string
  quads->block
 )

;; -----------------------------------------------------------------------------

(require
 require-typed-check
 "../base/core.rkt"
 (only-in racket/string string-append*))

;; =============================================================================

(define (quad-name q)
  (car q))

(define (quad-attrs q)
  (cond
    [(eq? '() q) '()] ;;bg also very bad
    [(eq? '() (cdr q)) '()] ;;bg do not understand, this is bad
    [else (car (cdr q))]))

(define (make-quadattr k v)
  (cons k v))

(define (quadattr-value qa)
  (cdr qa))

(define (quad-attr-keys qas)
  (if (eq? '() qas)
      qas
      (map car qas)))

(define (quad-list q)
  (cdr (cdr q)))

(define (group-quad-list q)
  (cdr (cdr q)))


(define (quad-attr-ref q-or-qas key [default attr-missing])
  (define qas (if (quad? q-or-qas) (quad-attrs q-or-qas) q-or-qas))
  (define qa-result (memf (λ(qap) (equal? key (car qap))) qas))
  (if qa-result
      ;; car beacause result of memf is a list tail; cadr because second element in pair
      (quadattr-value (car qa-result))
      (if (not (equal? default attr-missing)) default (error 'quad-attr-ref (format "Key ~v not found in quad attributes ~v" key qas)))))

(define cannot-be-common-attrs '(width x y page))
(define attr-missing (gensym))

(define (quad->string x)
  (let loop  ([x x])
    (cond
      [(string? x) x]
      ;; else branch relies on fact that x is either Quad or String
      [else (string-append* (map loop (quad-list x)))])))

(define (gather-common-attrs qs)
  (if (eq? '() qs)
      qs
      (let loop
        ([qs qs]
         ;; start with the set of pairs in the first quad, then filter it down
         [candidate-attr-pairs  (let ([first-attrs (quad-attrs (car qs))])
                                                     (if first-attrs
                                                         (for/fold ([caps  null]) ([cap (in-list first-attrs)])
                                                           (if (member (car cap) cannot-be-common-attrs)
                                                               caps
                                                               (cons cap caps)))
                                                         null))])
        (cond
          [(null? candidate-attr-pairs) null] ; ran out of possible pairs, so return #f
          [(null? qs) candidate-attr-pairs] ; ran out of quads, so return common-attr-pairs
          ;; todo: reconsider type interface between output of this function and input to quadattrs
          [else (loop (cdr qs) (filter (λ(cap ) (member cap (quad-attrs (car qs)))) candidate-attr-pairs))]))))

(define (make-quadattrs xs)
  ;; no point typing the input as (U QuadAttrKey QuadAttrValue)
  ;; because QuadAttrValue is Any, so that's the same as plain Any
  (let-values ([(ks vs even?) (for/fold
                               ([ks  null][vs  null][even?  #t])
                               ([x (in-list xs)])
                                (if (and even? (symbol? x))
                                    (values (cons x ks) vs #f)
                                    (values ks (cons x vs) #t)))])
    (when (not even?) (error 'quadattrs "odd number of elements in ~a" xs))
    ;; use for/fold rather than for/list to impliedly reverse the list
    ;; (having been reversed once above, this puts it back in order)
    (for/fold ([qas  null])([k (in-list ks)][v (in-list vs)])
      (cons (make-quadattr k v) qas))))

(define (whitespace? x [nbsp? #f])
  (cond
    [(quad? x) (whitespace? (quad-list x) nbsp?)]
    [(string? x) (or (and (regexp-match #px"\\p{Zs}" x) ; Zs = unicode whitespace category
                          (or nbsp? (not (regexp-match #px"\u00a0" x)))))] ; 00a0: nbsp
    [(list? x) (and (not (eq? '() x)) (andmap (λ(x) (whitespace? x nbsp?)) x))] ; andmap returns #t for empty lists
    [else #f]))

(define (whitespace/nbsp? x)
  (whitespace? x #t))

(define (quad-car q)
  (define ql (quad-list q))
  (if (not (eq? '() ql))
      ( car ql)
      (error 'quad-car "quad-list empty")))

(define (quad-has-attr? q key)
  (and ( member key (quad-attr-keys (quad-attrs q))) #t))

(define (word-string c) (car (quad-list c)))

;; -----------------------------------------------------------------------------

(define (box? x)
  (and (quad? x) (equal? (quad-name x) 'box)))
(define (box attrs . xs)
  (quad 'box (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (run? x)
  (and (quad? x) (equal? (quad-name x) 'run)))

(define (spacer? x)
  (and (quad? x) (equal? (quad-name x) 'spacer)))
(define (spacer attrs . xs)
  (quad 'spacer (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (doc? x)
  (and (quad? x) (equal? (quad-name x) 'doc)))
(define (doc attrs . xs)
  (quad 'doc (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))
(define (quads->doc qs)
  (apply doc (gather-common-attrs qs) qs))

(define (optical-kern? x)
  (and (quad? x) (equal? (quad-name x) 'optical-kern)))
(define (optical-kern attrs . xs)
  (quad 'optical-kern (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (piece? x)
  (and (quad? x) (equal? (quad-name x) 'piece)))
(define (piece attrs . xs)
  (quad 'piece (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (word? x)
  (and (quad? x) (equal? (quad-name x) 'word)))
(define (word attrs . xs)
  (quad 'word (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (word-break? x)
  (and (quad? x) (equal? (quad-name x) 'word-break)))
(define (word-break attrs . xs)
  (quad 'word-break (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (page-break? x)
  (and (quad? x) (equal? (quad-name x) 'page-break)))

(define (page-break)
  (define attrs '()) (define xs '())
  (quad 'page-break (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (column? x)
  (and (quad? x) (equal? (quad-name x) 'column)))

(define (column-break? x)
  (and (quad? x) (equal? (quad-name x) 'column-break)))

(define (block-break? x)
  (and (quad? x) (equal? (quad-name x) block-break)))

(define (block-break attrs . xs)
  (quad 'block-break (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (page attrs . xs)
  (quad 'page (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (column attrs . xs)
  (quad 'column (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (quads->page qs)
  (apply page (gather-common-attrs qs) qs))

(define (quads->column qs)
  (apply column (gather-common-attrs qs) qs))

(define (column-break)
  (define attrs '()) (define xs '())
  (quad 'column-break (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

(define (line? x)
  (and (quad? x) (equal? 'line (quad-name x))))
(define (line attrs . xs)
  (quad 'line (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))
(define (quads->line qs)
  (apply line (gather-common-attrs qs) qs))

(define (block? x)
  (and (quad? x) (equal? 'block (quad-name x))))
(define (block attrs . xs)
  (quad 'block (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))
(define (quads->block qs)
  (apply block (gather-common-attrs qs) qs))

