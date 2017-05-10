#lang racket/base

(provide
  quad
  quad?
  quad-attrs?
  ;;; --
  block
  block-break
  ;block-break?
  box
  column
  column-break
  ;column-break?
  ;column?
  ;group-quad-list
  line
  ;line?
  make-quadattrs
  optical-kern
  optical-kern?
  page
  page-break
  ;page-break?
  piece
  quad->string
  quad-attr-ref
  quad-attrs
  quad-car
  quad-has-attr?
  quad-list
  quad-name
  quads->block
  quads->column
  quads->doc
  quads->line
  quads->page
  ;run?
  spacer
  ;spacer?
  whitespace/nbsp?
  whitespace?
  word
  word-break
  ;word-break?
  word-string
  ;word?
 )

;; -----------------------------------------------------------------------------

(require
 require-typed-check
 "../base/quad-types.rkt"
 (only-in racket/string string-append*))

;; =============================================================================

(define (assert v p)
  (unless (p v) (error 'quad "assert"))
  v)

(define (listof-usq? v)
  (and (list? v) (andmap usq? v)))

(define (usq? v)
  (or (string? v) (quad? v)))

;; =============================================================================

;(: quad-name (-> Quad Symbol))
(define (quad-name q)
  (car q))

;(: quad-attrs (-> Quad (Listof Any)))
(define (quad-attrs q)
  (cond
    [(eq? '() q) '()] ;;bg also very bad
    [(eq? '() (cdr q)) '()] ;;bg do not understand, this is bad
    [else (cadr q)]))

;(: make-quadattr (-> Symbol Any (Pairof Symbol Any)))
(define (make-quadattr k v)
  (cons k v))

;(: quadattr-value (-> (Listof Any) Any))
(define (quadattr-value qa)
  (cdr qa))

;(define (quad-attr-keys qas)
;  (if (eq? '() qas)
;      qas
;      (map car qas)))

;(: quad-list (-> Quad (Listof USQ)))
(define (quad-list q)
  (assert (cddr q) listof-usq?))

;;bg;
;(: quad-attr-ref (->* ((U Quad QuadAttrs) Symbol) (Any) Any))
(define (quad-attr-ref q-or-qas key [default attr-missing])
  ;(: qas QuadAttrs)
  (define qas
    (if (quad? q-or-qas)
      (make-quadattrs (quad-attrs q-or-qas))
      q-or-qas))
  ;(: qa-result (U #f Any))
  (define qa-result ;;bg;
    (for/fold ;: (U #f Any)
              ([v  #f]) ([qap qas])
      (or v (and (equal? key (car qap))
                 (cdr qap)))))
  (if qa-result
      qa-result
      (if (not (equal? default attr-missing))
        default
        (error 'quad-attr-ref (format "Key ~v not found in quad attributes ~v" key qas)))))

(define cannot-be-common-attrs '(width x y page))
(define attr-missing 'g323613)

;(: quad->string (-> USQ String))
(define (quad->string q)
  (let loop  ([x  q])
    (cond
      [(string? x) x]
      [(quad? x) (string-append* (for/list ;: (Listof String)
                                   ([q (quad-list x)]) (loop q)))]
      [else (error 'quad->string "bg")])))

;(: gather-common-attrs (-> (Listof Quad) QuadAttrs))
(define (gather-common-attrs qs)
  (if (eq? '() qs)
      qs
      (let loop
        ([qs  qs]
         ;; start with the set of pairs in the first quad, then filter it down
         [candidate-attr-pairs 
           (let ([first-attrs (make-quadattrs (quad-attrs (car qs)))])
             (if first-attrs
               (for/fold ([caps  '()])
                         ([cap  (in-list first-attrs)])
                 (if (member (car cap) cannot-be-common-attrs)
                     caps
                     (cons cap caps)))
               null))])
        (cond
          [(null? candidate-attr-pairs) null] ; ran out of possible pairs, so return #f
          [(null? qs) candidate-attr-pairs] ; ran out of quads, so return common-attr-pairs
          ;; todo: reconsider type interface between output of this function and input to quadattrs
          [else (loop (cdr qs) (filter (λ(cap ) (member cap (quad-attrs (car qs)))) candidate-attr-pairs))]))))

;;bg; edited this
;(: make-quadattrs (-> (Listof Any) QuadAttrs))
(define (make-quadattrs xs)
  ;; no point typing the input as (U QuadAttrKey QuadAttrValue)
  ;; because QuadAttrValue is Any, so that's the same as plain Any
  (let loop ([xs  xs])
    (cond
     [(null? xs)
      '()]
     [(and (pair? (car xs)) (symbol? (caar xs)))
      (cons (car xs) (loop (cdr xs)))]
     [(null? (cdr xs))
      (if (string? (car xs)) '()
      (error 'make-quadattrs "odd-numbered list ~a ~a" xs (string? (car xs))))]
     [(symbol? (car xs))
      (cons (make-quadattr (car xs) (cadr xs))
            (loop (cddr xs)))]
     [else
      (error 'make-quadattrs "bad item ~a\n" (car xs))])))

;(: whitespace? (->* [Any] [Boolean] Boolean))
(define (whitespace? x [nbsp? #f])
  (cond
    [(quad? x) (whitespace? (quad-list x) nbsp?)]
    [(string? x) (or (and (regexp-match? #px"\\p{Zs}" x) ; Zs = unicode whitespace category
                          (or nbsp? (not (regexp-match? #px"\u00a0" x)))))] ; 00a0: nbsp
    [(list? x) (and (not (eq? '() x)) (andmap (λ(x) (whitespace? x nbsp?)) x))] ; andmap returns #t for empty lists
    [else #f]))

;(: whitespace/nbsp? (-> Any Boolean))
(define (whitespace/nbsp? x)
  (whitespace? x #t))

;;bg;
;(: quad-car (-> Quad USQ))
(define (quad-car q)
  (define ql (quad-list q))
  (if (not (null? ql))
      (let ([c  (car ql)])
        (cond
         [(string? c) c]
         [(quad? c) c]
         [else (error 'quad-car "type error")]))
      (error 'quad-car "quad-list empty")))

;(: quad-has-attr? (-> Quad Symbol Boolean))
(define (quad-has-attr? q key)
  (for/or ([attr (in-list (make-quadattrs (quad-attrs q)))])
    (eq? key (car attr))))

;(: word-string (-> Quad String))
(define (word-string c)
  (assert (car (quad-list c)) string?))

;;; -----------------------------------------------------------------------------
;
;(define (box? x)
;  (and (quad? x) (equal? (quad-name x) 'box)))

;(: box (->* ((Listof Any)) #:rest USQ Quad))
(define (box attrs . xs)
  (quad 'box (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(define (run? x)
;  (and (quad? x) (equal? (quad-name x) 'run)))
;
;(define (spacer? x)
;  (and (quad? x) (equal? (quad-name x) 'spacer)))

;(: spacer (->* ((Listof Any)) #:rest USQ Quad))
(define (spacer attrs . xs)
  (quad 'spacer (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(define (doc? x)
;  (and (quad? x) (equal? (quad-name x) 'doc)))

;(: doc (->* ((Listof Any)) #:rest USQ Quad))
(define (doc attrs . xs)
  (quad 'doc (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(: quads->doc (-> (Listof Quad) Quad))
(define (quads->doc qs)
  (apply doc (gather-common-attrs qs) qs))

;(: optical-kern? (-> Any Boolean))
(define (optical-kern? x)
  (and (quad? x) (equal? (quad-name x) 'optical-kern)))

;(: optical-kern (->* ((Listof Any)) #:rest USQ Quad))
(define (optical-kern attrs . xs)
  (quad 'optical-kern (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(define (piece? x)
;  (and (quad? x) (equal? (quad-name x) 'piece)))

;(: piece (->* ((Listof Any)) #:rest USQ Quad))
(define (piece attrs . xs)
  (quad 'piece (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(define (word? x)
;  (and (quad? x) (equal? (quad-name x) 'word)))

;(: word (->* ((Listof Any)) #:rest USQ Quad))
(define (word attrs . xs)
  (quad 'word (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(define (word-break? x)
;  (and (quad? x) (equal? (quad-name x) 'word-break)))

;(: word-break (->* ((Listof Any)) #:rest USQ Quad))
(define (word-break attrs . xs)
  (quad 'word-break (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(define (page-break? x)
;  (and (quad? x) (equal? (quad-name x) 'page-break)))

;;bg; I think I changed this
;(: page-break (-> Quad))
(define (page-break)
  (quad 'page-break '() '()))

;(define (column? x)
;  (and (quad? x) (equal? (quad-name x) 'column)))

;(define (column-break? x)
;  (and (quad? x) (equal? (quad-name x) 'column-break)))

;(define (block-break? x)
;  (and (quad? x) (equal? (quad-name x) block-break)))

;(: block-break (->* ((Listof Any)) #:rest USQ Quad))
(define (block-break attrs . xs)
  (quad 'block-break (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(: page (->* ((Listof Any)) #:rest USQ Quad))
(define (page attrs . xs)
  (quad 'page (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(: column (->* ((Listof Any)) #:rest USQ Quad))
(define (column attrs . xs)
  (quad 'column (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(: quads->page (-> (Listof Quad) Quad))
(define (quads->page qs)
  (apply page (gather-common-attrs qs) qs))

;(: quads->column (-> (Listof Quad) Quad))
(define (quads->column qs)
  (apply column (gather-common-attrs qs) qs))

;;bg; I think I changed this
;(: column-break (-> Quad))
(define (column-break)
  (quad 'column-break '() '()))

;(define (line? x)
;  (and (quad? x) (equal? 'line (quad-name x))))

;(: line (->* ((Listof Any)) #:rest USQ Quad))
(define (line attrs . xs)
  (quad 'line (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(: quads->line (-> (Listof Quad) Quad))
(define (quads->line qs)
  (apply line (gather-common-attrs qs) qs))

;(define (block? x)
;  (and (quad? x) (equal? 'block (quad-name x))))

;(: block (->* ((Listof Any)) () #:rest USQ Quad))
(define (block attrs . xs)
  (quad 'block (if (quad-attrs? attrs) attrs (make-quadattrs attrs)) xs))

;(: quads->block (-> (Listof Quad) Quad))
(define (quads->block qs)
  (apply block (gather-common-attrs qs) qs))

