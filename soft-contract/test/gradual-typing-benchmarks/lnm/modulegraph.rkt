#lang racket/base

;; Utilities for working with modules graphs.
;;
;; The source of truth are TiKZ'd module graphs
;; (because their layout requires human intervention)
;; so this file provides a (brittle) parser.

(provide
  from-tex
  module-names
  (struct-out modulegraph)
  path->project-name
  project-name
)

;; -----------------------------------------------------------------------------

(require
  racket/match
  (only-in racket/path file-name-from-path filename-extension)
  (only-in racket/sequence sequence->list)
  (only-in racket/string string-split string-trim)
)

;; =============================================================================
;; --- data definition: modulegraph

;; A module graph is represented as an adjacency list (all graphs are DAGs)
;; Invariant: names in the adjlist are kept in alphabetical order.
(struct modulegraph (project-name adjlist) #:transparent)

;; Get the name of the project represented by a module graph
(define (project-name mg)
  (modulegraph-project-name mg))

;; Get the names of all modules in this graph's project
;; (: module-names (-> ModuleGraph (Listof String)))
(define (module-names mg)
  (for/list ([node+neighbors (in-list (modulegraph-adjlist mg))])
    (car node+neighbors)))

;; Get the index matching the module name
;; (: name->index (-> ModuleGraph String Index))
(define (name->index mg name)
  (for/or ([node+neighbors (in-list (modulegraph-adjlist mg))]
           [i (in-range 0 (length (modulegraph-adjlist mg)))])
    (and (string=? name (car node+neighbors))
         i)))

;; Get the name of the module with index `i`
;; (: index->name (-> ModuleGraph Index String))
(define (index->name mg i)
  (car (list-ref (modulegraph-adjlist mg) i)))

;; Get the names of modules required by `name`.
;; (: require (-> ModuleGraph String (Listof String)))
(define (requires mg name)
  (for/or ([node+neighbors (in-list (modulegraph-adjlist mg))])
    (and (string=? name (car node+neighbors))
         (cdr node+neighbors))))

;; -----------------------------------------------------------------------------
;; --- parsing TiKZ

(struct texnode (id index name) #:transparent)
;; A `texedge` is a (Pairof Index Index)

(define-syntax-rule (parse-error msg arg* ...)
  (error 'modulegraph (format msg arg* ...)))

;; Interpret a .tex file containing a TiKZ picture as a module graph
;; (: from-tex (-> Path-String Module-Graph))
(define (from-tex filename)
  (define-values (path project-name) (ensure-tex filename))
  (call-with-input-file* filename
    (lambda (port)
      (ensure-tikz port)
      (define-values (edge1 tex-nodes) (parse-nodes port))
      (define tex-edges (cons edge1 (parse-edges port)))
      (tex->modulegraph project-name tex-nodes tex-edges))))

;; Verify that `filename` is a tex file, return the name of
;; the project it describes.
;; (: ensure-tex (-> (U Path-String Path) String))
(define (ensure-tex filename)
  (define path (or (and (path? filename) filename)
                   (string->path filename)))
  (unless (bytes=? #"tex" (filename-extension path))
    (parse-error "Cannot parse module graph from non-tex file '~a'" filename))
  ;; Remove anything past the first hyphen in the project name
  (define project-name (path->project-name path))
  (values path project-name))

;; Parse the project's name from a path
;; (: path->project-name (-> Path String))
(define (path->project-name path)
  (define without-ext
    (car (string-split (path->string (file-name-from-path path)) ".")))
  (define without-hyphen
    (car (string-split without-ext "-")))
  without-hyphen)

;; Verify that the lines contained in `port` contain a TiKZ picture
;; Advance the port
;; (: ensure-tikz (-> Port Void))
(define (ensure-tikz port)
  (define line (read-line port))
  (cond [(eof-object? line)
         ;; No more input = failed to read a module graph
         (parse-error "Input is not a TiKZ picture")]
        [(string=? "\\begin{tikzpicture}" (string-trim line))
         ;; Success! We have id'd this file as a TiKZ picture
         port]
        [else
         ;; Try again with what's left
         (ensure-tikz port)]))

;; Parse consecutive `\node` declarations in a TiKZ file,
;; ignoring blank spaces and comments.
;; (: parse-nodes (->* [Port] [(Listof texnode)] (Listof texnode)))
(define (parse-nodes port [nodes-acc '()])
  (define raw-line (read-line port))
  (when (eof-object? raw-line)
    ;; EOF here means there's no edges below
    (parse-error "Hit end-of-file while reading nodes. Module graphs must have edges."))
  (define line (string-trim raw-line))
  (cond
    [(< (string-length line) 4)
     ;; Degenerate line, can't contain anything useful
     (parse-nodes port nodes-acc)]
    [(equal? #\% (string-ref line 0))
     ;; Line is a comment, ignore
     (parse-nodes port nodes-acc)]
    [(string=? "\\node" (substring line 0 5))
     ;; Found node! Keep if it's a real node (not just for positioning), then continue parsing
     (define nodes-acc+
       (if (dummy-node? line)
         nodes-acc
         (cons (string->texnode line) nodes-acc)))
     (parse-nodes port nodes-acc+)]
    [(string=? "\\draw" (substring line 0 5))
     ;; Found edge, means this stage of parsing is over
     (values (string->texedge line) nodes-acc)]
    [else
     ;; Invalid input
     (parse-error "Cannot parse node from line '~a'" line)]))

;; Parse consecutive `\edge` declarations, ignore blanks and comments.
;; (: parse-edges (->* [Port] [(Listof texedge)] (Listof texedge)))
(define (parse-edges port [edges-acc '()])
  (define raw-line (read-line port))
  (when (eof-object? raw-line)
    ;; End of file; should have seen \end{tikzpicture}
    (parse-error "Parsing reached end-of-file before reading \end{tikzpicture}. Are you sure the input is valid .tex?"))
  (define line (string-trim raw-line))
  (cond
    [(< (string-length line) 4)
     ;; Degenerate line, can't contain anything useful
     (parse-edges port edges-acc)]
    [(equal? #\% (string-ref line 0))
     ;; Line is a comment, ignore
     (parse-edges port edges-acc)]
    [(string=? "\\draw" (substring line 0 5))
     ;; Found edge! Parse and recurse
     (parse-edges port (cons (string->texedge line) edges-acc))]
    [(string=? "\\node" (substring line 0 5))
     ;; Should never see nodes here
     (parse-error "Malformed TiKZ file: found node while reading edges.")]
    [(string=? "\\end{tikzpicture}" line)
     ;; End of picture, we're done!
     edges-acc]
    [else
     ;; Invalid input
     (parse-error "Cannot parse edge from line '~a'" line)]))

;; For parsing nodes:
;;   \node (ID) [pos]? {\rkt{ID}{NAME}};
(define NODE_REGEXP
  #rx"^\\\\node *\\(([0-9]+)\\) *(\\[.*\\])? *\\{\\\\rkt\\{([0-9]+)\\}\\{(.+)\\}\\};$")
;; For parsing edges
;;   \draw[style]? (ID) edge (ID);
(define EDGE_REGEXP
  #rx"^\\\\draw\\[.*\\]? *\\(([0-9]+)\\)[^(]*\\(([0-9]+)\\);$")

;; Check if a line represents a real node, or is just for positioning
(define (dummy-node? str)
  (define N (string-length str))
  (string=? "{};" (substring str (- N 3) N)))

;; Parse a string into a texnode struct.
;; (: string->texnode (-> String texnode))
(define (string->texnode str)
  (define m (regexp-match NODE_REGEXP str))
  (match m
    [(list _ id _ index name)
     (texnode (string->number id)
              (string->number index)
              name)]
    [else
     (parse-error "Cannot parse node declaration '~a'" str)]))

;; Parse a string into a tex edge.
;; Edges are represented as cons pairs of their source and destination.
;; Both source and dest. are represented as indexes.
;; (: string->texedge (-> String texedge))
(define (string->texedge str)
  (define m (regexp-match EDGE_REGEXP str))
  (match m
    [(list _ id-src id-dst)
     (cons (string->number id-src)
           (string->number id-dst))]
    [else
     (parse-error "Cannot parse edge declaration '~a'" str)]))

;; Convert nodes & edges parsed from a .tex file to a modulegraph struct
;; (: tex->modulegraph (-> (Listof texnode) (Listof texedge) ModuleGraph))
(define (tex->modulegraph project-name nodes edges)
  ;; Convert a TiKZ node id to a module name
  (define (id->name id)
    (for/or ([tx (in-list nodes)])
      (and (= id (texnode-id tx))
           (texnode-name tx))))
  ;; Create an adjacency list by finding the matching edges for each node
  (define adjlist
    (for/list ([tx (in-list nodes)])
      (cons (cons (texnode-index tx) (texnode-name tx))
            (for/list ([src+dst (in-list edges)]
                       #:when (= (texnode-id tx) (car src+dst)))
              (id->name (cdr src+dst))))))
  ;; Alphabetically sort the adjlist, check that the indices match the ordering
  ;; Need to append .rkt, else things like (string< "a-base" "a") fail. They should pass...
  (define sorted (sort adjlist string<? #:key (lambda (x) (string-append (cdar x) ".rkt"))))
  (unless (equal? (map caar sorted)
                  (sequence->list (in-range (length sorted))))
    (parse-error "Indices do not match alphabetical ordering on module names. Is the TiKZ graph correct?\n    Source: '~a'\n" (map car sorted)))
  ;; Drop the indices
  (define untagged
    (for/list ([tag+neighbors (in-list sorted)])
      (cons (cdar tag+neighbors) (cdr tag+neighbors))))
  (modulegraph project-name untagged))

