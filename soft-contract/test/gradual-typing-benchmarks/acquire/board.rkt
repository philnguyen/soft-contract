#lang racket

;; ---------------------------------------------------------------------------------------------------
;; a data representation for the board with operations for 
;; -- inspecting the board to strategize 
;; -- placing tiles on the board to realize a player's action 
;; the actions do not enforce the rules of the game only consistent placements 

;; also exports tiles+spots: A1 ... I12 via submodule tiles+spots

;; ---------------------------------------------------------------------------------------------------
(provide

 (struct-out tile)
 ; tile?
 ; ;; (-> Any Boolean)

 tile<=?
 ;; (-> Tile Tile Boolean)

 tile->string
 ;; (-> Tile String)

 ALL-TILES
 ;; (Listof Tile)
 ;; Postcondition: Sorted

 STARTER-TILES#
 ;; Natural

 FOUNDING GROWING MERGING SINGLETON IMPOSSIBLE
 ;; Symbol

 (rename-out [board make-board])
 ;; (-> Board)

 board-tiles
 ;; (-> Board (Listof Tile))

 (rename-out [ext:what-kind-of-spot what-kind-of-spot])
 ;; (-> Board Tile SpotType
 ;; (define-type SpotType (U FOUNDING GROWING MERGING SINGLETON IMPOSSIBLE))
 ;; Precondition:
 ;;   (free-spot? b t)
 ;; Postcondition:
 ;;   (U FOUNDING GROWING MERGING SINGLETON IMPOSSIBLE)

 (rename-out [ext:growing-which growing-which])
 ;; (-> Board Tile Hotel)
 ;; Precondition: (eq? (what-kind-of-spot b t) GROWING)

 (rename-out [ext:merging-which merging-which])
 ;; (-> Board Tile (Values (Pairof Hotel (Listof Hotel)) (Listof Hotel)))
 ;; Precondition: (eq? (what-kind-of-spot b t) MERGING)

 deduplicate/hotel

 size-of-hotel
 ;; (-> Board Hotel Natural)

 free-spot?
 ;; (-> Board Tile Boolean)

 (rename-out [ext:merge-hotels merge-hotels])
 ;; (-> Board Tile Hotel Board)
 ;; Precondition: (eq? (what-kind-of-spot b t) MERGING)
 ;; Precondition: (let-values ([(w _) (merging-which b t)]) (member h w))

 (rename-out [ext:found-hotel found-hotel])
 ;; (-> Board Tile Hotel Board)
 ;; Precondition: (eq? (what-kind-of-spot b t) FOUNDING)

 (rename-out [ext:grow-hotel grow-hotel])
 ;; (-> Board Tile Board)
 ;; Precondition: (eq? (what-kind-of-spot b t) GROWING)

 (rename-out [ext:place-tile place-tile])
 ;; (-> Board Tile Board)
 ;; Precondition: (memq (what-kind-of-spot b t) (list SINGLETON GROWING FOUNDING))

 (rename-out [ext:set-board set-board])
 ;; (-> Board Tile (U FOUNDING GROWING MERGING SINGLETON) (Option Hotel) Board)
 ;; Precondition: (free-spot? b t)
 ;; Precondition: (==> h (or (eq? FOUNDING a) (eq? MERGING a)))
 ;; Precondition: (==> (eq? MERGING a) h)

 (rename-out [ext:affordable? affordable?])
 ;; (-> Board Shares-Order Cash Boolean)

 (rename-out [ext:*create-board-with-hotels *create-board-with-hotels])
 ;; (-> (Listof Tile) (Listof (Pairof Hotel (Listof Tile))) Board)
 ;; Precondition: (distinct t*)
 ;; Precondition: ((distinct-and-properly-formed t) ht*)

 distinct-and-properly-formed
 ;; (-> (Listof Tile) (-> (Listof (Pairof Hotel (Listof Tile))) Boolean))
 )

;; ---------------------------------------------------------------------------------------------------
;; IMPLEMENTATION: SPOTS

(require
 "../base/untyped.rkt"
)
(require (only-in "basics.rkt"
 hotel?
 SAFE#
 price-per-share
 shares-order?
))
(require (only-in "auxiliaries.rkt"
  aux:partition
  distinct
))

;; =============================================================================

(module tiles racket
  (provide (all-defined-out))
  (require
   "../base/untyped.rkt")
  (require (only-in "basics.rkt"
    hotel->color
    hotel->label))
  (require (only-in "auxiliaries.rkt"
    randomly-pick))

  ;; ---------------------------------------------------------------------------------------------------
  ;; ROWS and COLUMNS


  (define COLUMNS
    '(1 2 3 4 5 6 7 8 9 10 11 12 13))

  (define (column? c)
    (if (member c COLUMNS) #t #f))

  (define (random-column)
    (randomly-pick COLUMNS))

  (define (column-> c)
    (let loop
         ([col* COLUMNS])
      (cond
       [(or (null? col*) (null? (cdr col*)))
        #f]
       [(eq? c (car col*))
        (cadr col*)]
       [else
        (loop (cdr col*))])))

  (define (column-< c)
    (let loop
         ([prev #f]
          [col* COLUMNS])
     (cond
       [(null? col*) #f]
       [(eq? c (car col*)) prev]
       [else (loop (car col*) (cdr col*))])))

  (define column<= <=)

  (define (string->column s)
    (and (string? s)
         (let ([n (string->number s)])
           (and n
                (member n COLUMNS)
                (exact-nonnegative-integer? n)
                n))))

  (define column->string number->string)

  (define ROWS '(A B C D E F G H I))

  (define (row? r)
    (if (member r ROWS) #t #f))

  (define (random-row) (randomly-pick ROWS))

  (define (row-v r)
    (let loop
         ([row* ROWS])
         (cond
           [(or (null? row*) (null? (cdr row*)))
            #f]
           [(eq? (car row*) r)
            (cadr row*)]
           [else
            (loop (cdr row*))])))

  (define (row-^ r)
    (let loop
         ([prev #f]
          [row* ROWS])
         (cond
           [(null? row*) #f]
           [(eq? (car row*) r) prev]
           [else (loop (car row*) (cdr row*))])))

  (define (list-index x y*)
    (or
     (for/or
             ([y  (in-list y*)]
             [i  (in-naturals)])
       (and (eq? x y) i))
     90))
  
  ;; ;; Row Row -> Boolean 
  ;; ;; does q appear before r in order?
  (define (row<= q r)
    (<= (list-index q ROWS)
        (list-index r ROWS)))
  
  ;; ;; Row Row -> Boolean 
  ;; ;; does q appear strictly before r in order?
  (define (row<< q r)
    (< (list-index q ROWS)
       (list-index r ROWS)))
  
  ;; (define (row->text r)
  ;;   (text/font  (symbol->string r) 24 "black" #f 'system 'normal 'normal #f))

  (define (string->row s)
    (and (string? s)
         (let ([n (string->symbol s)])
           (and n (member n ROWS) n))))

  (define row->string symbol->string)

  (define CELL-SIZE 66)
  
  ;; ---------------------------------------------------------------------------------------------------
  (struct tile
    (column
     row
     ) #:transparent)

  (define TILE-SIZE (assert (- CELL-SIZE 3) exact-nonnegative-integer?))
  (define TILE-COLOR 'gray)
  (define STARTER-TILES# 6)
  
  (define-syntax-rule
    ;; should be an identifier macro but contracts
    (ctile letter number) (tile/c number 'letter))

  ;; (-> column? row? any)
  (define (tile/c c r)
    (if (and (column? c) (row? r))
        (tile c r)
        (error 'tile "not (column,row): ~e, ~e" c r)))

  (define ALL-TILES 
    (for*/list
               ((r ROWS) (c  COLUMNS))
      (tile c r)))
  
  ;; Tile Tile -> Boolean 
  ;; is t1 closer to the top-left corner than t2?
  (define (tile<=? t1 t2)
    (or (row<< (tile-row t1) (tile-row t2))
        (and (row<= (tile-row t1) (tile-row t2))
             (column<= (tile-column t1) (tile-column t2)))))

  (define (tile<? s t)
    (and (tile<=? s t) (not (equal? s t))))

  (define (tile>? s t)
    (and (tile<=? t s) (not (equal? s t))))

  (define (tile->string t)
    (format "(~a,~a)" (tile-column t) (tile-row t)))

  )

(require 'tiles)

;; ---------------------------------------------------------------------------------------------------
;; data

(define FOUNDING 'FOUNDING)
(define GROWING 'GROWING)
(define MERGING 'MERGING)
(define SINGLETON 'SINGLETON)
(define IMPOSSIBLE 'IMPOSSIBLE)

;; no tile is placed in this cell
(define UNTAKEN 'UNTAKEN)

;; a tile is placed but it does not belong to a hotel 
(define TAKEN-NO-HOTEL 'taken-no-hotel)

;; Content = Hotel | UNTAKEN | TAKEN-NO-HOTEL

;; board   = [Hashof Tile Content]
;; if a (c,r) key maps to a hotel, it belongs to this hotel; otherwise it is free

(define (board? x)
  ;;bg; do more?
  (and (hash? x)))

(define (board) #hash())

(define (board-tiles b) (hash-keys b))

;; ---------------------------------------------------------------------------------------------------
;; FUNCTIONS internal 

;; Tile *-> Board 
;; place tiles; do not found or create hotels
(define (board* . t*)  
  (for/fold
            ((b  (board)))
            ((t  (in-list t*)))
    (place-tile b t)))

(define (ext:*create-board-with-hotels lt lh)
  (unless (distinct lt)
    (error 'create-board-with-hotels "precondition"))
  (unless ((distinct-and-properly-formed lt) lh)
    (error 'create-board-with-hotels "precondition"))
  (*create-board-with-hotels lt lh))

(define (*create-board-with-hotels lt lh)
  (for/fold
            ((b  (apply board* lt)))
            ((h lh))
    (define name (first h))
    (define til* (rest h))
    (for/fold
              ((b  b))
              ((t  (in-list (rest h))))
      (hash-set b t name))))

(define (board-ref b c r)
  (hash-ref b (tile c r) (lambda () UNTAKEN)))

;; Board Column Row -> Content
(define (board-set b c r [h TAKEN-NO-HOTEL])
  (hash-set b (tile c r) h))

;; Board Column Row [X X X X ->* Y] ->* Y 
;; produce neighbors in North East South and West
(define (neighbors b c r f)
  (f (north b c r) (east b c r) (south b c r) (west b c r)))

(define (cardinal-direction n-s e-w)
  (lambda (b
           c
           r)
    (define north-south (n-s r))
    (define east-west (e-w c))
    (cond 
      [(boolean? north-south) UNTAKEN]
      [(boolean? east-west)   UNTAKEN]
      [else (board-ref b east-west north-south)])))

(define north (cardinal-direction row-^ (lambda (x) x)))
(define south (cardinal-direction row-v (lambda (x) x)))
(define east (cardinal-direction (lambda (x) x) column->))
(define west (cardinal-direction (lambda (x) x) column-<))

;; Board Hotel -> [Listof Tile] | sorted * tile<=?
(define (tiles-with-specific-label b h)
  (define t* (for/list ([(s label) (in-hash b)] #:when (equal? h label)) s))
  (sort t* tile<=?))

;; ---------------------------------------------------------------------------------------------------
;; FUNCTIONS external functions  

(define (free-spot? board tile)
  (eq? (board-ref board (tile-column tile) (tile-row tile))
       UNTAKEN))

(define (ext:what-kind-of-spot board tile)
  (unless (free-spot? board tile)
    (error 'what-kind-of-spot (format "Precondition: (free-spot ~a ~a)" board tile)))
  (what-kind-of-spot board tile))

(define (what-kind-of-spot board tile)
  (define column (tile-column tile))
  (define row (tile-row tile))
  (define surroundings (neighbors board column row list))
  (define hotels (deduplicate/hotel
                  (for/list
                            ([s  (in-list surroundings)]
                             #:when (hotel? s))
                    (assert s string?))))
  (define hotels# (length hotels))
  (define neighbor-taken-no-hotel?
    (for/or
            ([s (in-list surroundings)])
      (and (eq? TAKEN-NO-HOTEL s) s)))
  (cond
    [(= hotels# 0) (if neighbor-taken-no-hotel? FOUNDING SINGLETON)]
    [(= hotels# 1) (if neighbor-taken-no-hotel? IMPOSSIBLE GROWING)]
    [(>= hotels# 2)
     (define any-hotel-safe?
       (for/or
               ((h  (in-list hotels)))
         (>= (size-of-hotel board h) SAFE#)))
     (if (or neighbor-taken-no-hotel? any-hotel-safe?) IMPOSSIBLE MERGING)]
    [else (error 'nope)]))

(define (ext:growing-which board tile)
  (unless (eq? (what-kind-of-spot board tile) GROWING)
    (error 'growing-which (format "Precondition: expected growing, got ~a" (what-kind-of-spot board tile))))
  (growing-which board tile))

(define (growing-which board tile)
  ;; the 'first' is guranateed by contract
  (define n* (neighbors board (tile-column tile) (tile-row tile) list))
  (for/or
          ([c (in-list n*)])
    (and (hotel? c) (assert c string?))))

(define (ext:merging-which board tile)
  (unless (eq? (what-kind-of-spot board tile) MERGING)
    (error 'merging-which (format "Precondition: expected merging, got ~a" (what-kind-of-spot board tile))))
  (merging-which board tile))

(define (merging-which board tile)
  (define surroundings (neighbors board (tile-column tile) (tile-row tile) list))
  (define hotels (deduplicate/hotel
                  (for/list
                            ([s  (in-list surroundings)]
                             #:when (hotel? s))
                    (assert s string?))))
  (define sorted
    (let ([x* (for/list
                        ([h  (in-list hotels)])
                (list h (size-of-hotel board h)))])
      (sort x* (lambda (x y) (> (cadr x) (cadr y))))))
  (define partitioned (aux:partition sorted second (lambda (x) (car x))))
  (values (assert (first partitioned) pairof-hotel-listof-hotel) (apply append (rest partitioned))))

(define (pairof-hotel-listof-hotel x)
  (and (pair? x)
       (hotel? (car x))
       (list? (cdr x))
       (andmap hotel? (cdr x))))

(define (deduplicate/hotel h*)
  (let loop ([h* h*])
       (cond [(null? h*) '()]
             [(member (car h*) (cdr h*)) (loop (cdr h*))]
             [else (cons (car h*) (loop (cdr h*)))])))

(define (size-of-hotel board hotel)
  (for/fold
            ((size  0))
            ([(key value) (in-hash board)])
    (if (equal? hotel value) (+ size 1) size)))

(define (ext:grow-hotel board tile)
  (unless (eq? (what-kind-of-spot board tile) GROWING)
    (error 'grow-hotel (format "Precondition: expected founding, got ~a" (what-kind-of-spot board tile))))
  (grow-hotel board tile))

(define (grow-hotel board tile)
  (define row (tile-row tile))
  (define column (tile-column tile))
  (define surroundings (neighbors board column row list))
  (define hotel-that-touches (first (filter hotel? surroundings)))
  (board-set board column row hotel-that-touches))

(define (ext:merge-hotels board tile hotel)
  (unless (eq? (what-kind-of-spot board tile) MERGING)
    (error 'merge-hotels (format "Precondition: expected merging, got ~a" (eq? (what-kind-of-spot board tile) MERGING))))
  (unless (let-values ([(w _) (merging-which board tile)]) (member hotel w))
    (error 'merge-hotels (format "Precondition: hotel ~a is not on a merging spot" hotel)))
  (merge-hotels board tile hotel))

(define (merge-hotels board tile hotel)
  (define row (tile-row tile))
  (define column (tile-column tile))
  (define-values (acquirers acquired) (merging-which board tile))
  (define acquired-hotels (append (remq hotel acquirers) acquired))
  (define relabeled-hotel
    (for/hash
              (([key current-content] (in-hash board)))
      (if (memq current-content acquired-hotels)
          (values key hotel)
          (values key current-content))))
  (board-set relabeled-hotel column row hotel))

(define (ext:found-hotel board tile hotel)
  (unless (eq? (what-kind-of-spot board tile) FOUNDING)
    (error 'found-hotel (format "Precondition: expected founding, got ~a" (what-kind-of-spot board tile))))
  (found-hotel board tile hotel))

(define (found-hotel board tile hotel)
  (define row (tile-row tile))
  (define column (tile-column tile))
  (board-set (hotel-take-over-neighboring-tiles board column row hotel) column row hotel))

;; Board Column Row Hotel -> Board 
;; mark all TAKEN-NO-HOTEL tiles on board reachable from (column,row) as belong to hotel
;; Global Invariant: This region does not touch any other hotels
(define (hotel-take-over-neighboring-tiles board column row hotel)
  (let loop
       ((board  board)
        (to-visit  (list (tile column row)))
        (visited  '()))
    (cond
      [(empty? to-visit) board]
      [(member (first to-visit) visited) (loop board (rest to-visit) visited)]
      [else 
       (define column (tile-column (first to-visit)))
       (define row (tile-row (first to-visit)))
       (define-values (n e s w)
         (let ([r (neighbors board column row list)])
           (values (car r) (cadr r) (caddr r) (cadddr r))))
       (define no-tiles '())
       (loop (board-set board column row hotel)
             (append (if (equal? TAKEN-NO-HOTEL n) (list (tile column (or (row-^ row) (error 'badrow)))) no-tiles)
                     (if (equal? TAKEN-NO-HOTEL e) (list (tile (or (column-> column) (error 'badcol)) row)) no-tiles)
                     (if (equal? TAKEN-NO-HOTEL s) (list (tile column (or (row-v row) (error 'badrow)))) no-tiles)
                     (if (equal? TAKEN-NO-HOTEL w) (list (tile (or (column-< column) (error 'badcol)) row)) no-tiles)
                     (rest to-visit))
             (cons (first to-visit) visited))])))

(define (ext:place-tile board tile)
  (unless (memq (what-kind-of-spot board tile) (list SINGLETON GROWING FOUNDING))
    (error 'place-tile "precondition"))
  (place-tile board tile))

(define (place-tile board tile)
  (define row (tile-row tile))
  (define column (tile-column tile))
  (board-set board column row))

(define (ext:set-board board tile kind hotel)
  (unless (free-spot? board tile)
    (error 'set-board "Precondition"))
  (unless (if hotel (or (eq? FOUNDING kind) (eq? MERGING kind)) #t)
    (error 'set-board "Precondition"))
  (unless (if (eq? MERGING kind) hotel #t)
    (error 'set-board "Precondition"))
  (set-board board tile kind hotel))

(define (set-board board tile kind hotel)
  (cond
    [(eq? FOUNDING kind) (if hotel (found-hotel board tile hotel) (place-tile board tile))]
    [(and hotel (eq? MERGING kind)) (merge-hotels board tile hotel)]
    [(and hotel (eq? SINGLETON kind)) (place-tile board tile)]
    [(and hotel (eq? GROWING kind)) (grow-hotel board tile)]
    [else (error 'nopers)]))

(define (ext:affordable? board hotels budget)
  (unless (shares-order? hotels)
    (error 'afoordable "precondigin"))
  (affordable? board hotels budget))

(define (affordable? board hotels budget)
  (define prices
    (for/list
              ([h  (in-list hotels)])
      (price-per-share h (size-of-hotel board h))))
  (define s
    (for/fold
              ([acc  0])
              ([c  (in-list prices)])
              (if c (+ c acc) acc)))
  (if (ormap boolean? prices) #f (<= s budget)))

;; ---------------------------------------------------------------------------------------------------
;; notions of contracts for creating a board with hotels specified as lists

;; (1) the hotels have distinct names 
;; (2) each hotel comes with at least two tiles 
;; (3) the tiles of the hotels and the unassociated tiles are distinct 
;; (4) the tiles of each hotel form connected graphs 
;; (5) no two hotel chains touch each other directly
(define ((distinct-and-properly-formed free-tiles) hotels-as-lists)
  (define hotel-tiles
    (for/list
              ([hl  (in-list hotels-as-lists)])
      (cdr hl)))
  (define first*
    (for/list
              ([hl  (in-list hotels-as-lists)])
      (car hl)))
  (and (or (distinct first*) (tee/#f "hotel names not distinct"))
       (or (andmap contains-at-least-two hotel-tiles) (tee/#f "hotels don't have 2 tiles"))
       (or (distinct (apply append free-tiles hotel-tiles)) (tee/#f "hotel & free tiles overlap"))
       (or (andmap connected-graph hotel-tiles) (tee/#f "hotels not graphs"))
       (or (no-two-hotels-touch hotel-tiles) (tee/#f "two hotels touch"))))

(define (tee/#f s)
  (error 'distint-and-properly-formed s))

;; ---------------------------------------------------------------------------------------------------
;; auxiliary notiones 

;; HT = (cons Tile (cons Tile [Listof Tile])) ;; the tiles of a syntactically well-formed hotel

;; ;; HT -> Boolean
(define (contains-at-least-two ht)
  (and (cons? ht) (cons? (rest ht))))

;; ;; HT -> Boolean 
;; ;; do the tiles of a hotel form a connected graph?
(define (connected-graph hotel-tiles)
  (define start (first hotel-tiles))
  (define remaining (rest hotel-tiles))
  (define next (connected-to start remaining))
  (and (cons? next)
       (let loop
            ((frontier next)
             (remaining (remove* next remaining)))
         (cond
           [(empty? remaining) #t]
           [else (define one-step (apply append
                                         (map (λ (f)
                                                (connected-to f remaining))
                                              frontier)))
                 (and (cons? one-step) (loop one-step (remove* one-step remaining)))]))))

;; ;; [Listof HT] -> Boolean 
;; ;; are any pairs of HTs connected? if so, return #f
(define (no-two-hotels-touch hotel-tiles*)
  (and-over-pairs-of-distinct-hotels 
   (lambda (one other)
     (not (connected-graph (append one other))))
   hotel-tiles*))

;; ;; [HT HT -> Boolean] [Listof HT] -> Boolean
;; ;; apply f to all pairs of distinct HTs on lh
(define (and-over-pairs-of-distinct-hotels f hotel-tiles*)
  (or (empty? hotel-tiles*)
      (let loop
           ([preceding  '()]
            [current  (first hotel-tiles*)]
            [remaining  (rest hotel-tiles*)])
        (cond
          [(empty? remaining) #t]
          [else (and (for/and
                              ((h  (append preceding remaining)))
                       (f current h))
                     (loop (cons current preceding) (first remaining) (rest remaining)))]))))

;; ;; Tile HT -> [Listof Tile]
;; ;; find all (at most four) tiles in lh that are connected to t
(define (connected-to t hotel-tiles*)
  (define r (tile-row t))
  (define c (tile-column t))
  (define (in r c)
    (if (and r c)
        (let ([m (member (tile c r) hotel-tiles*)])
          (if m
              (list (first m))
              '()))
        '()))
  (append (in (or (row-^ r) (error 'badr)) c)
          (in (or (row-v r) (error 'badr)) c)
          (in r (or (column-> c) (error 'badc)))
          (in r (or (column-< c) (error 'badc)))))

