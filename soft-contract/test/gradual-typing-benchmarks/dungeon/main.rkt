#lang racket
;(random-seed 4) ;; the old, unused random seed

;(provide
;  generate-dungeon
;  smooth-walls
;) ; for testing, and visibility

;; -----------------------------------------------------------------------------

(require
  require-typed-check
  racket/class
  "../base/un-types.rkt"
  racket/match
)
(require (only-in racket/set
  set-intersect
))
(require (only-in racket/dict
  dict-set
))
(require (only-in "cell.rkt"
  void-cell%
  wall%
  door%
  vertical-door%
  horizontal-door%
  horizontal-wall%
  four-corner-wall%
  pillar%
  vertical-wall%
  north-west-wall%
  north-east-wall%
  south-west-wall%
  south-east-wall%
  north-tee-wall%
  west-tee-wall%
  east-tee-wall%
  south-tee-wall%
  empty-cell%
))
(require (only-in "grid.rkt"
  left
  right
  up
  down
  grid-ref
  grid-height
  grid-width
  show-grid
  array-set!
  build-array
))
(require (only-in "utils.rkt"
  random-between
  random-from
  random
))

;; =============================================================================
;(define-type Poss->Cells (Listof (Pairof Pos Cell%)))
;(define-type Direction (->* (Pos) (Index) Pos))
;(define-type Cache (HashTable Pos Boolean))
;(define-type ExtPoints (Listof (Pairof Pos Room)))
;; dungeon generation

(struct room
  (height
   width
   poss->cells ; maps positions to cell constructors
   ;;            (so that we can construct the room later when we commit to it)
   free-cells   ; where monsters or treasure could go
   extension-points)) ; where a corridor could sprout

;; -----------------------------------------------------------------------------

(define N 1)

(define wall-cache (make-hash))

(define free-cache (make-hash))
(define animate-generation? #f) ; to see intermediate steps
(define ITERS 10)
(define dungeon-height 18) ; to be easy to display in 80x24, with other stuff
(define dungeon-width  60)

;; -----------------------------------------------------------------------------

(define (try-add-rectangle grid pos height width direction)
  ;; height and width include a wall of one cell wide on each side
  (match-define (vector x y) pos)
  (define min-x (match direction
                  [(== down) x]
                  ;; expanding north, we have to move the top of the room
                  ;; up so the bottom reaches the starting point
                  [(== up) (+ (- x height) 1)]
                  ;; have the entrance be at a random position on the
                  ;; entrance-side wall
                  [else    (sub1 (- x (random (- height 2))))]))
  (define min-y (match direction
                  ;; same idea as for x
                  [(== right) y]
                  [(== left)  (+ (- y width) 1)]
                  [else       (sub1 (- y (random (- width 2))))]))
  (define max-x (+ min-x height))
  (define max-y (+ min-y width))
  (define-values (success? poss->cells free-cells extension-points)
    (for*/fold
               ([success?         #t]
                [poss->cells       '()]
                [free-cells        '()]
                [extension-points  '()])
        ([x (in-range min-x max-x)]
         [y (in-range min-y max-y)])
      ;#:break (not success?)
      (cond
       [(not success?)
        (values success? poss->cells free-cells extension-points)]
       [success?
        (define c (and (index? x) (index? y) (grid-ref grid (vector x y))))
        (cond [(and c ; not out of bounds
                    (or (is-a? c void-cell%) ; unused yet
                        (is-a? c wall%)))    ; neighboring room, can abut
               (define p (vector (assert x index?) (assert y index?)))
               ;; tentatively add stuff
               (define x-wall? (or (= x min-x) (= x (sub1 max-x))))
               (define y-wall? (or (= y min-y) (= y (sub1 max-y))))
               (if (or x-wall? y-wall?)
                   ;; add a wall
                   (values #t ; still succeeding
                           (dict-set poss->cells p wall%)
                           free-cells
                           (if (and x-wall? y-wall?)
                               ;; don't extend from corners
                               extension-points
                               (cons p extension-points)))
                   (values #t
                           (dict-set poss->cells p empty-cell%)
                           (cons p free-cells)
                           extension-points))]
              [else ; hit something, give up
               (values #f '() '() '() )])])))
  (and success?
       (room height width poss->cells free-cells extension-points)))

;; mutate `grid` to add `room`
(define (commit-room grid room)
  (for ([pos+cell% (in-list (room-poss->cells room))])
    (match-define (cons pos cell%) pos+cell%)
    (array-set! grid pos (new cell%))))

;(module+ test
;  (require typed/rackunit)
;  (: render-grid (-> (Listof String) String))
;  (define (render-grid g) (string-join g "\n" #:after-last "\n"))
;  (: empty-grid (-> Grid))
;  (define (empty-grid)
;    (array->mutable-array
;     (build-array #(5 5) (lambda _ (new void-cell%)))))
;  (define g1 (empty-grid))
;  (check-equal? (show-grid g1)
;                (render-grid '("....."
;                               "....."
;                               "....."
;                               "....."
;                               ".....")))
;  (check-false (try-add-rectangle g1 #(10 10) 3 3 right)) ; out of bounds
;  (commit-room g1 (or (try-add-rectangle g1 #(2 1) 3 3 right) (error 'commit)))
;  (check-equal? (show-grid g1)
;                (render-grid '("....."
;                               ".XXX."
;                               ".X X."
;                               ".XXX."
;                               ".....")))
;  (check-false (or (try-add-rectangle g1 #(2 2) 2 2 up) (error 'commit)))
;  (commit-room g1 (or (try-add-rectangle g1 #(3 3) 2 2 down) (error 'commit)))
;  (check-equal? (show-grid g1)
;                (render-grid '("....."
;                               ".XXX."
;                               ".X X."
;                               ".XXX."
;                               "..XX.")))
;  (define g2 (empty-grid))
;  (commit-room g2 (or (try-add-rectangle g2 #(1 1) 2 4 right) (error 'commit)))
;  (check-equal? (show-grid g2)
;                (render-grid '(".XXXX"
;                               ".XXXX"
;                               "....."
;                               "....."
;                               ".....")))
;  )


(define (random-direction) (random-from (list left right up down)))

(define (horizontal? dir)  (or (eq? dir right)  (eq? dir left)))

(define (vertical? dir)    (or (eq? dir up) (eq? dir down)))

(define (new-room grid pos dir)
  (define w (assert (random-between 7 11) index?)) ; higher than that is hard to fit
  (define h (assert (random-between 7 11) index?))
  (try-add-rectangle grid pos w h dir))

(define (new-corridor grid pos dir)
  (define h? (horizontal? dir))
  (define len
    ;; given map proportions (terminal window), horizontal corridors are
    ;; easier to fit
    (assert
    (if h?
        (random-between 6 10)
        (random-between 5 8)) index?))
  (define h (if h? 3   len))
  (define w (if h? len 3))
  (try-add-rectangle grid pos h w dir))

(define (generate-dungeon encounters)
  ;; a room for each encounter, and a few empty ones
  (define n-rooms (max (length encounters) (random-between 6 9)))
  (define grid
     (build-array (vector dungeon-height dungeon-width)
                  (lambda _ (new void-cell%))))
  (define first-room
    (let loop  ()
      (define starting-point
        (vector (assert (random dungeon-height) index?)
                (assert (random dungeon-width) index?)))
      (define first-room
        (new-room grid starting-point (random-direction)))
      (or first-room (loop)))) ; if it doesn't fit, try again
  (commit-room grid first-room)
  (when animate-generation? (display (show-grid grid)))
  (define connections '()) ; keep track of pairs of connected rooms
  (define (extension-points/room room)
    (for/list  ([e (in-list (room-extension-points room))])
      (cons e room)))
  ;; for the rest of the rooms, try sprouting a corridor, with a room at the end
  ;; try until it works
  (let loop  ()
    (define-values (n all-rooms _2)
      (for/fold
                ([n-rooms-to-go    (sub1 n-rooms)]
                 [rooms             (list first-room)]
                 [extension-points  (extension-points/room first-room)])
          ([i (in-range ITERS)])
        (cond
         ((= n-rooms-to-go 0)
          (values n-rooms-to-go rooms extension-points))
         (else
        (define (add-room origin-room room ext [corridor #f] [new-ext #f])
          (when corridor
            (commit-room grid corridor))
          (commit-room grid room)
          ;; add doors
          (define door-kind
            (if (horizontal? dir) vertical-door% horizontal-door%))
          (array-set! grid ext     (new door-kind))
          (when new-ext
            (array-set! grid new-ext (new door-kind)))
          (set! connections (cons (cons origin-room room) connections))
          (when animate-generation? (display (show-grid grid)))
          (values (sub1 n-rooms-to-go)
                  (cons room rooms) ; corridors don't count
                  (append (if corridor
                              (extension-points/room corridor)
                              '())
                          (extension-points/room room)
                          extension-points)))
        ;; pick an extension point at random
        (match-define `(,ext . ,origin-room) (random-from extension-points))
        ;; first, try branching a corridor at random
        (define dir (random-direction))
        (cond [(and (zero? (random 4)) ; maybe add a room directly, no corridor
                    (new-room grid ext dir)) =>
               (lambda (room) (add-room origin-room room ext))]
              [(new-corridor grid ext dir) =>
               (lambda (corridor)
                 ;; now try adding a room at the end
                 ;; Note: we don't commit the corridor until we know the room
                 ;;   fits. This means that `try-add-rectangle` can't check
                 ;;   whether the two collide. It so happens that, since we're
                 ;;   putting the room at the far end of the corridor (and
                 ;;   extending from it), then that can't happen. We rely on
                 ;;   that invariant.
                 (define new-ext
                   (dir ext (if (horizontal? dir)
                                (assert (sub1 (room-width corridor)) index?) ; sub1 to make abut
                                (assert (sub1 (room-height corridor)) index?))))
                 (cond [(new-room grid new-ext dir) =>
                        (lambda (room) ; worked, commit both and keep going
                          (add-room origin-room room ext corridor new-ext))]
                       [else ; didn't fit, try again
                        (values n-rooms-to-go rooms extension-points)]))]
              [else ; didn't fit, try again
               (values n-rooms-to-go rooms extension-points)])))))
    (cond [(not (= n 0)) ; we got stuck, try again
           ;(log-error "generate-dungeon: had to restart")
           ;; may have gotten too ambitious with n of rooms, back off
           (set! n-rooms (max (length encounters) (sub1 n-rooms)))
           (loop)]
          [else ; we did it
           ;; try adding more doors
           (define potential-connections
             (for*/fold
                 ([potential-connections '()])
                 ([r1 (in-list all-rooms)]
                  [r2 (in-list all-rooms)]
                  #:unless (or (eq? r1 r2)
                               (member (cons r1 r2) connections)
                               (member (cons r2 r1) connections)
                               (member (cons r2 r1) potential-connections)))
               (cons (cons r1 r2) potential-connections)))
           ;; if the two in a pair share a wall, put a door through it
           (for ([r1+r2 (in-list potential-connections)])
             (match-define (cons r1 r2) r1+r2)
             (define common
               ;(set->list
               ;  (set-intersect (list->set (room-extension-points r1))
               ;                 (list->set (room-extension-points r2)))))
                 (set-intersect (room-extension-points r1)
                                (room-extension-points r2)))
             (define possible-doors
               (filter (lambda (x) x)
                       (for/list
                                 ([pos (in-list common)])
                         (cond [(and (counts-as-free? grid (up   pos))
                                     (counts-as-free? grid (down pos)))
                                (cons pos horizontal-door%)]
                               [(and (counts-as-free? grid (left  pos))
                                     (counts-as-free? grid (right pos)))
                                (cons pos vertical-door%)]
                               [else #f]))))
             (when (not (empty? possible-doors))
               (match-define (cons pos door-kind) (random-from possible-doors))
               (array-set! grid pos (new door-kind))))
           grid])))


(define (counts-as-free? grid pos) ; i.e., player could be there
  (cond [(hash-ref free-cache pos #f) => (lambda (x) x)]
        [else
         (define c   (grid-ref grid pos))
         (define res (or (is-a? c empty-cell%) (is-a? c door%)))
         (hash-set! free-cache pos res)
         res]))

(define (hash-clear! h)
  (void))

;; wall smoothing, for aesthetic reasons
(define (smooth-walls grid)
  (for* ([x (in-range (grid-height grid))]
         [y (in-range (grid-width  grid))])
    (smooth-single-wall grid (vector (assert x index?) (assert y index?))))
  (set! wall-cache (make-hash)) ; reset caches
  (set! free-cache (make-hash))
  grid)


(define (smooth-single-wall grid pos)
  (define (wall-or-door? pos)
    (cond [(hash-ref wall-cache pos #f) => (lambda (x) x)]
          [else
           (define c   (grid-ref grid pos))
           (define res (or (is-a? c wall%) (is-a? c door%)))
           (hash-set! wall-cache pos res)
           res]))
  (when (is-a? (grid-ref grid pos) wall%)
    (define u   (wall-or-door? (up    pos)))
    (define d   (wall-or-door? (down  pos)))
    (define l   (wall-or-door? (left  pos)))
    (define r   (wall-or-door? (right pos)))
    (define fu  (delay (counts-as-free? grid (up    pos))))
    (define fd  (delay (counts-as-free? grid (down  pos))))
    (define fl  (delay (counts-as-free? grid (left  pos))))
    (define fr  (delay (counts-as-free? grid (right pos))))
    (define ful (delay (counts-as-free? grid (up    (left  pos)))))
    (define fur (delay (counts-as-free? grid (up    (right pos)))))
    (define fdl (delay (counts-as-free? grid (down  (left  pos)))))
    (define fdr (delay (counts-as-free? grid (down  (right pos)))))
    (define (2-of-3? a b c) (or (and a b #t) (and a c #t) (and b c #t)))
    (array-set!
     grid pos
     (new
      (match* ( u d l r)
        [(#F #F #F #F) pillar%]
        [(#F #F #F #T) horizontal-wall%]
        [(#F #F #T #F) horizontal-wall%]
        [(#F #F #T #T) horizontal-wall%]
        [(#F #T #F #F) vertical-wall%]
        [( #F #T #F #T) north-west-wall%]
        [( #F #T #T #F) north-east-wall%]
        ;; only have tees if enough corners are "inside"
        [( #F #T #T #T) (cond [(2-of-3? (force fu) (force fdl) (force fdr))
                              north-tee-wall%]
                             [(force fu)  horizontal-wall%]
                             [(force fdl) north-east-wall%]
                             [(force fdr) north-west-wall%]
                             [else (raise-user-error 'cond)])]
        [(#T #F #F #F) vertical-wall%]
        [(#T #F #F #T) south-west-wall%]
        [(#T #F #T #F) south-east-wall%]
        [(#T #F #T #T) (cond [(2-of-3? (force fd) (force ful) (force fur))
                              south-tee-wall%]
                             [(force fd)  horizontal-wall%]
                             [(force ful) south-east-wall%]
                             [(force fur) south-west-wall%]
                             [else (raise-user-error 'cond)])]
        [(#T #T #F #F) vertical-wall%]
        [(#T #T #F #T) (cond [(2-of-3? (force fl) (force fur) (force fdr))
                              west-tee-wall%]
                             [(force fl)  vertical-wall%]
                             [(force fur) south-west-wall%]
                             [(force fdr) north-west-wall%]
                             [else (raise-user-error 'cond)])]
        [(#T #T #T #F) (cond [(2-of-3? (force fr) (force ful) (force fdl))
                              east-tee-wall%]
                             [(force fr)  vertical-wall%]
                             [(force ful) south-east-wall%]
                             [(force fdl) north-east-wall%]
                             [else (raise-user-error 'nocd)])]
        [(#T #T #T #T) (cond ; similar to the tee cases
                        [(or (and (force ful) (force fdr))
                             (and (force fur) (force fdl)))
                         ;; if diagonals are free, need a four-corner wall
                         four-corner-wall%]
                        [(and (force ful) (force fur)) south-tee-wall%]
                        [(and (force fdl) (force fdr)) north-tee-wall%]
                        [(and (force ful) (force fdl)) east-tee-wall%]
                        [(and (force fur) (force fdr)) west-tee-wall%]
                        [(force ful)                   south-east-wall%]
                        [(force fur)                   south-west-wall%]
                        [(force fdl)                   north-east-wall%]
                        [(force fdr)                   north-west-wall%]
                        [else (raise-user-error 'cond)])]
        [(_ _ _ _) (raise-user-error 'voidcase)])))))


(define (main)
  (show-grid (smooth-walls (generate-dungeon (range N)))))

(time (void (main)))
;; Change `void` to `display` to test. Should see:
;;............................................................
;;............................................................
;;............................................................
;;............................................................
;;............................................................
;;...................................╔═════╗......╔═══════╗...
;;...................................║     ║......║       ║...
;;...................................║     ║......║       ║...
;;......................╔═════╗......║     ║......║       ║...
;;......................║     ║......║     ╠══════╣       ║...
;;......................║     ╠══════╣     _      _       ║...
;;......................║     _      _     ╠══════╣       ║...
;;......................║     ╠══════╣     ║......║       ║...
;;......................║     ║......╚═════╝......║       ║...
;;......................╚═════╝...................╚═══════╝...
;;............................................................
;;............................................................
;;............................................................
;;cpu time: 8177 real time: 8175 gc time: 3379
