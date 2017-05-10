#lang racket

(provide
  tree-state
  lplaced%
  generate-tree
  tree-next
  hand-out?
)

(require
  "../base/untyped.rkt"
  "board.rkt"
  "state.rkt"
)
(require (only-in "basics.rkt"
  shares-available?
  shares-order?
))

;; -----------------------------------------------------------------------------

(struct hand-out (
  tile
  tree))

;; HandOut = (hand-out t st)
;; denotes that player received tile t and st is the Tree generated from the resulting state

(define (placed-tile p)
  (get-field tile p))

(define (placed-hotel p)
  (get-field hotel p))

(define atree% 
  (class object% ;(tree<%>)
    (init-field state)

    (super-new)

    (define/public (nothing-to-place?)
      #f)

    (define/public (to-state) 
      (get-field state this))

    ;(abstract next)
    (define/public (next t h d* h* pt)
      (error 'not-implemented))

    ;; template hook pattern: template
    (define/public (founding n order-policies)
      (unless (shares-order? order-policies)
        (error 'atree-founding "Precondition"))
      (traversal n order-policies (is-action FOUNDING)))

    ;; template hook pattern: template
    (define/public (merging n order-policies)
      (traversal n order-policies (is-action MERGING)))

    ;; hook
    ;; how many transitions in THIS tree (up to depth n) satisfy the given predicate 
    ;; Nat [Listof ShareOrder] [Placed -> Nat] -> Nat   
    (define/public (traversal n order-policies i)
      (error 'not-impolementd))

    ;; private field: ACTION -> Placed -> {0,1}
    ;; is the alternative a merging action?
    (define ((is-action tag) p)
      (if (and (placed-hotel p) (eq? (get-field reason p) tag)) 1 0))

    ;; use pick-tile to hand out a tile; extract the corresponding subtree 
    ;; [[Listof Tile] -> Tile] [Listof HandOut] ->* [Maybe Tile] Tree 
    (define/public (lookup-tile pick-tile lo-handout)
      (values #f this))
))

(define state% 
  (class atree% ;(tree<%>)
    (super-new)

    (define/override (next . _) 
      (error 'tree-next "finale state can't transition"))

    (define/override (traversal n policies p?) 0)

    (define/override (lookup-tile pick-tile lo-handout)
      (values #f this))))

(define lplaced%
  (class atree% ;(tree<%>)
    (super-new)
    (init-field
     lplaced)

    (define/override (nothing-to-place?)
      (null? lplaced))

    (define/override (next tile hotel decisions shares-to-buy pick-tile) 
      (define intermediate (send (lookup-purchase tile hotel) purchase decisions shares-to-buy))
      (unless (list? intermediate) (error "Expected a HandOut, got a State%"))
      (send this lookup-tile pick-tile intermediate))

    ;; Tile [Maybe Hotel] -> Placed 
    ;; lookup the one and only Placed from lo-placed that represents the action of placing t (& h)
    (define/private (lookup-purchase t h)
      (or 
       (for/or
               ((p  lplaced)
                #:when (and (equal? (placed-hotel p) h)
                            (equal? (placed-tile p) t)))
         p)
       (error 'noplace)))

    (define/override (lookup-tile pick-tile lo-hand-out)
      (define tile (pick-tile (map hand-out-tile lo-hand-out)))
      (define st (for/or
                         ((p  lo-hand-out)
                          #:when (equal? (hand-out-tile p) tile))
                   (hand-out-tree p)))
      (values tile (or st (error 'lookupfailed))))

    (define/override (traversal n policies p?)
      (if (= n 0)
          0
          (for/sum
                   ((branch  (in-list lplaced)))
            (define d* (map (lambda (p)
                              (list p '()))
                            (state-players (get-field state/tile branch))))
            (define a (send branch acceptable-policies policies))
            (+ (p? branch)
               ;; do not inspect every subtree because share buying does not affect actions
               (if (empty? a)
                   0
                   (* (length a) 
                      (for/sum
                               ((st  (send branch to-trees d* (first a))))
                        (send st traversal (- n 1) policies p?))))))))))

(define placed%
  (class object%
    (init-field state tile hotel state/tile reason)
    (super-new)

    ;; Decisions ShareOrder -> state% or [Listof HandOut]
    ;; given merger decisions and a purchase order, generate the next stage from THIS decision point
    (define/public (purchase decisions share-order)
      ;; ---------------------------------------------------------------------------------------------
      ;; contract checking 
      (when (eq? MERGING reason)
        (define players (state-players state/tile))
        (unless (= (length decisions) (length players))
          (printf "contract failure: received wrong number of decisions")
          ;; (pretty-print players)
          ;; (pretty-print (map first decisions))
          (error 'purchase "done")))
      ;; ---------------------------------------------------------------------------------------------
      (define state/decisions 
        (if (eq? MERGING reason)
            (state-return-shares state/tile decisions (state-board state))
            state/tile))
      (define state/bought (state-buy-shares state/decisions share-order))
      (define available-tiles (state-tiles state/bought))
      (if (empty? available-tiles) 
          (new state% [state state/bought])
          (for/list
                    ((tile  available-tiles))
            (hand-out tile (generate-tree (state-next-turn (state-move-tile state/bought tile)))))))

    ;; Decisions ShareOrder -> [Listof Tree]
    ;; given a purchase order, generate list of trees from THIS decision point's purchases 
    (define/public (to-trees decisions share-order)
      (define state-or-hand-out (purchase decisions share-order))
      (cond
        [(list? state-or-hand-out) (map hand-out-tree state-or-hand-out)]
        [else (list state-or-hand-out)]))

    ;; [Listof ShareOrder] -> [Listof ShareOrder]
    ;; filter out those share orders that are acceptable given THIS decision point's state 
    (define/public (acceptable-policies policies)
      (unless (andmap shares-order? policies)
        (error 'acceptable-policies "Precondigion"))
      (define state state/tile)
      (define budget (player-money (state-current-player state)))
      (define board  (state-board state))
      (define shares (state-shares state))
      (for/list ((p policies)
                 #:when (and (shares-available? shares p)
                             (affordable? board p budget)))
        p))))

(define (generate-tree state)
  (cond
    [(state-final? state)
     (new state% [state state])]
    [else (define board (state-board state))
          (define available-hotels (state-hotels state))
          (define lplaced
            (for/fold
                      ((lo-placed  '()))
                      ((t  (player-tiles (state-current-player state))))
              (define kind (what-kind-of-spot board t))
              (define hotels 
                (cond
                  [(eq? kind IMPOSSIBLE) '()]
                  [(and (eq? FOUNDING kind) (cons? available-hotels)) available-hotels]
                  [(eq? MERGING kind)
                   (define-values (acquirers _) (merging-which board t))
                   acquirers]
                  [else (list #f)]))
              (define new-placements
                (for/list
                          ((h  (in-list hotels)))
                  (define state/tile 
                    (if h (state-place-tile state t h) (state-place-tile state t)))
                  (new placed% [state state][tile t][hotel h][state/tile state/tile][reason kind])))
              (append new-placements lo-placed)))
          (new lplaced% (state state) (lplaced lplaced))]))

;; ASSUME: current player has enough money to buy the desired shares
(define (tree-next current-tree tile hotel decisions shares-to-buy pick-tile)
  (send current-tree next tile hotel decisions shares-to-buy pick-tile))

(define (tree-state t)
  (send t to-state))

