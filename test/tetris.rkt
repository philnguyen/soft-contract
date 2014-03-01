#lang racket
(require "../../read.rkt")
(provide TETRIS-BLOCK TETRIS-BSET TETRIS-DATA TETRIS-ELIM-ROW
         TETRIS-ELIM TETRIS-TETRAS TETRIS-VISUAL TETRIS-WORLD)

(define (c/listof c)
  `(μ X (or/c false? (cons/c ,c X))))
(define (c/nelistof c)
  `(cons/c ,c ,(c/listof c)))

(define c/color 'symbol?)
(define c/posn `(struct/c posn (real? real?)))
(define c/block `(struct/c block (real? real? ,c/color)))
(define c/bset (c/listof c/block))
(define c/tetra `(struct/c tetra (,c/posn ,c/bset)))
(define c/world `(struct/c world (,c/tetra ,c/bset)))

(define MODL-DATA
  `(module data
     (provide
      [struct block ([x real?] [y real?] [color ,c/color])]
      [struct posn ([x real?] [y real?])]
      [struct tetra ([center ,c/posn] [blocks ,c/bset])]
      [struct world ([tetra ,c/tetra] [blocks ,c/bset])]
      [posn=? (,c/posn ,c/posn . -> . bool?)])
     
     (struct posn (x y))
     (struct block (x y color))
     (struct tetra (center blocks))
     (struct world (tetra blocks))
     
     (define (posn=? p1 p2)
       (and (= (posn-x p1) (posn-x p2))
            (= (posn-y p1) (posn-y p2))))))

(define MODL-CONSTS
  `(module consts
     (provide
      [block-size int?]
      [board-width int?]
      [board-height int?])
     (define block-size 20)
     #'(define board-height 20)
     (define board-width 10)))

(define MODL-BLOCK
  `(module block
     (provide
      [block-rotate-ccw (,c/posn ,c/block . -> . ,c/block)]
      [block-rotate-cw (,c/posn ,c/block . -> . ,c/block)]
      [block=? (,c/block ,c/block . -> . bool?)]
      [block-move (real? real? ,c/block . -> . ,c/block)])
     (require data)
     
     ;; block=? : Block Block -> Boolean
     ;; Determines if two blocks are the same (ignoring color).
     (define (block=? b1 b2)
       (and (= (block-x b1) (block-x b2))
            (= (block-y b1) (block-y b2))))
     
     ;; block-move : Number Number Block -> Block
     (define (block-move dx dy b)
       (block (+ dx (block-x b))
              (+ dy (block-y b))
              (block-color b)))
     
     ;; block-rotate-ccw : Posn Block -> Block
     ;; Rotate the block 90 counterclockwise around the posn.
     (define (block-rotate-ccw c b)
       (block (+ (posn-x c) (- (posn-y c) (block-y b)))
              (+ (posn-y c) (- (block-x b) (posn-x c)))
              (block-color b)))
     
     ;; block-rotate-cw : Posn Block -> Block
     ;; Rotate the block 90 clockwise around the posn.
     (define (block-rotate-cw c b)
       (block-rotate-ccw c (block-rotate-ccw c (block-rotate-ccw c b))))))

(define MODL-BLOCK• (opaque MODL-BLOCK))

(define MODL-LIST-FUN
  `(module list-fun
     (provide
      [max (real? real? . -> . real?)]
      [min (real? real? . -> . real?)]
      [ormap ([,c/block . -> . bool?] ,[c/listof 'any] . -> . bool?)]
      [andmap ([,c/block . -> . bool?] ,[c/listof 'any] . -> . bool?)]
      [map ([,c/block . -> . ,c/block] ,c/bset . -> . ,c/bset)]
      [filter ([,c/block . -> . bool?] ,c/bset . -> . ,c/bset)]
      [append (,c/bset ,c/bset . -> . ,c/bset)]
      [length (,(c/listof 'any) . -> . int?)]
      [foldr ([,c/block ,c/bset . -> . ,c/bset] ,c/bset ,c/bset . -> . ,c/bset)]
      [foldr-i ([,c/block image? . -> . image?] image? ,c/bset . -> . image?)]
      [foldr-n ((,c/block real? . -> . real?) real? ,c/bset . -> . real?)])
     (require image data)))

(define MODL-BSET
  `(module bset
     (provide
      [blocks-contains? (,c/bset ,c/block . -> . bool?)]
      [blocks=? (,c/bset ,c/bset . -> . bool?)]
      [blocks-subset? (,c/bset ,c/bset . -> . bool?)]
      [blocks-intersect (,c/bset ,c/bset . -> . ,c/bset)]
      [blocks-count (,c/bset . -> . real?)]
      [blocks-overflow? (,c/bset . -> . bool?)]
      [blocks-move (real? real? ,c/bset . -> . ,c/bset)]
      [blocks-rotate-cw (,c/posn ,c/bset . -> . ,c/bset)]
      [blocks-rotate-ccw (,c/posn ,c/bset . -> . ,c/bset)]
      [blocks-change-color (,c/bset ,c/color . -> . ,c/bset)]
      [blocks-row (,c/bset real? . -> . ,c/bset)]
      [full-row? (,c/bset real? . -> . bool?)]
      [blocks-union (,c/bset ,c/bset . -> . ,c/bset)]
      [blocks-max-x (,c/bset . -> . real?)]
      [blocks-min-x (,c/bset . -> . real?)]
      [blocks-max-y (,c/bset . -> . real?)])
     (require data block list-fun consts)
     
     ;; blocks-contains? : BSet Block -> Boolean
     ;; Determine if the block is in the set of blocks.
     (define (blocks-contains? bs b)
       (ormap (λ (c) (block=? b c)) bs))
     
     ;; blocks-subset? : BSet BSet -> Boolean
     ;; is every element in bs1 also in bs2?
     (define (blocks-subset? bs1 bs2)
       (andmap (λ (b) (blocks-contains? bs2 b)) bs1))
     
     ;; blocks=? : BSet BSet -> Boolean
     ;; Determine if given sets of blocks are equal.
     (define (blocks=? bs1 bs2)
       (and (blocks-subset? bs1 bs2)
            (blocks-subset? bs2 bs1)))
     
     ;; blocks-intersect : BSet BSet -> BSet
     ;; Return the set of blocks that appear in both sets.
     (define (blocks-intersect bs1 bs2)
       (filter (λ (b) (blocks-contains? bs2 b)) bs1))
     
     ;; blocks-count : BSet -> Nat
     ;; Return the number of blocks in the set.
     (define (blocks-count bs)
       (length bs))  ;; No duplicates, cardinality = length.
     
     ;; blocks-move : Number Number BSet -> BSet
     ;; Move each block by the given X & Y displacement.
     (define (blocks-move dx dy bs)
       (map (λ (b) (block-move dx dy b)) bs))
     
     ;; blocks-rotate-ccw : Posn BSet -> BSet
     ;; Rotate the blocks 90 counterclockwise around the posn.
     (define (blocks-rotate-ccw c bs)
       (map (λ (b) (block-rotate-ccw c b)) bs))
     
     ;; blocks-rotate-cw : Posn BSet -> BSet
     ;; Rotate the blocks 90 clockwise around the posn.
     (define (blocks-rotate-cw c bs)
       (map (λ (b) (block-rotate-cw c b)) bs))
     
     ;; blocks-change-color : BSet Color -> BSet
     (define (blocks-change-color bs c)
       (map (λ (b) (block (block-x b) (block-y b) c))
            bs))
     
     ;; blocks-row : BSet Number -> BSet
     ;; Return the set of blocks in the given row.
     (define (blocks-row bs i)
       (filter (λ (b) (= i (block-y b))) bs))
     
     ;; full-row? : BSet Nat -> Boolean
     ;; Are there a full row of blocks at the given row in the set.
     (define (full-row? bs i)
       (= board-width (blocks-count (blocks-row bs i))))
     
     ;; blocks-overflow? : BSet -> Boolean
     ;; Have any of the blocks reach over the top of the board?
     (define (blocks-overflow? bs)
       (ormap (λ (b) (<= (block-y b) 0)) bs))
     
     ;; blocks-union : BSet BSet -> BSet
     ;; Union the two sets of blocks.
     (define (blocks-union bs1 bs2)
       (foldr (λ (b bs)
                (cond [(blocks-contains? bs b) bs]
                      [else (cons b bs)]))
              bs2
              bs1))
     
     ;; blocks-max-y : BSet -> Number
     ;; Compute the maximum y coordinate;
     ;; if set is empty, return 0, the coord of the board's top edge.
     (define (blocks-max-y bs)
       (foldr-n (λ (b n) (max (block-y b) n)) 0 bs))
     
     ;; blocks-min-x : BSet -> Number
     ;; Compute the minimum x coordinate;
     ;; if set is empty, return the coord of the board's right edge.
     (define (blocks-min-x bs)
       (foldr-n (λ (b n) (min (block-x b) n)) board-width bs))
     
     ;; blocks-max-x : BSet -> Number
     ;; Compute the maximum x coordinate;
     ;; if set is empty, return 0, the coord of the board's left edge.
     (define (blocks-max-x bs)
       (foldr-n (λ (b n) (max (block-x b) n)) 0 bs))))

(define MODL-ELIM
  `(module elim
     (provide
      [eliminate-full-rows (,c/bset . -> . ,c/bset)])
     (require data bset consts elim-row)
     ;; eliminate-full-rows : BSet -> BSet
     ;; Eliminate all full rows and shift down appropriately.
     (define (eliminate-full-rows bs)
       (elim-row bs board-height 0))))

(define MODL-ELIM-ROW
  `(module elim-row
     (provide
      [elim-row (,c/bset int? int? . -> . ,c/bset)])
     (require data bset consts)
     (define (elim-row bs i offset)
       (cond
         [(< i 0) bs]
         [(full-row? bs i) (elim-row bs (sub1 i) (add1 offset))]
         [else (elim-row (blocks-union bs
                                       (blocks-move 0 offset (blocks-row bs i)))
                         (sub1 i)
                         offset)]))))

(define MODL-TETRAS
  `(module tetras
     (provide ;[tetras (listof ,c/tetra)]
      [tetra-move (int? int? ,c/tetra . -> . ,c/tetra)]
      [tetra-rotate-ccw (,c/tetra . -> . ,c/tetra)]
      [tetra-rotate-cw (,c/tetra . -> . ,c/tetra)]
      [tetra-overlaps-blocks? (,c/tetra ,c/bset . -> . bool?)]
      [build-tetra-blocks (,c/color int? int? int? int? int? int? int? int? int? int?
                                    . -> .  ,c/tetra)]
      [tetra-change-color (,c/tetra ,c/color . -> . ,c/tetra)])
     (require bset data consts block)
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;; Tetras
     
     ;; tetra-move : Number Number Tetra -> Tetra
     ;; Move the Tetra by the given X & Y displacement.
     (define (tetra-move dx dy t)
       (tetra (posn (+ dx (posn-x (tetra-center t)))
                    (+ dy (posn-y (tetra-center t))))
              (blocks-move dx dy (tetra-blocks t))))
     
     ;; tetra-rotate-ccw : Tetra -> Tetra
     ;; Rotate the tetra 90 degrees counterclockwise around its center.
     (define (tetra-rotate-ccw t)
       (tetra (tetra-center t)
              (blocks-rotate-ccw (tetra-center t)
                                 (tetra-blocks t))))
     
     ;; tetra-rotate-cw : Tetra -> Tetra
     ;; Rotate the tetra 90 degrees clockwise around its center.
     (define (tetra-rotate-cw t)
       (tetra (tetra-center t)
              (blocks-rotate-cw (tetra-center t)
                                (tetra-blocks t))))
     
     ;; tetra-overlaps-blocks? : Tetra BSet -> Boolean
     ;; Is the tetra on any of the blocks?
     (define (tetra-overlaps-blocks? t bs)
       (false? (false? (blocks-intersect (tetra-blocks t) bs))))
     
     ;; tetra-change-color : Tetra Color -> Tetra
     ;; Change the color of the given tetra.
     (define (tetra-change-color t c)
       (tetra (tetra-center t)
              (blocks-change-color (tetra-blocks t) c)))
     
     (define (build-tetra-blocks color xc yc x1 y1 x2 y2 x3 y3 x4 y4)
       (tetra-move 3 0 
                   (tetra (posn xc yc)
                          (cons (block x1 y1 color)
                                (cons (block x2 y2 color)
                                      (cons (block x3 y3 color)
                                            (cons (block x4 y4 color) #f)))))))
     
     ;; Bogus centers
     #;(define tetras
         (list 
          (build-tetra-blocks 'green  	1/2 -3/2    0 -1 0 -2 1 -1 1 -2)
          (build-tetra-blocks 'blue   	1   -1      0 -1 1 -1 2 -1 3 -1)
          (build-tetra-blocks 'purple 	1   -1      0 -1 1 -1 2 -1 2 -2)
          (build-tetra-blocks 'cyan   	1   -1      0 -1 1 -1 2 -1 0 -2)
          (build-tetra-blocks 'orange  1   -1      0 -1 1 -1 2 -1 1 -2)
          (build-tetra-blocks 'red     1   -1      0 -1 1 -1 1 -2 2 -2)
          (build-tetra-blocks 'pink    1   -1      0 -2 1 -2 1 -1 2 -1)))))

(define MODL-WORLD
  `(module world
     (provide [world-key-move (,c/world str? . -> . ,c/world)]
              [next-world (,c/world . -> . ,c/world)]
              [ghost-blocks (,c/world . -> . ,c/bset)])
     (require data bset block tetras aux elim consts)
     
     ;; touchdown : World -> World
     ;; Add the current tetra's blocks onto the world's block list,
     ;; and create a new tetra.
     (define (touchdown w)
       (world (list-pick-random tetras)
              (eliminate-full-rows (blocks-union (tetra-blocks (world-tetra w))
                                                 (world-blocks w)))))
     
     ;; world-jump-down : World -> World
     ;; Take the current tetra and move it down until it lands.
     (define (world-jump-down w)
       (cond [(landed? w) w]
             [else (world-jump-down (world (tetra-move 0 1 (world-tetra w))
                                           (world-blocks w)))]))
     
     ;; landed-on-blocks? : World -> Boolean
     ;; Has the current tetra landed on blocks?
     ;; I.e., if we move the tetra down 1, will it touch any existing blocks?
     (define (landed-on-blocks? w)
       (tetra-overlaps-blocks? (tetra-move 0 1 (world-tetra w))
                               (world-blocks w)))
     
     ;; landed-on-floor? : World -> Boolean
     ;; Has the current tetra landed on the floor?
     (define (landed-on-floor? w)
       (= (blocks-max-y (tetra-blocks (world-tetra w)))
          (sub1 board-height)))
     
     ;; landed? : World -> Boolean
     ;; Has the current tetra landed?
     (define (landed? w)
       (or (landed-on-blocks? w)
           (landed-on-floor? w)))
     
     ;; next-world : World -> World
     ;; Step the world, either touchdown or move the tetra down on step.
     (define (next-world w)
       (cond [(landed? w) (touchdown w)]
             [else (world (tetra-move 0 1 (world-tetra w))
                          (world-blocks w))]))
     
     ;; try-new-tetra : World Tetra -> World
     ;; Make a world with the new tetra *IF* if doesn't lie on top of some other
     ;; block or lie off the board. Otherwise, no change.
     (define (try-new-tetra w new-tetra)
       (cond [(or (<  (blocks-min-x (tetra-blocks new-tetra)) 0)
                  (>= (blocks-max-x (tetra-blocks new-tetra)) board-width)
                  (tetra-overlaps-blocks? new-tetra (world-blocks w)))
              w]
             [else (world new-tetra (world-blocks w))]))
     
     ;; world-move : Number Number World -> World
     ;; Move the Tetra by the given X & Y displacement, but only if you can.
     ;; Otherwise stay put.
     (define (world-move dx dy w)
       (try-new-tetra w (tetra-move dx dy (world-tetra w))))
     
     ;; world-rotate-ccw : World -> World
     ;; Rotate the Tetra 90 degrees counterclockwise, but only if you can.
     ;; Otherwise stay put.
     (define (world-rotate-ccw w)
       (try-new-tetra w (tetra-rotate-ccw (world-tetra w))))
     
     ;; world-rotate-cw : World -> World
     ;; Rotate the Tetra 90 degrees clockwise, but only if you can.
     ;; Otherwise stay put.
     (define (world-rotate-cw w)
       (try-new-tetra w (tetra-rotate-cw (world-tetra w))))
     
     ;; ghost-blocks : World -> BSet
     ;; Gray blocks representing where the current tetra would land.
     (define (ghost-blocks w)
       (tetra-blocks (tetra-change-color (world-tetra (world-jump-down w))
                                         'gray)))
     
     ;; world-key-move : World KeyEvent -> World
     ;; Move the world according to the given key event.
     (define (world-key-move w k)
       (cond [(equal? k "left")
              (world-move neg-1 0 w)]
             [(equal? k "right")
              (world-move 1 0 w)]
             [(equal? k "down")
              (world-jump-down w)]
             [(equal? k "a")
              (world-rotate-ccw w)]
             [(equal? k "s")
              (world-rotate-cw w)]
             [else w]))))

(define MODL-IMAGE
  `(module image
     (provide
      [image? (any . -> . bool?)]
      [overlay (image? image? int? ,c/color ,c/color . -> . image?)]
      [circle (int? str? str? . -> . image?)]
      [rectangle (int? int? ,c/color ,c/color . -> . image?)]
      [place-image (image? int? int? image? . -> . image?)]
      [empty-scene (int? int? . -> . image?)])))

(define MODL-AUX•
  `(module aux
     (require data)
     (provide
      [list-pick-random (,(c/listof c/tetra) . -> . ,c/tetra)]
      [neg-1 int?] ;; ha!
      [tetras ,(c/listof c/tetra)])))

(define MODL-CONSTS• (opaque MODL-CONSTS))
(define MODL-BSET• (opaque MODL-BSET))
(define MODL-ELIM-ROW• (opaque MODL-ELIM-ROW))
(define MODL-WORLD• (opaque MODL-WORLD))

(define TETRIS-BLOCK
  ; https://github.com/samth/var/blob/master/examples/tetris-modules/block.rkt
  `(,MODL-DATA
    ,MODL-BLOCK
    (module H
      (provide
       [f-rotate ((,c/posn ,c/block . -> . ,c/block) . -> . any)]
       [f-move ((real? real? ,c/block . -> . ,c/block) . -> . any)]
       [f-= ((,c/block ,c/block . -> . bool?) . -> . any)])
      (require data))
    (require block H)
    (begin
      [f-rotate block-rotate-cw]
      [f-rotate block-rotate-ccw]
      [f-= block=?]
      [f-move block-move])))

(define TETRIS-BSET
  ; https://github.com/samth/var/blob/master/examples/tetris-modules/bset.rkt
  `(,MODL-DATA
    ,MODL-IMAGE
    ,MODL-BLOCK•
    ,MODL-LIST-FUN
    ,MODL-BSET
    ,MODL-CONSTS
    (module H
      (provide
       [f0 ((,c/bset ,c/block . -> . bool?) . -> . any)]
       [f1 ((,c/bset ,c/bset . -> . bool?) . -> . any)]
       [f2 ((,c/bset . -> . real?) . -> . any)]
       [f3 ((,c/bset ,c/bset . -> . ,c/bset) . -> . any)]
       [f4 ((,c/bset . -> . bool?) . -> . any)]
       [f-blocks-move ((real? real? ,c/bset . -> . ,c/bset) . -> . any)]
       [f-rotate ((,c/posn ,c/bset . -> . ,c/bset) . -> . any)]
       [f-blocks-change-color ((,c/bset ,c/color . -> . ,c/bset) . -> . any)]
       [f-blocks-row ((,c/bset real? . -> . ,c/bset) . -> . any)]
       [f-full-row? ((,c/bset real? . -> . bool?) . -> . any)]
       [f-blocks-union ((,c/bset ,c/bset . -> . ,c/bset) . -> . any)])
      (require data))
    (require H bset)
    (begin
      [f0 blocks-contains?]
      [f1 blocks-subset?]
      [f1 blocks=?]
      [f2 blocks-count]
      [f3 blocks-intersect]
      [f4 blocks-overflow?]
      [f-blocks-move blocks-move]
      [f-rotate blocks-rotate-ccw]
      [f-rotate blocks-rotate-cw]
      [f-blocks-change-color blocks-change-color]
      [f-full-row? full-row?]
      [f-blocks-row blocks-row]
      [f-blocks-union blocks-union]
      [f2 blocks-max-x]
      [f2 blocks-max-y]
      [f2 blocks-min-x])))

(define TETRIS-DATA
  ; https://github.com/samth/var/blob/master/examples/tetris-modules/data.rkt
  `(,MODL-DATA
    (module H
      (provide
       [f-block ((int? int? ,c/color . -> . ,c/block) . -> . any)]
       [f-block? ((any . -> . bool?) . -> . any)]
       [f-tetra? ((any . -> . bool?) . -> . any)]
       [f-world? ((any . -> . bool?) . -> . any)]
       [f-block-x ((,c/block . -> . int?) . -> . any)]
       [f-block-y ((,c/block . -> . int?) . -> . any)]
       [f-block-color ((,c/block . -> . ,c/color) . -> . any)]
       [f-tetra ((,c/posn ,c/bset . -> . ,c/tetra) . -> . any)]
       [f-tetra-center ((,c/tetra . -> . ,c/posn) . -> . any)]
       [f-tetra-blocks ((,c/tetra . -> . ,c/bset) . -> . any)]
       [f-world ((,c/tetra ,c/bset . -> . ,c/world) . -> . any)]
       [f-world-tetra ((,c/world . -> . ,c/tetra) . -> . any)]
       [f-world-blocks ((,c/world . -> . ,c/bset) . -> . any)])
      (require data))
    (require data H)
    (begin
      [f-world-blocks world-blocks]
      [f-world-tetra world-tetra]
      [f-world world]
      [f-world? world?]
      [f-tetra tetra]
      [f-tetra-center tetra-center]
      [f-tetra-blocks tetra-blocks]
      [f-tetra? tetra?]
      [f-block block]
      [f-block? block?]
      [f-block-color block-color]
      [f-block-x block-x]
      [f-block-y block-y])))

(define TETRIS-ELIM-ROW
  ; https://github.com/samth/var/blob/master/examples/tetris-modules/elim-row.rkt
  `(,MODL-DATA
    ,MODL-BLOCK
    ,MODL-CONSTS•
    ,MODL-BSET•
    ,MODL-ELIM-ROW
    ,MODL-LIST-FUN
    ,MODL-IMAGE
    (module H
      (provide
       [b ,c/bset]
       [n int?])
      (require data)
      (define b •)
      (define n •))
    (require elim-row H)
    (elim-row b n n)))

(define TETRIS-ELIM
  ; https://github.com/samth/var/blob/master/examples/tetris-modules/elim.rkt
  `(,MODL-DATA
    ,MODL-CONSTS•
    ,MODL-BSET•
    ,MODL-ELIM-ROW•
    ,MODL-BLOCK
    ,MODL-LIST-FUN
    ,MODL-IMAGE
    ,MODL-ELIM
    (module H
      (require data)
      (provide
       [b ,c/bset])
      (define b •))
    (require elim H)
    (eliminate-full-rows b)))

(define TETRIS-TETRAS
  ; https://github.com/samth/var/blob/master/examples/tetris-modules/tetras.rkt
  `(,MODL-DATA
    ,MODL-CONSTS•
    ,MODL-BSET•
    ,MODL-TETRAS
    ,MODL-BLOCK
    ,MODL-LIST-FUN
    ,MODL-IMAGE
    (module H
      (provide
       [n int?]
       [t ,c/tetra]
       [f-tetra-move ((int? int? ,c/tetra . -> . ,c/tetra) . -> . any)]
       [f-tetra-rotate-ccw ((,c/tetra . -> . ,c/tetra) . -> . any)]
       [f-tetra-rotate-cw ((,c/tetra . -> . ,c/tetra) . -> . any)]
       [f-tetra-overlaps-blocks? ((,c/tetra ,c/bset . -> . bool?) . -> . any)]
       [f-build-tetra-blocks
        ((,c/color int? int? int? int? int? int? int? int? int? int? . -> . ,c/tetra) . -> . any)]
       [f-tetra-change-color ((,c/tetra ,c/color . -> . ,c/tetra) . -> . any)])
      (require data))
    (require H tetras)
    (begin
      #;[f-tetra-move tetra-move]
      #;[f-tetra-change-color tetra-change-color]
      #;[f-tetra-rotate-cw tetra-rotate-cw]
      #;[f-tetra-rorate-ccw tetra-rotate-ccw]
      [f-tetra-overlaps-blocks? tetra-overlaps-blocks?]
      [f-build-tetra-blocks build-tetra-blocks])))

(define TETRIS-VISUAL
  ; https://github.com/samth/var/blob/master/examples/tetris-modules/visual.rkt
  `(,MODL-DATA
    ,MODL-CONSTS•
    ,MODL-LIST-FUN
    ,MODL-WORLD•
    ,MODL-IMAGE
    ,MODL-BLOCK
    ,MODL-BSET
    ,MODL-TETRAS
    ,MODL-ELIM
    ,MODL-ELIM-ROW•
    ,MODL-AUX•
    (module visual
      (provide
       [world->image (,c/world . -> . image?)]
       [blocks->image (,c/bset . -> . image?)]
       [block->image (,c/block . -> . image?)]
       [place-block (,c/block image? . -> . image?)])
      (require image data consts world list-fun aux)
      
      ;; Visualize whirled peas
      ;; World -> Scene
      (define (world->image w)
        (place-image (blocks->image (append (tetra-blocks (world-tetra w))
                                            (append (ghost-blocks w)
                                                    (world-blocks w))))
                     0 0 
                     (empty-scene (* board-width block-size)
                                  (* board-height block-size))))
      
      ;; BSet -> Scene
      (define (blocks->image bs)
        (foldr-i (λ (b img)
                   (cond [(<= 0 (block-y b)) (place-block b img)]
                         [else img]))
                 (empty-scene (add1 (* board-width block-size)) 
                              (add1 (* board-height block-size)))
                 bs))
      
      ;; Visualizes a block.
      ;; Block -> Image
      (define (block->image b)
        (overlay 
         (rectangle (add1 block-size) (add1 block-size) 'solid (block-color b))
         (rectangle (add1 block-size) (add1 block-size) 'outline 'black)))
      
      ;; Block Scene -> Scene
      (define (place-block b scene)
        (place-image (block->image b)
                     (+ (* (block-x b) block-size) (/ block-size 2))
                     (+ (* (block-y b) block-size) (/ block-size 2))
                     scene))
      
      (define (world0)
        (world (list-pick-random tetras) #f)))
    (module H
      (provide
       [f-world->image ((,c/world . -> . image?) . -> . any)]
       [bs ,c/bset]
       [b ,c/block]
       [w ,c/world])
      (require data image))
    (require H visual image)
    (f-world->image world->image)))

(define TETRIS-WORLD
  ; https://github.com/samth/var/blob/master/examples/tetris-modules/world.rkt
  `(,MODL-DATA
    ,MODL-CONSTS•
    ,MODL-BSET•
    ,(opaque MODL-TETRAS)
    ,MODL-AUX•
    ,(opaque MODL-ELIM)
    ,MODL-WORLD
    ,MODL-LIST-FUN
    ,MODL-BLOCK•
    ,MODL-ELIM-ROW•
    ,MODL-IMAGE
    (module H
      (require data)
      (provide
       [f-world-key-move ((,c/world str? . -> . ,c/world) . -> . any)]
       [f-next-world ((,c/world . -> . ,c/world) . -> . any)]))
    (require world H)
    (begin
      [f-world-key-move world-key-move]
      [f-next-world next-world])))

(define TETRIS-ALL
  `(,MODL-DATA
    ,MODL-CONSTS
    ,MODL-BLOCK
    ,MODL-LIST-FUN
    ,MODL-BSET
    ,MODL-ELIM
    ,MODL-ELIM-ROW
    ,MODL-TETRAS
    ,MODL-WORLD
    ,MODL-IMAGE
    ,MODL-AUX•
    (module visual
      (provide
       [world->image (,c/world . -> . image?)]
       [blocks->image (,c/bset . -> . image?)]
       [block->image (,c/block . -> . image?)]
       [place-block (,c/block image? . -> . image?)])
      (require image data consts world list-fun aux)
      
      ;; Visualize whirled peas
      ;; World -> Scene
      (define (world->image w)
        (place-image (blocks->image (append (tetra-blocks (world-tetra w))
                                            (append (ghost-blocks w)
                                                    (world-blocks w))))
                     0 0 
                     (empty-scene (* board-width block-size)
                                  (* board-height block-size))))
      
      ;; BSet -> Scene
      (define (blocks->image bs)
        (foldr-i (λ (b img)
                   (cond [(<= 0 (block-y b)) (place-block b img)]
                         [else img]))
                 (empty-scene (add1 (* board-width block-size)) 
                              (add1 (* board-height block-size)))
                 bs))
      
      ;; Visualizes a block.
      ;; Block -> Image
      (define (block->image b)
        (overlay 
         (rectangle (add1 block-size) (add1 block-size) 'solid (block-color b))
         (rectangle (add1 block-size) (add1 block-size) 'outline 'black)))
      
      ;; Block Scene -> Scene
      (define (place-block b scene)
        (place-image (block->image b)
                     (+ (* (block-x b) block-size) (/ block-size 2))
                     (+ (* (block-y b) block-size) (/ block-size 2))
                     scene))
      
      (define (world0)
        (world (list-pick-random tetras) #f)))
    (require block bset data elim-row elim tetras visual image world)
    (amb
     (• block-rotate-cw)
     (• block-rotate-ccw)
     (• block=?)
     (• block-move)
     (• blocks-contains?)
     (• blocks-subset?)
     (• blocks=?)
     (• blocks-count)
     (• blocks-intersect)
     (• blocks-overflow?)
     (• blocks-move)
     (• blocks-rotate-ccw)
     (• blocks-rotate-cw)
     (• blocks-change-color)
     (• full-row?)
     (• blocks-row)
     (• blocks-union)
     (• blocks-max-x)
     (• blocks-max-y)
     (• blocks-min-x)
     (• world-blocks)
     (• world-tetra)
     (• world)
     (• world?)
     (• tetra)
     (• tetra-center)
     (• tetra-blocks)
     (• tetra?)
     (• block)
     (• block?)
     (• block-color)
     (• block-x)
     (• block-y)
     (• elim-row)
     (• eliminate-full-rows)
     (• tetra-overlaps-blocks?)
     (• build-tetra-blocks)
     (• world->image)
     (• world-key-move)
     (• next-world))))