#lang racket
(require "../../read.rkt")
(provide SNAKE-COLLIDE SNAKE-CONST SNAKE-CUT-TAIL SNAKE-DATA SNAKE-HANDLERS
         SNAKE-MOTION-HELP SNAKE-MOTION-SMALL SNAKE-MOTION-SPLIT SNAKE-MOTION
         SNAKE-SCENES SNAKE-SLITHER)

(define (c/listof c)
  `(μ X (or/c empty? (cons/c ,c X))))
(define (c/nelistof c)
  `(cons/c ,c ,(c/listof c)))

(define c/dir `(one-of/c "up" "down" "left" "right"))
(define c/posn `(struct/c posn [real? real?]))
(define c/snake `(struct/c snake [,c/dir ,(c/nelistof c/posn)]))
(define c/world `(struct/c world [,c/snake ,c/posn]))

(define MODL-IMAGE
  `(module image
     (provide
      [image? (any . -> . bool?)]
      [circle (real? str? str? . -> . image?)]
      [empty-scene (real? real? . -> . image?)]
      [place-image (image? real? real? image? . -> . image?)])))

(define MODL-DATA
  `(module data
     (provide
      [struct posn ([x real?] [y real?])]
      [posn=? (,c/posn ,c/posn . -> . bool?)]
      [struct snake ([dir ,c/dir] [segs ,(c/nelistof c/posn)])]
      [struct world ([snake ,c/snake] [food ,c/posn])])
     
     (struct posn (x y))
     (define (posn=? p1 p2)
       (and (= (posn-x p1) (posn-x p2))
            (= (posn-y p1) (posn-y p2))))
     
     (struct snake (dir segs))
     (struct world (snake food))))

(define MODL-CONST
  `(module const
     (provide
      [WORLD (-> ,c/world)]
      [BACKGROUND (-> image?)]
      [FOOD-IMAGE (-> image?)]
      [SEGMENT-IMAGE (-> image?)]
      [GRID-SIZE real?]
      [BOARD-HEIGHT-PIXELS (-> real?)]
      [BOARD-WIDTH real?]
      [BOARD-HEIGHT real?])
     (require image data)
     
     (define GRID-SIZE 30)
     (define BOARD-HEIGHT 20)
     (define BOARD-WIDTH 30)
     (define (BOARD-HEIGHT-PIXELS) (* GRID-SIZE BOARD-HEIGHT))
     (define (BOARD-WIDTH-PIXELS) (* GRID-SIZE BOARD-WIDTH))
     (define (BACKGROUND) (empty-scene (BOARD-WIDTH-PIXELS) (BOARD-HEIGHT-PIXELS)))
     (define (SEGMENT-RADIUS) (/ GRID-SIZE 2))
     (define (SEGMENT-IMAGE)  (circle (SEGMENT-RADIUS) "solid" "red"))
     (define (FOOD-RADIUS) (SEGMENT-RADIUS))
     (define (FOOD-IMAGE)  (circle (FOOD-RADIUS) "solid" "green"))
     (define (WORLD) (world (snake "right" (cons (posn 5 3) empty))
                            (posn 8 12)))))

(define MODL-COLLIDE
  `(module collide
     (provide
      [snake-wall-collide? (,c/snake . -> . bool?)]
      [snake-self-collide? (,c/snake . -> . bool?)])
     (require data const)
     
     ;; snake-wall-collide? : Snake -> Boolean
     ;; Is the snake colliding with any of the walls?
     (define (snake-wall-collide? snk)
       (head-collide? (car (snake-segs snk))))
     
     ;; head-collide? : Posn -> Boolean
     (define (head-collide? p)
       (or (<= (posn-x p) 0)
           (>= (posn-x p) BOARD-WIDTH)
           (<= (posn-y p) 0)
           (>= (posn-y p) BOARD-HEIGHT)))
     
     ;; snake-self-collide? : Snake -> Boolean
     (define (snake-self-collide? snk)
       (segs-self-collide? (car (snake-segs snk))
                           (cdr (snake-segs snk))))
     
     ;; segs-self-collide? : Posn Segs -> Boolean
     (define (segs-self-collide? h segs)
       (cond [(empty? segs) #f]
             [else (or (posn=? (car segs) h)
                       (segs-self-collide? h (cdr segs)))]))))

(define MODL-CUT-TAIL
  `(module cut-tail
     (provide
      [cut-tail (,[c/nelistof c/posn] . -> . ,[c/listof c/posn])])
     (require data)
     ;; NeSegs is one of:
     ;; - (cons Posn empty)
     ;; - (cons Posn NeSegs)
     
     ;; cut-tail : NeSegs -> Segs
     ;; Cut off the tail.
     (define (cut-tail segs)
       (let ([r (cdr segs)])
         (cond [(empty? r) empty]
               [else (cons (car segs) (cut-tail r))])))))

(define MODL-CUT-TAIL• (opaque MODL-CUT-TAIL))

(define MODL-MOTION-HELP
  `(module motion-help
     (provide
      [snake-slither (,c/snake . -> . ,c/snake)]
      [snake-grow (,c/snake . -> . ,c/snake)])
     (require data cut-tail)
     
     ;; next-head : Posn Direction -> Posn
     ;; Compute next position for head.
     (define (next-head seg dir)
       (cond [(equal? "right" dir) (posn (add1 (posn-x seg)) (posn-y seg))]
             [(equal? "left" dir)  (posn (sub1 (posn-x seg)) (posn-y seg))]
             [(equal? "down" dir)  (posn (posn-x seg) (sub1 (posn-y seg)))]
             [else                 (posn (posn-x seg) (add1 (posn-y seg)))]))
     
     ;; snake-slither : Snake -> Snake
     ;; move the snake one step
     (define (snake-slither snk)
       (let ([d (snake-dir snk)])
         (snake d
                (cons (next-head (car (snake-segs snk))
                                 d)
                      (cut-tail (snake-segs snk))))))
     
     ;; snake-grow : Snake -> Snake
     ;; Grow the snake one segment.
     (define (snake-grow snk)
       (let ([d (snake-dir snk)])
         (snake d
                (cons (next-head (car (snake-segs snk))
                                 d)
                      (snake-segs snk)))))))

(define MODL-MOTION
  `(module motion
     (provide
      [world-change-dir (,c/world ,c/dir . -> . ,c/world)]
      [world->world (,c/world . -> . ,c/world)])
     (require data const motion-help)
     ;; world->world : World -> World
     (define (world->world w)
       (cond [(eating? w) (snake-eat w)]
             [else
              (world (snake-slither (world-snake w))
                     (world-food w))]))
     ;; eating? : World -> Boolean
     ;; Is the snake eating the food in the world.
     (define (eating? w)
       (posn=? (world-food w)
               (car (snake-segs (world-snake w)))))
     ;; snake-change-direction : Snake Direction -> Snake
     ;; Change the direction of the snake.
     (define (snake-change-direction snk dir)
       (snake dir
              (snake-segs snk)))
     ;; world-change-dir : World Direction -> World
     ;; Change direction of the world.
     (define (world-change-dir w dir)
       (world (snake-change-direction (world-snake w) dir)
              (world-food w)))
     ;; snake-eat : World -> World
     ;; Eat the food and generate a new one.
     (define (snake-eat w)
       (world (snake-grow (world-snake w))
              #;(posn (random BOARD-WIDTH) (random BOARD-HEIGHT))
              (posn (- BOARD-WIDTH 1) (- BOARD-HEIGHT 1))))))

(define SNAKE-COLLIDE
  ; https://github.com/samth/var/blob/master/examples/snake-modules/collide.rkt
  `(,MODL-IMAGE
    ,MODL-DATA
    ,MODL-CONST
    ,MODL-COLLIDE
    (module H
      (provide
       [D ((,c/snake . -> . bool?) . -> . any)])
      (require data)
      (define D •))
    (require collide H)
    (begin [D snake-wall-collide?]
           [D snake-self-collide?])))

(define SNAKE-CONST
  ; https://github.com/samth/var/blob/master/examples/snake-modules/const.rkt
  `(,MODL-IMAGE
    ,MODL-DATA
    ,MODL-CONST
    (module hole
      (provide [f (any . -> . any)]))
    (require const hole)
    (begin [f WORLD]
           [f BACKGROUND]
           [f FOOD-IMAGE]
           [f SEGMENT-IMAGE]
           [f GRID-SIZE]
           [f BOARD-HEIGHT-PIXELS]
           [f BOARD-WIDTH]
           [f BOARD-HEIGHT])))

(define SNAKE-CUT-TAIL
  ; https://github.com/samth/var/blob/master/examples/snake-modules/cut-tail.rkt
  `(,MODL-DATA
    ,MODL-CUT-TAIL
    (module H
      (provide
       [f ((,(c/nelistof c/posn) . -> . ,(c/listof c/posn)) . -> . any)])
      (require data))
    (require cut-tail H)
    (f cut-tail)))

(define SNAKE-DATA
  ; https://github.com/samth/var/blob/master/examples/snake-modules/data.rkt
  `(,MODL-DATA
    (module D
      (provide
       [f-posn ((real? real? . -> . ,c/posn) . -> . any)]
       [f-posn? ((any . -> . bool?) . -> . any)]
       [f-posn-x ((,c/posn . -> . real?) . -> . any)]
       [f-posn-y ((,c/posn . -> . real?) . -> . any)]
       [f-posn=? ((,c/posn ,c/posn . -> . bool?) . -> . any)]
       [f-snake ((,c/dir (cons/c ,c/posn ,(c/listof c/posn)) . -> . ,c/snake) . -> . any)]
       [f-snake? ((any . -> . bool?) . -> . any)]
       [f-snake-dir ((,c/snake . -> . ,c/dir) . -> . any)]
       [f-snake-segs ((,c/snake . -> . ,(c/nelistof c/posn)) . -> . any)]
       [f-world ((,c/snake ,c/posn . -> . ,c/world) . -> . any)]
       [f-world? ((any . -> . bool?) . -> . any)]
       [f-world-snake ((,c/world . -> . ,c/snake) . -> . any)]
       [f-world-food ((,c/world . -> . ,c/posn) . -> . any)])
      (require data))
    (require D data)
    (begin [f-posn posn]
           [f-posn? posn?]
           [f-posn-x posn-x]
           [f-posn-y posn-y]
           [f-posn=? posn=?]
           [f-snake snake]
           [f-snake? snake?]
           [f-snake-dir snake-dir]
           [f-snake-segs snake-segs]
           [f-world world]
           [f-world? world?]
           [f-world-snake world-snake]
           [f-world-food world-food])))

(define SNAKE-HANDLERS
  ; https://github.com/samth/var/blob/master/examples/snake-modules/handlers.rkt
  `(,MODL-IMAGE
    ,MODL-DATA
    
    (module collide
      (provide
       [snake-wall-collide? (,c/snake . -> . bool?)]
       [snake-self-collide? (,c/snake . -> . bool?)])
      (require data))
    
    (module motion
      (provide
       [world-change-dir (,c/world ,c/dir . -> . ,c/world)]
       [world->world (,c/world . -> . ,c/world)])
      (require data))
    
    (module handlers
      ;; Movie handlers
      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
      (provide
       [handle-key (,c/world str? . -> . ,c/world)]
       [game-over? (,c/world . -> . bool?)])
      (require data motion collide)
      
      ;; handle-key : World String -> World
      (define (handle-key w ke)
        (cond [(equal? ke "w") (world-change-dir w "up")]
              [(equal? ke "s") (world-change-dir w "down")]
              [(equal? ke "a") (world-change-dir w "left")]
              [(equal? ke "d") (world-change-dir w "right")]
              [else w]))
      
      ;; game-over? : World -> Boolean
      (define (game-over? w)
        (or (snake-wall-collide? (world-snake w))
            (snake-self-collide? (world-snake w)))))
    
    (module H
      (provide
       [D1 ((,c/world . -> . bool?) . -> . any)]
       [D2 ((,c/world str? . -> . ,c/world) . -> . any)])
      (require data))
    
    (require handlers H)
    (begin [D1 game-over?]
           [D2 handle-key])))

(define SNAKE-MOTION-HELP
  ; https://github.com/samth/var/blob/master/examples/snake-modules/motion-help.rkt
  `(,MODL-IMAGE
    ,MODL-DATA
    ,MODL-CUT-TAIL•
    ,MODL-MOTION-HELP
    
    (module H
      (provide
       [f ((,c/snake . -> . ,c/snake) . -> . any)])
      (require data))
    (require motion-help H)
    (begin [f snake-slither]
           [f snake-grow])))

(define SNAKE-MOTION-SMALL
  ; https://github.com/samth/var/blob/master/examples/snake-modules/motion-small.rkt
  `(,MODL-IMAGE
    ,MODL-DATA
    ,MODL-CONST
    ,MODL-CUT-TAIL•
    (module motion-help
      (provide
       [snake-slither (,c/snake . -> . ,c/snake)]
       [snake-grow (,c/snake . -> . ,c/snake)])
      (require data cut-tail))
    ,MODL-MOTION
    (module H
      (provide
       [f1 ((,c/world . -> . ,c/world) . -> . any)]
       [f2 ((,c/world ,c/dir . -> . ,c/world) . -> . any)])
      (require data))
    (require motion H)
    (begin [f1 world->world]
           [f2 world-change-dir])))

(define SNAKE-MOTION-SPLIT
  ; https://github.com/samth/var/blob/master/examples/snake-modules/motion-split.rkt
  `(,MODL-IMAGE
    ,MODL-DATA
    ,MODL-CONST
    ,MODL-CUT-TAIL•
    ,MODL-MOTION-HELP
    ,MODL-MOTION
    (module H
      (provide
       [f1 ((,c/world ,c/dir . -> . ,c/world) . -> . any)]
       [f2 ((,c/world . -> . ,c/world) . -> . any)]
       [f3 ((,c/snake . -> . ,c/snake) . -> . any)]
       [d ,c/dir]
       [p ,c/posn]
       [lop ,(c/nelistof c/posn)]
       [w ,c/world]
       [s ,c/snake])
      (require data))
    (require motion H slither grow) ; ??
    (begin [world-change-dir w d])))

(define SNAKE-MOTION
  ; https://github.com/samth/var/blob/master/examples/snake-modules/motion.rkt
  `(,MODL-IMAGE
    ,MODL-DATA
    ,MODL-CONST
    ,MODL-CUT-TAIL•
    ,MODL-MOTION-HELP
    ,MODL-MOTION
    (module hole
      (provide
       [f1 ((,c/world ,c/dir . -> . ,c/world) . -> . any)]
       [f2 ((,c/world . -> . ,c/world) . -> . any)]
       [f3 ((,c/snake . -> . ,c/snake) . -> . any)])
      (require data))
    (require motion hole slither)
    (begin [f1 world-change-dir]
           [f2 world->world])))

(define SNAKE-SCENES
  ; https://github.com/samth/var/blob/master/examples/snake-modules/scenes.rkt
  `(,MODL-IMAGE
    ,MODL-DATA
    ,MODL-CONST
    (module scenes
      
      (provide
       [world->scene (,c/world . -> . image?)]
       [food+scene (,c/posn image? . -> . image?)]
       [place-image-on-grid
        (image? real? real? image? . -> . image?)]
       [snake+scene (,c/snake image? . -> . image?)]
       [segments+scene (,(c/listof c/posn) image? . -> . image?)]
       [segment+scene (,c/posn image? . -> . image?)])
      (require data const image)
      
      ;; world->scene : World -> Image
      ;; Build an image of the given world.
      (define (world->scene w)
        (snake+scene (world-snake w)
                     (food+scene (world-food w) (BACKGROUND))))
      
      ;; food+scene : Food Image -> Image
      ;; Add image of food to the given scene.
      (define (food+scene f scn)
        (place-image-on-grid (FOOD-IMAGE) (posn-x f) (posn-y f) scn))
      
      ;; place-image-on-grid : Image Number Number Image -> Image
      ;; Just like PLACE-IMAGE, but use grid coordinates.
      (define (place-image-on-grid img x y scn)
        (place-image img
                     (* GRID-SIZE x)
                     (- (BOARD-HEIGHT-PIXELS) (* GRID-SIZE y))
                     scn))
      
      ;; snake+scene : Snake Image -> Image
      ;; Add an image of the snake to the scene.
      (define (snake+scene snk scn)
        (segments+scene (snake-segs snk) scn))
      
      ;; segments+scene : Segs Image -> Image
      ;; Add an image of the snake segments to the scene.
      (define (segments+scene segs scn)
        (cond [(empty? segs) scn]
              [else (segments+scene (cdr segs) ;; tail recursion
                                    (segment+scene (car segs) scn))]))
      
      ;; segment+scene : Posn Image -> Image
      ;; Add one snake segment to a scene.
      (define (segment+scene seg scn)
        (place-image-on-grid (SEGMENT-IMAGE) (posn-x seg) (posn-y seg) scn)))
    
    (module hole
      (provide
       [f ((,c/world . -> . image?) . -> . any)])
      (require data image))
    (require scenes hole)
    (f world->scene)))

(define SNAKE-SLITHER
  ; https://github.com/samth/var/blob/master/examples/snake-modules/slither.rkt
  `(,MODL-DATA
    ,MODL-CUT-TAIL
    ,MODL-MOTION-HELP
    (module S
      (provide
       [S ,c/snake]
       [L ,(c/nelistof c/posn)]
       [L2 ,(c/listof c/posn)])
      (require data))
    (require S motion-help)
    (begin [snake-slither S]
           #;[reverse L2 L2]
           #;[cut-tail/acc L L2])))

(define SNAKE-ALL
  `(,MODL-IMAGE
    ,MODL-DATA
    ,MODL-CONST
    ,MODL-COLLIDE
    ,MODL-CUT-TAIL
    ,MODL-MOTION-HELP
    ,MODL-MOTION
    (module handlers
      ;; Movie handlers
      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
      (provide
       [handle-key (,c/world str? . -> . ,c/world)]
       [game-over? (,c/world . -> . bool?)])
      (require data motion collide)
      
      ;; handle-key : World String -> World
      (define (handle-key w ke)
        (cond [(equal? ke "w") (world-change-dir w "up")]
              [(equal? ke "s") (world-change-dir w "down")]
              [(equal? ke "a") (world-change-dir w "left")]
              [(equal? ke "d") (world-change-dir w "right")]
              [else w]))
      
      ;; game-over? : World -> Boolean
      (define (game-over? w)
        (or (snake-wall-collide? (world-snake w))
            (snake-self-collide? (world-snake w)))))
    (module scenes
      
      (provide
       [world->scene (,c/world . -> . image?)]
       [food+scene (,c/posn image? . -> . image?)]
       [place-image-on-grid
        (image? real? real? image? . -> . image?)]
       [snake+scene (,c/snake image? . -> . image?)]
       [segments+scene (,(c/listof c/posn) image? . -> . image?)]
       [segment+scene (,c/posn image? . -> . image?)])
      (require data const image)
      
      ;; world->scene : World -> Image
      ;; Build an image of the given world.
      (define (world->scene w)
        (snake+scene (world-snake w)
                     (food+scene (world-food w) (BACKGROUND))))
      
      ;; food+scene : Food Image -> Image
      ;; Add image of food to the given scene.
      (define (food+scene f scn)
        (place-image-on-grid (FOOD-IMAGE) (posn-x f) (posn-y f) scn))
      
      ;; place-image-on-grid : Image Number Number Image -> Image
      ;; Just like PLACE-IMAGE, but use grid coordinates.
      (define (place-image-on-grid img x y scn)
        (place-image img
                     (* GRID-SIZE x)
                     (- (BOARD-HEIGHT-PIXELS) (* GRID-SIZE y))
                     scn))
      
      ;; snake+scene : Snake Image -> Image
      ;; Add an image of the snake to the scene.
      (define (snake+scene snk scn)
        (segments+scene (snake-segs snk) scn))
      
      ;; segments+scene : Segs Image -> Image
      ;; Add an image of the snake segments to the scene.
      (define (segments+scene segs scn)
        (cond [(empty? segs) scn]
              [else (segments+scene (cdr segs) ;; tail recursion
                                    (segment+scene (car segs) scn))]))
      
      ;; segment+scene : Posn Image -> Image
      ;; Add one snake segment to a scene.
      (define (segment+scene seg scn)
        (place-image-on-grid (SEGMENT-IMAGE) (posn-x seg) (posn-y seg) scn)))
    (require image data const collide cut-tail motion-help motion handlers scenes)
    (amb
     (• snake-wall-collide?)
     (• snake-self-collide?)
     (• WORLD)
     (• BACKGROUND)
     (• FOOD-IMAGE)
     (• SEGMENT-IMAGE)
     (• GRID-SIZE)
     (• BOARD-HEIGHT-PIXELS)
     (• BOARD-WIDTH)
     (• BOARD-HEIGHT)
     (• cut-tail)
     (• posn)
     (• posn?)
     (• posn-x)
     (• posn-y)
     (• posn=?)
     (• snake)
     (• snake?)
     (• snake-dir)
     (• snake-segs)
     (• world)
     (• world?)
     (• world-snake)
     (• world-food)
     (• game-over?)
     (• handle-key)
     (• snake-slither)
     (• snake-grow)
     (• world->world)
     (• world-change-dir)
     (• world->scene)
     (• snake-slither))))