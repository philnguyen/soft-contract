#lang racket

(require soft-contract/fake-contract)

(module image racket
  (require 2htdp/image)
  (define image/c (λ (x) (image? x)))
  (provide/contract
   [image/c any/c]
   [circle (real? string? string? . -> . image/c)]
   [empty-scene (real? real? . -> . image/c)]
   [place-image (image/c real? real? image/c . -> . image/c)])
  
  #;(define (image? x) •))

(module unsafe-image racket
  (require 2htdp/image)
  (define image/c (λ (x) (image? x)))
  (provide
   circle 
   empty-scene
   place-image)
  
  #;(define (image? x) •))

(module data racket
  (struct snake (dir segs))
  (struct world (snake food))
  (struct posn (x y))
  
  (define (nelistof c) (cons/c c (listof c)))
  (define DIR/C (or/c "up" "down" "left" "right"))
  (define POSN/C (struct/c posn real? real?))
  (define SNAKE/C (struct/c snake DIR/C (nelistof POSN/C)))
  (define WORLD/C (struct/c world SNAKE/C POSN/C))
    
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2))))  
  
  (provide (contract-out [struct posn ([x real?] [y real?])]))
  (provide/contract   
   [posn=? (POSN/C POSN/C . -> . boolean?)]
   [struct snake ([dir DIR/C] [segs (nelistof POSN/C)])]
   [struct world ([snake SNAKE/C] [food POSN/C])]
   [DIR/C any/c]
   [POSN/C any/c]
   [SNAKE/C any/c]
   [WORLD/C any/c]
   [nelistof (any/c . -> . any/c)]))

(module unsafe-data racket
  (struct snake (dir segs))
  (struct world (snake food))
  (struct posn (x y))
  
  (define (nelistof c) (cons/c c (listof c)))
  (define DIR/C (or/c "up" "down" "left" "right"))
  (define POSN/C (struct/c posn real? real?))
  (define SNAKE/C (struct/c snake DIR/C (nelistof POSN/C)))
  (define WORLD/C (struct/c world SNAKE/C POSN/C))
    
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2))))  
  
  (provide [struct-out posn])
  
  (provide
   posn=?
   [struct-out snake]
   [struct-out world]
   DIR/C
   POSN/C
   SNAKE/C
   WORLD/C))

(module const racket  
  (require (submod ".." image)
           (submod ".." data))
  
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
                         (posn 8 12)))
  
  (provide/contract
   [WORLD (-> WORLD/C)]
   [BACKGROUND (-> image/c)]
   [FOOD-IMAGE (-> image/c)]
   [SEGMENT-IMAGE (-> image/c)]
   [GRID-SIZE real?]
   [BOARD-HEIGHT-PIXELS (-> real?)]
   [BOARD-WIDTH real?]
   [BOARD-HEIGHT real?]))

(module unsafe-const racket  
  (require (submod ".." unsafe-image)
           (submod ".." unsafe-data))
  
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
                         (posn 8 12)))
  
  (provide
   WORLD
   BACKGROUND
   FOOD-IMAGE
   SEGMENT-IMAGE
   GRID-SIZE
   BOARD-HEIGHT-PIXELS
   BOARD-WIDTH
   BOARD-HEIGHT))

(module collide racket  
  (require (submod ".." data)
           (submod ".." const))
  
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
                    (segs-self-collide? h (cdr segs)))]))
  (provide/contract
   [snake-wall-collide? (SNAKE/C . -> . boolean?)]
   [snake-self-collide? (SNAKE/C . -> . boolean?)]))

(module unsafe-collide racket  
  (require (submod ".." unsafe-data)
           (submod ".." unsafe-const))
  
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
                    (segs-self-collide? h (cdr segs)))]))
  (provide
   snake-wall-collide?
   snake-self-collide?))

(module cut-tail racket
  
  (require (submod ".." data))
  ;; NeSegs is one of:
  ;; - (cons Posn empty)
  ;; - (cons Posn NeSegs)
  
  ;; cut-tail : NeSegs -> Segs
  ;; Cut off the tail.
  (define (cut-tail segs)
    (let ([r (cdr segs)])
      (cond [(empty? r) empty]
            [else (cons (car segs) (cut-tail r))])))
  
  (provide/contract
   [cut-tail ((nelistof POSN/C) . -> . (listof POSN/C))]))

(module unsafe-cut-tail racket
  
  (require (submod ".." unsafe-data))
  ;; NeSegs is one of:
  ;; - (cons Posn empty)
  ;; - (cons Posn NeSegs)
  
  ;; cut-tail : NeSegs -> Segs
  ;; Cut off the tail.
  (define (cut-tail segs)
    (let ([r (cdr segs)])
      (cond [(empty? r) empty]
            [else (cons (car segs) (cut-tail r))])))
  
  (provide
   cut-tail))

(module motion-help racket
  (require (submod ".." data)
           (submod ".." cut-tail))
  
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
                   (snake-segs snk)))))
  
  (provide/contract
   [snake-slither (SNAKE/C . -> . SNAKE/C)]
   [snake-grow (SNAKE/C . -> . SNAKE/C)]))

(module unsafe-motion-help racket
  (require (submod ".." unsafe-data)
           (submod ".." unsafe-cut-tail))
  
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
                   (snake-segs snk)))))
  
  (provide
   snake-slither
   snake-grow))

(module motion racket  
  (require (submod ".." data)
           (submod ".." const)
           (submod ".." motion-help))

  (provide reset!)
  (define r (make-pseudo-random-generator)) 
  (define (reset!)
    (parameterize ((current-pseudo-random-generator r))
		  (random-seed 1324)))

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
    (define i (add1 (random (sub1 BOARD-WIDTH) r)))
    (define j (add1 (random (sub1 BOARD-HEIGHT) r)))
    (world (snake-grow (world-snake w))
           (posn i j)
	   #;(posn (- BOARD-WIDTH 1) (- BOARD-HEIGHT 1))))

  (provide/contract
   [world-change-dir (WORLD/C DIR/C . -> . WORLD/C)]
   [world->world (WORLD/C . -> . WORLD/C)]))

(module unsafe-motion racket  
  (require (submod ".." unsafe-data)
           (submod ".." unsafe-const)
           (submod ".." unsafe-motion-help))

  (provide reset!)
  (define r (make-pseudo-random-generator)) 
  (define (reset!)
    (parameterize ((current-pseudo-random-generator r))
		  (random-seed 1324)))

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
    (define i (add1 (random (sub1 BOARD-WIDTH) r)))
    (define j (add1 (random (sub1 BOARD-HEIGHT) r)))
    (world (snake-grow (world-snake w))
           (posn i j)
                 
           #;(posn (- BOARD-WIDTH 1) (- BOARD-HEIGHT 1))))
  (provide
   world-change-dir
   world->world))


(module handlers racket
  ;; Movie handlers
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  
  (require (submod ".." data)
           (submod ".." motion)
           (submod ".." collide))
  
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
        (snake-self-collide? (world-snake w))))
  
  (provide/contract
   [handle-key (WORLD/C string? . -> . WORLD/C)]
   [game-over? (WORLD/C . -> . boolean?)]))

(module unsafe-handlers racket
  ;; Movie handlers
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  
  (require (submod ".." unsafe-data)
           (submod ".." unsafe-motion)
           (submod ".." unsafe-collide))
  
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
        (snake-self-collide? (world-snake w))))
  
  (provide
   handle-key 
   game-over?))


(module scenes racket    
  (require (submod ".." data)
           (submod ".." const)
           (submod ".." image))
  
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
    (place-image-on-grid (SEGMENT-IMAGE) (posn-x seg) (posn-y seg) scn))
  
  (provide/contract
   [world->scene (WORLD/C . -> . image/c)]
   [food+scene (POSN/C image/c . -> . image/c)]
   [place-image-on-grid (image/c real? real? image/c . -> . image/c)]
   [snake+scene (SNAKE/C image/c . -> . image/c)]
   [segments+scene ((listof POSN/C) image/c . -> . image/c)]
   [segment+scene (POSN/C image/c . -> . image/c)]))

(module unsafe-scenes racket    
  (require (submod ".." unsafe-data)
           (submod ".." unsafe-const)
           (submod ".." unsafe-image))
  
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
    (place-image-on-grid (SEGMENT-IMAGE) (posn-x seg) (posn-y seg) scn))
  
  (provide
   world->scene
   food+scene
   place-image-on-grid
   snake+scene
   segments+scene
   segment+scene))


(require 2htdp/universe)
(require 'data 'const 'scenes 'handlers 'motion 'collide)
(require (prefix-in unsafe: 'unsafe-data)
         (prefix-in unsafe: 'unsafe-const)
         (prefix-in unsafe: 'unsafe-scenes)
         (prefix-in unsafe: 'unsafe-handlers)
         (prefix-in unsafe: 'unsafe-motion)
         (prefix-in unsafe: 'unsafe-collide))
         

(define history empty)
(define (! e)
  (set! history (cons e history)))

(define (play)
  (big-bang (WORLD)
            (on-tick (λ (w) (! `(on-tick)) (world->world w)) 1/5)
            (on-key (λ (w ke) (! `(on-key ,ke)) (handle-key w ke)))
            (to-draw (λ (w) (world->scene w)))
            (stop-when (λ (w) (! `(stop-when)) (game-over? w)))))

#;
(with-output-to-file "snake-hist-2.txt" 
  (λ () 
    (set! history empty)
    (play)
    (write history)))


(define (replay w0 hist)
  (reset!)
  (let loop ((w w0) (h hist))
    (if (empty? h)
        w
        (let ()
          (loop
           (match (car h)
             [`(on-key ,ke)
              (handle-key w ke)]
             [`(on-tick)
              (world->world w)]
             [`(stop-when)
              (game-over? w)
              w])
           (cdr h))))))

(define (unsafe:replay w0 hist)
  (unsafe:reset!)
  (let loop ((w w0) (h hist))
    (if (empty? h)
        w
        (let ()
          (loop
           (match (car h)
             [`(on-key ,ke)
              (unsafe:handle-key w ke)]
             [`(on-tick)
              (unsafe:world->world w)]
             [`(stop-when)
              (unsafe:game-over? w)
              w])
           (cdr h))))))

(define (start w)
  (big-bang w
            (on-tick unsafe:world->world 1/5)
            (on-key unsafe:handle-key)
            (to-draw unsafe:world->scene)
            (stop-when unsafe:game-over?)))

(define w0 (WORLD))
(define unsafe:w0 (unsafe:WORLD))
;(replay (WORLD) h)
(provide replay unsafe:replay w0 unsafe:w0 start)


