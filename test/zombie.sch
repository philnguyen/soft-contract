(module image
  (provide
   [image? (any . -> . bool?)]
   [empty-scene (real? real? . -> . image?)]
   [place-image (image? real? real? image? . -> . image?)]
   [circle (real? str? str? . -> . image?)])
  (struct image (impl)))

(module math
  (provide
   [min (real? real? . -> . real?)]
   [max (real? real? . -> . real?)]
   [abs (real? . -> . real?)]
   [sqrt (real? . -> . real?)]
   [sqr (real? . -> . real?)])
  (define (min x y) (if (<= x y) x y))
  (define (max x y) (if (>= x y) x y))
  (define (abs x) (if (>= x 0) x (- 0 x)))
  (define (sqr x) (* x x)))

(module zombie
  (provide
   [posn/c any]
   [player/c any]
   [zombie/c any]
   [zombies/c any]
   [horde/c any]
   [world/c any]
   
   [new-world (player/c posn/c horde/c . -> . world/c)]
   [new-player (posn/c . -> . player/c)]
   [new-horde (zombies/c zombies/c . -> . horde/c)]
   [new-cons-zombies (zombie/c zombies/c . -> . zombies/c)]
   [new-mt-zombies (-> zombies/c)]
   [new-zombie (posn/c . -> . zombie/c)]
   [new-posn (real? real? . -> . posn/c)]
   [w0 world/c])
  (require image math)
  
  (define WIDTH 400)
  (define HEIGHT 400)
  (define MT-SCENE (empty-scene WIDTH HEIGHT))
  (define PLAYER-SPEED 4)
  (define ZOMBIE-SPEED 2)
  (define ZOMBIE-RADIUS 20)
  (define PLAYER-RADIUS 20)
  (define PLAYER-IMG (circle PLAYER-RADIUS "solid" "green"))
  
  (define posn/c
    ([msg : (one-of/c 'x 'y 'posn 'move-toward/speed 'draw-on/image 'dist)]
     . -> .
     (cond
       [(equal? msg 'x) (-> real?)]
       [(equal? msg 'y) (-> real?)]
       [(equal? msg 'posn) (-> posn/c)]
       [(equal? msg 'move-toward/speed) (posn/c real? . -> . posn/c)]
       [(equal? msg 'draw-on/image) (image? image? . -> . image?)]
       [(equal? msg 'dist) (posn/c . -> . real?)]
       [else "error"])))
  
  (define player/c
    ([msg : (one-of/c 'posn 'move-toward 'draw-on)]
     . -> .
     (cond
       [(equal? msg 'posn) (-> posn/c)]
       [(equal? msg 'move-toward) (posn/c . -> . player/c)]
       [(equal? msg 'draw-on) (image? . -> . image?)]
       [else "error"])))
  
  (define zombie/c
    ([msg : (one-of/c 'posn 'draw-on/color 'touching? 'move-toward)]
     . -> . 
     (cond
       [(equal? msg 'posn) (-> posn/c)]
       [(equal? msg 'draw-on/color) (str? image? . -> . image?)]
       [(equal? msg 'touching?) (posn/c . -> . bool?)]
       [(equal? msg 'move-toward) (posn/c . -> . zombie/c)]
       [else "error"])))
  
  (define horde/c
    ([msg : (one-of/c 'dead 'undead 'draw-on 'touching? 'move-toward 'eat-brains)]
     . -> .
     (cond
       [(equal? msg 'dead) (-> zombies/c)]
       [(equal? msg 'undead) (-> zombies/c)]
       [(equal? msg 'draw-on) (image? . -> . image?)]
       [(equal? msg 'touching?) (posn/c . -> . bool?)]
       [(equal? msg 'move-toward) (posn/c . -> . horde/c)]
       [(equal? msg 'eat-brains) (-> horde/c)]
       [else "error"])))
  
  (define zombies/c
    ([msg : (one-of/c 'move-toward 'draw-on/color 'touching? 'kill-all)]
     . -> .
     (cond
       [(equal? msg 'move-toward) (posn/c . -> . zombies/c)]
       [(equal? msg 'draw-on/color) (str? image? . -> . image?)]
       [(equal? msg 'touching?) (posn/c . -> . bool?)]
       [(equal? msg 'kill-all) (zombies/c . -> . horde/c)]
       [else "error"])))
  
  (define world/c
    ([msg : (one-of/c 'on-mouse 'on-tick 'to-draw 'stop-when)]
     . -> .
     (cond
       [(equal? msg 'on-mouse) (real? real? str? . -> . world/c)]
       [(equal? msg 'on-tick) (-> world/c)]
       [(equal? msg 'to-draw) (-> image?)]
       [(equal? msg 'stop-when) (-> bool?)]
       [else "error"])))
  
  (define (new-world player mouse zombies)
    (λ (msg)
      (cond
        [(equal? msg 'on-mouse)
         (λ (x y me)
           (new-world player
                      (if (equal? me "leave") ((player 'posn)) (new-posn x y))
                      zombies))]
        [(equal? msg 'on-tick)
         (λ ()
           (new-world ((player 'move-toward) mouse)
                      mouse
                      ((((zombies 'eat-brains)) 'move-toward) ((player 'posn)))))]
        [(equal? msg 'to-draw)
         (λ ()
           ((player 'draw-on) ((zombies 'draw-on) MT-SCENE)))]
        [(equal? msg 'stop-when)
         (λ ()
           ((zombies 'touching?) ((player 'posn))))]
        [else "unknown message"])))
  
  (define (new-player p)
    (λ (msg)
      (cond
        [(equal? msg 'posn) (λ () p)]
        [(equal? msg 'move-toward)
         (λ (q)
           (new-player ((p 'move-toward/speed) q PLAYER-SPEED)))]
        [(equal? msg 'draw-on)
         (λ (scn)
           ((p 'draw-on/image) PLAYER-IMG scn))]
        [else "unknown message"])))
  
  (define (new-horde undead dead)
    (λ (msg)
      (cond
        [(equal? msg 'dead) (λ () dead)]
        [(equal? msg 'undead) (λ () undead)]
        [(equal? msg 'draw-on)
         (λ (scn)
           ((undead 'draw-on/color) "yellow" ((dead 'draw-on/color) "black" scn)))]
        [(equal? msg 'touching?)
         (λ (p)
           (or ((undead 'touching?) p) ((dead 'touching?) p)))]
        [(equal? msg 'move-toward)
         (λ (p)
           (new-horde ((undead 'move-toward) p) dead))]
        [(equal? msg 'eat-brains) (λ () ((undead 'kill-all) dead))]
        [else "unknown message"])))
  
  (define (new-cons-zombies z r)
    (λ (msg)
      (cond
        [(equal? msg 'move-toward)
         (λ (p)
           (new-cons-zombies ((z 'move-toward) p) ((r 'move-toward) p)))]
        [(equal? msg 'draw-on/color)
         (λ (c s)
           ((z 'draw-on/color) c ((r 'draw-on/color) c s)))]
        [(equal? msg 'touching?)
         (λ (p)
           (or ((z 'touching?) p) ((r 'touching?) p)))]
        [(equal? msg 'kill-all)
         (λ (dead)
           (cond
             [(or ((r 'touching?) ((z 'posn)))
                  ((dead 'touching?) ((z 'posn))))
              ((r 'kill-all) (new-cons-zombies z dead))]
             [else (let ([res ((r 'kill-all) dead)])
                     (new-horde
                      (new-cons-zombies z ((res 'undead)))
                      ((res 'dead))))]))]
        [else "unknown message"])))
  
  (define (new-mt-zombies)
    (λ (msg)
      (cond
        [(equal? msg 'move-toward) (λ (p) (new-mt-zombies))]
        [(equal? msg 'draw-on/color) (λ (c s) s)]
        [(equal? msg 'touching?) (λ (p) #f)]
        [(equal? msg 'kill-all)
         (λ (dead)
           (new-horde (new-mt-zombies) dead))]
        [else "unknown message"])))
  
  (define (new-zombie p)
    (λ (msg)
      (cond
        [(equal? msg 'posn) (λ () p)]
        [(equal? msg 'draw-on/color)
         (λ (c s)
           ((p 'draw-on/image)
            (circle ZOMBIE-RADIUS "solid" c)
            s))]
        [(equal? msg 'touching?)
         (λ (q)
           (<= ((p 'dist) q) ZOMBIE-RADIUS))]
        [(equal? msg 'move-toward)
         (λ (q)
           (new-zombie ((p 'move-toward/speed) q ZOMBIE-SPEED)))]
        [else "unknown message"])))
  
  (define (new-posn x y)
    (λ (msg)
      (let ([this (new-posn x y)]) ; FIXME
        (cond
          [(equal? msg 'x) (λ () x)]
          [(equal? msg 'y) (λ () y)]
          [(equal? msg 'posn) (λ () this)]
          [(equal? msg 'move-toward/speed)
           (λ (p speed)
             (let* ([δx (- ((p 'x)) x)]
                    [δy (- ((p 'y)) y)]
                    [move-distance (min speed (max (abs δx) (abs δy)))])
               (cond
                 [(< (abs δx) (abs δy))
                  ((this 'move)
                   0
                   (if (positive? δy) move-distance (- 0 move-distance)))]
                 [else
                  ((this 'move)
                   (if (positive? δx) move-distance (- 0 move-distance))
                   0)])))]
          [(equal? msg 'move)
           (λ (δx δy)
             (new-posn (+ x δx) (+ y δy)))]
          [(equal? msg 'draw-on/image)
           (λ (img scn)
             (place-image img x y scn))]
          [(equal? msg 'dist)
           (λ (p)
             (sqrt (+ (sqr (- ((p 'y)) y))
                      (sqr (- ((p 'x)) x)))))]
          [else "unknown message"]))))
  
  (define w0
    (new-world
     (new-player (new-posn 0 0))
     (new-posn 0 0)
     (new-horde
      (new-cons-zombies
       (new-zombie (new-posn 100 300))
       (new-cons-zombies
        (new-zombie (new-posn 100 200))
        (new-mt-zombies)))
      (new-cons-zombies
       (new-zombie (new-posn 200 200))
       (new-mt-zombies))))))

(require zombie)

(amb (• new-posn)
     (• new-player)
     (• new-zombie)
     (• new-cons-zombies)
     (• new-mt-zombies)
     (• new-horde)
     (• new-world))