#lang racket
(require 2htdp/image)
(require 2htdp/universe)
(require rackunit)
(require (only-in mzlib/etc rec))

; TO DISABLE CONTRACTS
#;(define-syntax-rule (define/contract (f x ...) e ...)
  (define (f x ...) e ...))

;; Start a new game of Zombie Attack!
#;(define (start w)
  (big-bang w
   [on-tick   (λ (w0) ((w0 'on-tick))) 1/10]
   [on-mouse  (λ (w0 x y me) ((w0 'on-mouse) x y me))]
   [to-draw   (λ (w0) ((w0 'to-draw)))]
   [stop-when (λ (w0) ((w0 'stop-when)))]))

;; Constants
(define WIDTH 400)
(define HEIGHT 400)
(define MT-SCENE (empty-scene WIDTH HEIGHT))
(define PLAYER-SPEED 4)
(define ZOMBIE-SPEED 2)
(define ZOMBIE-RADIUS 20)
(define PLAYER-RADIUS 20)
(define PLAYER-IMG (circle PLAYER-RADIUS "solid" "green"))

(define posn/c
  (->i ([msg (or/c 'x 'y 'posn 'move-toward/speed 'draw-on/image 'dist)])
       [result (msg)
               (case msg
                 [(x) (-> real?)]
                 [(y) (-> real?)]
                 [(posn) (-> posn/c)]
                 [(move-toward/speed)
                  (-> posn/c real? posn/c)]
                 [(draw-on/image)
                  (-> image? image? image?)]
                 [(dist)
                  (-> posn/c real?)])]))

(define player/c
  (->i ([msg (or/c 'posn 'move-toward 'draw-on)])
       [result (msg)
               (case msg
                 [(posn) (-> posn/c)]
                 [(move-toward) (-> posn/c player/c)]
                 [(draw-on) (-> image? image?)])]))

(define zombie/c
  (->i [(msg (or/c 'posn 'draw-on/color 'touching? 'move-toward))]
       [result (msg)
               (case msg
                 [(posn) (-> posn/c)]
                 [(draw-on/color) (-> string? image? image?)]
                 [(touching?) (-> posn/c boolean?)]
                 [(move-toward) (-> posn/c zombie/c)])]))

(define horde/c
  (->i ([msg (or/c 'dead 'undead 'draw-on 
                   'touching? 'move-toward 'eat-brains)])
       [result (msg)
               (case msg
                 [(dead) (-> zombies/c)]
                 [(undead) (-> zombies/c)]
                 [(draw-on) (-> image? image?)]
                 [(touching?) (-> posn/c boolean?)]
                 [(move-toward) (-> posn/c horde/c)]
                 [(eat-brains) (-> horde/c)])]))

(define zombies/c
  (->i ([msg (or/c 'move-toward 'draw-on/color 'touching? 'kill-all)])
       [result (msg)
               (case msg
                 [(move-toward) (-> posn/c zombies/c)]
                 [(draw-on/color) (-> string? image? image?)]
                 [(touching?) (-> posn/c boolean?)]
                 [(kill-all) (-> zombies/c horde/c)])]))

(define world/c
  (->i ([msg (or/c 'on-mouse 'on-tick 'to-draw 'stop-when)])
       [result (msg)
               (case msg
                 [(on-mouse)
                  (-> real? real? string? world/c)]
                 [(on-tick)
                  (-> world/c)]
                 [(to-draw)
                  (-> image?)]
                 [(stop-when)
                  (-> boolean?)])]))


(define/contract (new-world player mouse zombies)
  (player/c posn/c horde/c . -> . world/c)
  (λ (msg)
    (case msg
      [(on-mouse)
       ;; Update mouse position unless it has left the screen
       ;; on-mouse : Number Number MouseEvent -> World  
       (λ (x y me)                  
         (new-world player
                    (cond [(string=? me "leave") ((player 'posn))]
                          [else
                           (new-posn x y)])
                    zombies))]
      
      ;; Advance and eat brains!
      ;; on-tick : -> World
      [(on-tick)
       (λ ()
         (new-world ((player 'move-toward) mouse)
                    mouse
                    ((((zombies 'eat-brains)) 'move-toward) 
                     ((player 'posn)))))]
  
      ;; Draw the player and zombies in this world
      ;; to-draw : -> Scene
      [(to-draw)
       (λ ()
         ((player 'draw-on)
          ((zombies 'draw-on) MT-SCENE)))]
      
      ;; Game is over when zombies touch the player
      ;; stop-when : -> Boolean
      [(stop-when)
       (λ ()
         ((zombies 'touching?) ((player 'posn))))]
      
      [else
         (error "unkown message")])))

;; Interp: a player at posn
(define/contract (new-player p)
  (posn/c . -> . player/c)
  (λ (msg)
    (case msg
      [(posn) (λ () p)]
      [(move-toward)
       ;; move-toward : Posn -> Player
       ;; Move this player toward the given position  
       (λ (p1)
         (new-player ((p 'move-toward/speed) p1 PLAYER-SPEED)))]
  
      [(draw-on)       
       ;; draw-on : Scene -> Scene
       ;; Draw this player on the scene
       (λ (scn)         
         ((p 'draw-on/image) PLAYER-IMG scn))]
      
      [else
       (error "unkown message" msg)])))

;; Interp: a Horde of undead and dead zombies
(define/contract (new-horde undead dead)
  (zombies/c zombies/c . -> . horde/c)
  (λ (msg)
    (case msg
      [(dead) (λ () dead)]
      [(undead) (λ () undead)]
      ;; draw-on : Scene -> Scene
      [(draw-on)
       (λ (scn)
         ((undead 'draw-on/color) "yellow"
                                  ((dead 'draw-on/color) "black"
                                                         scn)))]
              
      ;; touching? : posn -> Boolean
      [(touching?)
       (λ (p)
         (or ((undead 'touching?) p)
             ((dead 'touching?) p)))]
  
      ;; move-toward : posn -> Horde
      [(move-toward)
       (λ (p)
         (new-horde
          ((undead 'move-toward) p)
          dead))]
  
      ;; eat-brains : -> Horde
      [(eat-brains)
       (λ ()
         ((undead 'kill-all) dead))]
      
      [else
       (error "unkown message")])))

;; A Zombies implements
;; - move-toward : Posn -> Zombies
;; - Move all of these zombies toward the given position
;;
;; - draw-on/color : Color Scene -> Scene
;; - Draw all of these zombies
;;
;; - touching? : Posn -> Boolean
;; - Are any of these zombies touching the given location?
;;
;; - kill-all : Zombies -> Horde
;; - Kill all touching zombies in this set and given dead zombies

(define/contract (new-cons-zombies z r)
  (zombie/c zombies/c . -> . zombies/c)
  (λ (msg)
    (case msg
      [(move-toward)
       (λ (p)
         (new-cons-zombies ((z 'move-toward) p)
                           ((r 'move-toward) p)))]
      [(draw-on/color)
       (λ (c s)
         ((z 'draw-on/color) c
                             ((r 'draw-on/color) c s)))]
      [(touching?)
       (λ (p)
         (or ((z 'touching?) p)
             ((r 'touching?) p)))]
      
      [(kill-all)
       (λ (dead)         
         (cond [(or ((r 'touching?) ((z 'posn)))
                    ((dead 'touching?) ((z 'posn))))
                ((r 'kill-all)
                 (new-cons-zombies z dead))]
               [else
                (local [(define res ((r 'kill-all) dead))]
                  (new-horde
                   (new-cons-zombies z ((res 'undead)))
                   ((res 'dead))))]))]

      [else (error "unkown message" msg)])))

(define/contract (new-mt-zombies)
  (-> zombies/c)  
  (λ (msg)
    (case msg
      [(move-toward)
       (λ (p)
         (new-mt-zombies))]
      [(draw-on/color)
       (λ (c s)
         s)]
      [(touching?)
       (λ (p)
         false)]
      [(kill-all)
       ;; kill-all : Zombies -> Horde
       (λ (dead)       
         (new-horde (new-mt-zombies) dead))]
      
      [else (error "unkown message")])))

(define/contract (new-zombie p)
  (posn/c . -> . zombie/c)
  (λ (msg)
    (case msg
      [(posn) (λ () p)]
      [(draw-on/color)
       (λ (c s)
         ((p 'draw-on/image)
          (circle ZOMBIE-RADIUS "solid" c)
          s))]
      [(touching?)
       (λ (p0)
         (<= ((p 'dist) p0) ZOMBIE-RADIUS))]
      [(move-toward)
       (λ (p2)
         (new-zombie ((p 'move-toward/speed) p2 ZOMBIE-SPEED)))]
      [else
       (error "unkown message")])))



;; A Posn implements
;; - x : -> Real
;; - Get x-coorinate
;;
;; - y : -> Real
;; - Get y-coordinate
;;
;; - move-toward/speed : Posn Real -> Posn
;; - Move horizontally or vertically toward location at given speed
;;
;; - Draw image at this position on scene
;; - draw-on/image : Image Scene -> Scene
;;
;; - dist : Posn -> Real
;; - Compute distance from this position to given location

(define/contract (new-posn x y)
  (real? real? . -> . posn/c)
  (rec this
    (λ (msg)
      (case msg
        [(x) (λ () x)]
        [(y) (λ () y)]
        [(posn) (λ () this)]
        [(move-toward/speed)
         (λ (p speed)
           (local [(define δ-x (- ((p 'x)) x))
                   (define δ-y (- ((p 'y)) y))
                   (define move-distance
                     (min speed
                          (max (abs δ-x)
                               (abs δ-y))))]
             
             (cond [(< (abs δ-x) (abs δ-y))
                    ((this 'move) ;; move along y-axis
                     0
                     (cond [(positive? δ-y) move-distance]
                           [else (- move-distance)]))]
                   [else
                    ((this 'move) ;; move along x-axis
                     (cond [(positive? δ-x) move-distance]
                           [else (- move-distance)])
                     0)])))]
        
        ;; Move this position by given offsets
        ;; move : Number Number -> Posn
        [(move)
         (λ (δ-x δ-y)
           (new-posn (+ x δ-x)
                     (+ y δ-y)))]
        
        [(draw-on/image)
         (λ (img scn)
           (place-image img x y scn))]
        [(dist)
         (λ (p)
           (sqrt (+ (sqr (- ((p 'y)) y))
                    (sqr (- ((p 'x)) x)))))]
        [else
         (error "unkown message")]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define w0
  (new-world
   (new-player (new-posn 0 0))
   (new-posn 0 0)
   (new-horde
    ;; undead zombies
    (new-cons-zombies
     (new-zombie (new-posn 100 300))
     (new-cons-zombies
      (new-zombie (new-posn 100 200))
      (new-mt-zombies)))
    ;; dead zombies
    (new-cons-zombies
     (new-zombie (new-posn 200 200))
     (new-mt-zombies)))))

;; measure contracts overhead
;; uncomment macro at beginning of file to disable contracts
(collect-garbage)
(time (for/fold ([w w0]) ([i 20])
        ((w 'on-tick))))