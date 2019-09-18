#lang racket/base

(require racket/contract
         (submod "image.rkt" #%type-decl ".."))

(define g6 (recursive-contract g31 #:chaperone))
(define g7 (recursive-contract g42 #:chaperone))
(define g8 (recursive-contract g49 #:chaperone))
(define g9 symbol?)
(define g10 'stop-when)
(define g11 '#t)
(define g12 '#f)
(define g13 (or/c g11 g12))
(define g14 (-> (values g13)))
(define g15 (cons/c g10 g14))
(define g16 'to-draw)
(define g17 (lambda (x) (image? x)))
(define g18 (-> g17))
(define g19 (cons/c g16 g18))
(define g20 'on-tick)
(define g21 g8)
(define g22 (-> (values g21)))
(define g23 (cons/c g20 g22))
(define g24 'on-mouse)
(define g25 real?)
(define g26 (or/c g25))
(define g27 string?)
(define g28 (-> g26 g26 g27 (values g21)))
(define g29 (cons/c g24 g28))
(define g30 (or/c g15 g19 g23 g29))
(define g31 (-> g9 (values g30)))
(define g32 (-> (values g13)))
(define g33 (cons/c g10 g32))
(define g34 (-> (values g17)))
(define g35 (cons/c g16 g34))
(define g36 g7)
(define g37 (-> (values g36)))
(define g38 (cons/c g20 g37))
(define g39 (-> g26 g26 g27 (values g36)))
(define g40 (cons/c g24 g39))
(define g41 (or/c g33 g35 g38 g40))
(define g42 (-> g9 (values g41)))
(define g43 g6)
(define g44 (-> (values g43)))
(define g45 (cons/c g20 g44))
(define g46 (-> g26 g26 g27 (values g43)))
(define g47 (cons/c g24 g46))
(define g48 (or/c g33 g35 g45 g47))
(define g49 (-> g9 (values g48)))
(define generated-contract3 g7)
(define generated-contract4 (-> g21 (values g39)))
(define generated-contract5 (-> g21 (values g37)))

(require require-typed-check
         (for-syntax
          racket/sequence
          racket/base
          syntax/parse
          racket/syntax)
         "image-adapted.rkt")
(begin (require "math.rkt") (void))
(define WIDTH 400)
(define HEIGHT 400)
(define MT-SCENE (empty-scene WIDTH HEIGHT))
(define PLAYER-SPEED 4)
(define ZOMBIE-SPEED 2)
(define ZOMBIE-RADIUS 20)
(define PLAYER-RADIUS 20)
(define PLAYER-IMG (circle PLAYER-RADIUS "solid" "green"))
(define-syntax make-fake-object-type*
  (syntax-parser
    ((_ ty (f* t*) ...)
     #:with
     (id* ...)
     (for/list
         ((f (in-list (syntax->list #'(f* ...)))))
       (format-id
        #'ty
        "~a-~a"
        (string-downcase (symbol->string (syntax-e #'ty)))
        f))
     #:with
     (f-sym* ...)
     (for/list ((f (in-list (syntax->list #'(f* ...))))) (syntax-e f))
     #'(begin
         (define (id* v)
           (let ((r (v 'f-sym*)))
             (if (eq? 'f-sym* (car r))
                 (cdr r)
                 (error 'id* "type error"))))
         ...))))
(make-fake-object-type*
 Posn
 (x (-> Real))
 (y (-> Real))
 (posn (-> Posn))
 (move-toward/speed (-> Posn Real Posn))
 (move (-> Real Real Posn))
 (draw-on/image (-> Image Image Image))
 (dist (-> Posn Real)))
(make-fake-object-type*
 Player
 (posn (-> Posn))
 (move-toward (-> Posn Player))
 (draw-on (-> Image Image)))
(make-fake-object-type*
 Zombie
 (posn (-> Posn))
 (draw-on/color (-> String Image Image))
 (touching? (-> Posn Boolean))
 (move-toward (-> Posn Zombie)))
(make-fake-object-type*
 Horde
 (dead (-> Zombies))
 (undead (-> Zombies))
 (draw-on (-> Image Image))
 (touching? (-> Posn Boolean))
 (move-toward (-> Posn Horde))
 (eat-brains (-> Horde)))
(make-fake-object-type*
 Zombies
 (move-toward (-> Posn Zombies))
 (draw-on/color (-> String Image Image))
 (touching? (-> Posn Boolean))
 (kill-all (-> Zombies Horde)))
(make-fake-object-type*
 World
 (on-mouse (-> Real Real String World))
 (on-tick (-> World))
 (to-draw (-> Image))
 (stop-when (-> Boolean)))

(define (new-world player mouse zombies)
  (lambda (msg)
    (cond
      ((equal? msg 'on-mouse)
       (cons
        'on-mouse
        (lambda (x y me)
          (new-world
           player
           (if (equal? me "leave") ((player-posn player)) (new-posn x y))
           zombies))))
      ((equal? msg 'on-tick)
       (cons
        'on-tick
        (lambda ()
          (new-world
           ((player-move-toward player) mouse)
           mouse
           ((horde-move-toward ((horde-eat-brains zombies)))
            ((player-posn player)))))))
      ((equal? msg 'to-draw)
       (cons
        'to-draw
        (lambda ()
          ((player-draw-on player) ((horde-draw-on zombies) MT-SCENE)))))
      ((equal? msg 'stop-when)
       (cons
        'stop-when
        (lambda () ((horde-touching? zombies) ((player-posn player))))))
      (else (error 'world "unknown message")))))

(define (new-player p)
  (lambda (msg)
    (cond
      ((equal? msg 'posn) (cons 'posn (lambda () p)))
      ((equal? msg 'move-toward)
       (cons
        'move-toward
        (lambda (q)
          (new-player ((posn-move-toward/speed p) q PLAYER-SPEED)))))
      ((equal? msg 'draw-on)
       (cons
        'draw-on
        (lambda (scn) ((posn-draw-on/image p) PLAYER-IMG scn))))
      (else (error 'player "unknown message")))))

(define (new-horde undead dead)
  (lambda (msg)
    (cond
      ((equal? msg 'dead) (cons 'dead (lambda () dead)))
      ((equal? msg 'undead) (cons 'undead (lambda () undead)))
      ((equal? msg 'draw-on)
       (cons
        'draw-on
        (lambda (scn)
          ((zombies-draw-on/color undead)
           "yellow"
           ((zombies-draw-on/color dead) "black" scn)))))
      ((equal? msg 'touching?)
       (cons
        'touching?
        (lambda (p)
          (or ((zombies-touching? undead) p)
              ((zombies-touching? dead) p)))))
      ((equal? msg 'move-toward)
       (cons
        'move-toward
        (lambda (p)
          (new-horde ((zombies-move-toward undead) p) dead))))
      ((equal? msg 'eat-brains)
       (cons 'eat-brains (lambda () ((zombies-kill-all undead) dead))))
      (else (error 'horde "unknown message")))))

(define (new-cons-zombies z r)
  (lambda (msg)
    (cond
      ((equal? msg 'move-toward)
       (cons
        'move-toward
        (lambda (p)
          (new-cons-zombies
           ((zombie-move-toward z) p)
           ((zombies-move-toward r) p)))))
      ((equal? msg 'draw-on/color)
       (cons
        'draw-on/color
        (lambda (c s)
          ((zombie-draw-on/color z) c ((zombies-draw-on/color r) c s)))))
      ((equal? msg 'touching?)
       (cons
        'touching?
        (lambda (p)
          (or ((zombie-touching? z) p) ((zombies-touching? r) p)))))
      ((equal? msg 'kill-all)
       (cons
        'kill-all
        (lambda (dead)
          (cond
            ((or ((zombies-touching? r) ((zombie-posn z)))
                 ((zombies-touching? dead) ((zombie-posn z))))
             ((zombies-kill-all r) (new-cons-zombies z dead)))
            (else
             (let ((res ((zombies-kill-all r) dead)))
               (new-horde
                (new-cons-zombies z ((horde-undead res)))
                ((horde-dead res)))))))))
      (else (error 'zombies "unknown message")))))

(define (new-mt-zombies)
  (lambda (msg)
    (cond
      ((equal? msg 'move-toward)
       (cons 'move-toward (lambda (p) (new-mt-zombies))))
      ((equal? msg 'draw-on/color)
       (cons 'draw-on/color (lambda (c s) s)))
      ((equal? msg 'touching?) (cons 'touching? (lambda (p) #f)))
      ((equal? msg 'kill-all)
       (cons
        'kill-all
        (lambda (dead) (new-horde (new-mt-zombies) dead))))
      (else (error 'zombies "unknown message")))))

(define (new-zombie p)
  (lambda (msg)
    (cond
      ((equal? msg 'posn) (cons 'posn (lambda () p)))
      ((equal? msg 'draw-on/color)
       (cons
        'draw-on/color
        (lambda (c s)
          ((posn-draw-on/image p) (circle ZOMBIE-RADIUS "solid" c) s))))
      ((equal? msg 'touching?)
       (cons
        'touching?
        (lambda (q) (<= ((posn-dist p) q) ZOMBIE-RADIUS))))
      ((equal? msg 'move-toward)
       (cons
        'move-toward
        (lambda (q)
          (new-zombie ((posn-move-toward/speed p) q ZOMBIE-SPEED)))))
      (else (error 'zombie "unknown message")))))

(define (new-posn x y)
  (lambda (msg)
    (let ((this (new-posn x y)))
      (cond
        ((equal? msg 'x) (cons 'x (lambda () x)))
        ((equal? msg 'y) (cons 'y (lambda () y)))
        ((equal? msg 'posn) (cons 'posn (lambda () this)))
        ((equal? msg 'move-toward/speed)
         (cons
          msg
          (lambda (p speed)
            (let* ((x2 (- ((posn-x p)) x))
                   (y2 (- ((posn-y p)) y))
                   (move-distance (min speed (max (abs x2) (abs y2)))))
              (cond
                ((< (abs x2) (abs y2))
                 ((posn-move this)
                  0
                  (if (positive? y2) move-distance (- 0 move-distance))))
                (else
                 ((posn-move this)
                  (if (positive? x2) move-distance (- 0 move-distance))
                  0)))))))
        ((equal? msg 'move)
         (cons
          'move
          (lambda (x2 y2) (new-posn (+ x x2) (+ y y2)))))
        ((equal? msg 'draw-on/image)
         (cons
          'draw-on/image
          (lambda (img scn) (place-image img x y scn))))
        ((equal? msg 'dist)
         (cons
          'dist
          (lambda (p)
            (msqrt (+ (sqr (- ((posn-y p)) y)) (sqr (- ((posn-x p)) x)))))))
        (else (error 'posn "unknown message"))))))

(define w0
  (new-world
   (new-player (new-posn 0 0))
   (new-posn 0 0)
   (new-horde
    (new-cons-zombies
     (new-zombie (new-posn 100 300))
     (new-cons-zombies (new-zombie (new-posn 100 200)) (new-mt-zombies)))
    (new-cons-zombies (new-zombie (new-posn 200 200)) (new-mt-zombies)))))

(provide (contract-out (world-on-mouse generated-contract4))
         (contract-out (w0 generated-contract3))
         (contract-out (world-on-tick generated-contract5)))
