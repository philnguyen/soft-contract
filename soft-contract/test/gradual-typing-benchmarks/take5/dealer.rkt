#lang racket/base

;; the dealer and supervisor of the deck

(provide
 ;; [Listof Player] -> Dealer
 ;; create a dealer object that connects the players with the deck
 ;; and places the player's chosen cards
 create-dealer)

(require
  racket/list
  require-typed-check
  racket/class)
(require "card.rkt")
(require (only-in "basics.rkt"
  FACE
  FIVE
  STACKS
  SIXTYSIX
  HAND
  MIN-BULL
  MAX-BULL
  configuration
))
(require (only-in "card-pool.rkt"
  create-card-pool
))
(require (only-in "deck.rkt"
  create-deck
))
(require (only-in "player.rkt"
  player%
))
;; ---------------------------------------------------------------------------------------------------

;; TODO should not need to supply this
(define (default-order loc)
  (sort loc > #:key card-face))

(define (default-faces)
  MIN-BULL)

;; Note to self: the types for the below descriptions are used out of scope for now
;; in a file-module they come back into scope 

(define (create-dealer players)
  (new dealer% [players players]))

(define dealer%
  (class object%
    (init-field
     players)

    (super-new)

    (field
     [internal%
      (class player%
        (init-field player)
        (super-new [n (send player name)] [order default-order])
        (field [my-bulls 0])
        (define/public (bulls) (get-field my-bulls this))
        (define/public (add-score n)
          (set-field! my-bulls this (+ n (get-field my-bulls this)))))]
     [internals (for/list
                          ([p (in-list (get-field players this))])
                  (new internal% [player p]))])

    ;; ---------------------------------------------------------------------------------------------
    ;; running a game 

    (define/public (play-game (shuffle values) (faces default-faces))
      (define n (length (get-field internals this)))
      (when (> (+ (* n HAND) STACKS) FACE)
        (error 'play-game "cannot play with ~a players; more cards needed" n))

      (let play-game  ([i  1])
        (play-round shuffle faces)
        (if (any-player-done?)
            (present-results i)
            (play-game (+ i 1)))))

    (define/public (present-results i)
      (define sorted
        (sort
         (get-field internals this) < #:key (lambda (i ) (send i bulls))))
      `((after-round ,i)
        ,(for/list
            ([p  (in-list sorted)])
           `(,(send p name) ,(send p bulls)))))

    (define/public (any-player-done?)
      (for/or
              ((p  (in-list (get-field internals this))))
        (> (send p bulls) SIXTYSIX)))

    (define/public (play-round shuffle faces)
      (define card-pool (create-card-pool shuffle faces))
      (define deck (create-deck card-pool))
      (deal-cards card-pool)
      (for ((p HAND))
        (play-turn deck)))

    (define/private (deal-cards card-pool)
      (for ((p  (in-list (get-field internals this))))
        (send p start-round (send card-pool draw-hand))))

    (define/private (play-turn deck)
      (define played-cards
        (for/list
                  ((p  (in-list (get-field internals this))))
          (list p (send p start-turn deck))))
      (define sorted-played-cards
        (sort played-cards < #:key (lambda (x) (card-face (second x)))))
      (place-cards deck sorted-played-cards))

    (define/private (place-cards deck sorted-player-cards)
      (for ((p+c  (in-list sorted-player-cards)))
        (define player (first p+c))
        (define card (second p+c))
        (cond
          [(send deck larger-than-some-top-of-stacks? card)
           (define closest-fit-stack (send deck fit card))
           (cond
             [(< (length closest-fit-stack) FIVE)
              (send deck push card)]
             [(= (length closest-fit-stack) FIVE)
              (define bulls (send deck replace closest-fit-stack card))
              (send player add-score bulls)])]
          [else ;; the tops of all stacks have larger face values than card
           (define chosen-stack (send player choose deck))
           (define bulls (send deck replace chosen-stack card))
           (send player add-score bulls)])))

))
