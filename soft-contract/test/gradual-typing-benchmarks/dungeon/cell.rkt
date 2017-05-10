#lang racket/base

;; TODO use open?

(provide
  empty-cell%
  void-cell%
  door%
  vertical-door%
  horizontal-door%
  char->cell%
  wall%
  void-cell%
)

;; -----------------------------------------------------------------------------

(require
 racket/class
 "../base/un-types.rkt"
)
(require (only-in "message-queue.rkt"
  enqueue-message!
))
(require (only-in racket/dict
  dict-ref
  dict-set!
))
;; =============================================================================

;; maps printed representations to cell classes
;; for map parsing
(define chars->cell%s
  (make-hash))

(define (register-cell-type! c% char)
  (dict-set! chars->cell%s char c%))

(define (char->cell% char)
  (dict-ref chars->cell%s char))

(define cell% ; some kind of obstacle by default
  (class object%
    (init-field [items    '()]
                [occupant #f]) ; player, monster, etc.
    (define/public (free?)
      #f)
    (define/public (show)
      #\*) ; for debugging
    (define/public (open)
      (enqueue-message! "Can't open that."))
    (define/public (close)
      (enqueue-message! "Can't close that."))
    (super-new)))
(register-cell-type! cell% #\*)

(define empty-cell%
  (class cell%
    (inherit-field occupant)
    (define/override (free?)
      (not occupant))
    (define/override (show)
      (if occupant
          (send (or occupant (raise-user-error 'show)) show)
          #\space))
    (super-new)))
(register-cell-type! empty-cell% #\space)

(define void-cell%
  (class cell%
    (define/override (show) #\.) ; for testing only
    (super-new)))
(register-cell-type! void-cell% #\.)

(define wall%
  (class cell%
    (define/override (show) #\X) ; for testing only
    (super-new)))
(register-cell-type! wall% #\X)

(define double-bar? #t)
(define-syntax-rule (define-wall name single-bar double-bar)
  (begin (define name
           (class wall%
             (define/override (show) (if double-bar? double-bar single-bar))
             (super-new)))
         ;; parse either kind
         (register-cell-type! name single-bar)
         (register-cell-type! name double-bar)
         (provide name)))
(define-wall pillar%           #\+     #\#)
(define-wall vertical-wall%    #\u2502 #\u2551)
(define-wall horizontal-wall%  #\u2500 #\u2550)
(define-wall four-corner-wall% #\u253c #\u256c)
(define-wall north-east-wall%  #\u2510 #\u2557)
(define-wall north-west-wall%  #\u250c #\u2554)
(define-wall south-east-wall%  #\u2518 #\u255d)
(define-wall south-west-wall%  #\u2514 #\u255a)
(define-wall north-tee-wall%   #\u252c #\u2566)
(define-wall south-tee-wall%   #\u2534 #\u2569)
(define-wall east-tee-wall%    #\u2524 #\u2563)
(define-wall west-tee-wall%    #\u251c #\u2560)

(define door%
  (class cell%
    ;(init-field [open? #f])
    (inherit-field occupant)
    (define/override (free?)
      (and #;open? (not occupant)))
    (define/override (open)
      (if #t ;open?
          (enqueue-message! "The door is already open.")
          (void) #;(set! open? #t)))
    (define/override (close)
      (if #t ;open?
          (void) #;(set! open? #f)
          (enqueue-message! "The door is already closed.")))
    (super-new)))

(define vertical-door%
  (class door%
    (inherit-field #;open? occupant)
    (define/override (show)
      (if #t ;open?
          (if occupant (send (or occupant (raise-user-error 'vdoor)) show) #\_)
          #\|))
    (super-new)))
(register-cell-type! vertical-door% #\|)
(register-cell-type! (class vertical-door% (super-new #;[open? #t])) #\_)

(define horizontal-door%
  (class door%
    (inherit-field #;open? occupant)
    (define/override (show)
      (if #t ;open?
          (if occupant (send (or occupant (raise-user-error 'hdoor)) show) #\')
          #\-))
    (super-new)))
(register-cell-type! horizontal-door% #\-)
(register-cell-type! (class horizontal-door% (super-new #;[open? #t])) #\')

;; TODO chests, entry/exit
