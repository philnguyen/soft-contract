(module utils racket
  (provide/contract [loop (any/c . -> . (λ (_) #f))]
		    [STATE/C any/c])
  (define (loop x) (loop #f))
  (define STATE/C (one-of/c 'init 'opened 'closed 'ignore)))

(module read racket
  (provide/contract
   [readit ((one-of/c 'opened 'ignore) . -> . (one-of/c 'opened 'ignore))]
   [read_ (any/c STATE/C . -> . STATE/C)])
  (require (submod ".." utils))
  (define (readit st)
    (if (equal? 'opened st) 'opened 'ignore))
  (define (read_ x st)
    (if x (readit st) st)))

(module close racket
  (provide/contract
   [closeit (STATE/C . -> . (one-of/c 'closed 'ignore))]
   [close_ (any/c STATE/C . -> . STATE/C)])
  (require (submod ".." utils))
  (define (closeit st)
    (cond
      [(equal? 'opened st) 'closed]
      [(equal? 'ignore st) 'ignore]
      [else (begin (loop #f) 0)]))
  (define (close_ x st)
    (if x (closeit st) st)))

(module f racket
  (provide/contract [f (any/c any/c STATE/C . -> . any/c)])
  (require (submod ".." read) (submod ".." close) (submod ".." utils))
  (define (f x y st)
    (begin (close_ y (close_ x st))
           (f x y (read_ y (read_ x st))))))

(module next racket
  (provide/contract [next (STATE/C . -> . STATE/C)])
  (require (submod ".." utils))
  (define (next st) (if (equal? 'init st) 'opened 'ignore)))

(module g racket
  (provide/contract [g (integer? any/c STATE/C . -> . any/c)])
  (require (submod ".." f) (submod ".." next) (submod ".." utils))
  (define (g b3 x st)
    (if (> b3 0) (f x #t (next st)) (f x #f st))))

(module main racket
  (provide/contract [main (integer? integer? . -> . any/c)])
  (require (submod ".." g) (submod ".." utils))
  (define (main b2 b3)
    (begin
      (if (> b2 0) (g b3 #t 'opened) (g b3 #f 'init))
      'unit)))

(require 'main)
(main • •)
