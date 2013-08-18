(abbrev/c STATE/C (one-of/c 'init 'opened 'closed 'ignore))

(module loop (provide [loop (any . -> . (λ (_) #f))])
  (define (loop x) (loop #f)))

(module read
  (provide [readit ((one-of/c 'opened 'ignore) . -> . (one-of/c 'opened 'ignore))]
           [read_ (any STATE/C . -> . STATE/C)])
  (define (readit st)
    (if (equal? 'opened st) 'opened 'ignore))
  (define (read_ x st)
    (if x (readit st) st)))

(module close
  (provide [closeit (STATE/C . -> . (one-of/c 'closed 'ignore))]
           [close_ (any STATE/C . -> . STATE/C)])
  (require loop)
  (define (closeit st)
    (cond
      [(equal? 'opened st) 'closed]
      [(equal? 'ignore st) 'ignore]
      [else (begin (loop #f) 0)]))
  (define (close_ x st)
    (if x (closeit st) st)))

(module f (provide [f (any any STATE/C . -> . any)])
  (require read close)
  (define (f x y st)
    (begin (close_ y (close_ x st))
           (f x y (read_ y (read_ x st))))))

(module next (provide [next (STATE/C . -> . STATE/C)])
  (define (next st) (if (equal? 'init st) 'opened 'ignore)))

(module g (provide [g (int? any STATE/C . -> . any)])
  (require f next)
  (define (g b3 x st)
    (if (> b3 0) (f x #t (next st)) (f x #f st))))

(module main (provide [main (int? int? . -> . any)])
  (require g)
  (define (main b2 b3)
    (begin
      (if (> b2 0) (g b3 #t 'opened) (g b3 #f 'init))
      'unit)))

(require main)
(main • •)