(module negate
  (provide [negate ((or/c integer? boolean?) . -> . (or/c integer? boolean?))])
  (define (negate x)
    (if (integer? x) (- 0 x) (not x))))

(module maybe-apply
  (provide [maybe-apply (integer? (or/c false? (integer? . -> . integer?)) . -> . integer?)])
  (define (maybe-apply x f)
    (if (false? f) x (f x))))

(module opaque (provide [n integer?]))

(module main
  (provide [main (-> integer?)])
  (require maybe-apply negate opaque)
  (define (main)
    (maybe-apply n negate)))

(require negate maybe-apply main)
(amb (negate •) (maybe-apply • •) (main))
