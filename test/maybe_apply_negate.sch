(module negate
  (provide
   [negate ((or/c int? bool?) . -> . (or/c int? bool?))])
  (define (negate x)
    (if (int? x) (- 0 x) (not x))))

(module maybe-apply
  (provide
   [maybe-apply (int? (or/c false? (int? . -> . int?)) . -> . int?)])
  (define (maybe-apply x f)
    (if (false? f) x (f x))))

(module opaque (provide [n int?]))

(module main
  (provide [main (-> int?)])
  (require maybe-apply negate opaque)
  (define (main)
    (maybe-apply n negate)))

(require negate maybe-apply main)
(amb (negate •) (maybe-apply • •) (main))
