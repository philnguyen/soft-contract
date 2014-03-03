(module f
  (provide
   [f ([or/c num? str?] cons? . -> . num?)])
  (define (f input extra)
    (cond
      [(and (num? input) (num? (car extra)))
       (+ input (car extra))]
      [(num? (car extra))
       (+ (str-len input) (car extra))]
      [else 0])))

(require f)
(f • •)