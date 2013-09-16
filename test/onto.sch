(module onto
  (provide
   [onto ([callbacks : (listof proc?)] . -> .
         ([f : (or/c false? str? (any . -> . any))] . -> .
         ([obj : (and/c (=>/c (λ (_) (false? f)) (any . -> . any))
                        (=>/c (λ (_) (str? f)) (str? . -> . (any . -> . any))))]
          . -> . (listof proc?))))])
  (define (onto callbacks)
    (λ (f)
      (λ (obj)
        (if (false? f) (cons obj callbacks)
            (let [cb (if (str? f) (obj f) f)]
              (cons (λ () (cb obj)) callbacks)))))))

(require onto)
(((onto •) •) •)
