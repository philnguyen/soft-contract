(module onto
  (provide
   [onto ([A : (any . -> . bool?)] . -> . ; poor man's quantifier
         ([callbacks : (listof proc?)] . -> .
         ([f : (or/c false? str? (A . -> . any))] . -> .
         ([obj : (and/c
                  A
                  (cond
                   [(false? f) (any . -> . any)]
                   [(str? f) ([k : any] . -> . (if (equal? k f) (A . -> . any) any))]
                   [else any]))]
          . -> . (listof proc?)))))])
  (define (onto A)
    (λ (callbacks)
      (λ (f)
        (λ (obj)
          (if (false? f) (cons obj callbacks)
              (let [cb (if (str? f) (obj f) f)]
                (cons (λ () (cb obj)) callbacks))))))))

(require onto)
((((onto •) •) •) •)