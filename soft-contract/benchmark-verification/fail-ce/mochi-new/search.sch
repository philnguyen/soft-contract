(module search racket
  (provide/contract
   [main (integer? integer? . -> . (not/c false?))])
  
  ;; Option = #f | integer?
  
  (define (exists test f n m)
    (cond [(< n m)
           (if (test (f n)) n (exists test f (+ n 1) m))]
          [else #f]))

  (define (mult3 n) (* 3 n))

  (define (main n m)
    (let* ([test (λ (x) (= x m))]
           [res (exists test mult3 0 n)])
      (if res (and (< #|HERE|# 0 res) (< res n)) #t))))

(require 'search)
(main • •)
