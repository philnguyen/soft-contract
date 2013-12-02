(module list
  (provide [reverse ([xs : (listof any)] . -> . (and/c (listof any) (λ (ys) (equal? (empty? xs) (empty? ys)))))]
           [append ((listof any) (listof any) . -> . (listof any))]
           [length ((listof any) . -> . (and/c int? (>=/c 0)))]))

(module functional-queue
  (provide
   [queue? (any . -> . bool?)]
   [make-queue (-> queue/c)]
   [enqueue (queue/c any . -> . queue/c)]
   [enqueue-all (queue/c (listof any) . -> . queue/c)]
   [dequeue ((and/c queue/c (not/c queue-empty?)) . -> . (cons/c any queue/c))]
   [list->queue ((listof any) . -> . queue/c)]
   [queue->list (queue/c . -> . (listof any))]
   [queue-length (queue/c . -> . int?)]
   [queue-empty? (queue/c . -> . bool?)]
   [queue-append (queue/c queue/c . -> . queue/c)]
   [queue-append-list (queue/c (listof any) . -> . queue/c)]
   [queue-extract (queue/c (any . -> . bool?) any . -> . (cons/c any queue/c))]
   [queue/c any])
  
  (define queue/c (struct/c queue (listof any) (listof any)))
  
  (require list)
  
  (struct queue (head tail))
  
  (define (make-queue)
    (queue empty empty))
  
  (define (enqueue q v)
    (queue (queue-head q)
           (cons v (queue-tail q))))
  
  (define (enqueue-all q v)
    (queue (queue-head q)
           (append (reverse v) (queue-tail q))))
  
  (define (shuffle q)
    (if (empty? (queue-head q))
        (queue (reverse (queue-tail q)) empty)
        q))
  
  (define (dequeue q)
    (let [q1 (shuffle q)]
      (cons (car (queue-head q1))
            (queue (cdr (queue-head q1)) (queue-tail q1)))))
  
  (define (list->queue xs)
    (queue xs empty))
  
  (define (queue->list q)
    (append (queue-head q) (reverse (queue-tail q))))
  
  (define (queue-length q)
    (+ (length (queue-head q)) (length (queue-tail q))))
  
  (define (queue-empty? q)
    (and (empty? (queue-head q))
         (empty? (queue-tail q))))
  
  (define (queue-append q1 q2)
    (queue (append (queue-head q1)
                   (append (reverse (queue-tail q1)) (queue-head q2)))
           (queue-tail q2)))
  
  (define (queue-append-list q1 xs)
    (queue (queue-head q1)
           (append (reverse xs) (queue-tail q1))))
  
  (define (queue-extract q predicate default-value)
    (search-head (queue-head q) empty q predicate default-value))
  
  (define (search-head head rejected-head-rev q predicate default-value)
    (cond
      [(empty? head) (search-tail (reverse (queue-tail q)) empty q predicate default-value)]
      [(predicate (car head)) (cons (car head)
                                    (queue (append (reverse rejected-head-rev)
                                                   (cdr head))
                                           (queue-tail q)))]
      [else (search-head (cdr head) (cons (car head) rejected-head-rev) q predicate default-value)]))
  
  (define (search-tail tail rejected-tail-rev q predicate default-value)
    (cond
      [(empty? tail) (cons default-value q)]
      [(predicate (car tail)) (cons (car tail)
                                    (queue (queue-head q)
                                           (append (reverse (cdr tail))
                                                   rejected-tail-rev)))]
      [else (search-tail (cdr tail) (cons (car tail) rejected-tail-rev) q predicate default-value)])))

(require functional-queue)
(amb (queue? •)
     (make-queue)
     (enqueue • •)
     (enqueue-all • •)
     (dequeue •)
     (list->queue •)
     (queue->list •)
     (queue-length •)
     (queue-empty? •)
     (queue-append • •)
     (queue-append-list • •)
     (queue-extract • • •))