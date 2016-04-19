#lang racket

;; This version differs from the original version in that tests are converted
;; to contracted exports

(define-syntax-rule (rec f e)
  (letrec ([f e]) f))

(define node (lambda (v l r) (vector v l r)))
(define tree-foreach
  (lambda (t f)
    (let foreach ([t t])
      (match t
        ['() '()]
        [(vector v l r) (begin (f v) (foreach l) (foreach r))]))))
(define tree-forall?
  (lambda (t f)
    (let forall? ([t t])
      (match t
        ['() #t]
        [(vector v l r) (and (f v) (forall? l) (forall? r))]))))
(define tree-exists?
  (lambda (t f)
    (not (tree-forall? t (lambda (x) (not (f x)))))))   
(define tree-fold
  (lambda (t b f)
    (let fold ([t t])
      (match t
        ['() b]
        [(vector v l r) (f v (fold l) (fold r))]))))   
(define tree-size
  (lambda (t)
    (tree-fold t 0 (lambda (_ l r) (+ 1 l r)))))   
(define tree->list
  (lambda (t)
    (let ->list ([t t] [accum '()])
      (match t
        ['() accum]
        [(vector v l r) (->list l (cons v (->list r accum)))]))))
;;------------------------------
;;         Splay Trees
;;------------------------------
(define splay
  (lambda (t k)
    (let splay ([t t])
      (match t
        [(vector v l r)
         (cond
           [(= k v) t]
           [(< k v)
            (match l
              ['() t]
              [(vector v1 l1 r1)
               (cond
		 [(= k v1) (node v1 l1 (node v r1 r))]
		 [(< k v1)
		  (if (null? l1)
		      (node v1 '() (node v r1 r))
		      (match-let ([(vector v2 l2 r2) (splay l1)])
			(node v2 l2 (node v1 r2 (node v r1 r)))))]
		 [(null? r1)  (node v1 l1 (node v '() r))]
		 [else (match-let ([(vector v2 l2 r2) (splay r1)])
			 (node v2 (node v1 l1 l2)
			       (node v r2 r)))])])]
           [(null? r)  t]
           [else (match-let ([(vector v1 l1 r1) r])
                   (cond
		     [(= k v1) (node v1 (node v l l1) r1)]
		     [(< k v1)
		      (if (null? l1)
			  (node v1 (node v l '()) r1)
			  (match-let ([(vector v2 l2 r2) (splay l1)])
			    (node v2 (node v l l2)
				  (node v1 r2 r1))))]
		     [(null? r1)  (node v1 (node v l l1) '())]
		     [else (match-let ([(vector v2 l2 r2) (splay r1)])
			     (node v2
				   (node v1 (node v l l1) l2)
				   r2))]))])]))))
(define splay-to-max
  (rec splay
       (match-lambda
         [(vector v l '()) (vector v l)]
         [(vector v l (vector v1 l1 '())) (vector v1 (node v l l1))]
         [(vector v l (vector v1 l1 r1))
          (match-let ([(vector v2 l2) (splay r1)])
            (vector v2 (node v1 (node v l l1) l2)))])))

(define splay-to-min
  (rec splay
       (match-lambda
         [(vector v '() r) (vector v r)]
         [(vector v (vector v1 '() r1) r) (vector v1 (node v r1 r))]
         [(vector v (vector v1 l1 r1) r)
          (match-let ([(vector v2 r2) (splay l1)])
            (vector v2 (node v1 r2 (node v r1 r))))])))
(define join
  (match-lambda*
    [(list '() '())  '()]
    [(list '() t)   t]
    [(list t '())   t]
    [(list t t1)   (match-let ([(vector v l) (splay-to-max t)])
                     (node v l t1))]))
(define split
  (lambda (t x no yes)
    (match t
      [(vector x1 l r)
       (cond
         [(= x x1) (yes l r)]
         [(< x x1) (no l (node x1 '() r))]
         [else (no (node x1 l '()) r)])])))
(define splay-and-split
  (lambda (t x no yes)
    (if (null? t)
        (no '() '())
        (split (splay t x) x no yes))))
(define splay-keep-all
  (lambda (t p?)
    (tree-fold t '()
               (lambda (v l r)
                 (if (p? v) (node v l r) (join l r))))))
(define splay-combine
  (lambda (base alone-left alone-right left both)
    (rec combine
         (match-lambda*
           [(list '() '())  base]
           [(list '() t)   (alone-right t)]
           [(list t '())   (alone-left t)]
           [(list (vector x l r) t)
            (let ([continue
                   (lambda (c)
                     (lambda (l1 r1)
                       (c x (lambda () (combine l l1))
                          (lambda () (combine r r1)))))])
              (splay-and-split
               t x (continue left) (continue both)))]))))
;;------------------------------
;;             Sets             
;;------------------------------
;; a set is a boxed tree
(define set box)
(define set-tree! set-box!)
(define tree unbox)
(define empty (lambda () (set '())))
(define empty? (lambda (s) (null? (tree s))))
(define singleton (lambda (x) (set (node x '() '()))))
(define size (lambda (s) (tree-size (tree s))))
(define extremum
  (lambda (splay-to node)
    (lambda (s)
      (let ([t (tree s)])
        (if (null? t)
            (error 'ordset-extremum "empty set")  
            (match-let ([(vector x lr) (splay-to t)])
              (set-tree! s (node x lr))
              x))))))
(define min (extremum splay-to-min (lambda (x r) (node x '() r))))
(define max (extremum splay-to-max (lambda (x l) (node x l '()))))
(define set-split
  (lambda (s x no yes)
    (let ([t (tree s)])
      (if (null? t)
          (no '() '())
          (let ([t (splay (tree s) x)])
            (set-tree! s t)
            (split t x no yes))))))
(define contains?
  (lambda (s x)
    (set-split s x (lambda _ #f) (lambda _ #t))))
(define add
  (lambda (s x)
    (set-split s x
               (lambda (l r) (set (node x l r)))
               (lambda _ s))))
(define remove
  (lambda (s x)
    (set-split
     s x (lambda _ s)
     (lambda (l r)
       (set (cond
              [(null? l) r]
              [(null? r) l]
              [else (match-let ([(vector v l) (splay-to-max l)])
                      (set-tree! s (node x (node v l '()) r))
                      (node v l r))]))))))
(define subset (lambda (s p?) (set (splay-keep-all (tree s) p?))))
(define set-combine
  (lambda (base alone no yes top)
    (lambda (left both right)
      (let* ([node (lambda (b) (if b yes no))]
             [combine (splay-combine
                       base (alone left) (alone right)
                       (node left) (node both))])
        (lambda (s s1)
          (top (combine (tree s) (tree s1))))))))

(define combine-bool
  (set-combine #t (lambda (b) (lambda _ b))
               (lambda _ #f)
               (lambda (_ l r) (and (l) (r)))
               (lambda (b) b)))
(define subset?   (combine-bool #f #t #t))
(define superset? (combine-bool #t #t #f))
(define disjoint? (combine-bool #t #f #t))
(define splay-equal?    (combine-bool #f #t #f))
(define combine-sets
  (set-combine
   '() (lambda (b) (if b (lambda (t) t) (lambda _ '())))
   (lambda (_ l r) (join (l) (r)))
   (lambda (x l r) (node x (l) (r)))
   set))
(define union        (combine-sets #t #t #t))
(define intersection (combine-sets #f #t #f))
(define difference   (combine-sets #t #f #f))
(define list->
  (lambda (l)
    (let loop ([l l] [s (empty)])
      (if (null? l)
          s
          (loop (cdr l) (add s (car l)))))))
(define ->list (lambda (s) (tree->list (tree s))))
(define exists? (lambda (s p?) (tree-exists? (tree s) p?)))
(define forall? (lambda (s p?) (tree-forall? (tree s) p?)))
(define foreach (lambda (s f) (tree-foreach (tree s) f)))

;----------------------------------------
;                Tests
;----------------------------------------  
(define odds (list-> (list 1 3 5 7 9)))
(define evens (list-> (list 2 4 6 8 10)))
(define mix (list-> (list 1 2 4 7 8)))

(define empty-empty? (empty? empty))
(define not-empty-odds? (not (empty? odds)))
(define empty-size-0? (= 0 (size empty)))
(define odd-size-5? (= 5 (size odds)))
(define odd-=-odd? (splay-equal? odds odds))
(define odd-≠-even? (not (splay-equal? odds evens)))
(define max-evens-10? (= 10 (max evens)))
(define min-odds-1? (= 1 (min odds)))
(define odds-contains-5? (contains? odds 5))
(define odds-not-contains-6? (not (contains? odds 6)))
(define odds-subset-odds? (subset? odds odds))
(define mix-not-subset-odds? (not (subset? mix odds)))
(define mix-subset-odds-evens? (subset? mix (union odds evens)))
(define add-odds-superset? (superset? (add odds 11) odds))
(define odds-superset? (superset? odds (difference mix evens)))
(define difference-disjoint? (disjoint? (difference mix odds) odds))
(define evens-not-disjoint? (not (disjoint? evens evens)))
(define remove-supersets? (superset? odds (remove odds 1)))
(define remove-same-equal? (splay-equal? odds (remove odds 2)))
(define all-odds-odd? (forall? odds (lambda (n) (odd? n))))
(define all-evens-even? (forall? evens (lambda (n) (even? n))))
(define subset-mix-even? (subset? (subset mix (lambda (n) (even? n))) evens))
(define sum-odds-25?
  (let ([sum 0])
    (foreach odds (lambda (x) (set! sum (+ sum x))))
    (= sum 25)))
(define intersect-subset? (subset? (intersection mix odds) odds))

(provide ;; provide useless "proof terms"
 (contract-out
  [empty-empty? values]
  [not-empty-odds? values]
  [empty-size-0? values]
  [odd-size-5? values]
  [odd-=-odd? values]
  [odd-≠-even? values]
  [max-evens-10? values]
  [min-odds-1? values]
  [odds-contains-5? values]
  [odds-not-contains-6? values]
  [odds-subset-odds? values]
  [mix-not-subset-odds? values]
  [mix-subset-odds-evens? values]
  [add-odds-superset? values]
  [odds-superset? values]
  [difference-disjoint? values]
  [evens-not-disjoint? values]
  [remove-supersets? values]
  [remove-same-equal? values]
  [all-odds-odd? values]
  [all-evens-even? values]
  [subset-mix-even? values]
  [sum-odds-25? values]
  [intersect-subset? values]))
