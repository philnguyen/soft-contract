(module onto
  (provide
   [onto ([callbacks : (listof proc?)] . -> .
	 ([f : (or/c false? str? (any . -> . any))] . -> .
	 ([obj : (and/c (=>/c (lambda (_) (false? f)) (any . -> . any))
			(=>/c (lambda (_) (str? f)) (str? . -> . (any . -> . any))))]
	  . -> . (listof proc?))))])
  (define (onto callbacks)
    (lambda (f)
      (lambda (obj)
	(if (false? f) (cons obj callbacks)
	    (let [cb (if (str? f) (obj f) f)]
	      (cons (lambda () (cb obj)) callbacks)))))))

(require onto)
(((onto •) •) •)
