(module lib racket
  (provide
   (contract-out
    [string->list (string? . -> . (listof integer?))]
    [list->string ((listof integer?) . -> . string?)]
    [substring (->i ([str string?])
		    (res (str)
			 (->i ([start (and/c integer? (>=/c 0))]
			       [end (and/c
				     integer?
				     (>=/c 0)
				     (</c (string-length str)))])
			      (res (start end)
				   (and/c string? (λ (s) (>= (string-length s) (- end start))))))))])))

(module f racket
  (provide (contract-out [split-snd (-> string? string?)]))
  (require (submod ".." lib))

  (define (split-snd x)
    ((substring x) 2 3)))
