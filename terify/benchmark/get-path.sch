(module lib
  (provide
   [path/c any/c]
   [dom/c any/c])
  (define path/c
    (->i ([msg (one-of/c "hd" "tl")])
	 (res (msg) (cond [(equal? msg "hd") string?]
			  [else (or/c false? path/c)]))))
  (define dom/c
    (->i ([msg (one-of/c "get-child")])
	 (res (msg) (string? . -> . dom/c)))))

(module get-path
  (provide [get-path (dom/c path/c . -> . dom/c)])
  (require lib)
  (define (get-path root p)
    (while root p))
  (define (while cur path)
    (if (and (not (false? path)) (not (false? cur)))
        (while ((cur "get-child") (path "hd"))
          (path #|HERE|# "hd" #;"tl"))
        cur)))

(require get-path)
(get-path • •)
