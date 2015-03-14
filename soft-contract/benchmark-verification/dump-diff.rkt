#lang racket/base

(require racket/system racket/port racket/file racket/format)

(for* ([sub-dir (in-list (directory-list "safe"))]
       [file (in-list (directory-list (format "safe/~a" sub-dir)))]
       [fn (in-value (path->string file))]
       #:when (regexp-match-exact? #rx".*.sch" fn)
       [fn-unsafe (in-value (format "fail-ce/~a/~a" sub-dir fn))]
       #:when (file-exists? fn-unsafe))
  (printf "=========================================~n")
  (printf "Diff between safe/~a/~a and ~a:~n" sub-dir fn fn-unsafe)
  (printf ; hack to play nice with piping
   "~a~n"
   (with-output-to-string
     (λ ()
       (system (format "diff safe/~a/~a ~a" sub-dir fn fn-unsafe))))))
