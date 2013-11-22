#lang typed/racket
(require "../utils.rkt" "../show.rkt" "../lang.rkt" "../closure.rkt" "../machine.rkt")
(require/typed "../read.rkt" [read-p (Any → .p)])
(require/typed racket/file [file->lines (Path-String → (Listof String))])
(require/typed racket [string-trim (String String → String)])

(define-type Mode (U 'tex 'verbose 'overbose))
(define-type N Nonnegative-Integer)
(define-type Bm-Result (List .ς+ N N N))

(define: mode : Mode 'tex)
(define: files : (Listof String) '())
(define TIMEOUT 30)

(command-line
 #:once-each
 [("-v" "--verbose") "Verbose mode" (set! mode 'verbose)]
 [("-V" "--overbose") "Verbose, with heap dump" (set! mode 'overbose)]
 #:args fnames
 (set! files (if (empty? fnames)
                 (sort (map path->string (directory-list)) string<=?)
                 (#|TODO: ok?|# filter string? fnames))))

(define time-app (cast time-apply ((.p → .ς+) (List .p) → (Values (List .ς+) N N N))))

(: exec : (.p → .ς+) .p → Bm-Result)
(define (exec r p)
  (let-values: ([([r : (List .ς+)] [t1 : N] [t2 : N] [t3 : N]) (time-app r (list p))])
    (list (first r) t1 t2 t3)))

(: a→time : (U #f (List Bm-Result)) → (U Str N))
(define a→time (match-lambda [#f "$\\infty$"]
                             [(list (list _ t _ _)) t]))

(: a→#blame : (U #f (List Bm-Result)) → (U Str N))
(define a→#blame
  (match-lambda
    [#f "-"]
    [(list (list as _ _ _))
     #;(for/sum: : N ([a as] #:when (match? a (.ς (? .blm?) _ _))) 1)
     (set-count (for/set: Any ([a as] #:when (match? a (.ς (? .blm?) _ _))) (.ς-e a)))]))

(: benchmark : (.p → .ς+) .p → (U #f (List Bm-Result)))
(define (benchmark ev p)
  (within-time: Bm-Result TIMEOUT (exec ev p)))

(define-syntax-rule (+! x v) (when (number? v) (set! x (+ x v))))

(when (eq? mode 'tex)
  (printf "Program & Lines & Checks & T1 & B1 & T2 & B2\\\\ \\hline \\hline~n"))
(define-values (L C T1 T2 B1 B2) (values 0 0 0 0 0 0))
(for ([fn files] #:when (regexp-match? #rx"sch$" fn))
  (let* ([lines (for/sum: : Int ([s (file->lines fn)]
                                 #:unless (regexp-match? #rx"^( *)(;.*)*( *)$" s)) 1)]
         [name (string-trim fn ".sch")]
         #;[_ (printf "reading ~a...~n" fn)]
         [p (read-p (file->list fn))]
         [checks (checks# p)])
    (match mode
      [(or 'verbose 'overbose)
       ; only run the improved interpreter for verbose modes
       (match (benchmark ev p)
         [#f (printf "~a: ~a lines, ~a checks, timeout~n~n" name lines checks)]
         [(list (list r t1 t2 t3))
          (printf "~a: ~a lines, ~a checks~ncpu time: ~a, real time: ~a, gc time: ~a~n"
                  name lines checks t1 t2 t3)
          (match mode
            ['verbose (for ([r (for/set: Any ([ς r])
                                 (match-let ([(.ς (? .A? A) σ _) ς])
                                   (show-A σ A)))])
                        (printf "-- ~a~n" r))]
            ['overbose (for ([r (for/set: (Pairof Any Any) ([ς r])
                                  (match-let* ([(.ς (? .A? A) σ _) ς])
                                    (show-Ans σ A)))])
                         (printf "-- ~a~n   ~a~n" (car r) (cdr r)))])
          (printf "~n")])]
      ['tex
       ; compare with disabled interpreter, dump table in latex format
       (let ([a1 (benchmark ev p)]
             [a2 #f]) ; FIXME
         (let ([t1 (a→time a1)]
               [t2 "$\\infty$"] ; FIXME
               [b1 (a→#blame a1)]
               [b2 "$\\infty$"]) ; FIXME
           (+! L lines) (+! C checks)
           (+! T1 t1) (+! T2 t2) (+! B1 b1) (+! B2 b2)
           (printf "~a & ~a & ~a & ~a & ~a & ~a & ~a\\\\~n" name lines checks t1 b1 t2 b2)))])))
(when (eq? mode 'tex)
  (printf "\\hline~n")
  (printf "TOTAL & ~a & ~a & ~a & ~a & ~a & ~a~n" L C T1 B1 T2 B2))
