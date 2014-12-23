#lang typed/racket/base
(require racket/match racket/set racket/cmdline racket/list racket/set racket/bool
         (only-in racket/file file->list)
         "../../utils.rkt" "../../lang.rkt" "../../show.rkt" "../../runtime.rkt" "../machine.rkt"
         (only-in "../../query-cvc4.rkt" [query cvc4])
         (only-in "../../query-z3.rkt" [query z3])
         (only-in "../model.rkt" [model z3/model])
         (only-in "../../provability.rkt" ext-solver model))
(require/typed "../read.rkt" [read-p (Any → .p)])
(require/typed racket/file [file->lines (Path-String → (Listof String))])
(require/typed racket [string-trim (String String → String)])

(define-type Mode (U 'tex 'verbose 'overbose))
(define-type N Nonnegative-Integer)
(define-type Bm-Result (List (Option .Ans) N N N))

(define mode : Mode 'verbose)
(define files : (Listof String) '())
(define solver : (.σ .V .V → .R) z3)
(define TIMEOUT 120)
#;(define ITER 1)
#;(: avg : Real → Real)
#;(define (avg x) (* (/ x ITER) 1.0))

(ext-solver z3 #;cvc4)
(command-line
 #:once-each
 [("-v" "--verbose") "Verbose mode" (set! mode 'verbose)]
 [("-V" "--overbose") "Verbose, with heap dump" (set! mode 'overbose)]
 [("-z" "--z3") "User Z3 instead of CVC4" (ext-solver z3)]
 #:args fnames
 (set! files (if (empty? fnames)
                 (sort (map path->string (directory-list)) string<=?)
                 (#|TODO: ok?|# filter string? fnames))))

(define time-app
  (cast time-apply ((.p → (Option .Ans)) (List .p) → (Values (List (Option .Ans)) N N N))))

(: benchmark : (.p → (Option .Ans)) .p → (U #f (List Bm-Result)))
(define (benchmark ev p)
  (collect-garbage)
  (collect-garbage)
  (within-time: Bm-Result
                TIMEOUT
                (let-values ([([r : (List (Option .Ans))] [t1 : N] [t2 : N] [t3 : N])
                              (time-app ev (list p))])
                  (list (first r) t1 t2 t3))))

(define-syntax-rule (+! x v) (when (number? v) (set! x (+ x v))))

#;(when (eq? mode 'tex)
   (printf "Program & Lines & Checks & T1 & B1 & T2 & B2\\\\ \\hline \\hline~n"))
#;(define-values (L C T1 T2 B1 B2) (values 0 0 0 0 0 0))
(for ([fn files] #:when (regexp-match? #rx"sch$" fn))
  (define lines ; count non-empty, non-comment lines
    (for/sum : Integer ([s (file->lines fn)] #:unless (regexp-match? #rx"^( *)(;.*)*( *)$" s)) 1))
  (define name (string-trim fn ".sch"))
  (define p (read-p (file->list fn)))
  (define checks (checks# p))
  (match mode
    [(or 'verbose 'overbose)
     (printf "~a: " name)
     ;; Only run the improved interpreter for verbose modes
     (match (benchmark ev p)
       [#f (printf "~a lines, ~a checks, timeout~n~n" lines checks)]
       [(list (list r t1 t2 t3))
        (printf "~a lines, ~a checks, ~ams~n"
                lines checks t1)
        (cond
         [(false? r) (printf "   (CORRECT)~n")]
         [else
          (match-define (cons σ (? .blm? blm)) r)
          (printf "-- ~a~n" (show-A σ blm))
          #;(printf "Store:~n~a~n" (show-σ σ))
          (define σ′ (model p σ))
          #;(printf "Store′:~n~a~n" (show-σ σ′))
          (define σ′′ (z3/model σ′))
          #;(printf "Store′′:~n~a~n" (if σ′′ (show-σ σ′′) #f))
          (when (.σ? σ′′)
            (printf "   Counterexample:~n~a~n" (show-ce p σ′′)))])
        (printf "~n")])]
    #;['tex
    ;; Compare with disabled interpreter, dump table in latex format
    (let ([a1 (benchmark ev p)]
    [a2 #f]) ; FIXME
    (let ([t1 (a→time a1)]
    [t2 "$\\infty$"] ; FIXME
    [b1 (a→#blame a1)]
    [b2 "$\\infty$"]) ; FIXME
    (+! L lines) (+! C checks)
    (+! T1 t1) (+! T2 t2) (+! B1 b1) (+! B2 b2)
    (printf "~a & ~a & ~a & ~a & ~a & ~a & ~a\\\\~n" name lines checks t1 b1 t2 b2)))]))
#;(when (eq? mode 'tex)
(printf "\\hline~n")
(printf "TOTAL & ~a & ~a & ~a & ~a & ~a & ~a~n" L C T1 B1 T2 B2))
