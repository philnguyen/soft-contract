#lang racket/base

;; Command-line UI for exploring decompiled bytecode.
;; (Use `raco make` to generate bytecode)

(provide
 init)

(require require-typed-check
         (only-in racket/string string-split string-join string-trim)
         racket/match)

(require "zo-string.rkt"
 "zo-transition.rkt"
 "zo-find.rkt"
 compiler/zo-parse)

;; -----------------------------------------------------------------------------

;; --- constants & contracts

;; when set, print extra debugging information
(define DEBUG   #f)
;; For aesthetic purposes
(define VERSION 1.0)
(define VNAME   "vortex")
;(define-type Context (U zo (Listof zo) (Listof result)))
;(define-type History (Listof Context))
;(define-type History* (Listof History))

;; --- API functions

;; Entry point to the REPL, expects command-line arguments passed as a list.
;; In the future, there may be more entry points.
(define (init args)
  (match args
    ['#()
     (print-usage)]
    ;; Catch --help flag, and any others
    [(? has-any-flags?) (print-usage)]
    [(vector fname)
     (filename->shell fname)]
    [(vector fname args ...)
     (find-all fname args)]))

;; --- Commands (could go in their own file)

(struct command (
  name
  num-args
  aliases
  help-msg
)
#:transparent)
;(define-type Command command)
(define index? integer?)

(define ALST (command "alst"
                      0
                      (list "a" "alias" "aliases")
                      "Print command aliases"))
(define BACK (command "back"
                      0
                      (list "b" "up" "u" ".." "../" "cd .." "cd ../")
                      "Move up to the previous context"))
(define DIVE (command "dive"
                      1
                      (list "d" "cd" "next" "step")
                      "Step into struct field ARG"))
(define FIND (command "find"
                      1
                      (list "f" "query" "search" "look")
                      "Search the current subtree for structs with the name ARG"))
(define HELP (command "help"
                      0
                      (list "h" "-h" "--h" "-help" "--help")
                      "Print this message"))
(define INFO (command "info"
                      0
                      (list "i" "ls" "print" "p" "show")
                      "Show information about current context"))
(define JUMP (command "jump"
                      0
                      (list "j" "warp" "top")
                      "Revert to last saved position"))
(define SAVE (command "save"
                      0
                      (list "mark")
                      "Save the current context as jump target"))
(define QUIT (command "quit"
                      0
                      (list "q" "exit" "leave" "bye")
                      "Exit the interpreter"))
(define COMMANDS
  (list ALST BACK DIVE FIND HELP INFO JUMP SAVE QUIT))

(define ((cmd? c) str)
  (define splt (string-split str))
  (or
   ;; Special cases
   (and (string=? "back" (command-name c))
        (member? str (list "cd .." "cd ../")))
   ;; Everything else
   (and
    ;; Has the right number of arguments
    (= (sub1 (length splt))
       (command-num-args c))
    ;; First word matches command name (or an alias)
    (or (string=? (car splt) (command-name c))
        (member?   (car splt) (command-aliases c))))))

;; --- REPL

;; Start REPL from a filename
(define (filename->shell name)
  (print-info (format "Loading bytecode file '~a'..." name))
  (call-with-input-file name
    (lambda (port )
      (print-info "Parsing bytecode...")
      (define ctx  (zo-parse port))
      (print-info "Parsing complete!")
      (print-welcome)
      ((repl ctx '() '()) '()))))

(define (zo->shell z)
  ;; (-> zo? void?)
  (print-welcome)
  ((repl z '() '()) '()))

;; Split a path like "cd ../BLAH/.." into a list of commands "cd ..; cd BLAH; cd .."
(define (split-cd cmd*)
  ;; (-> (listof string?) (listof string?))
  (match cmd*
    ['() '()]
    [(cons cd-cmd rest)
     #:when (starts-with? cd-cmd "cd ")
     ;; Split "cd " commands by "/"
     (append
      (map (lambda (x) (string-append "cd " x)) (string-split (substring cd-cmd 3) "/"))
      (split-cd rest))]
    [(cons cmd rest)
     ;; Leave other commands alone
     (cons cmd (split-cd rest))]))

;; The REPL loop. Process a command using context `ctx` and history `hist`.
(define ((repl ctx hist pre-hist) cmd*)
  (when DEBUG (print-history hist))
  (match cmd*
    ['()
     (print-prompt ctx)
     (define ln (read-line))
     (if (eof-object? ln)
         (error 'zo-shell:repl "EOF: you have penetrated me")
         ((repl ctx hist pre-hist)
          (split-cd (for/list
                                ([str (in-list (string-split ln ";"))])
                      (string-trim str)))))]
    [(cons (? (cmd? ALST) raw) cmd*)
     (print-alias) ((repl ctx hist pre-hist) cmd*)]
    [(cons (? (cmd? BACK) raw) cmd*)
     ((call-with-values (lambda () (back raw ctx hist pre-hist)) repl) cmd*)]
    [(cons (? (cmd? DIVE) raw) cmd*)
     ((call-with-values (lambda () (dive raw ctx hist pre-hist)) repl) cmd*)]
    [(cons (? (cmd? FIND) raw) cmd*)
     ((call-with-values (lambda () (find raw ctx hist pre-hist)) repl) cmd*)]
    [(cons (? (cmd? HELP) raw) cmd*)
     (begin (print-help) ((repl ctx hist pre-hist) cmd*))]
    [(cons (? (cmd? INFO) raw) cmd*)
     (begin (print-context ctx) ((repl ctx hist pre-hist) cmd*))]
    [(cons (? (cmd? JUMP) raw) cmd*)
     ((call-with-values (lambda () (jump raw ctx hist pre-hist)) repl) cmd*)]
    [(cons (? (cmd? SAVE) raw) cmd*)
     ((call-with-values (lambda () (save raw ctx hist pre-hist)) repl) cmd*)]
    [(cons (? (cmd? QUIT) raw) cmd*)
     (print-goodbye)]
    [(cons raw cmd*)
     (begin (print-unknown raw) ((repl ctx hist pre-hist) cmd*))]))

;; --- command implementations

;; 2015-01-23: Warn about possible-unexpected behavior
(define BACK-WARNING
  (string-append
   "BACK removing most recent 'save' mark. "
   "Be sure to save if you want to continue exploring search result."))

;; Step back to a previous context, if any, and reduce the history.
;; Try popping from `hist`, fall back to list-of-histories `pre-hist`.
(define (back raw ctx hist pre-hist)
  (match (list hist pre-hist)
    [(list '() '())
     ;; Nothing to pop from
     (print-unknown raw)
     (values ctx hist pre-hist)]
    [(list '() _)
     ;; Pop from pre-history
     (displayln BACK-WARNING)
     (define-values (hist* pre-hist*) (pop pre-hist))
     (back raw ctx hist* pre-hist*)]
    [_
     (define-values (ctx* hist*) (pop hist))
     (values ctx* hist* pre-hist)]))

;; Search context `ctx` for a new context matching string `raw`.
;; Push `ctx` onto the stack `hist` on success.
(define (dive raw ctx hist pre-hist)
  (define arg (split-snd raw))
  (define-values (ctx* hist*)
    (cond
     [(not arg)
      ;; Failed to parse argument,
      (print-unknown raw)
      (values ctx hist)]
     [(list? ctx)
      ;; Context is a list, try accessing by index
      (dive-list ctx hist arg)]
     [(zo?   ctx)
      ;; Context is a zo, try looking up field
      (dive-zo   ctx hist arg)]
     [else
      ;; Should never happen! REPL controls the context.
      (error 'zo-shell:dive (format "Invalid context '~a'" ctx))]))
  ;; Return pre-hist unchanged
  (values ctx* hist* pre-hist))

;; Parse the string `arg` to an integer n.
;; If n is within the bounds of the list `ctx`,
;; push `ctx` onto the stack `hist` and return the n-th element of `ctx`.
;; Otherwise, return `ctx` and `hist` unchanged.
(define (dive-list ctx hist arg)
  (define index (string->number arg))
  (cond [(or (not index) (not (index? index)) (< index 0) (>= index (length ctx)))
         ;; Index out of bounds, or not a number. Cannot dive.
         (print-unknown (format "dive ~a" arg))
         (values ctx hist)]
        [else
         ;; Select from list,
         (define res (list-ref ctx index))
         ;; If list elements are search results, current `hist` can be safely ignored.
         (if (result? res)
             (values (result-zo res) (result-path res))
             (values res             (push hist ctx)))]))

;; Use the string `field` to access a field in the zo struct `ctx`.
;; If the field exists and denotes another zo struct, return that
;; struct and push `ctx` on to the stack `hist`.
;; Otherwise, return `ctx` and `hist` unchanged.
(define (dive-zo ctx hist field)
  (define-values (ctx* success?) (zo-transition ctx field))
  (cond
   [success?
    (values ctx* (push hist ctx))]
   [else
    (print-unknown (format "dive ~a" field))
    (values ctx hist)]))

;; Parse argument, then search for & save results.
(define (find raw ctx hist pre-hist)
  (define arg (split-snd raw))
  (cond [(and arg (zo? ctx))
         (define results (zo-find ctx arg))
         (printf "FIND returned ~a results\n" (length results))
         (match results
           ['()
            ;; No results, don't make a save mark
            (values ctx hist pre-hist)]
           [_
            ;; Success! Show the results and save them, to allow jumps
            (printf "FIND automatically saving context\n")
            (print-context results)
            (save "" results (push hist ctx) pre-hist)])]
        [else
         (print-unknown raw)
         (values ctx hist pre-hist)]))

;; Jump back to a previously-saved location, if any.
(define (jump raw ctx hist pre-hist)
  (match pre-hist
    ['()
     ;; Nothing to jump to
     (print-unknown raw)
     (values ctx hist pre-hist)]
    [_
     (define-values (hist* pre-hist*) (pop pre-hist))
     (back raw ctx hist* pre-hist*)]))

;; Save the current context and history to the pre-history
;; For now, erases current history.
(define (save raw ctx hist pre-hist)
  (values ctx '() (push pre-hist (push hist ctx))))

;; --- history manipulation

;; Add the context `ctx` to the stack `hist`.
(define (push hist ctx)
  (cons ctx hist))

;; Remove the top context from the stack `hist`.
;; Return the popped value and tail of `hist`.
;; Callers must avoid calling `pop` on empty stacks.
(define (pop hist)
  (values (car hist) (cdr hist)))

;; --- print

(define (print-alias)
  ;; (-> void?)
  (displayln "At your service. Command aliases:")
  (displayln (string-join
    (for/list ([cmd  COMMANDS])
      (format "  ~a        ~a"
              (command-name cmd)
              (string-join (command-aliases cmd))))))
  (newline))

;; Print a history object.
(define (print-history hist)
  ;; (-> history? void?)
  (printf "History is: ~a\n" hist))

;; Print a help message for the REPL.
(define (print-help)
  ;; (-> void?)
  (displayln "At your service. Available commands:")
  (displayln
   (string-join
    (for/list  ([cmd COMMANDS])
      (format "  ~a~a    ~a"
              (command-name cmd)
              (if (= 1 (command-num-args cmd)) " ARG" "    ") ;; hack
              (command-help-msg cmd)))
    "\n")))

;; Print a context.
(define (print-context ctx)
  ;; (-> context? void?)
  (match ctx
    [(? zo?)
     (displayln (zo->string ctx))]
    ['()
     (displayln "'()")]
    [(cons x _)
     (define z (if (result? x) (result-zo x) x))
     (printf "~a[~a]\n"
             (zo->string z #:deep? #f)
             (length ctx))]
    [_
     (error 'zo-shell:info (format "Unknown context '~a'"  ctx))]))

;; Print an error message (after receiving an undefined/invalid command).
(define (print-unknown raw)
  (printf "'~a' not permitted.\n" raw))

;; Print a goodbye message (when the user exits the REPL).
(define (print-goodbye)
  (printf "Ascending to second-level meditation. Goodbye.\n\n"))

;; Print a debugging message.
(define (print-debug str)
  ;; (-> string? void?)
  (printf "DEBUG: ~a\n" str))

;; Print a welcome message (when the user enters the REPL).
(define (print-welcome)
  (display
   (format "\033[1;34m--- Welcome to the .zo shell, version ~a '~a' ---\033[0;0m\n" VERSION VNAME)))

;; Print the REPL prompt.
(define (print-prompt ctx)
  (define tag (cond [(list? ctx) (format "[~a]" (length ctx))]
                    [(zo? ctx)   (format "(~a)" (car (zo->spec ctx)))]
                    [else ""]))
  (display (string-append tag " \033[1;32mzo> \033[0;0m")))

;; Print an informative message.
(define (print-info str)
  ;; (-> string? void?)
  (printf "INFO: ~a\n" str))

;; Print a warning.
(define (print-warn str)
  ;; (-> string? void?)
  (printf "WARN: ~a\n" str))

;; Print an error message.
(define (print-error str)
  ;; (-> string? void?)
  (printf "ERROR: ~a\n" str))

;; Print usage information.
(define USAGE
  "Usage: zo-shell <OPTIONS> FILE.zo")
(define (print-usage)
  (displayln USAGE))

;; --- misc

(define (member? s str*)
  (if (member s str*) #t #f))

;; Check if second arg is a prefix of the first
(define (starts-with? str prefix)
  ;; (-> string? string? boolean?)
  (and (<= (string-length prefix)
           (string-length str))
       (for/and ([c1 (in-string str)]
                 [c2 (in-string prefix)])
         (char=? c1 c2))))

(define (find-all name args #:limit [lim #f])
  (print-info (format "Loading bytecode file '~a'..." name))
  (call-with-input-file name
    (lambda (port)
      (print-info "Parsing bytecode...")
      (define ctx (zo-parse port))
      (print-info "Parsing complete! Searching...")
      (for ([arg (in-list args)])
        (printf "FIND '~a' : " arg)
        (printf "~a results\n" (length (zo-find ctx arg #:limit lim))))
      (displayln "All done!"))))

;; Split the string `raw` by whitespace and
;; return the second element of the split, if any.
;; Otherwise return `#f`.
(define (split-snd raw)
  (define splt (string-split raw))
  (match splt
    [(list _ x)       x]
    [(list _ x ys ...) (print-warn (format "Ignoring extra arguments: '~a'" ys))
                       x]
    [_ #f]))

;; True if the vector contains any command-line flags.
;; All flags begin with a hyphen, -
(define (has-any-flags? v)
  ;; (-> (vectorof string) boolean?)
  (for/or ([str (in-vector v)])
    (and (< 0 (string-length str))
         (eq? #\- (string-ref str 0)))))

