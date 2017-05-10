#lang racket

;; implement the view (renderer) for the T path finder

(provide 
 ;; type Manage = 
 ;; (Class 
 ;;  ;; disable the given station: #f for sucecss, String for failure
 ;;  [add-to-disabled (-> String [Maybe String]]
 ;;  ;; enable the given station: #f for sucecss, String for failure
 ;;  [remove-from-disabled (-> String [Maybe String]]
 ;;  ;; turn the inquiry strings into stations and find a path from the first to the second  
 ;;  [find (-> String String String)])
 manage%)

;; ===================================================================================================
(require "t-graph.rkt")

;; [X -> Real] [Listof X] -> X
;; argmax also okay 
;; select an [Listof X] that satisfies certain length criteria 
(define selector
  (curry argmin (lambda (p) (length (filter string? p))))) 

;; ---------------------------------------------------------------------------------------------------

(define INTERNAL           "find path: it is impossible to get from ~a to ~a [internal error]")

(define CURRENT-LOCATION   "disambiguate your current location: ~a") 
(define CURRENT-LOCATION-0 "no such station: ~a") 
(define DESTINATION        "disambiguate your destination: ~a")
(define DESTINATION-0      "no such destination: ~a")
(define NO-PATH            "it is currently impossible to reach ~a from ~a via subways")
(define DISABLED           "clarify station to be disabled: ~a")
(define ENABLED            "clarify station to be enabled: ~a")
(define DISABLED-0         "no such station to disable: ~a")
(define ENABLED-0          "no such station to enable: ~a")

(define ENSURE             "---ensure you are on ~a")
(define SWITCH             "---switch from ~a to ~a")

(define manage%
  (class object% 
    (super-new)
    
    (field 
     ;; [instance-of MBTA%]
     [mbta-subways (read-t-graph)]
     ;; [Listof Station]
     [disabled '()])
    
    ;; -----------------------------------------------------------------------------------------------
    (define/public (add-to-disabled s)
      (define station (send mbta-subways station s))
      (cond
        [(string? station) (set! disabled (cons station disabled)) #f]
        [(empty? station) (format DISABLED-0 s)]
        [else (format DISABLED (string-join station))]))
    
    ;; -----------------------------------------------------------------------------------------------
    (define/public (remove-from-disabled s)
      (define station (send mbta-subways station s))
      (cond
        [(string? station) (set! disabled (remove* (list station) disabled)) #f]
        [(empty? station) (format ENABLED-0 s)]
        [else (format ENABLED (string-join station))]))
    
    ;; -----------------------------------------------------------------------------------------------
    (define/public (find from to)
      (define from-station (send mbta-subways station from))
      (define to-station   (send mbta-subways station to))
      (cond
        [(string=? from to) (format "Close your eyes and tap your heels three times. Open your eyes. You will be at ~a." to)]
        [(cons? from-station) (format CURRENT-LOCATION (string-join from-station))]
        [(cons? to-station)   (format DESTINATION (string-join to-station))]
        [(empty? from-station) (format CURRENT-LOCATION-0 from)]
        [(empty? to-station)   (format DESTINATION-0 to)]
        [else 
         (define paths (send mbta-subways find-path from-station to-station))
         (define path* (removed-paths-with-disabled-stations paths))
         (cond
           [(empty? paths) (format INTERNAL from-station to-station)]
           [(empty? path*) (format NO-PATH to-station from-station)]
           [else 
            (define paths-with-switch (for/list ([p path*]) (insert-switch p)))
            (define best-path-as-string*
              (for/list ([station-or-comment (pick-best-path paths-with-switch)])
               (match station-or-comment
                 [`(,name ,line) (string-append name ", take " (send mbta-subways render line))]
                 [(? string? comment) comment])))
            (string-join best-path-as-string* "\n")])]))
    
    ;; -----------------------------------------------------------------------------------------------
    (define/private (removed-paths-with-disabled-stations paths*)
      (for/list ([p paths*] 
                 #:unless ;; any of the disabled stations is on the path 
                 (let ([stations (map first p)]) 
                   (for/or ((s stations)) (member s disabled))))
        p))
    
    ;; type Path* ~~ Path with "switch from Line to Line" strings in the middle 
    
    ;; -----------------------------------------------------------------------------------------------
    ;; [Listof Path*] -> Path*
    (define/private (pick-best-path paths*)
      (selector paths*))
    
    ;; -----------------------------------------------------------------------------------------------
    ;; Path -> Path* 
    (define/private (insert-switch path0)  
      (define start (first path0))
      (define pred-lines0 (second start))
      (define pred-string0 (send mbta-subways render pred-lines0))
      (cons start
            (let loop ([pred-lines pred-lines0][pred-string pred-string0][path (rest path0)])
              (cond
                [(empty? path) '()]
                [else 
                 (define stop (first path))
                 (define name (first stop))
                 (define stop-lines (second stop))
                 (define stop-string (send mbta-subways render stop-lines))
                 (define remainder (loop stop-lines stop-string (rest path)))
                 (cond
                   [(proper-subset? stop-lines pred-lines)
                    (list* (format ENSURE stop-string) stop remainder)]
                   [(set-empty? (set-intersect stop-lines pred-lines)) 
                    (list* (format SWITCH pred-string stop-string) stop remainder)]
                   [else (cons stop remainder)])]))))))
