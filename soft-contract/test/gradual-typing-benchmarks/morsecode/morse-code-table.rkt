#lang racket/base

;; Copyright 2014 John Clements, except the portion that comes from wikipedia!

(provide char-table)
(require racket/match)

(define wikipedia-text
#<<#
| {{Audio-nohelp|A morse code.ogg|A}} || '''·&nbsp;–'''
| {{Audio-nohelp|J morse code.ogg|J}} || '''·&nbsp;–&nbsp;–&nbsp;–'''
| {{Audio-nohelp|S morse code.ogg|S}} || '''·&nbsp;·&nbsp;·'''
| {{Audio-nohelp|1 number morse code.ogg|1}} || '''·&nbsp;–&nbsp;–&nbsp;–&nbsp;–'''
| [[Full stop|Period]] [.] || '''·&nbsp;–&nbsp;·&nbsp;–&nbsp;·&nbsp;–'''
| [[Colon (punctuation)|Colon]] [:] || '''–&nbsp;–&nbsp;–&nbsp;·&nbsp;·&nbsp;·'''
| {{Audio-nohelp|B morse code.ogg|B}} || '''–&nbsp;·&nbsp;·&nbsp;·'''
| {{Audio-nohelp|K morse code.ogg|K}} || '''–&nbsp;·&nbsp;–'''
| {{Audio-nohelp|T morse code.ogg|T}} || '''–'''
| {{Audio-nohelp|2 number morse code.ogg|2}} || '''·&nbsp;·&nbsp;–&nbsp;–&nbsp;–'''
| [[Comma (punctuation)|Comma]] [,] || '''–&nbsp;–&nbsp;·&nbsp;·&nbsp;–&nbsp;–'''
| [[Semicolon]] [;] || '''–&nbsp;·&nbsp;–&nbsp;·&nbsp;–&nbsp;·'''
| {{Audio-nohelp|C morse code.ogg|C}} || '''–&nbsp;·&nbsp;–&nbsp;·'''
| {{Audio-nohelp|L morse code.ogg|L}} || '''·&nbsp;–&nbsp;·&nbsp;·'''
| {{Audio-nohelp|U morse code.ogg|U}} || '''·&nbsp;·&nbsp;–'''
| {{Audio-nohelp|3 number morse code.ogg|3}} || '''·&nbsp;·&nbsp;·&nbsp;–&nbsp;–'''
| [[Question mark]] [?] || '''·&nbsp;·&nbsp;–&nbsp;–&nbsp;·&nbsp;·'''
| [[Equal sign|Double dash]] [=] || '''–&nbsp;·&nbsp;·&nbsp;·&nbsp;–'''
| {{Audio-nohelp|D morse code.ogg|D}} || '''–&nbsp;·&nbsp;·'''
| {{Audio-nohelp|M morse code.ogg|M}} || '''–&nbsp;–'''
| {{Audio-nohelp|V morse code.ogg|V}} || '''·&nbsp;·&nbsp;·&nbsp;–'''
| {{Audio-nohelp|4 number morse code.ogg|4}} || '''·&nbsp;·&nbsp;·&nbsp;·&nbsp;–'''
| [[Apostrophe (punctuation)|Apostrophe]] ['] || '''·&nbsp;–&nbsp;–&nbsp;–&nbsp;–&nbsp;·'''
| [[Plus and minus signs|Plus]] [+] || '''·&nbsp;–&nbsp;·&nbsp;–&nbsp;·'''
| {{Audio-nohelp|E morse code.ogg|E}} || '''·'''
| {{Audio-nohelp|N morse code.ogg|N}} || '''–&nbsp;·'''
| {{Audio-nohelp|W morse code.ogg|W}} || '''·&nbsp;–&nbsp;–'''
| {{Audio-nohelp|5 number morse code.ogg|5}} || '''·&nbsp;·&nbsp;·&nbsp;·&nbsp;·'''
| [[Exclamation mark]] [!] || '''–&nbsp;·&nbsp;–&nbsp;·&nbsp;–&nbsp;–'''
| [[Plus and minus signs|Minus]] [-] || '''–&nbsp;·&nbsp;·&nbsp;·&nbsp;·&nbsp;–'''
| {{Audio-nohelp|F morse code.ogg|F}} || '''·&nbsp;·&nbsp;–&nbsp;·'''
| {{Audio-nohelp|O morse code.ogg|O}} || '''–&nbsp;–&nbsp;–'''
| {{Audio-nohelp|X morse code.ogg|X}} || '''–&nbsp;·&nbsp;·&nbsp;–'''
| {{Audio-nohelp|6 number morse code.ogg|6}} || '''–&nbsp;·&nbsp;·&nbsp;·&nbsp;·'''
| [[Slash (punctuation)|Slash]] [/] || '''–&nbsp;·&nbsp;·&nbsp;–&nbsp;·'''
| [[Underscore]] [_] || '''·&nbsp;·&nbsp;–&nbsp;–&nbsp;·&nbsp;–'''
| {{Audio-nohelp|G morse code.ogg|G}} || '''–&nbsp;–&nbsp;·'''
| {{Audio-nohelp|P morse code.ogg|P}} || '''·&nbsp;–&nbsp;–&nbsp;·'''
| {{Audio-nohelp|Y morse code.ogg|Y}} || '''–&nbsp;·&nbsp;–&nbsp;–'''
| {{Audio-nohelp|7 number morse code.ogg|7}} || '''–&nbsp;–&nbsp;·&nbsp;·&nbsp;·'''
| [[Parenthesis open]] [(] || '''–&nbsp;·&nbsp;–&nbsp;–&nbsp;·'''
| [[Quotation mark]] ["] || '''·&nbsp;–&nbsp;·&nbsp;·&nbsp;–&nbsp;·'''
| {{Audio-nohelp|H morse code.ogg|H}} || '''·&nbsp;·&nbsp;·&nbsp;·'''
| {{Audio-nohelp|Q morse code.ogg|Q}} || '''–&nbsp;–&nbsp;·&nbsp;–'''
| {{Audio-nohelp|Z morse code.ogg|Z}} || '''–&nbsp;–&nbsp;·&nbsp;·'''
| {{Audio-nohelp|8 number morse code.ogg|8}} || '''–&nbsp;–&nbsp;–&nbsp;·&nbsp;·'''
| [[Parenthesis close]] [)] || '''–&nbsp;·&nbsp;–&nbsp;–&nbsp;·&nbsp;–'''
| [[Dollar sign]] [$] || '''·&nbsp;·&nbsp;·&nbsp;–&nbsp;·&nbsp;·&nbsp;–'''
| {{Audio-nohelp|I morse code.ogg|I}} || '''·&nbsp;·'''
| {{Audio-nohelp|R morse code.ogg|R}} || '''·&nbsp;–&nbsp;·'''
| {{Audio-nohelp|0 number morse code.ogg|0}} || '''–&nbsp;–&nbsp;–&nbsp;–&nbsp;–'''
| {{Audio-nohelp|9 number morse code.ogg|9}} || '''–&nbsp;–&nbsp;–&nbsp;–&nbsp;·'''
| [[Ampersand]] [&] || '''·&nbsp;–&nbsp;·&nbsp;·&nbsp;·'''
| [[Commercial at|At sign]] [@] || '''·&nbsp;–&nbsp;–&nbsp;·&nbsp;–&nbsp;·'''
#
)

;; the lines of the wikipedia text
(define lines (regexp-split #px"\n" wikipedia-text))

;; replace some unicode chars with ascii ones in the wikipedia patterns
(define (clean-pattern pat)
  (regexp-replace*
   #px"·"
   (regexp-replace*
    #px"–"
    (apply string-append (regexp-split (regexp-quote "&nbsp;") pat))
    "-")
   "."))

;; parse the wikipedia text into a table mapping characters to their morse code representations
(define char-table
(make-hash
 (for/list
   ([l lines])
    (match 
        (regexp-match #px"^\\| \\{\\{[^|]*\\|[^|]*\\|(.)\\}\\} \\|\\| '''([^']*)'''" l)
      [#f
       (match 
           (regexp-match #px"^\\| \\[\\[[^]]*\\]\\] \\[([^]]*)\\] \\|\\| '''([^']*)'''" l)
         [(list whole-match char pattern)
          (cond [(and char pattern)
                 (cons (car (string->list char)) (clean-pattern pattern))]
                [else
                 (error 'char-table "broken regexp")])]
         [#f (error 'char-table "what goes here?")])
       ]
      [(list whole-match letter pattern) 
       (cond [(and letter pattern)
              (cons (char-downcase (car (string->list letter))) (clean-pattern pattern))]
             [else (error 'char-table "broken regexp 2")])]))))
