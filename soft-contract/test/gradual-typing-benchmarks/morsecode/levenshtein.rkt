;;; @Package     levenshtein
;;; @Subtitle    Levenshtein Distance Metric in Scheme
;;; @HomePage    http://www.neilvandyke.org/levenshtein-scheme/
;;; @Author      Neil Van Dyke
;;; @Version     0.6
;;; @Date        2009-03-14
;;; @PLaneT      neil/levenshtein:1:3

;; $Id: levenshtein.ss,v 1.49 2009/03/14 07:32:45 neilpair Exp $

;;; @legal
;;; Copyright @copyright{} 2004--2009 Neil Van Dyke.  This program is Free
;;; Software; you can redistribute it and/or modify it under the terms of the
;;; GNU Lesser General Public License as published by the Free Software
;;; Foundation; either version 3 of the License (LGPL 3), or (at your option)
;;; any later version.  This program is distributed in the hope that it will be
;;; useful, but without any warranty; without even the implied warranty of
;;; merchantability or fitness for a particular purpose.  See
;;; @indicateurl{http://www.gnu.org/licenses/} for details.  For other licenses
;;; and consulting, please contact the author.
;;; @end legal

#lang racket/base

;;; @section Introduction
;;;
;;; This is a Scheme implementation of the @dfn{Levenshtein Distance}
;;; algorithm, which is an @dfn{edit distance} metric of string similarity, due
;;; to Vladimir Levenshtein.  The Levenshtein Distance is a function of two
;;; strings that represents a count of single-character insertions, deletions,
;;; and substitions that will change the first string to the second.  More
;;; information is available in
;;; @uref{http://www.nist.gov/dads/HTML/Levenshtein.html, NIST DADS} and the
;;; Michael Gilleland article, ``@uref{http://www.merriampark.com/ld.htm,
;;; Levenshtein Distance in Three Flavors}.''
;;;
;;; This implementation is modeled after a
;;; @uref{http://www.mgilleland.com/ld/ldperl2.htm, space-efficient Perl
;;; implementation} by Jorge Mas Trullenque.  It has been written in R5RS
;;; Scheme, and extended to support heterogeneous combinations of Scheme types
;;; (strings, lists, vectors), user-supplied predicate functions, and
;;; optionally reusable scratch vectors.

(define (%identity x) x)

(define (%string-empty? v) (zero? (string-length v)))
(define (%vector-empty? v) (zero? (vector-length v)))

(define (%string->vector s)
  (list->vector (string->list s)))

;;; @section Basic Comparisons

;;; In the current implementation, all comparisons are done internally via
;;; vectors.

;;; @defproc vector-levenshtein/predicate/get-scratch a b pred get-scratch
;;;
;;; Few, if any, programs will use this procedure directly.  This is like
;;; @code{vector-levenshtein/predicate}, but allows @var{get-scratch} to be
;;; specified.  @var{get-scratch} is a procedure of one term, @i{n}, that
;;; yields a vector of length @i{n} or greater, which is used for
;;; record-keeping during execution of the Levenshtein algorithm.
;;; @code{make-vector} can be used for @var{get-scratch}, although some
;;; programs comparing a large size or quantity of vectors may wish to reuse a
;;; record-keeping vector, rather than each time allocating a new one that will
;;; need to be garbage-collected.

(define (vector-levenshtein/predicate/get-scratch a b pred get-scratch)
  (let ((a-len (vector-length a))
        (b-len (vector-length b)))
    (cond ((zero? a-len) b-len)
          ((zero? b-len) a-len)
          (else
           (let ((w    (get-scratch (+ 1 b-len)))
                 (next #f))
             (let fill ((k b-len))
               (vector-set! w k k)
               (or (zero? k) (fill (- k 1))))
             (let loop-i ((i 0))
               (if (= i a-len)
                   next
                   (let ((a-i (vector-ref a i)))
                     (let loop-j ((j   0)
                                  (cur (+ 1 i)))
                       (if (= j b-len)
                           (begin (vector-set! w b-len next)
                                  (loop-i (+ 1 i)))
                           ;; TODO: Make these costs parameters.
                           (begin (set! next (min (+ 1 (vector-ref w (+ 1 j)))
                                                  (+ 1 cur)
                                                  (if (pred a-i
                                                            (vector-ref b j))
                                                      (vector-ref w j)
                                                      (+ 1 (vector-ref w j)))))
                                  (vector-set! w j cur)
                                  (loop-j (+ 1 j) next))))))))))))

;;; @defproc  vector-levenshtein/predicate a b pred
;;; @defprocx vector-levenshtein/eq        a b
;;; @defprocx vector-levenshtein/eqv       a b
;;; @defprocx vector-levenshtein/equal     a b
;;; @defprocx vector-levenshtein           a b
;;;
;;; Calculate the Levenshtein Distance of vectors @var{a} and @var{b}.
;;; @var{pred} is the predicate procedure for determining if two elements are
;;; equal.  The @code{/eq}, @code{/eqv}, and @code{/equal} variants correspond
;;; to the standard equivalence predicates, @code{eq?}, @code{eqv?}, and
;;; @code{equal?}.  @code{vector-levenshtein} is an alias for
;;; @code{vector-levenshtein/equal}.
;;;
;;; @lisp
;;; (vector-levenshtein '#(6 6 6) '#(6 35 6 24 6 32)) @result{} 3
;;; @end lisp

(define (vector-levenshtein/predicate a b pred)
  (vector-levenshtein/predicate/get-scratch a b pred make-vector))

(define (vector-levenshtein/eq    a b)
  (vector-levenshtein/predicate a b eq?))
(define (vector-levenshtein/eqv   a b)
  (vector-levenshtein/predicate a b eqv?))
(define (vector-levenshtein/equal a b)
  (vector-levenshtein/predicate a b equal?))

(define (vector-levenshtein a b) (vector-levenshtein/equal a b))

;;; @defproc  list-levenshtein/predicate a b pred
;;; @defprocx list-levenshtein/eq        a b
;;; @defprocx list-levenshtein/eqv       a b
;;; @defprocx list-levenshtein/equal     a b
;;; @defprocx list-levenshtein           a b
;;;
;;; Calculate the Levenshtein Distance of lists @var{a} and @var{b}.
;;; @var{pred} is the predicate procedure for determining if two elements are
;;; equal.  The @code{/eq}, @code{/eqv}, and @code{/equal} variants correspond
;;; to the standard equivalence predicates, @code{eq?}, @code{eqv?}, and
;;; @code{equal?}.  @code{list-levenshtein} is an alias for
;;; @code{list-levenshtein/equal}.  Note that comparison of lists is less
;;; efficient than comparison of vectors.
;;;
;;; @lisp
;;; (list-levenshtein/eq '(b c e x f y) '(a b c d e f)) @result{} 4
;;; @end lisp

(define (list-levenshtein/predicate a b pred)
  (cond ((null? a) (length b))
        ((null? b) (length a))
        (else (vector-levenshtein/predicate (list->vector a)
                                            (list->vector b)
                                            pred))))

(define (list-levenshtein/eq    a b) (list-levenshtein/predicate a b eq?))
(define (list-levenshtein/eqv   a b) (list-levenshtein/predicate a b eqv?))
(define (list-levenshtein/equal a b) (list-levenshtein/predicate a b equal?))

(define (list-levenshtein       a b) (list-levenshtein/equal     a b))

;; TODO: Maybe make a version that does the O(n) access to the list elements in
;;       exchange for not allocating a vector.

;;; @defproc string-levenshtein a b
;;;
;;; Calculate the Levenshtein Distance of strings @var{a} and @var{b}.
;;;
;;; @lisp
;;; (string-levenshtein "adresse" "address") @result{} 2
;;; @end lisp

(define (string-levenshtein a b)
  ;; TODO: Maybe make a version that doesn't convert to vectors but also
  ;;       doesn't do lots of string-refs.
  (cond ((zero? (string-length a)) (string-length b))
        ((zero? (string-length b)) (string-length a))
        (else (vector-levenshtein/eqv
               (%string->vector a)
               (%string->vector b)))))

(define (%string-levenshtein/predicate a b pred)
  (cond ((zero? (string-length a)) (string-length b))
        ((zero? (string-length b)) (string-length a))
        (else (vector-levenshtein/predicate
               (%string->vector a)
               (%string->vector b)
               pred))))

;;; @section Type-Coercing Comparisons

;;; Procedures @code{levenshtein} and @code{levenshtein/predicate} provide a
;;; convenient interface for comparing a combination of vectors, lists, and
;;; strings, the types of which might not be known until runtime.

;;; @defproc levenshtein/predicate a b pred
;;;
;;; Calculates the Levenshtein Distance of two objects @var{a} and @var{b},
;;; which are vectors, lists, or strings.  @var{a} and @var{b} need not be of
;;; the same type.  @var{pred} is the element equivalence predicate used.
;;;
;;; @lisp
;;; (levenshtein/predicate '#(#\A #\B #\C #\D)
;;;                        "aBXcD"
;;;                        char-ci=?)
;;; @result{} 1
;;; @end lisp

;;;bg too hard
;(define levenshtein/predicate
;  ;; TODO: Change this to a let-syntax.
;  (let ((foo (lambda (a b pred a-emp a-len a-vec)
;               (let ((bar (lambda (b-emp b-len b-vec)
;                            (if (b-emp b)
;                                (a-len a)
;                                (vector-levenshtein/predicate (a-vec a)
;                                                              (b-vec b)
;                                                              pred)))))
;                 (cond ((vector? b) (bar %vector-empty?
;                                         vector-length
;                                         %identity))
;                       ((string? b) (bar %string-empty?
;                                         string-length
;                                         %string->vector))
;                       ((list?   b) (bar null? length list->vector))
;                       (else (error "term 2 must be vector, list, or string:"
;                                    b)))))))
;    (lambda (a b pred)
;      (cond ((vector? a) (if (vector? b)
;                             (vector-levenshtein/predicate a b pred)
;                             (foo a b pred
;                                  %vector-empty?
;                                  vector-length
;                                  %identity)))
;            ((string? a) (if (string? b)
;                             (%string-levenshtein/predicate
;                              a b pred)
;                             (foo a b pred
;                                  %string-empty?
;                                  string-length
;                                  %string->vector)))
;            ((list?   a) (if (list? b)
;                             (list-levenshtein/predicate a b pred)
;                             (foo a b pred null? length list->vector)))
;            (else (error "term 1 must be vector, list, or string:" a))))))

;;; @defproc levenshtein a b
;;;
;;; Calculate the levenshtein distance of @var{a} and @var{b}, in a similar
;;; manner as using @code{levenshtein/predicate} with @code{equal?} as the
;;; predicate.
;;;
;;; @lisp
;;; (define g '#(#\g #\u #\m #\b #\o))
;;;
;;; (levenshtein g "gambol")  @result{} 2
;;; (levenshtein g "dumbo")   @result{} 1
;;; (levenshtein g "umbrage") @result{} 5
;;; @end lisp

;;;bg
;(define (levenshtein a b)
;  (if (and (string? a) (string? b))
;      (string-levenshtein a b)
;      (levenshtein/predicate a b equal?)))
(define (levenshtein a b)
  (cond [(and (string? a) (string? b))
         (string-levenshtein a b)]
        [(and (vector? a) (vector? b))
         (vector-levenshtein a b)]
        [(and (list? a) (list? b))
         (list-levenshtein a b)]
        [else (error "levenshtein")]))

;; @appendix Trullenque Perl Implementation
;;
;; For reference, the implementation from [Trullenque] is reproduced here.
;;
;; @verbatim
;; sub levenshtein($$){
;;   my @A=split //, lc shift;
;;   my @B=split //, lc shift;
;;   my @W=(0..@B);
;;   my ($i, $j, $cur, $next);
;;   for $i (0..$#A){
;;     $cur=$i+1;
;;     for $j (0..$#B){
;;             $next=min(
;;                     $W[$j+1]+1,
;;                     $cur+1,
;;                     ($A[$i] ne $B[$j])+$W[$j]
;;             );
;;             $W[$j]=$cur;
;;             $cur=$next;
;;     }
;;     $W[@B]=$next;
;;   }
;;   return $next;
;; }
;;
;; sub min($$$){
;;   if ($_[0] < $_[2]){ pop @_; } else { shift @_; }
;;   return $_[0] < $_[1]? $_[0]:$_[1];
;; }
;; @end verbatim

;;; @unnumberedsec History
;;;
;;; @table @asis
;;;
;;; @item Version 0.6 --- 2009-03-14 -- PLaneT @code{(1 3)}
;;; Documentation fixes.
;;;
;;; @item Version 0.5 --- 2009-02-24 -- PLaneT @code{(1 2)}
;;; License is now LGPL 3.  Tests moved out of main file.  Converted to
;;; author's new Scheme administration system.
;;;
;;; @item Version 0.4 --- 2005-07-10 -- PLaneT @code{(1 1)}
;;; Added Testeez tests.
;;;
;;; @item Version 0.3 --- 2005-07-09 -- PLaneT @code{(1 0)}
;;; PLaneT release, and minor documentation changes.
;;;
;;; @item Version 0.2 --- 2004-07-06
;;; Documentation changes.
;;;
;;; @item Version 0.1 --- 2004-05-13
;;; First release.  Tested only lightly, and today @emph{is} the 13th, so
;;; @i{caveat emptor}.
;;;
;;; @end table

(provide
 levenshtein
 ;levenshtein/predicate
 list-levenshtein
 list-levenshtein/eq
 list-levenshtein/equal
 list-levenshtein/eqv
 list-levenshtein/predicate
 string-levenshtein
 vector-levenshtein
 vector-levenshtein/eq
 vector-levenshtein/equal
 vector-levenshtein/eqv
 vector-levenshtein/predicate
 vector-levenshtein/predicate/get-scratch)
