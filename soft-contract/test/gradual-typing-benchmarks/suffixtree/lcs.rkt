#lang racket/base
;; Some utilities.

(require
 racket/contract
 (except-in "data.rkt" make-label)
 "label.rkt"
 "structs.rkt"
 "ukkonen.rkt")

#|FIXME|# (define make-label ext:make-label)
(define false-thunk (lambda () #f))


;; longest-common-substring: string string -> string
;; Returns the longest common substring between the two strings.
(provide/contract [longest-common-substring (string? string? . -> . string?)])
(define (longest-common-substring s1 s2)
  (label->string (longest-common-sublabel (string->label/with-sentinel s1)
                                          (string->label/with-sentinel s2))))


;; longest-common-sublabel: label label -> label
;;
;; Naive use of suffix trees to find longest common sublabel between
;; two labels.  Note that there's a better way to do this with
;; matching statistics: I'll try using matching statistics as soon
;; as I get this version running.
;;
;; This approach simply adds both labels to a common suffix tree,
;; does a postorder traversal to mark up the inner nodes, and then
;; finds the inner node with the deepest string depth.
(provide/contract [longest-common-sublabel (label/c label/c . -> . label/c)])
(define (longest-common-sublabel label-1 label-2)
  (let ((label-1-marks (make-hasheq))
        (label-2-marks (make-hasheq))
        (deepest-node (node (make-label "no lcs") #f '() #f))
        (deepest-depth 0))
    (letrec
        [
         (main
          (lambda ()
            (let ((tree (make-tree)))
              (tree-add! tree label-1)
              (tree-add! tree label-2)
              (mark-up-inner-nodes! (tree-root tree) 0)
              (path-label deepest-node))))

         (mark-up-inner-nodes!
          (lambda (node depth)
            (if (null? (node-children node))
                (begin (when (label-source-eq? (node-up-label node) label-1)
                         (mark-with-label-1! node))
                       (when (label-source-eq? (node-up-label node) label-2)
                         (mark-with-label-2! node)))
                (begin (for-each
                        (lambda (child)
                          (mark-up-inner-nodes!
                           child
                           (+ depth (label-length (node-up-label child)))))
                        (node-children node))
                       (absorb-children-marks! node depth)))))

         (mark-with-label-1!
          (lambda (node)
            (hash-set! label-1-marks node #t)))

         (mark-with-label-2!
          (lambda (node)
            (hash-set! label-2-marks node #t)))

         (marked-by-label-1?
          (lambda (node)
            (hash-ref label-1-marks node false-thunk)))

         (marked-by-label-2?
          (lambda (node)
            (hash-ref label-2-marks node false-thunk)))
         
         (marked-by-both?
          (lambda (node)
            (and (marked-by-label-1? node)
                 (marked-by-label-2? node))))
         
         (absorb-children-marks!
          (lambda (node depth)
            (let/ec escape
              (for-each (lambda (child)
                          (when (marked-by-label-1? child)
                            (mark-with-label-1! node))
                          (when (marked-by-label-2? child)
                            (mark-with-label-2! node))
                          (when (marked-by-both? node)
                            (escape)))
                        (node-children node)))
            (when (and (marked-by-both? node)
                       (> depth deepest-depth))
              (set! deepest-depth depth)
              (set! deepest-node node))))
         ]
      
      (if (or (= 0 (label-length label-1))
              (= 0 (label-length label-2)))
          (string->label "")
          (begin
            (main))))))



;; path-label: node -> label
;;
;; Returns a new label that represents the path from the tree root
;; to this node.
;;
;; Fixme: optimize the representation of label to be able to do this
;; without much reallocation.  Maybe another label class that uses a
;; rope data structure might be better...  I need to read Hans
;; Boehm's paper on "Ropes, an alternative to strings" to see how
;; much work this would be.
(provide/contract [path-label (node/c . -> . label/c)])
(define path-label
  (letrec
      [(collect-loop
        (lambda (current-node collected-labels total-length)
          (if current-node
              (collect-loop (node-parent current-node)
                            (cons (node-up-label current-node)
                                  collected-labels)
                            (+ total-length
                               (label-length (node-up-label current-node))))
              (build-new-label collected-labels total-length))))

       (vector-blit!
        (lambda (src-label dest-vector dest-offset)
          (let loop ((i 0))
            (when (< i (label-length src-label))
              (vector-set! dest-vector
                           (+ i dest-offset)
                           (label-ref src-label i))
              (loop (add1 i))))))
       
       (build-new-label
        (lambda (labels total-length)
          (let ((vector (make-vector total-length)))
            (let loop ((labels labels)
                       (i 0))
              (if (null? labels)
                  (begin
                    (vector->label vector))
                  (begin
                    (vector-blit! (car labels) vector i)
                    (loop (cdr labels)
                          (+ i (label-length (car labels))))))))))]
    (lambda (node)
      (collect-loop node '() 0))))

