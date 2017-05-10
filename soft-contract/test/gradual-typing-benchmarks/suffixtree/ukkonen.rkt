#lang racket/base

;; Much of this comes from reading Dan Gusfield's Algorithms on
;; strings, trees, and sequences: computer science and computational
;; biology.

(require "structs.rkt"
  (except-in "data.rkt" make-label)
  "label.rkt")

(define dummy-node (node (make-label "dummy") #f '() #f))


(provide skip-count)
;; skip-count: node label -> (values node number)
;;
;; Follows down the node using the skip-count rule until we exhaust
;; the label.  Assumes that there does exist a labeled path starting
;; from the node that exactly matches label.
(define skip-count
  (lambda (node label)
    (skip-count-helper node label 0 (label-length label))))

;; Utility function for skip count, but also visible for those in
;; the know to skip-count from an arbitrary position in label.
(define (skip-count-helper node label k N)
  (define (loop node k)
    (let* ((child (node-find-child node (label-ref label k)))
           (child-label (node-up-label child))
           (child-label-length (label-length child-label))
           (rest-of-chars-left-to-skip (- N k)))
      (if (> rest-of-chars-left-to-skip child-label-length)
          (loop child
                (+ k child-label-length))
          (values child rest-of-chars-left-to-skip))))
  (if (>= k N)
      (values node (label-length (node-up-label node)))
      (loop node k)))






(provide jump-to-suffix)
;; jump-to-suffix: node -> (values node (union boolean number))
;;
;; Given an internal node, jumps to the suffix from that node.
;; According to the theory of suffix trees, such a node will exist
;; in the tree if we follow the Ukkonen construction.  If we had to
;; go up a few characters, returns the number of chars at the suffix
;; end that need to be compared to get the real suffix.

;; If we hit the root, that offset is #f to indicate that we have to
;; start searching the suffix from scratch.
(define (jump-to-suffix node)
  (define PARENT (node-parent node))
  (cond ((node-root? node)
         (values node #f))
        ((node-suffix-link node)
         (begin 
                (let ([node2 (node-suffix-link node)])
                  (unless node2 (error "jump to suffix"))
                  (values node2 0))))
        ((and PARENT (node-root? PARENT))
           (values PARENT #f))
        (else
         (let* ([parent (node-parent node)]
                [sl (begin (unless parent (error "j2s"))
                           (node-suffix-link parent))])
           (unless sl (error "j2s whoahao"))
           (values sl
                   (label-length (node-up-label node)))))))

(provide try-to-set-suffix-edge!)
;; try-to-set-suffix-edge!: node node -> void
;;
;; Sets the suffix edge of from-node directed to to-node if it
;; hasn't been set yet.
(define (try-to-set-suffix-edge! from-node to-node)
  (when (not (node-suffix-link from-node))
    
    (set-node-suffix-link! from-node to-node)))



(provide find-next-extension-point/add-suffix-link!)
;; find-next-extension-point/add-suffix-link!: node label number number ->
;;     (values node number number)
;;
;; Given the last active node where an extension was last made,
;; looks for the next position for extension.  Returns that
;; extension point's node and label offset, as well as the new phase
;; number i.  (Postcondition: (>= i initial-i))
;;
;; The first pass through the loop is a special case: we set the
;; suffix link from node to suffix-node unless we expect it to be
;; done from a splicing extension.
;;
;; If we run off the label (implicit tree), returns (values #f #f #f).
(define (find-next-extension-point/add-suffix-link! node label initial-i j)
  (define (fixed-start suffix-offset)
    (if suffix-offset (- initial-i suffix-offset) j))

  (let*-values
      (((suffix-node suffix-offset) (jump-to-suffix node))
       ((K N) (values (fixed-start suffix-offset)
                      (label-length label))))
    (letrec
        [
         (loop-first
          (lambda (i)
            (loop-general i (lambda (skipped-node skip-offset)
                              (when (node-position-at-end?
                                     skipped-node skip-offset)
                                (try-to-set-suffix-edge!
                                 node skipped-node))))))
         
         (loop-rest
          (lambda (i)
            (loop-general i (lambda (skipped-node skip-offset)
                              (void)))))

         (loop-general
          (lambda (i first-shot)
            (if (>= i N)
                (values #f #f #f)
                (let-values
                    (((skipped-node skipped-offset)
                      (skip-count-helper suffix-node label K i)))
                  (first-shot skipped-node skipped-offset)
                  (if (node-position-at-end? skipped-node skipped-offset)
                      (find-extension-at-end!
                       skipped-node skipped-offset i)
                      (find-extension-in-edge
                       skipped-node skipped-offset i))))))           

         (find-extension-in-edge
          (lambda (skipped-node skip-offset i)
            (if (label-element-equal?
                 (label-ref label i)
                 (label-ref (node-up-label skipped-node)
                            skip-offset))
                (loop-rest (add1 i))
                (values skipped-node skip-offset i))))

         (find-extension-at-end!
          (lambda (skipped-node skip-offset i)
            (if (node-find-child skipped-node (label-ref label i))
                (loop-rest (add1 i))
                (values skipped-node skip-offset i))))
         ]
      (loop-first initial-i))))


(provide extend-at-point!)
;; extend-at-point!: node number label number -> node
(define extend-at-point!
  (letrec [
           (main-logic
            (lambda (node offset label i)
              (if (should-extend-as-leaf? node offset)
                  (attach-as-leaf! node label i)
                  (splice-with-internal-node! node offset label i))))

           (should-extend-as-leaf?
            (lambda (node offset)
              (node-position-at-end? node offset)))

           (attach-as-leaf!
            (lambda (node label i)
              (let ((leaf (node-add-leaf! node (sublabel label i))))
                
                node)))

           (splice-with-internal-node!
            (lambda (node offset label i)
              ;; otherwise, extend by splicing
              (let-values (((split-node leaf)
                            (node-up-splice-leaf!
                             node offset (sublabel label i))))
                split-node)))
           ]
    main-logic))





(provide suffix-tree-add!)
;; suffix-tree-add!: tree label -> void
;; Adds a new label and its suffixes to the suffix tree.
;; Precondition: label is nonempty.
(define suffix-tree-add!
  (letrec
      [
       (do-construction!
        (lambda (tree label)
          (let* ((pair (add-first-suffix! tree label))
                 (starting-node (car pair))
                 (starting-offset (cdr pair)))
            (add-rest-suffixes! label starting-node starting-offset)
            )))
       
       (add-first-suffix!
        (let
            [
             (matched-at-node
              (lambda (node)
                (report-implicit-tree-constructed)))
             (matched-in-node
              (lambda (node offset)
                (report-implicit-tree-constructed)))
             (mismatched-at-node
              (lambda (node label label-offset)
                (let ((leaf (node-add-leaf!
                             node (sublabel label label-offset))))
                  (cons node label-offset))))
             (mismatched-in-node
              (lambda (node offset label label-offset)
                (let-values (((joint leaf)
                              (node-up-splice-leaf!
                               node offset
                               (sublabel label label-offset))))
                  (cons joint label-offset))))
             ]
          (lambda (tree label)
            (node-follow/k
             (suffix-tree-root tree) label
             matched-at-node
             matched-in-node
             mismatched-at-node
             mismatched-in-node))))

       (add-rest-suffixes!
        (lambda (label starting-node starting-offset)
          (add-rest-suffixes-loop!
           label
           (label-length label)
           (max starting-offset 1)
           1
           starting-node)))
       
       (add-rest-suffixes-loop!
        (lambda (label N i j active-node)
          (when (< j N)
            (let-values (((next-extension-node next-extension-offset i*)
                          (find-next-extension-point/add-suffix-link!
                           active-node label i j)))
              (if i*
                  (begin
                    (let ((new-active-node
                           (extend-at-point! next-extension-node
                                             next-extension-offset
                                             label i*)))
                      (try-to-set-suffix-edge! active-node new-active-node)
                      (add-rest-suffixes-loop!
                       label N
                       (max i* (add1 j)) (add1 j) new-active-node)))
                  (begin
                    (report-implicit-tree-constructed)
                    (void)))))))

       
       (report-implicit-tree-constructed
        (lambda ()
          (cons dummy-node 0)))
       ]
    
    do-construction!))

;; -- from suffixtree.rkt

(provide tree-add!)
(define tree-add! suffix-tree-add!)


