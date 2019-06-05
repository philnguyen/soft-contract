#lang racket/base

(provide (struct-out posn-2d)
         (struct-out posn-3d))
(struct posn-2d (x y))
(struct posn-3d (x y z))
