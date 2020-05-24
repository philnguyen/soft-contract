#lang racket/base
(require racket/contract)
(struct foo ())
(provide (contract-out (struct foo ())))

