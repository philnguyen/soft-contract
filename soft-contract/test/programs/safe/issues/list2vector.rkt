#lang racket

(define int-list->int-vec list->vector)

(provide/contract
 [int-list->int-vec ((listof integer?) . -> . (vectorof integer?))])
