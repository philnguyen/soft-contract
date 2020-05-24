#lang racket

(struct k1 (elem))
(struct k2 (elem))
(struct k3 (elem))
(struct k4 (elem))
(struct k5 (elem))
(struct k6 (elem))
(struct k7 (elem))
(struct k8 (elem))
(struct k9 (elem))
(struct ka (elem))
(struct kb (elem))
(struct kc (elem))
(struct kd (elem))
(struct ke (elem))
(struct kf (elem))
(struct k0 (elem))

(let loop ([s '()])
  (match (read)
    [1  (loop (k1 s))]
    [2  (loop (k2 s))]
    [3  (loop (k3 s))]
    [4  (loop (k4 s))]
    [5  (loop (k5 s))]
    [6  (loop (k6 s))]
    #;[7  (loop (k7 s))]
    #;[8  (loop (k8 s))]
    #;[9  (loop (k9 s))]
    #;[10 (loop (ka s))]
    #;[11 (loop (kb s))]
    #;[12 (loop (kc s))]
    #;[13 (loop (kd s))]
    #;[14 (loop (ke s))]
    #;[15 (loop (kf s))]
    [_ (loop (k0 s))]))
