(module base•
  (provide [handle-evt (any any . -> . any #|TODO|#)]
           [system-idle-evt (-> any)]
           [max (real? real? . -> . real?)]))

(module hash
  (provide
   [hash? any]
   [hash (-> hash?)]
   [hash-ref (hash? any (-> any) . -> . any)]
   [hash-set (hash? any any . -> . hash?)]
   [hash-remove (hash? any . -> . hash?)])
  (define hash? (listof cons?))
  (define (hash) empty)
  (define (hash-ref h k default)
    (cond
      [(empty? h) (default)]
      [else (let* ([kv (car h)]
                   [ki (car kv)])
              (if (equal? k kv) (cdr kv)
                  (hash-ref (cdr h) k default)))]))
  (define (hash-set h k v)
    (cond
      [(empty? h) (list (cons k v))]
      [else (let ([kv (car h)]
                  [hr (cdr h)])
              (if (equal? (car kv) k) (cons (cons k v) hr)
                  (cons kv (hash-set hr k v))))]))
  (define (hash-remove h k)
    (cond
      [(empty? h) empty]
      [else (let ([kv (car h)]
                  [hr (cdr h)])
              (if (equal? (car kv) k) hr
                  (cons kv (hash-remove hr k))))])))

(module list
  (provide [reverse ([xs : (listof any)] . -> . (and/c (listof any) (λ (ys) (equal? (empty? xs) (empty? ys)))))]
           [append ((listof any) (listof any) . -> . (listof any))]
           [length ((listof any) . -> . (and/c int? (>=/c 0)))]
           [filter-map ((any . -> . any) (listof any) . -> . (listof any))]
           [map ((any . -> . any) (listof any) . -> . (listof any))]
           [ormap ((any . -> . bool?) (listof any) . -> . (listof any))]
           [foldl ((any any . -> . any) any (listof any) . -> . any)]
           [flatten (any . -> . (listof any))])
  (define (filter-map f xs)
    (cond [(empty? xs) empty]
          [else (let ([y (f (car xs))])
                  (if y (cons y (filter-map f (cdr xs)))
                      (filter-map f (cdr xs))))]))
  (define (map f xs)
    (cond [(empty? xs) empty]
          [else (cons (f (car xs)) (map f (cdr xs)))]))
  
  (define (foldl f z xs)
    (cond [(empty? xs) z]
          [else (foldl f (f (car xs) z) cdr xs)]))
  
  (define (append xs ys)
    (if (empty? xs) ys
        (cons (car xs) (append (cdr xs) ys))))
  (define (flatten x)
    (cond
      [(empty? x) empty]
      [(cons? x) (append [flatten (car x)] [flatten (cdr x)])]
      [else (cons x empty)]))
  
  (define (ormap p? xs)
    (if (empty? xs) #f
        (or (p? (car xs)) (ormap p? (cdr xs))))))

(module functional-queue
  (provide
   [queue? (any . -> . bool?)]
   [make-queue (-> queue/c)]
   [enqueue (queue/c any . -> . queue/c)]
   [enqueue-all (queue/c (listof any) . -> . queue/c)]
   [dequeue ((and/c queue/c (not/c queue-empty?)) . -> . (cons/c any queue/c))]
   [list->queue ((listof any) . -> . queue/c)]
   [queue->list (queue/c . -> . (listof any))]
   [queue-length (queue/c . -> . int?)]
   [queue-empty? (queue/c . -> . bool?)]
   [queue-append (queue/c queue/c . -> . queue/c)]
   [queue-append-list (queue/c (listof any) . -> . queue/c)]
   [queue-extract (queue/c (any . -> . bool?) any . -> . (cons/c any queue/c))]
   [queue/c any])
  
  (define queue/c (struct/c queue (listof any) (listof any)))
  
  (require list)
  
  (struct queue (head tail))
  
  (define (make-queue)
    (queue empty empty))
  
  (define (enqueue q v)
    (queue (queue-head q)
           (cons v (queue-tail q))))
  
  (define (enqueue-all q v)
    (queue (queue-head q)
           (append (reverse v) (queue-tail q))))
  
  (define (shuffle q)
    (if (empty? (queue-head q))
        (queue (reverse (queue-tail q)) empty)
        q))
  
  (define (dequeue q)
    (let [q1 (shuffle q)]
      (cons (car (queue-head q1))
            (queue (cdr (queue-head q1)) (queue-tail q1)))))
  
  (define (list->queue xs)
    (queue xs empty))
  
  (define (queue->list q)
    (append (queue-head q) (reverse (queue-tail q))))
  
  (define (queue-length q)
    (+ (length (queue-head q)) (length (queue-tail q))))
  
  (define (queue-empty? q)
    (and (empty? (queue-head q))
         (empty? (queue-tail q))))
  
  (define (queue-append q1 q2)
    (queue (append (queue-head q1)
                   (append (reverse (queue-tail q1)) (queue-head q2)))
           (queue-tail q2)))
  
  (define (queue-append-list q1 xs)
    (queue (queue-head q1)
           (append (reverse xs) (queue-tail q1))))
  
  (define (queue-extract q predicate default-value)
    (search-head (queue-head q) empty q predicate default-value))
  
  (define (search-head head rejected-head-rev q predicate default-value)
    (cond
      [(empty? head) (search-tail (reverse (queue-tail q)) empty q predicate default-value)]
      [(predicate (car head)) (cons (car head)
                                    (queue (append (reverse rejected-head-rev)
                                                   (cdr head))
                                           (queue-tail q)))]
      [else (search-head (cdr head) (cons (car head) rejected-head-rev) q predicate default-value)]))
  
  (define (search-tail tail rejected-tail-rev q predicate default-value)
    (cond
      [(empty? tail) (cons default-value q)]
      [(predicate (car tail)) (cons (car tail)
                                    (queue (queue-head q)
                                           (append (reverse (cdr tail))
                                                   rejected-tail-rev)))]
      [else (search-tail (cdr tail) (cons (car tail) rejected-tail-rev) q predicate default-value)])))

(module pattern
  (provide
   [pattern? (any . -> . bool?)]
   [wildcard? (any . -> . bool?)]
   [? (-> wildcard?)]
   [specialization? (pattern? pattern? . -> . bool?)]
   [ground? (any . -> . bool?)]
   [intersect (#|cheat|#pattern? pattern? (any . -> . any) (-> any) . -> . any)]
   [intersect? (any any . -> . bool?)]
   [pattern-subst (pattern? pattern? pattern? . -> . pattern?)])
  
  (define (intersection a b ks kf)
    (amb (ks •) (kf))))

(module core•
  (provide [pid-stack• (listof int?)]))

(module core
  (provide
   [struct route ([subscription? bool?] [pattern pattern?] [meta-level int?] [level int?])]
   [struct routing-update ([routes (listof any)])]
   [struct message ([body any] [meta-level int?] [feedback? bool?])]
   [struct quit ()]
   [struct process ([routes (listof any)] [behavior any] [state any])]
   [struct transition ([state any] [actions (listof any)])]
   [? wildcard?]
   [wildcard? (any . -> . bool?)]
   [sub (pattern? int? int? . -> . route?)]
   [pub (pattern? int? int? . -> . route?)]
   [spawn ((any any . -> . any) any (listof route?) . -> . process?)]
   [send (any int? . -> . message?)]
   [feedback (any int? . -> . message?)]
   [drop-routes ((listof route?) . -> . (listof route?))]
   [lift-routes ((listof route?) . -> . (listof route?))]
   [co-route (route? (or/c false? int?) . -> . route?)]
   [route-accepts? (route? message? . -> . bool?)]
   [intersect-routes ((listof route?) (listof route?) . -> . (listof route?))]
   [spawn-world ((listof action?) . -> . process?)]
   [deliver-event (event? int? process? . -> . (or/c false? transition?))]
   [transition-bind ((any . -> . transition?) transition? . -> . transition?)]
   [sequence-transitions (transition? (listof (any . -> . transition?)) . -> . transition?)]
   [log-events-and-actions? (-> bool?)]
   
   [action? (any . -> . bool?)]
   [event? (any . -> . bool?)]
   [transition/c any])
  
  (require pattern functional-queue list hash core•)
  
  (define (pid-stack) pid-stack•)
  (define (log-events-and-actions?) (amb #t #f))
  
  (struct route (subscription? pattern meta-level level))
  
  ; Events
  (struct routing-update (routes))
  (struct message (body meta-level feedback?))
  
  ; Actions
  (struct quit ())
  
  ; Actors & Configurations
  (struct process (routes behavior state))
  (struct world (next-pid event-queue process-table downward-routes process-actions))
  
  ; Behavior : maybe-event * state -> transition
  (struct transition (state actions))
  (define transition/c (struct/c transition any (listof any)))
  
  (struct trigger-guard (process downward-routes))
  
  (define (drop-route r)
    (let ([s? (route-subscription? r)]
          [p (route-pattern r)]
          [ml (route-meta-level r)]
          [l (route-level r)])
      (and (positive? ml) (route s? p (- ml 1) l))))
  
  (define (lift-route r)
    (let ([s? (route-subscription? r)]
          [p (route-pattern r)]
          [ml (route-meta-level r)]
          [l (route-level r)])
      (route s? p (+ ml 1) l)))
  
  (define (sub p ml l) (route #t p ml l))
  (define (pub p ml l) (route #f p ml l))
  
  (define (spawn behavior state initial-routes) (process initial-routes behavior state))
  (define (send body ml) (message body ml #f))
  (define (feedback body ml) (message body ml #t))
  
  (define (drop-routes rs) (filter-map drop-route rs))
  (define (lift-routes rs) (map lift-route rs))
  
  (define (co-route r level-override)
    (let ([s? (route-subscription? r)]
          [p (route-pattern r)]
          [ml (route-meta-level r)]
          [l (route-level r)])
      (route (not s?) p ml (or level-override l))))
  
  (define (route-accepts? r m)
    (and (= (message-meta-level m) (route-meta-level r))
         (equal? (message-feedback? m) (not (route-subscription? r)))
         (intersect? (message-body m) (route-pattern r))))
  
  (define (intersect-routes rs1 rs2)
    (intersect-routes-loop1 rs1 rs2 empty))
  (define (intersect-routes-loop1 rs1 rs2 acc)
    (cond
      [(empty? rs1) (reverse acc)]
      [else (let ([r1 (car rs1)]
                  [rs1 (cdr rs1)])
              (intersect-routes-loop2 r1 rs1 rs2 acc))]))
  (define (intersect-routes-loop2 r1 rs1 rs2 acc)
    (cond
      [(empty? rs2) (intersect-routes-loop1 rs1 rs2 acc)]
      [else (let ([r2 (car rs2)]
                  [rs2 (cdr rs2)])
              (if (and (equal? (route-subscription? r1) (not (route-subscription? r2)))
                       (= (route-meta-level r1) (route-meta-level r2))
                       (< (route-level r1) (route-level r2)))
                  (intersect (route-pattern r1) (route-pattern r2)
                             (λ (rr) (intersect-routes-loop2
                                      r1 rs1 rs2
                                      (cons (let ([s? (route-subscription? r1)]
                                                  [ml (route-meta-level r1)]
                                                  [l (route-level r1)])
                                              (route s? (route-pattern rr) ml l))
                                            acc)))
                             (λ () (intersect-routes-loop2 r1 rs1 rs2 acc)))
                  (intersect-routes-loop2 r1 rs1 rs2 acc)))]))
  
  (define (filter-event e rs)
    (cond
      [(routing-update? e) (routing-update (intersect-routes (routing-update-routes e) rs))]
      [(message? e) (if (ormap (λ (r) (route-accepts? r e)) rs) e #f)]
      [else #f]))
  
  (define (spawn-world boot-actions)
    (spawn world-handle-event
           (enqueue-actions (world 0 (make-queue) (hash) empty (make-queue))
                            -1
                            boot-actions)
           empty))
  
  (define (event? x) (or (routing-update? x) (message? x)))
  (define (action? x) (or (event? x) (process? x) (quit? x)))
  
  (define (enqueue-actions w pid actions)
    (world (world-next-pid w)
           (world-event-queue w)
           (world-process-table w)
           (world-downward-routes w)
           (queue-append-list (world-process-actions w)
                              (filter-map (λ (a) (and (action? a) (cons pid a)))
                                          (flatten actions)))))
  
  (define (quiescent? w)
    (and (queue-empty? (world-event-queue w))
         (queue-empty? (world-process-actions w))))
  
  (define (deliver-event e pid p)
    (let ([x ((process-behavior p) e (process-state p))])
      (cond
        [(false? x) #f]
        [(transition? x) x]
        [else #|LOG|# (transition (process-state p) (list (quit)))])))
  
  (define (apply-transition pid t w)
    (cond
      [(transition? t)
       (let ([new-state (transition-state t)]
             [new-actions (transition-actions t)])
         (let ([w (transform-process pid w
                                     (λ (p) #|LOG|#
                                       (let ([r (process-routes p)]
                                             [b (process-behavior p)])
                                         (process r b new-state))))])
           (enqueue-actions w pid new-actions)))]
      [else w]))
  
  (define (step-children w)
    (let ([ans (step-children/fold w #f (world-process-table w))])
      (let ([w (car ans)]
            [step-taken? (cdr ans)])
        (and step-taken? (transition w empty)))))
  (define (step-children/fold w step-taken? ht)
    (cond
      [(empty? ht) (cons w step-taken?)]
      [else (let ([kv (car ht)])
              (let ([pid (car kv)]
                    [g (cdr kv)])
                (let* ([p (trigger-guard-process g)]
                       [t (deliver-event #f pid p)])
                  (step-children/fold (apply-transition pid t w)
                                      (or step-taken? (transition? t))
                                      (cdr ht)))))]))
  
  (define (transition-bind k t0)
    (let ([state0 (transition-state t0)]
          [actions0 (transition-actions t0)])
      (let ([t1 (k state0)])
        (let ([state1 (transition-state t1)]
              [actions1 (transition-actions t1)])
          (transition state1 (cons actions0 actions1))))))
  
  (define (sequence-transitions t0 steps)
    (foldl transition-bind t0 steps))
  
  (define (perform-actions w)
    (perform-actions/fold (transition (world (world-next-pid w)
                                             (world-event-queue w)
                                             (world-process-table w)
                                             (world-downward-routes w)
                                             (make-queue))
                                      empty)
                          (queue->list (world-process-actions w))))
  (define (perform-actions/fold t l)
    (cond
      [(empty? l) t]
      [else (let ([entry (car l)])
              (let ([pid (car entry)]
                    [a (cdr entry)])
                (perform-actions/fold (transition-bind (perform-action pid a) t)
                                      (cdr l))))]))
  
  (define (dispatch-events w)
    (transition (dispatch-events/fold (world (world-next-pid w)
                                             (make-queue)
                                             (world-process-table w)
                                             (world-downward-routes w)
                                             (world-process-actions w))
                                      (queue->list (world-event-queue w)))))
  (define (dispatch-events/fold w l)
    (cond
      [(empty? l) w]
      [else (let ([e (car l)])
              (dispatch-events/fold (dispatch-event e w) (cdr l)))]))
  
  (define (transform-process pid w fp frs)
    (let ([ans (hash-ref (world-process-table w) pid (λ () #f))])
      (cond
        [(false? ans) w]
        [else (let ([p (trigger-guard-process ans)]
                    [downward-rs (trigger-guard-downward-routes ans)])
                (world (world-next-pid w)
                       (world-event-queue w)
                       (hash-set (world-process-table w)
                                 pid
                                 (trigger-guard (fp p) (frs downward-rs)))
                       (world-downward-routes w)
                       (world-process-actions w)))])))
  
  (define (enqueue-event e w)
    (world (world-next-pid w)
           (enqueue (world-event-queue w) e)
           (world-process-table w)
           (world-downward-routes w)
           (world-process-actions w)))
  
  (define (upward-routes-change-ignorable? pid w rs)
    (let ([ans (hash-ref (world-process-table w) pid (λ () #f))])
      (cond
        [(false? ans) #t]
        [else (let ([p (trigger-guard-process ans)])
                (equal? (process-routes p) rs))])))
  
  (define (perform-action pid a)
    (λ (w)
      (cond
        [(process? a)
         (let* ([new-p a]
                [new-pid (world-next-pid w)]
                [w (world (+ 1 new-pid)
                          (world-event-queue w)
                          (hash-set (world-process-table w)
                                    new-pid
                                    (trigger-guard new-p empty))
                          (world-downward-routes w)
                          (world-process-actions w))])
           ; LOG removed
           (issue-routing-update w))]
        [(quit? a)
         ; LOG removed
         (let ([w (world (world-next-pid w)
                         (world-event-queue w)
                         (hash-remove (world-process-table w) pid)
                         (world-downward-routes w)
                         (world-process-actions w))])
           (issue-routing-update w))]
        [(routing-update? a)
         (let ([routes (routing-update-routes a)])
           (if (upward-routes-change-ignorable? pid w routes)
               (transition w empty)
               (let ([w (transform-process pid w
                                           (λ (p) (process routes
                                                           (process-behavior p)
                                                           (process-state p)))
                                           (λ (x) x) #|TODO confirm|#)])
                 (issue-routing-update w))))]
        [else ; TODO make sure it's safe
         (let ([body (message-body a)]
               [meta-level (message-meta-level a)]
               [feedback? (message-feedback? a)])
           (if (= 0 meta-level)
               (transition (enqueue-event a w) empty)
               (transition w (message body (- meta-level 1) feedback?))))])))
  
  (define (aggregate-routes base w)
    (append base (aggregate-routes/list (map cdr (world-process-table w)))))
  (define (aggregate-routes/list l)
    (cond
      [(empty? l) empty]
      [else (cons (process-routes (trigger-guard-process (car l)))
                  (aggregate-routes/list (cdr l)))]))
  
  (define (issue-local-routing-update w)
    (enqueue-event (routing-update (aggregate-routes (world-downward-routes w) w)) w))
  
  (define (issue-routing-update w)
    (transition (issue-local-routing-update w)
                (routing-update (drop-routes (aggregate-routes empty w)))))
  
  (define (dispatch-event e w)
    (dispatch-event/fold e w (world-process-table w)))
  (define (dispatch-event/fold e w ht)
    (cond
      [(empty? ht) w]
      [else (let ([kv (car ht)])
              (let ([pid (car kv)]
                    [g (cdr kv)])
                (let ([p (trigger-guard-process g)]
                      [old-downward-rs (trigger-guard-downward-routes g)])
                  (let ([e1 (filter-event e (process-routes g))])
                    (dispatch-event/fold
                     e
                     (cond
                       [(false? e1) w]
                       [(routing-update? e1)
                        (let ([new-downward-rs (routing-update-routes e1)])
                          (if (equal? old-downward-rs new-downward-rs) w
                              (transform-process pid
                                                 (apply-transition pid (deliver-event e1 pid p) w)
                                                 (λ (x) x) #|TODO confirm|#
                                                 (λ (old-rs) new-downward-rs))))]
                       [else (apply-transition pid (deliver-event e1 pid p) w)])
                     (cdr ht))))))]))
  
  (define (world-handle-event e w)
    (if (or e (not (quiescent? w)))
        (sequence-transitions (transition (inject-event e w) empty)
                              dispatch-events
                              perform-actions
                              (λ (w) (or (step-children w) (transition w empty))))
        (step-children w)))
  
  (define (inject-event e w)
    (cond
      [(routing-update? e)
       (let ([routes (routing-update-routes e)])
         (issue-local-routing-update (world (world-next-pid w)
                                            (world-event-queue w)
                                            (world-process-table w)
                                            (lift-routes routes)
                                            (world-process-actions w))))]
      [(message? e)
       (let ([body (message-body e)]
             [meta-level (message-meta-level e)]
             [feedback? (message-feedback? e)])
         (enqueue-event (message body (+ meta-level 1) feedback?) w))]
      [else w])))

(module ground•
  (provide [event• event?])
  (require core))

(module ground
  (provide
   [struct event ([descriptor any] [values any])]
   [run-ground ((listof action?) . -> . any #|TODO|#)])
  (require core ground• base• list)
  
  (struct event (descriptor values))
  
  (define (event-handler descriptor)
    (handle-evt descriptor (λ (vs) (send (event descriptor vs)))))
  
  (define (extract-active-events routes)
    (filter-map (λ (r)
                  (and (route-subscription? r)
                       (zero? (route-meta-level r))
                       (zero? (route-level r))
                       (let ([rp (route-pattern r)])
                         (cond
                           [(and (event? rp) (wildcard? (event-values rp)))
                            (event-handler (event-descriptor rp))]
                           [else #f]))))
                routes))
  
  (define (idle-handler)
    (handle-evt (system-idle-evt) (λ (_) #f)))
  
  (define (run-ground boot-actions)
    (await-interrupt #f (spawn-world boot-actions) empty))
  
  (define (await-interrupt inert? p active-events)
    (let ([event-list (if inert? active-events (cons (idle-handler) active-events))])
      (if (empty? event-list) 'void
          (let* ([e event• #|TODO|#]
                 [ans (deliver-event e -2 p)])
            (cond
              [(transition? ans)
               (let ([new-state (transition-state ans)]
                     [actions (transition-actions ans)])
                 (process-actions new-state actions inert? p (flatten actions) active-events))]
              [else (await-interrupt #t p active-events)])))))
  
  (define (process-actions new-state actions inert? p actions active-events)
    (cond
      [(empty? actions) (await-interrupt #f
                                         (process (process-routes p)
                                                  (process-behavior p)
                                                  new-state)
                                         active-events)]
      [else
       (let ([a (car actions)]
             [actions (cdr actions)])
         (cond
           [(routing-update? a) (let ([routes (routing-update-routes a)])
                                  (process-actions new-state
                                                   actions
                                                   inert?
                                                   p
                                                   actions
                                                   (extract-active-events routes)))]
           [(quit? a) 'void]
           [else (process-actions new-state actions inert? p actions active-events)]))])))

(module presence-detector•
  (provide ; set = list for now ^^
   [set-subtract ((listof route?) (listof route?) . -> . (listof route?))]
   [list->set ((listof route?) . -> . (listof route?))]
   [set->list ((listof route?) . -> . (listof route?))])
  (require core)
  (define (list->set x) x)
  (define (set->list x) x))

(module presence-detector
  (provide
   [struct presence-detector ([route-set (listof any #|TODO|#)])]
   [presence-detector-update (presence-detector/c (listof route?) . -> . (list/c presence-detector/c (listof route?) (listof route?)))]
   [presence-detector-routes (presence-detector/c . -> . (listof route?))]
   [presence-detector/c any])
  (require core pattern presence-detector•)
  
  (struct presence-detector (route-set))
  (define presence-detector/c (struct/c presence-detector (listof route?)))
  
  (define (presence-detector-update p rs)
    (let* ([old-route-set (presence-detector-route-set p)]
           [new-route-set (list->set rs)])
      (list (presence-detector new-route-set)
            (set-subtract new-route-set old-route-set)
            (set-subtract old-route-set new-route-set))))
  (define (presence-detector-routes p)
    (set->list (presence-detector-route-set p))))

(module demand-matcher
  (provide
   [struct demand-matcher ([demand-is-subscription? bool?]
                           [pattern pattern?]
                           [meta-level int?]
                           [demand-level int?]
                           [supply-level int?]
                           [increase-handler (any any . -> . any) #|FIXME|#]
                           [decrease-handler (any any . -> . any) #|FIXME|#]
                           [state any])]
   [demand-matcher-update
    (demand-matcher/c any (listof route?) . -> . (cons/c demand-matcher/c any))]
   [spawn-demand-matcher (pattern?
                          (any . -> . any) ;FIXME
                          (any . -> . any) ;FIXME
                          bool?
                          int?
                          int?
                          int?)]
   [demand-matcher/c any])
  (require base• list pattern core presence-detector)
  (define demand-matcher/c
    (struct/c demand-matcher bool? pattern? int? int? int? any #|FIXME|# any #|FIXME|# any))
  (struct demand-matcher (demand-is-subscription?
                          pattern
                          meta-level
                          demand-level
                          supply-level
                          increase-handler
                          decrease-handler
                          state))
  
  (define (unexpected-supply-decrease r) empty)
  
  (define (default-decrease-handler removed state) state)
  
  (define (make-demand-matcher demand-is-subscription?
                               pattern
                               meta-level
                               demand-level
                               supply-level
                               increase-handler
                               decrease-handler)
    (demand-matcher demand-is-subscription?
                    pattern
                    meta-level
                    demand-level
                    supply-level
                    increase-handler
                    decrease-handler
                    (presence-detector empty)))
  
  (define (compute-detector demand? d)
    (route (if (demand-matcher-demand-is-subscription? d) (not demand?) demand?)
           (demand-matcher-pattern d)
           (demand-matcher-meta-level d)
           (+ 1 (max (demand-matcher-demand-level d)
                     (demand-matcher-supply-level d)))))
  
  (define (incorporate-delta arrivals? routes d state)
    (let* ([relevant-change-detector (compute-detector arrivals? d)]
           [expected-change-level
            (if arrivals? (demand-matcher-demand-level d) (demand-matcher-supply-level d))]
           [expected-peer-level
            (if arrivals? (demand-matcher-supply-level d) (demand-matcher-demand-level d))])
      (incorporate-delta/fold arrivals?
                              d
                              relevant-change-detector
                              expected-change-level
                              expected-peer-level
                              state
                              routes)))
  
  (define (incorporate-delta/fold arrivals?
                                  d
                                  relevant-change-detector
                                  expected-change-level
                                  expected-peer-level
                                  s
                                  routes)
    (cond
      [(empty? routes) s]
      [else (let ([changed (car routes)])
              (incorporate-delta/fold
               arrivals?
               d
               relevant-change-detector
               expected-change-level
               expected-peer-level
               (if (= (route-level changed) expected-change-level)
                   (let ([ans (intersect-routes (list changed) (list relevant-change-detector))])
                     (cond
                       [(empty? ans) s]
                       [else
                        (let ([relevant-changed-route (car ans)])
                          (let* ([peer-detector (route (route-subscription? relevant-changed-route)
                                                       (route-pattern relevant-changed-route)
                                                       (route-meta-level relevant-changed-route)
                                                       (+ 1 expected-peer-level))]
                                 [peer-exists?
                                  (ormap (λ (r) (= (route-level r) expected-peer-level))
                                         (intersect-routes (presence-detector-routes (demand-matcher-state d))
                                                           (list peer-detector)))])
                            (cond
                              [(and arrivals? (not peer-exists?))
                               ((demand-matcher-increase-handler d) relevant-changed-route s)]
                              [(and (not arrivals?) peer-exists?)
                               ((demand-matcher-decrease-handler d) relevant-changed-route s)]
                              [else s])))]))
                   s)
               (cdr routes)))]))
  
  (define (demand-matcher-update d state0 rs)
    (let* ([ans (presence-detector-update (demand-matcher-state d) rs)]
           [new-state (car ans)]
           [added (car (cdr ans))]
           [removed (car (cdr (cdr ans)))]
           [new-d (demand-matcher (demand-matcher-demand-is-subscription? d)
                                  (demand-matcher-pattern d)
                                  (demand-matcher-meta-level d)
                                  (demand-matcher-demand-level d)
                                  (demand-matcher-supply-level d)
                                  (demand-matcher-increase-handler d)
                                  (demand-matcher-decrease-handler d)
                                  new-state)]
           [state1 (incorporate-delta #t added new-d state0)]
           [state2 (incorporate-delta #f removed new-d state1)])
      (cons new-d state2)))
  
  (define (demand-matcher-handle-event e d)
    (cond
      [(routing-update? e)
       (let ([routes (routing-update-routes e)])
         (let ([ans (demand-matcher-update d empty routes)])
           (transition (car ans) (cdr ans))))]
      [else #f]))
  
  (define (spawn-demand-matcher pattern
                                increase-handler
                                decrease-handler
                                demand-is-subscription?
                                meta-level
                                demand-level
                                supply-level)
    (let ([d (make-demand-matcher demand-is-subscription?
                                  pattern
                                  meta-level
                                  demand-level
                                  supply-level
                                  (λ (r actions) (cons (increase-handler r) actions))
                                  (λ (r actions) (cons (decrease-handler r) actions)))])
      (spawn demand-matcher-handle-event
             d
             (list (compute-detector #t d)
                   (compute-detector #f d))))))

(require functional-queue core ground presence-detector demand-matcher)
(amb
 ; functional-queue
 (queue? •)
 (make-queue)
 (enqueue • •)
 (enqueue-all • •)
 (dequeue •)
 (list->queue •)
 (queue->list •)
 (queue-length •)
 (queue-empty? •)
 (queue-append • •)
 (queue-append-list • •)
 (queue-extract • • •)
 ; core
 (route • • • •) (route? •)
 (route-subscription? •) (route-pattern •) (route-meta-level •) (route-level •)
 (routing-update •) (routing-update? •)
 (routing-update-routes •)
 (message • • •) (message? •)
 (message-body •) (message-meta-level •) (message-feedback? •)
 (quit) (quit? •)
 (process • • •) (process? •)
 (process-routes •) (process-behavior •) (process-state •)
 (transition • •) (transition? •)
 (transition-state •) (transition-actions •)
 (? •)
 (wildcard? •)
 (sub • • •)
 (pub • • •)
 (spawn • • •)
 (send • •)
 (feedback • •)
 (drop-routes •)
 (lift-routes •)
 (co-route • •)
 (route-accepts? • •)
 (intersect-routes • •)
 #;(spawn-world •) ; FIXME currently looping, ⊕ broken
 (deliver-event • • •)
 (transition-bind • •)
 (sequence-transitions • •)
 (log-events-and-actions?)
 (action? •)
 (event? •)
 ; ground
 #;(run-ground •) ; ⊕ broken
 ; presence-detector
 (presence-detector •)
 (presence-detector? •)
 (presence-detector-route-set •)
 (presence-detector-update • •) ;FIXME weird blame
 (presence-detector-routes •) ;FIXME weird blame
 ; demand-matcher
 (demand-matcher • • • • • • • •) (demand-matcher? •)
 (demand-matcher-demand-is-subscription? •)
 (demand-matcher-pattern •)
 (demand-matcher-meta-level •)
 (demand-matcher-demand-level •)
 (demand-matcher-supply-level •)
 (demand-matcher-increase-handler •)
 (demand-matcher-decrease-handler •)
 (demand-matcher-state •)
 #;(demand-matcher-update • • •) ; FIXME ⊕ broken
 (spawn-demand-matcher • • • • • • •))