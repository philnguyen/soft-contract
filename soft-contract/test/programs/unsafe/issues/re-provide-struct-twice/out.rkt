(module "/home/philnguyen0112/Downloads/missing/mine/data.rkt" scv:lang
  (define-values (foo foo?) (values _foo _foo?))
  (define foo1 foo)
  (provide (foo (->i (_1302 (scv:struct/c foo))))
           (foo? (->i (_1303 any/c) (_1304 boolean?)))))

(module "/home/philnguyen0112/Downloads/missing/mine/data-adaptor.rkt" scv:lang
  (module "/home/philnguyen0112/Downloads/missing/mine/data-adaptor.rkt:require/contracts" scv:lang
    (define lifted/11 foo?)
    (provide (foo (->i (_1305 (scv:struct/c foo))))
             (foo? (->i (_1306 any/c) (_1307 boolean?)))))
  (define lifted/1 (void))
  (provide foo foo?))

(module "/home/philnguyen0112/Downloads/missing/mine/const.rkt" scv:lang
  (define p (provide/contract-struct-expansion-info-id-foo)))

