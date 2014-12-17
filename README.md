soft-contract
=============

This collection implements a small functional language with contract verification
and counterexample generation.
Examples are under [examples/](https://github.com/philnguyen/soft-contract/tree/release/examples)

Core language supported currently:

    program      ::= module-form
	module-form  ::= (module module-name racket
	                   (provide provide-spec …)
                       (require require-spec …)
                       (define name value) …)
    provide-spec ::= (name contract)
	require-spec ::= (submod ".." module-name)
	value        ::= (λ (var) expr) | number | boolean | string | symbol | op
	expr         ::= var | (if expr expr expr) | (expr expr …)
	contract     ::= expr | (or/c contract …) | (and/c contract …)
	               | (->i ([var contract] …) (res (var …) contract))
    op           ::= + | - | * | / | string-length
	               | number? | real? | integer? | boolean? | false? | cons? | empty?
