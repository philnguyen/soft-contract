OPTION "produce-models";

%% ([x : int?] -> (lambda (z) (= x (sub1 z))))
%% (lambda (q) (add1 q))

%% Assertions from function running
lQ, lADD1Q : INT;

ASSERT lADD1Q = lQ + 1;

%% Assertions from dependent contract running

lSUB1Z : INT;
lEQ : BOOLEAN;

ASSERT lSUB1Z = lADD1Q - 1;

ASSERT lEQ = (lQ = lSUB1Z);

%% Assert the predicate holds
ASSERT lEQ = TRUE;

CHECKSAT;

