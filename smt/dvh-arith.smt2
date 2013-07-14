OPTION "produce-models";

%% ([x : int?] -> (lambda (z) (= (add1 x) z)))
%% (lambda (q) (add1 q))

%% Assertions from function running
lQ, lADD1Q : INT;

ASSERT lADD1Q = lQ + 1;

%% Assertions from dependent contract running

lADD1X : INT;
lEQ : BOOLEAN;

ASSERT lADD1X = lQ + 1;

ASSERT lEQ = (lADD1X = lADD1Q);

%% Assert the predicate holds
ASSERT lEQ = TRUE;

CHECKSAT;

