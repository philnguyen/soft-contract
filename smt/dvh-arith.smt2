OPTION "produce-models";

%% ([x : int?] -> (lambda (z) (= (add1 x) z)))
%% (lambda (q) (add1 q))

%% Assertions from function running
lQ, lADD1Q : INT;

ASSERT lADD1Q = lQ + 1;

%% Assertions from dependent contract running

lX, lZ, lADD1X : INT;
lEQ : BOOLEAN;

ASSERT lX = lQ;
ASSERT lZ = lADD1Q;
ASSERT lADD1X = lX + 1;

ASSERT lEQ = (lADD1X = lZ);

%% Assert the predicate holds
ASSERT lEQ = TRUE;

CHECKSAT;

