Require Import P06.



Check mod3_cases: forall n,
  exists k, n = 3*k \/ n = 1 + 3*k \/ n = 2 + 3*k.

