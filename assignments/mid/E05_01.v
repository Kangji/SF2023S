Require Import P05.



Check sorted_example1: sorted nat leb [1; 3; 4; 4; 5].
Check sorted_example2: sorted string String.leb (["2"; "2"; "3"; "6"]%string).
Check sorted_non_example1: sorted nat leb [1; 3; 2] -> False.

