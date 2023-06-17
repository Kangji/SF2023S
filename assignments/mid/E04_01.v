Require Import P04.



Check app_head_tail_cancel: forall X hd1 hd2 (l1 l2: list X) end1 end2
    (EQ: [hd1] ++ l1 ++ [end1] = [hd2] ++ l2 ++ [end2]),
  l1 = l2.

