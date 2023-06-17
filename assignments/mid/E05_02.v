Require Import P05.



Check insert_sorted:
  forall X lex n l
         (LEX: forall x y, lex x y = false -> lex y x = true)
         (SORTED: sorted X lex l),
    sorted X lex (insert lex n l).

Check bubble_sort_sorted:
  forall X lex l
         (LEX: forall x y, lex x y = false -> lex y x = true),
    sorted X lex (bubble_sort lex l).

