(* Request-prefix companion to bodyFullStructLit. *)
Theory s1PrefixStructLit
Ancestors
  s1PrefixPreds bodyFullStructLit

Theorem structlit_expr_prefix_ok:
  !cx v7 src_id_opt id kes.
  (!ks. ks = MAP FST kes ==> body_exprs_full_ok cx (MAP SND kes)) /\
  (!ks. ks = MAP FST kes ==> body_exprs_prefix_ok cx (MAP SND kes)) ==>
  body_expr_prefix_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  cheat
QED
