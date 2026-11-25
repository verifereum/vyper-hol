(* Guarded full and prefix argument judgments for MakeArray. *)
Theory s1PrefixGuardedMakeArray
Ancestors
  s1PrefixPreds bodyFullPreds vyperAST list s1PrefixMakeArray

Theorem make_array_expr_prefix_ok:
  !cx ty bt es.
  (?t n. bt = MakeArray t n) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  rpt strip_tac >> gvs[] >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  irule make_array_builtin_sim_prefix >> metis_tac[]
QED
