(* ptr_discipline with its per-function part weakened to fn_ptr_ok of
   each function, the form the LowerDload leaves use. *)
Theory o1LowerDloadPtrDiscipline
Ancestors
  ptrDiscipline list

Theorem ptr_discipline_fn_ptr_ok:
  ptr_discipline lo ctx vs ==>
  lo <= vs.vs_alloca_next /\
  ?P. EVERY (fn_ptr_ok P) ctx.ctx_functions /\
      !stk PG G tn fn inst s.
        frame_reachable vs ctx stk PG G tn fn inst s ==>
        access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
        allocas_from lo s /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp s)
Proof
  rewrite_tac[ptr_discipline_def] >> strip_tac >> asm_rewrite_tac[] >>
  qexists_tac `P` >> asm_rewrite_tac[] >>
  fs[EVERY_MEM]
QED
