(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: sha256 (S1: exprSimBuiltins' compile_sha256_case, exprSimHash). *)
Theory bodyMemBiSha256
Ancestors
  bodyMemoryPreds bodyMemBiSha256Compose exprSimSource exprSimHypsDefs
  vyperTyping vyperTypeSystem vyperTypeBuiltins

Theorem body_builtin_sha256_mem:
  !cx ty es.
    (builtin_args_length_ok Sha256 (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty Sha256 es)
Proof
  rpt gen_tac >> strip_tac >>
  rw[body_expr_mem_ok_def] >>
  `?e. es = [e]` by
    (gvs[expr_body_pre_def, well_typed_expr_def,
         well_typed_builtin_app_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  gvs[vyperContextTheory.builtin_args_length_ok_def, body_exprs_mem_ok_def] >>
  `expr_body_pre cenv cx env e es'` by
    (irule expr_body_pre_builtin_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     gvs[expr_body_pre_def]) >>
  metis_tac[body_expr_mem_ok_def, compile_sha256_typed_sim_mem,
            compile_sha256_typed_vv_sim_mem]
QED
