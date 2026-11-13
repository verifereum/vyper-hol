(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: blobhash (S1: exprSimBuiltins' compile_blobhash_case). *)
Theory bodyMemBiBlobHash
Ancestors
  bodyMemoryPreds bodyMemBiBlobHashSim exprSimSource exprSimHypsDefs
  vyperTyping vyperTypeSystem vyperAST vyperValue builtinProps builtinSimple vyperContext list

Theorem body_builtin_blobhash_mem:
  !cx ty es.
    (builtin_args_length_ok BlobHash (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty BlobHash es)
Proof
  rpt gen_tac >> strip_tac >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >>
  rpt gen_tac >> strip_tac >>
  `?e. es = [e] /\ ty = BaseT (BytesT (Fixed 32)) /\
       expr_type e = BaseT (UintT 256)` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `es` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[builtin_args_length_ok_def, body_exprs_mem_ok_def] >>
  `expr_body_pre cenv cx env e es'` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     conj_tac >- gvs[expr_body_pre_def] >>
     qexistsl_tac [`BaseT (BytesT (Fixed 32))`, `[e]`, `BlobHash`, `es'`] >>
     simp[] >> gvs[expr_body_pre_def]) >>
  `expr_sim_mem ctx func cenv cx ty' e es'` by
    metis_tac[body_expr_mem_ok_def] >>
  conj_tac
  >- (irule compile_blobhash_sim_mem >> metis_tac[]) >>
  irule compile_blobhash_vv_sim_mem >> metis_tac[]
QED
