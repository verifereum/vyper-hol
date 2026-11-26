(* Word and clean-operand facts at ECMul's reached second cut. *)
Theory bodyECMulScalarCutMods
Ancestors
  bodyFullPostsMods loweringPosts exprBopSimProps bodyPtrDefs exprSimMemDefs
  compileEnv vyperValue vyperStorageFootprint vyperContext vyperState

Theorem ecmul_scalar_at_cut_mods:
  expr_type e2 = BaseT (UintT 256) /\
  storage_trace_domain cx st0 es2.storage_trace /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    expr_post_mods H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
    expr_store_bound cx (post_value_type cenv e2) v2 y t2 /\
    ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 t2) ==>
  ?q. eval_operand y t2 = SOME q /\
      q = typed_val_to_w256 (BaseTV (UintT 256)) v2 /\
      expr_val_rel cx (BaseT (UintT 256)) v2 y t2 /\
      expr_store_bound cx (BaseT (UintT 256)) v2 y t2 /\
      ptr_val_ok cx (BaseT (UintT 256)) v2 y G2 tn2 t2 /\
      op_taint tn2 y = {} /\ op_prov G2 y = NONE
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `post_value_type cenv e2 = BaseT (UintT 256)` by simp[is_word_type_def] >>
  `expr_val_rel cx (BaseT (UintT 256)) v2 y t2` by
    fs[expr_post_mods_def, expr_post_def] >>
  `eval_operand y t2 = SOME (typed_val_to_w256 (BaseTV (UintT 256)) v2)` by
    (irule expr_val_rel_typed >> qexistsl_tac [`cx`, `BaseT (UintT 256)`] >>
     simp[is_word_type_def, evaluate_type_def]) >>
  qexists_tac `typed_val_to_w256 (BaseTV (UintT 256)) v2` >>
  gvs[ptr_val_ok_def, is_word_type_def]
QED
