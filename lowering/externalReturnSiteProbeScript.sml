Theory externalReturnSiteProbe
Ancestors
  exprSimHypsDefs vyperTypeEvalSoundness vyperTypeArgFits vyperTyping
  vyperTypeExprSoundness vyperTypeSystem vyperTypeInvariants
  vyperInterpreter vyperState vyperAST loweringPosts valueEncoding valueEncodingDefs exprLowering

(* A successful typed return read is already a fixed point of its cast.
   This uses annotation typing, not any physical-layout assumption. *)
Theorem return_site_cast:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
  evaluate_type (get_tenv cx) ret = SOME tv ==>
  safe_cast tv v = SOME v
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\
   type_widens_to env.type_defs (expr_type e) ret` by
    (gvs[type_stmt_def, AllCaseEqs()]) >>
  `env_consistent env cx es /\ state_well_typed es /\
   accounts_well_typed es.accounts /\ context_well_typed cx /\
   functions_well_typed cx` by gvs[expr_sim_inv_def] >>
  drule_all eval_expr_read_type_sound >>
  simp[] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def] >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  gvs[] >> irule safe_cast_well_typed >> simp[]
QED

(* Equal annotation/return types require no physical-type reconstruction. *)
Theorem return_site_equal_memory:
  expr_post ctx func ce cx e es sa sb s0 es' v op s /\
  expr_type e = ret /\ ~is_word_type ret /\
  evaluate_type (get_tenv cx) ret = SOME tv ==>
  ?w. eval_operand op s = SOME w /\
      val_in_memory tv v (w2n w) s.vs_memory
Proof
  rw[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

(* Bytestring widening does not change physical reads or actual footprints. *)
Theorem return_site_bytes_memory:
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p mem =
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p mem
Proof
  simp[val_in_memory_def]
QED

Theorem return_site_string_memory:
  val_in_memory (BaseTV (StringT n)) (StringV str) p mem =
  val_in_memory (BaseTV (StringT m)) (StringV str) p mem
Proof
  simp[val_in_memory_def]
QED

Theorem return_site_empty_struct:
  val_in_memory (StructTV []) (StructV []) p mem /\
  val_footprint (StructTV []) (StructV []) = 0
Proof
  simp[val_in_memory_def, val_footprint_def,
       type_memory_size_def]
QED

(* The current invariant cannot constrain the physical IntCall return table. *)
Theorem return_site_inv_return_table:
  expr_sim_inv (ce with ce_func_return_type := f) cx env es <=>
  expr_sim_inv ce cx env es
Proof
  simp[expr_sim_inv_def,
       placeTypingPropsTheory.place_map_tables_agree_on_defined_def]
QED

Theorem return_site_intcall_physical_type:
  lowered_value_type (ce with ce_func_return_type := f)
    (Call ann (IntCall fid) args drv) = f (nsid_to_string fid)
Proof
  simp[lowered_value_type_def]
QED
