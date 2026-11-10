(* Zero-edge local-name pointer boundaries. Gas observation transport is
   ghost_inv_gas_obs in stmtFragPtr; reuse it rather than duplicate it. *)
Theory bodyPtrBopInNameBoundary
Ancestors
  bodyPtrDefs stmtFragPtr exprSimHyps exprSimHypsDefs exprSimNameValue
  exprSimProps exprSimDefs exprLoweringProps loweringPosts loweringSlice
  exprLowering compileEnv loweringStateRelDefs context venomState venomInst ptrDiscipline
  vyperInterpreter vyperState vyperAST vyperTypeEnv vyperTypeSystem
  vyperTypeInvariants
  valueEncoding valueEncodingProofs finite_map words arithmetic

Theorem ghost_kept_refl:
  ghost_kept cenv es sa G tn s G tn
Proof
  simp[ghost_kept_def]
QED

Theorem local_name_ptr_mem_ok:
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  val_wf entry.type entry.value /\ type_memory_size entry.type <= sz /\
  ghost_inv d cenv cx es G tn s ==>
  ptr_mem_ok cx ann entry.value (Var p) G tn s
Proof
  strip_tac >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\
     mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by
    (fs[ghost_inv_def] >> first_x_assum drule_all >> simp[]) >>
  drule val_store_size_le >> strip_tac >>
  gvs[ptr_mem_ok_def, ptr_covers_def, eval_operand_def]
QED

Theorem local_name_ptr_buf_ok:
  expr_body_pre cenv cx env (Name ann id) es /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  type_memory_size entry.type <= sz /\
  ghost_inv d cenv cx es G tn s ==>
  ptr_buf_ok cenv (Name ann id) (Var p) G s
Proof
  strip_tac >>
  `type_memory_bytes cenv ann = type_memory_size entry.type` by
    (irule expr_sim_inv_memory_size >>
     gvs[expr_body_pre_def] >> metis_tac[]) >>
  `ptr_covers G tn p s sz` by
    (fs[ghost_inv_def] >> first_x_assum drule_all >> simp[]) >>
  gvs[ptr_buf_ok_def, lowered_value_type_def, ptr_covers_def,
      eval_operand_def, expr_type_def]
QED

Theorem local_name_ptr_post:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  value_has_type entry.type entry.value /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME ann /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s ==>
  ptr_vv_ok cx ann (PlaceR (MemoryPlace id []))
    (LocatedValue ann (mk_ptr (Var p) LocMemory))
    (es with gas_obs := []) G tn s
Proof
  strip_tac >>
  `read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
    (INL entry.value, es with gas_obs := [])` by
    (qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := []`, `entry`]
       mp_tac eval_name_word >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, ignore_bind_def]) >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `ptr_mem_ok cx ann entry.value (Var p) G tn s` by
    (irule local_name_ptr_mem_ok >> metis_tac[]) >>
  `ptr_covers G tn p s sz` by
    (fs[ghost_inv_def] >> first_x_assum drule_all >> simp[]) >>
  gvs[ptr_vv_ok_def, mk_ptr_def, ptr_covers_def]
QED

Theorem local_name_body_ptr_boundary:
  expr_body_pre cenv cx env (Name ann id) es /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s ==>
  ptr_vv_ok cx ann (PlaceR (MemoryPlace id []))
    (LocatedValue ann (mk_ptr (Var p) LocMemory))
    (es with gas_obs := []) G tn s /\
  ptr_buf_ok cenv (Name ann id) (Var p) G s
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
     evaluate_type (get_tenv cx) ann = SOME entry.type /\
     value_has_type entry.type entry.value` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  conj_tac
  >- (irule local_name_ptr_post >> metis_tac[]) >>
  irule local_name_ptr_buf_ok >> metis_tac[]
QED
