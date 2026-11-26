(* Forcing a nonword Name preserves the local pointer and its whole frame. *)
Theory bodyLocalNameAliasMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs fragGasOriginPtr
  exprSimNameValue exprSimUnwrapProps exprSimMemDefs exprSimProps nameLoweringProps stateRelProj
  exprLowering loweringPosts compileEnv context loweringStateRelDefs allocaHistory
  vyperAST vyperState vyperInterpreter vyperTypeSystem vyperStorageFootprint
  valueEncodingProofs valueEncoding venomState finite_map

Theorem local_name_alias_bounds[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx (es with gas_obs := []) G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  type_memory_bytes cenv ann = type_memory_size entry.type /\
  ~is_word_type ann ==>
  expr_store_bound cx ann entry.value (Var p) s /\
  ptr_val_ok cx ann entry.value (Var p) G tn s /\
  ptr_buf_ok cenv (Name ann id) (Var p) G s
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_at_mods_def] >> strip_tac >>
  qpat_x_assum `!name ent q n. _ ==> ptr_covers _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  drule_then assume_tac val_store_size_le >>
  gvs[expr_store_bound_def, ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
      ptr_covers_def, eval_operand_def, lowered_value_type_def, expr_type_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem local_name_alias_post[local]:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  value_has_type entry.type entry.value /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME ann /\
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
    (INL entry.value, es with gas_obs := []) /\
  ~is_word_type ann ==>
  expr_post H ctx func cenv cx (Name ann id) es sa sa s
    (es with gas_obs := []) entry.value (Var p) s
Proof
  strip_tac >>
  `vv_post H ctx func cenv cx (Name ann id) es sa sa s (es with gas_obs := [])
     (PlaceR (MemoryPlace id [])) (LocatedValue ann (mk_ptr (Var p) LocMemory)) s`
    by (irule name_value_post >> simp[]) >>
  drule_all_then assume_tac vv_post_read_result >>
  drule expr_post_of_vv_post_memory >> simp[mk_ptr_def]
QED

Theorem local_name_alias_read_mods:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  value_has_type entry.type entry.value /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME ann /\
  type_memory_bytes cenv ann = type_memory_size entry.type /\
  ~is_word_type ann /\
  read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
    (INL entry.value, es with gas_obs := []) /\
  lower_value compile_expr cenv ty (Name ann id) sa = (op,sb) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       immutable_frame_mods func cenv cx (es with gas_obs := []) s0 /\
       ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0) ==>
  ?z G' tn'. !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK z,G',tn') /\
    expr_post_mods H ctx func cenv cx (Name ann id) es sa sb s0
      (es with gas_obs := []) entry.value op z /\
    expr_store_bound cx (post_value_type cenv (Name ann id)) entry.value op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G' tn' z /\
    ptr_val_ok cx (post_value_type cenv (Name ann id)) entry.value op G' tn' z /\
    (~is_word_type (post_value_type cenv (Name ann id)) ==>
      ptr_buf_ok cenv (Name ann id) op G' z) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`,`sa`,`ann`] assume_tac) >>
  gvs[lower_value_def, comp_bind_def, unwrap_memory_value_eq] >>
  qexistsl_tac [`s0`,`G0`,`tn0`] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac local_name_alias_bounds >>
  drule_all_then assume_tac local_name_alias_post >>
  simp[gas_origin_ptr_path_rules, expr_post_mods_def, expr_type_def, ghost_kept_at_def]
QED
