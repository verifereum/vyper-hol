(* Memory-boundary probes for tuple assignment.  In particular these do not
   require a newly executed ALLOCA to increase the allocation frontier. *)
Theory bodyMemAssignTupleTargetsFacts
Ancestors
  bodyDeclMemoryCounted tupleTypedLoad instMemFrontier
  exprLoweringProps venomMemDefs compileEnv tupleMemoryLayout valueEncodingProofs
  context venomInst bodyDeclMemoryCore exprSimAlloc exprSimBufferStore
  venomExecSemantics venomState loweringSlice loweringPosts list
  fragExec fragExecMem bodyMemoryDefs bodyExprPreFacts bodySim
  tupleTargetStoreProps memoryLocalRhsProps allocLimitsProps allocLimits
  supportedStmtTraverse supportedStmts exprSimHyps exprSimAggregateLayout
  exprSimTopLevelProps exprSimFieldLayout exprSimAttributeFields
  accountsRelProps vyperStorageLayoutSafety vyperPlaceResultTyping
  vyperTypeEnv vyperLookupStorage vyperTypeSystem vyperTypeCallGraph gasContext
  vyperTypeCallStackSoundness exprSimHypsDefs exprSimSource
  vyperTypeInvariants stmtSimAugAssign stmtSimDeclStore
  bodyStorageMetadata stmtSimAssignAttr supportedExprForms supportedExprs
  exprSimUnwrap supportedTypes vyperLookup vyperState
Libs
  monadsyntax

(* Strengthen the existing tuple_container_bound interface from word-address
   representability to the actual memory-check frontier. *)
Theorem tuple_container_frontier:
  !ctx func cenv cx es s b sz.
    stmt_state_rel ctx func cenv cx es s /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) ==>
    b + sz <= s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      metis_tac[]) >>
  fs[local_region_def, stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

(* All loads, not just the bytes occupied by the current value, fit. *)
Theorem tuple_element_frontier:
  !tvs i base s.
    i < LENGTH tvs /\
    base + type_memory_size_list tvs <= s.vs_alloca_next ==>
    base + SUM (MAP type_memory_size (TAKE i tvs)) +
      type_memory_size (EL i tvs) <= s.vs_alloca_next
Proof
  rpt strip_tac >> drule tuple_element_interval >>
  fs[type_memory_size_list_sum] >> decide_tac
QED

(* Provenance is retained across the copy, even when the ALLOCA is reused.
   Room alone is not used to infer the existence of a backing allocation. *)
Theorem tuple_scratch_prefix_provenance:
  !ctx func ce cx es s sa sm sn buf src n sw a t.
    compile_alloc_buffer n sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
    fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ n < dimword (:256) /\
    run_inst_seq (emitted_insts sa sm) s = OK a /\
    run_inst_seq (emitted_insts sm sn) a = OK t ==>
    ?w. eval_operand buf.buf_operand t = SOME w /\
        FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  `a.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src a = SOME sw` by
    (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
  `n < dimword (:256)` by decide_tac >>
  drule_all buffer_copy_memory_run >> strip_tac >> gvs[] >>
  qexists_tac `w` >> Cases_on `n = 0` >>
  gvs[mcopy_def, write_memory_with_expansion_def, eval_operand_def,
      lookup_var_def]
QED

Theorem tuple_scratch_prefix_path_mem:
  !ctx func ce cx es s sa sm sn buf src n sw tv v d.
    compile_alloc_buffer n sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
    fn_has_code sa sn func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
    alloca_history func s /\ return_buf_frame d ce sa s /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ n < dimword (:256) /\
    w2n sw + n <= s.vs_alloca_next /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sn.cs_current_bb /\
      t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
      return_buf_frame d ce sn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      eval_operand buf.buf_operand t = SOME w /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      w2n w + n <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_scratch_prefix_shape >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all body_scratch_prefix_run >> strip_tac >>
  drule_all tuple_scratch_prefix_provenance >> strip_tac >> gvs[] >>
  `run_inst_seq (emitted_insts sa sn) s = OK t` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK a`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sn) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
     rpt strip_tac >> gvs[]) >>
  `return_buf_frame d ce sn t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sn)` by
    metis_tac[body_scratch_prefix_no_gas] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sn)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sn.cs_current_insts`, `w`] >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def] >>
  Cases_on `buf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]
QED

(* This is the actual emitted tuple snapshot, not an uncounted S1 run.
   There is intentionally no premise that the allocation site is new. *)
Theorem tuple_stage_copy_path_mem:
  !ctx func ce cx es s sa sb staged src n sw tv v d.
    (do buf <- compile_alloc_buffer n;
        emit_void MCOPY [buf.buf_operand; src; Lit (n2w n)];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    0 < n /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
    alloca_history func s /\ return_buf_frame d ce sa s /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ n < dimword (:256) /\
    w2n sw + n <= s.vs_alloca_next /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
      return_buf_frame d ce sb t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      eval_operand staged t = SOME w /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      w2n w + n <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ sa = (staged,sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer n sa = (buf,sm)` >>
  rename1 `fn_has_code sa sb func` >>
  `compile_copy_memory buf.buf_operand src n sm = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  `w2n sw + n <= s.vs_alloca_next` by decide_tac >>
  drule_all tuple_scratch_prefix_path_mem >>
  strip_tac >> qexistsl_tac [`t`, `w`] >> simp[]
QED

(* S1 originals: bodySimStmtCases.tuple_staging_bound and
   body_assign_tuple_rhs_pre (local in the owner reference). *)
Theorem tuple_staging_bound:
  !cenv cx env es g e tys tvs.
    expr_sim_inv cenv cx env es /\
    stmt_exprs_ok cenv (Assign (TupleTarget g) e) /\
    expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    is_memory_view e ==>
    type_memory_size (TupleTV tvs) < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv (TupleT tys) < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size (TupleTV tvs)` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_size (TupleTV tvs) + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >> decide_tac
QED

Theorem body_assign_tuple_rhs_pre:
  body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==>
     occurs_abi_decode_target target tops) /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, int_calls_stmt_def, body_inv_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

(* S1 originals: bodySimStmtCases.body_tuple_target_local_* (local). *)
Theorem body_tuple_target_local_aligned:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty /\
  0 < type_memory_bytes cenv ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv
Proof
  rpt strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  simp[tuple_target_aligned_local] >> metis_tac[expr_sim_inv_local]
QED

Theorem body_tuple_target_local_layout:
  expr_sim_inv cenv cx env es /\
  well_typed_atarget env (BaseTarget (NameTarget id)) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v
Proof
  rpt strip_tac >>
  gvs[well_typed_atarget_def, well_typed_target_def,
      type_place_target_NameTarget] >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\ entry.assignable` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `entry.type = tv` by metis_tac[expr_sim_inv_local, optionTheory.SOME_11] >>
  simp[tuple_target_layout_local] >> metis_tac[store_lays_out_typed]
QED

Theorem body_tuple_target_local_room:
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[allocation_limit_word_room]
QED

(* S1 originals: bodySimStmtCases.body_tuple_target_toplevel_aligned,
   body_tuple_target_field_aligned and body_tuple_target_ready (local). *)
(* Necessary local prerequisites from the same S1 owner file. *)
Theorem tuple_env_assignable_find_NONE[local]:
  !env cx st src id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_global_assignable (src, id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem find_var_decl_storage_some[local]:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem tuple_supported_scalar_target_decl[local]:
  !tops src id.
    supported_scalar_target tops (src, id) ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\
                      is_word_type ty
Proof
  rpt gen_tac >> simp[supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x3` >> simp[] >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[find_var_decl_storage_some] >>
  gvs[supported_full_word_type_def] >> first_assum (irule_at Any) >>
  simp[is_word_type_def]
QED

Theorem tuple_supported_storage_field_write_decl[local]:
  !tops src id fld.
    supported_storage_field_write tops (src, id) fld ==>
    src = NONE /\ find_var_decl_by_name id tops <> NONE /\
    ?mut sid slot. MEM (VariableDecl Private mut id (StructT sid) slot) tops
Proof
  rpt gen_tac >>
  simp[supported_storage_field_write_def, supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >> simp[] >>
  metis_tac[find_var_decl_storage_some]
QED

Theorem body_tuple_target_toplevel_aligned:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_scalar_target tops nsid /\
  type_place_target env (TopLevelNameTarget nsid) = SOME (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx (BaseTarget (TopLevelNameTarget nsid)) ty tv
Proof
  Cases_on `nsid` >> rename1 `(src, id)` >> rpt strip_tac >>
  drule tuple_supported_scalar_target_decl >> strip_tac >> gvs[] >>
  rename1 `is_word_type declared_ty` >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) = build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[type_place_target_TopLevelNameTarget]
  >- (drule_all tuple_env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `declared_ty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  simp[tuple_target_aligned_toplevel] >>
  rpt strip_tac >> irule storage_dead_update_word_region >>
  qexistsl_tac [`NONE`, `id`, `[]`, `tv`] >>
  simp[declared_storage_region_def] >>
  metis_tac[exprSimUnwrapTheory.word_type_slot_size]
QED

Theorem body_tuple_target_field_aligned:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  supported_storage_field_write tops nsid fld /\
  type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
    SOME (Type ty) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  tuple_target_aligned cenv cx
    (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) ty tv
Proof
  Cases_on `nsid` >> rename1 `(src, id)` >> rpt strip_tac >>
  drule tuple_supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[type_place_target_AttributeTarget, type_place_target_TopLevelNameTarget]
  >- (drule_all tuple_env_assignable_find_NONE >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >> gvs[] >>
  drule_all attribute_type_struct_field >> strip_tac >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >> gvs[] >>
  drule struct_field_slot_exists >> strip_tac >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  simp[tuple_target_aligned_field] >>
  rpt gen_tac >> irule storage_dead_update_struct_word_field >>
  goal_assum (drule_at Any) >> qexistsl_tac [`NONE`, `id`] >>
  simp[declared_storage_region_def] >>
  metis_tac[exprSimUnwrapTheory.word_type_slot_size]
QED

Theorem body_tuple_target_ready:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  locals_alloc_ok cenv env /\ well_typed_atarget env g ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ((?id lty. g = BaseTarget (NameTarget id) /\
            FLOOKUP env.var_types id = SOME lty /\
            0 < type_memory_bytes cenv lty) \/
   (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
           supported_scalar_target tops nsid) \/
   (?nsid fld fty.
      g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
      supported_storage_field_write tops nsid fld /\
      type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
        SOME (Type fty) /\ is_word_type fty)) ==>
  tuple_target_aligned cenv cx g ty tv /\
  (~is_word_type ty ==> type_memory_size tv + 64 < dimword (:256)) /\
  (!es1 v. expr_sim_inv cenv cx env es1 /\ value_has_type tv v ==>
     tuple_target_layout es1.scopes g ty tv v)
Proof
  rpt strip_tac >> gvs[tuple_target_base_type]
  >- (gvs[type_place_target_NameTarget] >>
      irule body_tuple_target_local_aligned >> metis_tac[])
  >- (gvs[type_place_target_NameTarget] >>
      metis_tac[body_tuple_target_local_room])
  >- (irule body_tuple_target_local_layout >>
      simp[well_typed_atarget_def, well_typed_target_def] >> metis_tac[])
  >- (irule body_tuple_target_toplevel_aligned >> metis_tac[])
  >- (drule_all body_tuple_target_toplevel_aligned >> Cases_on `nsid` >>
      simp[tuple_target_aligned_toplevel])
  >- simp[tuple_target_layout_def]
  >- (irule body_tuple_target_field_aligned >> metis_tac[])
  >> simp[tuple_target_layout_def]
QED
