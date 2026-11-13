Theory placeStorageNormalizedSuffixMem
Ancestors
  placeStorageDynamicFrame placeStorageFixedCounted placeStorageFixedSemantic
  bodyMemAssignTopCopySuffix bodyDeclMemoryCounted stmtLowering context
  compileEnv venomState valueEncodingProps vyperTyping vyperValue
  words arithmetic list rich_list fragGasMode stmtSimStoreCopy
  emitHelper emitHelperProps exprLoweringProps allocaHistory bodyMemAssignTopCopyPaths
  bodyMemAssignTopCopyLoop bodyMemAssignTopCopySem venomInst

Theorem normalized_storage_assign_value_mem:
  compile_assign_value ce dst (if tr then LocTransient else LocStorage) src F src_loc
    dty dty (case dty of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes ce et+31) DIV 32,type_memory_bytes ce et) | _ => NONE)
    (type_memory_bytes ce dty) sa = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  evaluate_type (get_tenv cx) dty = SOME tv /\ well_formed_type_value tv /\
  value_has_type tv v /\ 0 < type_memory_size tv /\
  type_memory_bytes ce dty = type_memory_size tv /\
  (!et cap. dty = ArrayT et (Dynamic cap) ==>
    ?etv. evaluate_type (get_tenv cx) et = SOME etv /\
      type_memory_bytes ce et = type_memory_size etv) /\
  val_in_memory tv v (w2n p) s.vs_memory /\
  w2n p + type_memory_size tv <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword(:256) /\
  declared_storage_region cx mid name subs = SOME (tr,k,root) /\
  storage_subregion root path delta tv /\ w2n d = w2n k+delta /\
  w2n k+type_slot_size root <= dimword(:256) /\
  (!mid' name' subs' k' root'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
    (k',root') <> (k,root) ==>
    ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
  encode_value tv v = SOME writes ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx
      (set_storage cx es tr (apply_writes d writes (get_storage cx es tr))) t /\
    alloca_history func t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  Cases_on `?et cap. dty = ArrayT et (Dynamic cap)`
  >- suspend "dynamic" >>
  ` (case dty of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes ce et+31) DIV 32,type_memory_bytes ce et)
      | _ => NONE) = NONE` by
    (Cases_on `dty` >> simp[] >> rename1 `ArrayT et sz` >>
     Cases_on `sz` >> gvs[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_return_def] >>
  Cases_on `type_memory_size tv <= 32`
  >- suspend "single" >> suspend "fixed"
QED

Resume normalized_storage_assign_value_mem[dynamic]:
  gvs[] >> rename1 `evaluate_type _ (ArrayT et (Dynamic cap)) = _` >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `compile_dynarray_to_storage src dst ((type_memory_bytes ce et+31) DIV 32)
      (type_memory_bytes ce et) tr sa = ((),sb)` by
    (Cases_on `tr` >> gvs[compile_assign_value_def, comp_bind_def, comp_return_def]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) =
    SOME (ArrayTV etv (Dynamic cap)) /\
   value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV l))` by
    simp[evaluate_type_def, value_has_type_def] >>
  drule_at (Pat `local_ptrs_reserved _ _`) dynamic_storage_normalized_endpoint_frame >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qx_choose_then `t` strip_assume_tac) >> qexists_tac `t` >> simp[]
QED
Resume normalized_storage_assign_value_mem[single]:
  `type_slot_size tv = 1 /\ type_memory_size tv = 32` by
    (fs[type_memory_size_slots] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx
    (set_storage cx es tr (apply_writes d writes (get_storage cx es tr)))
    (store_copy_prefix (if tr then LocTransient else LocStorage) p d s 1)` by
    (`w2n p + type_memory_size tv <= dimword(:256)` by decide_tac >>
     drule_all storage_fixed_subregion_state >> simp[]) >>
  Cases_on `tr` >> simp[comp_bind_def] >>
  pairarg_tac >> simp[comp_bind_def] >> strip_tac >>
  gvs[comp_return_def] >> pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  drule_all emitted_insts_append >> strip_tac >>
  suspend "single_path"

QED
Resume normalized_storage_assign_value_mem[fixed]:
  strip_tac >>
  `stmt_state_rel ctx func ce cx
    (set_storage cx es tr (apply_writes d writes (get_storage cx es tr)))
    (store_copy_prefix (if tr then LocTransient else LocStorage) p d s
      (type_slot_size tv))` by
    (`w2n p + type_memory_size tv <= dimword(:256)` by decide_tac >>
     drule_all storage_fixed_subregion_state >> simp[]) >>
  Cases_on `tr` >>
  gvs[compile_memory_to_storage_def, compile_memory_to_transient_def,
    comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[type_memory_size_slots] >>
  `type_slot_size tv < dimword(:256) /\
   w2n p + 32 * type_slot_size tv <= s.vs_alloca_next` by decide_tac >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`) storage_fixed_place_path >>
  simp[] >> disch_then drule_all >>
  disch_then (qx_choose_then `t` strip_assume_tac) >> qexists_tac `t` >>
  fs[gas_marked_path_def, store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `(\a. (a.vs_memory,a.vs_labels))`) >>
  simp[store_copy_normalize_def]

QED
Resume normalized_storage_assign_value_mem[single_path]:
  markerLib.RESUME_TAC >>
  rename1 `emit_op MLOAD [src] sa = (loaded,sm)` >>
  gvs[] >> qmatch_asmsub_abbrev_tac `Var out` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> decide_tac) >>
  `!x. dst = Var x ==> x <> out` by metis_tac[] >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[same_blocks_def] >> simp[GSYM APPEND_ASSOC]) >>
  qmatch_asmsub_abbrev_tac `store_copy_prefix loc p d s 1` >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    store_copy_normalize s u = store_copy_prefix loc p d s 1 /\
    (!x. x <> out ==> lookup_var x u = lookup_var x s) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx /\
    u.vs_halted = s.vs_halted` by
    (mp_tac (Q.INST [`loc` |-> `loc`, `b` |-> `p`, `k` |-> `d`,
       `v` |-> `out`, `id` |-> `sa.cs_next_id`] (SPEC_ALL topcopy_singleton_run)) >>
     simp[Abbr `loc`] >>
     `dst <> Var out` by metis_tac[] >>
     `COUNT_LIST 1 = [0]` by EVAL_TAC >>
     simp[store_copy_prefix_def, WORD_ADD_0, WORD_MULT_CLAUSES]) >>
  suspend "single_post"
QED
Resume normalized_storage_assign_value_mem[single_post]:
  markerLib.RESUME_TAC >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (mp_tac (Q.INST [`loc` |-> `loc`, `b` |-> `p`, `k` |-> `d`,
       `v` |-> `out`, `id` |-> `sa.cs_next_id`]
       (SPEC_ALL body_mem_storage_singleton_mem_ok)) >>
     simp[Abbr `loc`] >> metis_tac[]) >>
  `gas_path_mem ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >>
     simp[mk_inst_def, is_terminator_def]) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func ce cx esnew
    (store_copy_prefix loc p d s 1)` >>
  `stmt_state_rel ctx func ce cx esnew u` by
    (irule bodyMemAssignTopCopySemTheory.topcopy_normalized_state >>
     qexistsl_tac [`s`, `sa`] >> simp[GSYM store_copy_normalize_def] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `store_copy_normalize s u = _`
       (mp_tac o Q.AP_TERM `\a. (a.vs_memory,a.vs_labels,a.vs_allocas,a.vs_alloca_next)`) >>
     `COUNT_LIST 1 = [0]` by EVAL_TAC >>
     simp[store_copy_normalize_def, store_copy_prefix_def, Abbr `loc`,
       sstore_def, tstore_def]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    suspend "single_history" >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  fs[same_blocks_def] >> metis_tac[lookup_var_def]
QED
Resume normalized_storage_assign_value_mem[single_history]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `alloca_history func s` mp_tac >>
  simp[alloca_history_def] >> strip_tac >>
  map_every qx_gen_tac [`bb`, `idx`, `inst`] >> strip_tac >>
  Cases_on `idx < LENGTH sa.cs_current_insts`
  >- metis_tac[] >>
  fs[fragExecTheory.fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
  gvs[] >>
  `idx = LENGTH sa.cs_current_insts \/ idx = LENGTH sa.cs_current_insts + 1`
    by decide_tac >>
  gvs[get_instruction_def, EL_APPEND_EQN, mk_inst_def])
QED
Finalise normalized_storage_assign_value_mem
