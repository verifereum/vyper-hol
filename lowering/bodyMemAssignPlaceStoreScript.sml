(* Finite counted stores of a value already captured in a safe operand. *)
Theory bodyMemAssignPlaceStore
Ancestors
  assignPlaceMemoryContinuationMem assignPlaceBackendContinuationMem
  augAssignPlaceWordStoreMemory bodyMemAssignSnapshot bodyMemBopRestWordPath
  stmtLowering loweringPosts exprLoweringProps exprSimHypsDefs
  exprSimProps compileEnv fragGasMode fragGasPathMem stmtSimAugAssignPlaceMemory
  venomState words vyperState vyperValue context

Theorem assign_place_captured_store_mem:
  compile_assign_value ce dst loc (vv_operand saved) (is_word_type dty)
    (vv_location saved) dty sty
    (type_memory_bytes ce dty) sa = ((),sb) /\
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
  type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  well_formed_type_value stv /\ well_formed_type_value dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  (is_word_type dty ==> expr_val_rel cx dty v (vv_operand saved) s) /\
  (~is_word_type dty ==>
    ~is_word_type sty /\
    vv_at ce cx sty origin sa ee (Value v) saved s /\
    vv_location saved = SOME LocMemory /\
    eval_operand (vv_operand saved) s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  eval_operand dst s = SOME w /\
  (!x. vv_operand saved = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (loc = LocMemory ==> w2n w + type_memory_size dtv <= s.vs_alloca_next) /\
  place_ptr_rel ce cx s (PlaceR p) w (SOME loc) (Type dty) /\
  storage_place_region cx p /\ expr_sim_inv ce cx env ee /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  stmt_state_rel ctx func ce cx ee s /\
  local_ptrs_reserved ce sa /\ alloca_history func s /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (loc <> LocMemory /\ dty <> sty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
    type_memory_size dtv < dimword (:256)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path T ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx ff z /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP z.vs_allocas aid = SOME b) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?z. gas_marked_path T ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx ff z /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts` by suspend "dispatch" >>
  qexists_tac `z` >> simp[] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next` by
    (drule_all rest_word_marked_allocation_posts >> simp[stmt_state_rel_def]) >>
  simp[] >> rpt strip_tac >> PairCases_on `b` >>
  metis_tac[snapshot_gas_allocas, gas_marked_path_exec]
QED

Resume assign_place_captured_store_mem[dispatch]:
  markerLib.RESUME_TAC >>
  `!x. vv_operand saved = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  Cases_on `is_word_type dty`
  >- (fs[] >>
      `type_memory_size dtv = 32` by metis_tac[word_tv_memory_size] >>
      `loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next` by
        (strip_tac >> fs[] >> decide_tac) >>
      `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
        | _ => MSTORE) [dst;vv_operand saved] sa = ((),sb)` by
        (Cases_on `loc` >>
         gvs[compile_assign_value_def, comp_bind_def, comp_return_def]) >>
      drule_all place_store_word_run_mem >> strip_tac >>
      qexists_tac `t` >> simp[]) >>
  fs[] >> Cases_on `loc = LocMemory`
  >- (fs[] >>
      mp_tac (Q.INST [`cenv` |-> `ce`, `dst_op` |-> `dst`,
        `op` |-> `vv_operand saved`, `src_loc` |-> `SOME LocMemory`,
        `mem_size` |-> `type_memory_bytes ce dty`]
        (SPEC_ALL assign_place_memory_continuation_mem)) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
      qexists_tac `t` >> simp[gas_marked_path_def]) >>
  `(if loc = LocTransient then LocTransient else LocStorage) = loc` by
    metis_tac[] >>
  mp_tac (Q.INST [`tr` |-> `loc = LocTransient`, `vv` |-> `saved`,
    `raw` |-> `Value v`] (SPEC_ALL assign_place_backend_continuation_mem)) >>
  (impl_tac
  >- (simp[] >> Cases_on `saved` >>
      gvs[vv_location_def, read_result_def, return_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Finalise assign_place_captured_store_mem
