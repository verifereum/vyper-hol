(* Nonmemory materialization keeps its allocation certificate at the F endpoint. *)
Theory bodyIntCallPostProvenanceArmCopy
Ancestors
  bodyIntCallWindowCode bodyIntCallWindowStorage bodyIntCallWindowPosts
  bodyIntCallProducerInterface exprSimProps exprSimIfExpWidenedAdapter
  exprSimUnwrapProps exprSimCopy fragGasPath gasSummary
  loweringPosts intCallFrame context compileEnv venomState words finite_map
  exprLoweringProps valueEncoding fragGasMode exprLowering
  vyperInterpreter vyperState loweringStateRelDefs
  exprSimIfExpWidenedReattach bodyIntCallMemoryView freshWrites

Theorem nonmemory_unwrap_owned_path:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\
  p.ptr_location <> LocMemory /\
  vv_holds ce cx ty (Value v) (LocatedValue ty p) es s /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  (!a k. Win a k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\ expr_val_rel cx ty v op u /\
    (!sv. sv.cs_next_id <= sa.cs_next_id ==>
      expr_val_at ce cx ty sv sb es v op u) /\
    intcall_vv_provenance ce cx ty sa sb es (Value v)
      (LocatedValue ty (mk_ptr op LocMemory)) u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!a k. Win a k ==> mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
    locals_kept ce es es s u /\ pure_frame ce func es sa s u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `p.ptr_location <> LocCalldata` by (Cases_on `p.ptr_location` >> fs[vv_holds_def]) >>
  `sa.cs_next_id < sb.cs_next_id` by (drule_all unwrap_materialization_id >> simp[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- suspend "code" >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  mp_tac (Q.INST [`lo` |-> `0`, `P` |-> `\a k. F`,
    `reserved` |-> `\q. F`, `scopes` |-> `es.scopes`]
    (SPEC_ALL protected_storage_value_window_forcing_footprint)) >>
  (impl_tac >- simp[allocas_above_def]) >> strip_tac >>
  suspend "finish"
QED

Resume nonmemory_unwrap_owned_path[code]:
  mp_tac (Q.INST [`lo` |-> `0`, `P` |-> `\a k. F`,
    `reserved` |-> `\q. F`, `scopes` |-> `es.scopes`]
    (SPEC_ALL protected_code_value_window_forcing_footprint)) >>
  (impl_tac >- simp[allocas_above_def]) >> strip_tac >>
  suspend "finish_code"
QED

Resume nonmemory_unwrap_owned_path[finish]:
  markerLib.RESUME_TAC >>
  `pure_frame ce func es sa s u` by
    (rewrite_tac[pure_frame_def] >> conj_tac
     >- fs[locals_kept_def] >>
     rpt strip_tac >>
     qpat_x_assum `!a k. regions_disjoint _ _ _ _ ==> _` irule >>
     first_x_assum irule >> qexists_tac `inst` >> simp[]) >>
  `!sv. sv.cs_next_id <= sa.cs_next_id ==>
     expr_val_at ce cx ty sv sb es v op u` by
    (mp_tac (Q.INST [`s` |-> `s`, `u` |-> `u`, `ty` |-> `ty`]
       (SPEC_ALL materialized_value_location)) >>
     (impl_tac >- (simp[] >> metis_tac[])) >> metis_tac[]) >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  qexists_tac `u` >> simp[] >>
  simp[intcall_vv_provenance_def, mk_ptr_def, read_result_def,
       vyperStateTheory.return_def] >>
  disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_size tv`] >>
  simp[] >> fs[regions_disjoint_def] >> metis_tac[]
QED

Resume nonmemory_unwrap_owned_path[finish_code]:
  `pure_frame ce func es sa s u` by
    (rewrite_tac[pure_frame_def] >> conj_tac
     >- fs[locals_kept_def] >>
     rpt strip_tac >>
     qpat_x_assum `!a k. regions_disjoint _ _ _ _ ==> _` irule >>
     first_x_assum irule >> qexists_tac `inst` >> simp[]) >>
  `!sv. sv.cs_next_id <= sa.cs_next_id ==>
     expr_val_at ce cx ty sv sb es v op u` by
    (mp_tac (Q.INST [`s` |-> `s`, `u` |-> `u`, `ty` |-> `ty`]
       (SPEC_ALL materialized_value_location)) >>
     (impl_tac >- (simp[] >> metis_tac[])) >> metis_tac[]) >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  qexists_tac `u` >> simp[] >>
  simp[intcall_vv_provenance_def, mk_ptr_def, read_result_def,
       vyperStateTheory.return_def] >>
  disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_size tv`] >>
  simp[] >> fs[regions_disjoint_def] >> metis_tac[]
QED

Finalise nonmemory_unwrap_owned_path

Theorem nonmemory_unwrap_owned_post:
  unwrap_value ce (LocatedValue ty p) sm = (op,sb) /\
  p.ptr_location <> LocMemory /\ ~is_word_type ty /\
  ty = expr_type e /\ post_value_type ce e = ty /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue ty p) s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    intcall_vv_provenance ce cx ty sa sb ee (Value v)
      (LocatedValue ty (mk_ptr op LocMemory)) u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s` by
    metis_tac[vv_post_read_result] >>
  `vv_holds ce cx ty (Value v) (LocatedValue ty p) ee s /\
   stmt_state_rel ctx func ce cx ee s` by (fs[vv_post_def] >> metis_tac[]) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `es` |-> `ee`,
    `Win` |-> `\a k. ?aid. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,k)`]
    (SPEC_ALL nonmemory_unwrap_owned_path)) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> qexistsl_tac [`aid`,`a`,`k`] >> simp[])) >>
  strip_tac >>
  `expr_post ctx func ce cx e ee (sa with cs_next_var := sm.cs_next_var)
     sb s ee v op u` by
    (simp[expr_post_def, not_fresh_at_def] >> rpt conj_tac
     >- metis_tac[]
     >- metis_tac[]
     >- (rpt strip_tac >> first_x_assum irule >>
         BETA_TAC >> qexists_tac `aid` >> simp[] >> decide_tac) >>
     qpat_x_assum `pure_frame ce func ee sm s u` mp_tac >>
     simp[pure_frame_def] >> strip_tac >> strip_tac >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` irule >>
       qexists_tac `n` >> simp[]) >>
     rpt strip_tac >>
     qpat_x_assum `!off len. _ ==> mem_bytes_at off len _ = _` irule >>
     rpt strip_tac >> first_x_assum irule >>
     qexists_tac `inst` >> simp[] >> decide_tac) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule vv_post_reattach_expr_post >> simp[] >>
      conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
      qexistsl_tac [`sm`, `raw`, `s`, `LocatedValue ty p`] >> simp[]) >>
  gvs[] >> irule intcall_vv_provenance_memory_view >>
  goal_assum (drule_at Any) >> simp[mk_ptr_def]
QED

(* The source result and both reads refer to this very copy endpoint. *)
Theorem ifexp_arm_copy_continuation:
  (is_word_type target_ty \/ same_memory_layout ce at target_ty) /\
  compile_ifexp_arm ce target_ty at (LocatedValue ty p) sm = (op,sb) /\
  p.ptr_location <> LocMemory /\ ~is_word_type ty /\
  ty = expr_type e /\ post_value_type ce e = ty /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue ty p) s /\
  read_result cx raw ee = (INL v,ee) /\
  read_result cx result ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL result,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_exec F (ctx,func) (conditional_result cx raw)
        (ee,s) [] (INL result) ee (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    intcall_vv_provenance ce cx ty sa sb ee result
      (LocatedValue ty (mk_ptr op LocMemory)) u
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `unwrap_value ce (LocatedValue ty p) sm = (op,sb)` by
    gvs[compile_ifexp_arm_def] >>
  drule_all nonmemory_unwrap_owned_post >> strip_tac >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (simp[gas_marked_exec_def] >>
      drule conditional_result_gas_obs >> simp[]) >>
  gvs[] >> irule intcall_vv_provenance_memory_view >>
  goal_assum (drule_at Any) >> simp[mk_ptr_def, read_result_def,
    vyperStateTheory.return_def] >> rpt strip_tac >> gvs[]
QED
