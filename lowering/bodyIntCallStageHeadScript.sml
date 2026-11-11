(* One actual endpoint for allocation followed by argument staging. *)
Theory bodyIntCallStageHead
Ancestors
  bodyIntCallStageAllocation bodyIntCallStageStore bodyIntCallHeldByteFrame
  exprSimCopy exprSimStorageCopy stmtSimReturn bodyMemoryDefs
  exprLoweringProps loweringHalt loweringPosts freshWrites
  compileEnv context venomState venomInst finite_map words fragGasPath

Theorem intcall_stage_alloc_store_map:
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm = (buf,si) /\
  compile_store_memory ce op buf.buf_operand ty ty si = ((),sn) /\
  fn_has_code sm si func /\ fn_has_code si sn func /\
  MAX 32 (type_memory_bytes ce ty) < dimword (:256) /\
  sm.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ intcall_held_args ce cx a sm es s H /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  eval_operand op s = SOME sw /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) ==>
  ?t inst. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
    intcall_held_args ce cx a sn es t H /\ wb_frame ce es sm s t /\
    eval_operand buf.buf_operand t = SOME (n2w s.vs_alloca_next) /\
    val_in_memory tv v s.vs_alloca_next t.vs_memory /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\
    FLOOKUP t.vs_allocas sm.cs_next_id =
      SOME (s.vs_alloca_next,MAX 32 (type_memory_bytes ce ty)) /\
    (!y. not_fresh_at sm y ==> lookup_var y t = lookup_var y s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!off len. off+len <= s.vs_alloca_next \/
      s.vs_alloca_next+MAX 32 (type_memory_bytes ce ty) <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) ==>
      regions_disjoint s.vs_alloca_next (MAX 32 (type_memory_bytes ce ty)) lb sz) /\
    type_memory_size tv <= MAX 32 (type_memory_bytes ce ty) /\
    t.vs_allocas = s.vs_allocas |+
      (sm.cs_next_id,(s.vs_alloca_next,MAX 32 (type_memory_bytes ce ty)))
Proof
  strip_tac >> drule_all intcall_stage_allocation >>
  strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `u.vs_labels = s.vs_labels` by simp[update_var_def] >>
  `eval_operand op u = SOME sw` by
    (drule_all eval_operand_old_vars >> simp[]) >>
  `(!x. op = Var x ==> not_fresh_at si x)` by metis_tac[] >>
  `(!x. buf.buf_operand = Var x ==> not_fresh_at si x)` by simp[] >>
  `if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) u.vs_memory` by simp[] >>
  drule_all intcall_stage_store_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    (gvs[stmt_state_rel_def] >> metis_tac[alloca_room_next_lt]) >>
  `w2n (n2w s.vs_alloca_next : 256 word) = s.vs_alloca_next` by simp[] >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_labels = s.vs_labels /\
   contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by suspend "fields" >>
  `wb_frame ce es sm s t /\ intcall_held_args ce cx a sn es t H` by
    suspend "held" >>
  `stmt_state_rel ctx func ce cx es t` by suspend "state" >>
  qexistsl_tac [`t`,`inst`] >> simp[] >>
  conj_tac >- suspend "path" >>
  conj_tac >- metis_tac[eval_operand_old_vars] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[not_fresh_at_mono]
QED

Resume intcall_stage_alloc_store_map[fields]:
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
    mp_tac >>
  simp[venom_state_component_equality, contract_storage_def,
       contract_transient_def, update_var_def]
QED

Resume intcall_stage_alloc_store_map[held]:
  `sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`,`op`,`buf.buf_operand`,`ty`,`ty`,`si`]
      ci_mono_compile_store_memory) >> gvs[ci_mono_def]) >>
  irule intcall_held_allocation_bytes_frame >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`sm.cs_next_id`,
    `MAX 32 (type_memory_bytes ce ty)`,`si`,`u`] >> simp[] >>
  qpat_x_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` mp_tac >>
  simp[arithmeticTheory.ADD_COMM] >> disch_tac >> rpt gen_tac >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k t.vs_memory = _`
    (qspecl_then [`off`,`len`] mp_tac) >> simp[arithmeticTheory.ADD_COMM]
QED

Resume intcall_stage_alloc_store_map[state]:
  `!name lb len. local_region ce es.scopes u name lb len ==>
     s.vs_alloca_next + MAX 32 (type_memory_bytes ce ty) <= lb \/
     lb + len <= s.vs_alloca_next` by
    (rpt strip_tac >>
     `local_region ce es.scopes s name lb len` by
       (qspecl_then [`ce`,`sm`,`s`,`u`] mp_tac copy_buffer_local_region_frame >>
        (impl_tac >- simp[]) >>
        disch_then (qspecl_then [`es.scopes`,`name`,`lb`,`len`] mp_tac) >>
        metis_tac[]) >>
     disj2_tac >> irule body_local_region_frontier >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `u = _` kall_tac >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`s.vs_alloca_next`,`inst`,`u`,`si`,
    `MAX 32 (type_memory_bytes ce ty)`] >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (rpt gen_tac >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at a k t.vs_memory = _`
       (qspecl_then [`off`,`len`] mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  suspend "static"
QED

Resume intcall_stage_alloc_store_map[static]:
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
    mp_tac >> simp[venom_state_component_equality, copy_static_def]
QED

Resume intcall_stage_alloc_store_map[path]:
  metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED
Finalise intcall_stage_alloc_store_map

(* Compatibility projection: the implementation above owns the execution. *)
Theorem intcall_stage_alloc_store:
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm = (buf,si) /\
  compile_store_memory ce op buf.buf_operand ty ty si = ((),sn) /\
  fn_has_code sm si func /\ fn_has_code si sn func /\
  MAX 32 (type_memory_bytes ce ty) < dimword (:256) /\
  sm.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ intcall_held_args ce cx a sm es s H /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  eval_operand op s = SOME sw /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) ==>
  ?t inst. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
    intcall_held_args ce cx a sn es t H /\ wb_frame ce es sm s t /\
    eval_operand buf.buf_operand t = SOME (n2w s.vs_alloca_next) /\
    val_in_memory tv v s.vs_alloca_next t.vs_memory /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\
    FLOOKUP t.vs_allocas sm.cs_next_id =
      SOME (s.vs_alloca_next,MAX 32 (type_memory_bytes ce ty)) /\
    (!y. not_fresh_at sm y ==> lookup_var y t = lookup_var y s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!off len. off+len <= s.vs_alloca_next \/
      s.vs_alloca_next+MAX 32 (type_memory_bytes ce ty) <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) ==>
      regions_disjoint s.vs_alloca_next (MAX 32 (type_memory_bytes ce ty)) lb sz) /\
    type_memory_size tv <= MAX 32 (type_memory_bytes ce ty)
Proof
  strip_tac >> drule_all intcall_stage_alloc_store_map >> strip_tac >>
  qexistsl_tac [`t`,`inst`] >> gvs[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
