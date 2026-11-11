Theory assignEffectfulIndexSnapshotRun
Ancestors
  assignEffectfulIndexPhysical assignEffectfulIndexAllocUnwrap
  assignEffectfulIndexWord assignEffectfulIndexBytesCopy assignEffectfulIndexMemoryCopy
  exprSimMemoryRead exprSimMemoryPath exprSimUnwrapProps exprSimCopy
  stmtSimDefs exprSimProps freshWrites venomState loweringPosts
  valueCopyBytes exprLowering context compileEnv fragGasMode fragGasPath
  loweringStateRelDefs valueEncodingProps exprLoweringProps
  placeStoreStorage exprSimUnwrap emitHelperProps emitHelper venomInst
  venomExecSemantics vyperStorage

(* Memory unwrap does not write memory.  Unlike the ordinary read boundary,
   this retains entry-relative frames even for allocations made after the
   original expression's ownership origin. *)
Theorem snapshot_memory_unwrap_frame[local]:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  read_result cx tv ee = (INL v,ee) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `(is_word_type t ==> t = post_value_type ce e) /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
     (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt ==>
       val_in_memory tvt v (w2n w) s.vs_memory /\
       (is_word_type (post_value_type ce e) ==>
         mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v))` by
    (gvs[vv_post_def, vv_holds_def, is_bytestring_word_type] >> metis_tac[]) >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
    metis_tac[vv_post_read_result] >>
  Cases_on `is_word_type t`
  >- (gvs[unwrap_memory_compile] >>
      qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var))
        (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
      `eval_operand op u = SOME (mload (w2n w) s) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\
       u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory` by
        (drule_all emit_mload_endpoint >> simp[Abbr `u`]) >>
      `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
        (simp[Abbr `u`, lookup_var_def, update_var_def, not_fresh_at_def] >>
         rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
      `alloca_frame ce ee sm s ce ee u` by
        (simp[alloca_frame_def] >> rpt strip_tac >>
         drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
      qexists_tac `u` >> simp[] >> conj_tac
      >- (drule_all emit_mload_marked_path >> simp[Abbr `u`]) >>
      conj_tac
      >- (irule expr_post_of_vv_post_load_physical >> simp[] >>
          conj_tac >- (rpt strip_tac >> fs[GSYM mem_word_at_eq_mload]) >>
          conj_tac
          >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
              irule stmt_state_rel_update_var >>
              `stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
              simp[] >> irule local_ptrs_reserved_fresh >>
              qexists_tac `sm` >> simp[]) >>
          qexistsl_tac [`p`,`s`,`sm`,`post_value_type ce e`] >> simp[]) >>
      simp[Abbr `u`, update_var_def]) >>
  gvs[unwrap_memory_compile, comp_return_def] >>
  qexists_tac `s` >> simp[alloca_frame_def, gas_marked_path_def, cj 1 gas_path_rules] >>
  metis_tac[expr_post_of_vv_post_memory]
QED

Theorem snapshot_storage_word_frame[local]:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  is_word_type t /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t = post_value_type ce e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
     storage_holds cx (p.ptr_location = LocTransient) (post_value_type ce e)
       (Value v) w ee s /\ stmt_state_rel ctx func ce cx ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qabbrev_tac `ld = if p.ptr_location = LocTransient then tload w s else sload w s` >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt ==>
    ld = typed_val_to_w256 tvt v` by
    (rpt strip_tac >> qunabbrev_tac `ld` >> drule_all storage_holds_load >> simp[]) >>
  `emit_op (if p.ptr_location = LocTransient then TLOAD else SLOAD)
     [p.ptr_operand] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  `same_blocks sm sb` by metis_tac[emit_op_same_blocks] >>
  drule_all emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var)) ld s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (qunabbrev_tac `u` >> irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sm` >>
     simp[mk_inst_def, run_inst_seq_def, is_terminator_def] >>
     Cases_on `p.ptr_location = LocTransient` >>
     gvs[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
         is_terminator_def, Abbr `ld`]) >>
  `eval_operand op u = SOME ld` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
    (simp[Abbr `u`, lookup_var_def, update_var_def, not_fresh_at_def] >>
     rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func ce cx ee u` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
     simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    simp[Abbr `u`, update_var_def] >>
  `alloca_frame ce ee sm s ce ee u` by
    (simp[alloca_frame_def] >> rpt strip_tac >>
     drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule expr_post_of_vv_post_load_physical >> simp[] >>
      conj_tac >- (qexists_tac `ld` >> gvs[]) >>
      qexistsl_tac [`p`,`s`,`sm`,`post_value_type ce e`] >>
      simp[Abbr `u`, update_var_def]) >>
  simp[Abbr `u`, update_var_def, alloca_frame_def] >> rpt strip_tac >>
  drule_all copy_buffer_local_region_frame >> simp[update_var_def] >> strip_tac >> metis_tac[]
QED
