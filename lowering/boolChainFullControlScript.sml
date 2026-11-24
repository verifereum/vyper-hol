(* Joint control steps used between BoolChain operands and at the exit. *)
Theory boolChainFullControl
Ancestors
  bodyFullIfExpReach fragGasEmitCtrl fragGasSeqPtr fragGasOriginPtr
  bodyPtrIfExpAssignFrame bodyMemoryDefs bodyPtrDefs bodyFullShared[qualified]
  loweringPosts loweringStateRelDefs exprLoweringProps freshWrites allocaHistory
  vyperStorageFootprint vyperState codegenRel contextCodegenRel fragExec
  compileEnv emitHelper emitHelperProps instMemFrontier ptrDiscipline ptrSafeRun
  unitTransformDefs venomExecProofs venomExecSemantics venomInst venomState
  list finite_map memSafeRun arithmetic

(* Re-entry uses the prefix at the intrinsic horizon for the reachability
   argument, but the emitted JNZ has the same endpoint at every horizon. *)
Theorem bool_word_selected_entry_full:
  emit_inst JNZ [op; Label lt; Label lf] [] sm = ((),sn) /\
  fn_has_code sm sn func /\ se.cs_current_bb = (if b then lt else lf) /\
  se.cs_current_insts = [] /\ sa.cs_next_var <= se.cs_next_var /\
  u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~u.vs_halted /\
  eval_operand op u = SOME (if b then 1w else 0w) /\ op_taint tn op = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ alloca_history func u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ return_buf_frame d cenv sa s0 /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) marks (OK u,G,tn) /\
    expr_post H ctx func cenv cx e es sa sb s0 ee v op u /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn u) ==>
  ?z. z = jump_to (if b then lt else lf) u /\
    return_buf_frame d cenv se z /\ alloca_history func z /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!fn inst s. frag_reachable ctx func z fn inst s ==> dalloca_fmp_headroom inst s) /\
    ~z.vs_halted /\ z.vs_current_bb = se.cs_current_bb /\
    z.vs_inst_idx = LENGTH se.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK z,G,tn) /\
      stmt_state_rel H ctx func cenv cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee G tn z)
Proof
  strip_tac >> qabbrev_tac `h = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 h ee.storage_trace` by
    fs[Abbr `h`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `h` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo u` by fs[ghost_inv_at_def] >>
  qabbrev_tac `z = jump_to (if b then lt else lf) u` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK z,G,tn)` by
    (gen_tac >> simp[Abbr `z`] >> irule emit_jnz_origin_ptr >> simp[] >>
     qexistsl_tac [`op`,`sm`,`sn`] >> simp[]) >>
  `~z.vs_halted /\ z.vs_current_bb = se.cs_current_bb /\ z.vs_inst_idx = 0 /\
   z.vs_alloca_next = u.vs_alloca_next /\ z.vs_allocas = u.vs_allocas /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (simp[Abbr `z`, jump_to_def, allocas_below_fmp_def] >>
     metis_tac[allocas_below_fmp_def]) >>
  qexists_tac `z` >> simp[] >> conj_tac
  >- (simp[Abbr `z`, return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
      goal_assum (drule_at Any) >> simp[] >> fs[expr_post_def]) >>
  conj_tac
  >- (irule alloca_history_jump >> simp[] >> qexists_tac `u` >> simp[]) >>
  conj_tac
  >- (`gas_origin_ptr_path (DF h,lo,explicit,ctx,func,PG)
          (s0,G0,tn0) marks (OK z,G,tn)` by
        (qpat_assum `gas_origin_ptr_path _ _ marks _`
          (mp_then Any (qspecl_then [`u`,`G`,`tn`,`[]`] mp_tac) gas_origin_ptr_path_append) >> simp[]) >>
      qpat_assum `gas_origin_ptr_path _ _ marks (OK z,_,_)`
        (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
      simp[] >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  simp[Abbr `z`, stmt_state_rel_jump_to, bodyFullSharedTheory.ghost_inv_at_jump] >>
  fs[expr_post_def]
QED

Theorem emitted_assign_origin_ptr_edge[local]:
  emit_inst ASSIGN [src] [rv] sd = ((),sy) /\ fn_has_code sd sy func /\
  u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
  ~u.vs_halted /\ eval_operand src u = SOME w /\ allocas_from lo u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G,tn) []
    (OK (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts),
     step_prov PG G (mk_inst sd.cs_next_id ASSIGN [src] [rv]) (update_var rv w u),
     step_taint (mk_inst sd.cs_next_id ASSIGN [src] [rv]) u (update_var rv w u) tn)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `i = mk_inst sd.cs_next_id ASSIGN [src] [rv]` >>
  `get_instruction bb u.vs_inst_idx = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `i`]) >>
  `step_inst_base i u = OK (update_var rv w u)` by
    simp[Abbr `i`, mk_inst_def, step_inst_base_opcode_eqs,
         exec_pure1_def, comp_bind_def, comp_return_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn i u` by
    (simp[Abbr `i`, ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure1_def,
          comp_bind_def, comp_return_def, update_var_def, allocas_from_def,
          allocas_below_fmp_def]) >>
  `inst_mem_below_frontier i u` by
    (irule below_frontier_no_ranges >> simp[Abbr `i`, mk_inst_def]) >>
  `inst_dload_in_section i u` by simp[Abbr `i`, inst_dload_in_section_def, mk_inst_def] >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   i.inst_opcode <> GAS /\ dalloca_no_wrap i u` by
    simp[Abbr `i`, dalloca_no_wrap_def, mk_inst_def, is_terminator_def] >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `ctx_has_dalloca ctx ==> dalloca_no_wrap i u` by simp[] >>
  drule_all straight_line_origin_ptr_edge >> simp[ADD1]
QED

Theorem bool_word_assign_exit_full:
  emit_inst ASSIGN [src] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
  ~u.vs_halted /\ alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  eval_operand src u = SOME w /\ ptr_val_ok cx ty v src G tn u /\ is_word_type ty /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa rv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn u) ==>
  ?z Gz tf.
    z = jump_to xl (update_var rv w u) /\
    Gz = step_prov PG G (mk_inst sd.cs_next_id ASSIGN [src] [rv]) (update_var rv w u) /\
    tf = step_taint (mk_inst sd.cs_next_id ASSIGN [src] [rv]) u (update_var rv w u) tn /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    z.vs_alloca_next = u.vs_alloca_next /\
    ptr_val_ok cx ty v (Var rv) Gz tf z /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tf /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK z,Gz,tf) /\
      ghost_inv_at (DF H) lo d cenv cx ee Gz tf z)
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst sd.cs_next_id ASSIGN [src] [rv]` >>
  qabbrev_tac `u1 = update_var rv w u` >>
  qabbrev_tac `z = jump_to xl u1` >>
  qabbrev_tac `Gz = step_prov PG G i u1` >>
  qabbrev_tac `tf = step_taint i u u1 tn` >>
  qexistsl_tac [`z`,`Gz`,`tf`] >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\ z.vs_inst_idx = 0` by
    simp[Abbr `z`, Abbr `u1`, jump_to_def, update_var_def] >>
  simp[] >> conj_tac
  >- (irule alloca_history_jump >> simp[] >> qexists_tac `u` >> simp[]) >>
  conj_tac
  >- (simp[Abbr `z`, Abbr `u1`, jump_to_def, update_var_def, allocas_below_fmp_def] >>
      metis_tac[allocas_below_fmp_def]) >>
  conj_tac
  >- (simp[ptr_val_ok_def, Abbr `Gz`, Abbr `tf`, Abbr `i`, Abbr `u1`, assign_result_prov] >>
      drule assign_result_taint >> simp[] >> fs[ptr_val_ok_def]) >>
  conj_tac
  >- (simp[Abbr `Gz`, Abbr `tf`, Abbr `i`, Abbr `u1`] >>
      irule assign_ghost_kept_at >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo u` by fs[ghost_inv_at_def] >>
  conj_tac
  >- (`gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (u,G,tn) []
          (OK (u1 with vs_inst_idx := LENGTH sy.cs_current_insts),Gz,tf)` by
        (simp[Abbr `Gz`, Abbr `tf`, Abbr `i`, Abbr `u1`] >>
         irule emitted_assign_origin_ptr_edge >> simp[]) >>
      drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
      `z = jump_to xl (u1 with vs_inst_idx := LENGTH sy.cs_current_insts)` by
        simp[Abbr `z`, jump_to_def] >>
      pop_assum SUBST1_TAC >> irule emit_jmp_origin_ptr >>
      simp[Abbr `u1`, update_var_def, allocas_from_def, allocas_below_fmp_def] >>
      conj_tac >- metis_tac[allocas_below_fmp_def] >>
      conj_tac >- metis_tac[allocas_from_def] >>
      qexistsl_tac [`sy`,`sz`] >>
      qpat_assum `emit_inst ASSIGN _ _ _ = _` (mp_then Any mp_tac emit_inst_extends) >>
      simp[]) >>
  `ghost_inv_at (DF H) lo d cenv cx ee Gz tf u1` by
    (simp[Abbr `Gz`, Abbr `tf`, Abbr `i`, Abbr `u1`] >>
     irule assign_ghost_inv_at >> simp[] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[Abbr `z`, bodyFullSharedTheory.ghost_inv_at_jump]
QED
