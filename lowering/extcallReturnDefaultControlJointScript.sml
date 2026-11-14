(* Joint routing edges for the default-return shell. *)
Theory extcallReturnDefaultControlJoint
Ancestors
  extcallReturnDefaultWordJoint extcallReturnDefaultRouting fragGasCopyLoop extCallCodeCheck
  externalEntryProps context emitHelper emitHelperProps fragExec fragExecPtr venomMemDefs venomState venomInst
  venomExecSemantics ptrDiscipline compileEnv ptrSafeRun contextCodegenRel codegenRel
  exprLoweringProps list fragGasSeqPtr fragExecMem bodyPtrDefs
  bodyFullGhostFrame extcallReturnDefaultResources loweringStateRelDefs
  bodyPtrEnvBuiltinsAllocation allocationPtr bodyFullUnwrapRun

Theorem return_default_join_joint:
  emit_inst JMP [Label lbl] [] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (jump_to lbl s),G,tn)
Proof
  strip_tac >> gen_tac >>
  drule_all emitted_jump_common_instruction >> strip_tac >>
  irule copy_jmp_origin_ptr >> simp[] >> qexists_tac `a.cs_next_id` >> simp[]
QED

Theorem return_default_select_joint:
  emit_inst JNZ [test;Label yes;Label no] [] a = ((),b) /\
  fn_has_code a b func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand test s = SOME (if empty then 1w else 0w) /\
  op_taint tn test = {} ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to (if empty then yes else no) s),G,tn)
Proof
  strip_tac >> gen_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id JNZ [test;Label yes;Label no] []]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule copy_jump_origin_ptr >> simp[] >>
  qexists_tac `mk_inst a.cs_next_id JNZ [test;Label yes;Label no] []` >>
  simp[mk_inst_def] >>
  conj_tac >- (Cases_on `empty` >> simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[mk_inst_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    allocas_from_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
    GSYM op_taint_def] >>
  conj_tac >- (gen_tac >> Cases_on `op = test` >> gvs[] >> Cases_on `op` >> gvs[op_taint_def]) >>
  Cases_on `empty` >> simp[GSYM mk_inst_def, step_inst_non_invoke,
    step_inst_base_opcode_eqs, mk_inst_def, jump_to_def]
QED

(* Both test instructions share one concrete operational and ghost run. *)
Theorem return_default_test_joint:
  emit_op RETURNDATASIZE [] a = (rds,m) /\
  emit_op ISZERO [rds] m = (test,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?u H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,H,tm)) /\
    eval_operand test u = SOME (if s.vs_returndata = [] then 1w else 0w) /\
    op_taint tm test = {} /\
    H = DRESTRICT (DRESTRICT G
      (COMPL {STRING #"%" (toString a.cs_next_var)}))
      (COMPL {STRING #"%" (toString m.cs_next_var)}) /\
    tm = tn with t_var :=
      (tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{})) |+
        (STRING #"%" (toString m.cs_next_var),{}) /\
    u = (update_var (STRING #"%" (toString m.cs_next_var))
      (if s.vs_returndata = [] then 1w else 0w)
      (update_var (STRING #"%" (toString a.cs_next_var))
        (n2w (LENGTH s.vs_returndata)) s))
      with vs_inst_idx := LENGTH b.cs_current_insts
Proof
  strip_tac >>
  drule_all return_default_test_run >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `y = STRING #"%" (toString m.cs_next_var)` >>
  `rds = Var x /\ test = Var y /\
   b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id RETURNDATASIZE [] [x];
      mk_inst m.cs_next_id ISZERO [Var x] [y]] /\
   emitted_insts a b = [mk_inst a.cs_next_id RETURNDATASIZE [] [x];
      mk_inst m.cs_next_id ISZERO [Var x] [y]]` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, Abbr `x`, Abbr `y`,
      emitted_insts_def] >>
     simp[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH b.cs_current_insts`,
    `DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})`,
    `tn with t_var := (tn.t_var |+ (x,{})) |+ (y,{})`] >>
  conj_tac >- suspend "path" >>
  simp[op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
    eval_operand_def, lookup_var_def]
QED
Resume return_default_test_joint[path]:
  gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  conj_tac >- simp[] >>
  qexistsl_tac [`emitted_insts a b`, `a`] >> simp[is_terminator_def] >>
  conj_tac >- (simp[run_inst_seq_mem_ok_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_base_opcode_eqs, exec_read0_def, exec_pure1_def,
    eval_operands_def, eval_operand_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]) >>
  irule inst_seq_ptr_lower_bound_transport >>
  conj_tac >- simp[mk_inst_def] >> simp[] >>
  qexists_tac `0` >> simp[] >>
  simp[inst_seq_ptr_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_read0_def, exec_pure1_def, eval_operands_def, eval_operand_def,
    lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read0_def,
    exec_pure1_def, eval_operands_def, eval_operand_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    step_prov_def, set_prov_def, out_prov_def,
    step_taint_def, out_taint_def, set_var_taint_def, mem_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, adopt_reset_def,
    store_taint_def, imm_taint_def, range_bytes_def,
    finite_mapTheory.FLOOKUP_DEF, SF CONJ_ss] >>
  simp[op_taint_def, finite_mapTheory.FLOOKUP_UPDATE, taint_component_equality]
QED
Finalise return_default_test_joint

Theorem return_default_shell_joint:
  emit_op RETURNDATASIZE [] a = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (test,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [test;Label dl;Label cl] [] a5 = ((),a6) /\
  fn_has_code a a2 func /\ fn_has_code a5 a6 func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?u H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,H,tm)) /\
    H = DRESTRICT (DRESTRICT G
      (COMPL {STRING #"%" (toString a.cs_next_var)}))
      (COMPL {STRING #"%" (toString a1.cs_next_var)}) /\
    tm = tn with t_var :=
      (tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{})) |+
        (STRING #"%" (toString a1.cs_next_var),{}) /\
    u = jump_to (if s.vs_returndata = [] then dl else cl)
      ((update_var (STRING #"%" (toString a1.cs_next_var))
        (if s.vs_returndata = [] then 1w else 0w)
        (update_var (STRING #"%" (toString a.cs_next_var))
          (n2w (LENGTH s.vs_returndata)) s))
        with vs_inst_idx := LENGTH a2.cs_current_insts)
Proof
  strip_tac >> drule_all return_default_test_joint >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`jump_to (if s.vs_returndata = [] then dl else cl) u`, `H`, `tm`] >>
  simp[] >> gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,H,tm) []
    (OK (jump_to (if s.vs_returndata = [] then dl else cl) u),H,tm)` by
    (irule return_default_select_joint >> simp[] >>
     qexistsl_tac [`a5`, `a6`, `test`] >> simp[] >>
     gvs[fresh_label_def, comp_bind_def, comp_return_def,
       emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
       update_var_def, allocas_from_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` assume_tac) >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >> simp[] >>
  disch_then irule >> gvs[]
QED

(* Read-only shell transport is independent of the chosen dead mask. *)
Theorem return_default_shell_joint_frame:
  sa.cs_next_var <= n1 /\ sa.cs_next_var <= n2 /\
  u = jump_to lbl ((update_var (STRING #"%" (toString n2)) w2
        (update_var (STRING #"%" (toString n1)) w1 s))
          with vs_inst_idx := k) /\
  H = DRESTRICT (DRESTRICT G (COMPL {STRING #"%" (toString n1)}))
        (COMPL {STRING #"%" (toString n2)}) /\
  tm = tn with t_var :=
    (tn.t_var |+ (STRING #"%" (toString n1),{})) |+
      (STRING #"%" (toString n2),{}) ==>
  (!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!lo cenv es sa0 G0 tn0 s0.
    sa0.cs_next_var <= sa.cs_next_var /\
    ghost_kept_at lo cenv es sa0 G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es sa0 G0 tn0 s0 H tm) /\
  (!D lo d cenv cx ee.
    ghost_inv_at D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    ghost_inv_at D lo d cenv cx ee H tm u) /\
  (!H0 cenv cx ee.
    local_ptrs_reserved cenv sa /\ stmt_state_rel H0 ctx func cenv cx ee s ==>
    stmt_state_rel H0 ctx func cenv cx ee u) /\
  (!cenv es ee sa0 s0.
    sa0.cs_next_var <= sa.cs_next_var /\ wb_frame cenv es ee sa0 s0 s ==>
    wb_frame cenv es ee sa0 s0 u)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def, jump_to_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_DRESTRICT, op_taint_def] >> metis_tac[]) >>
  simp[] >> conj_tac >- suspend "kept" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- (rpt strip_tac >> irule return_default_shell_state >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule return_default_shell_wb_frame >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume return_default_shell_joint_frame[kept]:
  rpt strip_tac >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sa x` by
    (rw[not_fresh_at_def] >> first_x_assum irule >> decide_tac) >>
  irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
Resume return_default_shell_joint_frame[ghost]:
  rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
  goal_assum (drule_at Any) >> simp[jump_to_def, update_var_def] >>
  qexistsl_tac [`G`, `ee`, `s`, `tn`] >> simp[] >>
  gvs[jump_to_def, update_var_def, lookup_var_def]
QED
Finalise return_default_shell_joint_frame

(* Certify the selected allocation run, without selecting a second endpoint. *)
Theorem return_default_alloc_joint:
  compile_alloc_buffer n a = (buf,b) /\ fn_has_code a b func /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (r with vs_inst_idx := LENGTH b.cs_current_insts),
     step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString a.cs_next_var)]) r,
     step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString a.cs_next_var)]) s r tn)
Proof
  strip_tac >> gen_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString a.cs_next_var)]] /\
   emitted_insts a b = [mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString a.cs_next_var)]]` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def, emitted_insts_def] >> simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`emitted_insts a b`, `a`] >> simp[is_terminator_def] >>
  conj_tac >- suspend "mem" >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  simp[inst_seq_ptr_def] >>
  irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >> simp[] >>
  qexists_tac `0` >> simp[ptr_inst_ok_alloca]
QED
Resume return_default_alloc_joint[mem]:
  simp[run_inst_seq_mem_ok_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  CASE_TAC >> simp[]
QED
Finalise return_default_alloc_joint

Theorem return_default_alloc_ghost_inv_at:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa out /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ghost_inv_at D lo d cenv cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  strip_tac >> drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- suspend "return" >>
  conj_tac >- (rpt strip_tac >> `x <> out` by metis_tac[] >> metis_tac[]) >>
  suspend "fixed"
QED
Resume return_default_alloc_ghost_inv_at[locals]:
  rpt gen_tac >> strip_tac >>
  `p <> out` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  conj_tac >- (drule_all alloca_step_old_ptr_covers >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  irule alloca_step_local_robust >> simp[] >> metis_tac[]
QED
Resume return_default_alloc_ghost_inv_at[return]:
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> fs[return_buf_ptr_def] >>
  `x <> out` by metis_tac[] >>
  `ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) x u x1` by
    (drule_all alloca_step_old_ptr_covers >> simp[]) >>
  metis_tac[]
QED
Resume return_default_alloc_ghost_inv_at[fixed]:
  conj_tac >- suspend "storage" >>
  conj_tac >- (rpt strip_tac >> simp[] >> first_x_assum irule >>
    simp[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  conj_tac >- (rpt strip_tac >> `x <> out` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >> metis_tac[]) >>
  irule ptrSafetyTransportTheory.step_inst_allocas_from >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ctx`, `0`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`] >>
  simp[step_inst_non_invoke, mk_inst_def]
QED
Resume return_default_alloc_ghost_inv_at[storage]:
  `u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def]) >>
  gvs[stor_taint_ok_at_def, step_taint_def, store_taint_def, imm_taint_def,
    adopt_reset_def, mk_inst_def]
QED
Finalise return_default_alloc_ghost_inv_at

Theorem return_default_alloc_ghost_kept_at:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  ~not_fresh_at sa out /\ lo <= s.vs_alloca_next ==>
  ghost_kept_at lo cenv es sa G tn s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  strip_tac >> drule_all alloca_step_ghost_kept >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >>
  rewrite_tac[ghost_kept_def, ghost_kept_at_def] >> strip_tac >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!aid off sz i. FLOOKUP _ aid = SOME (off,sz) /\ _ ==> _` irule >>
    simp[] >> qexistsl_tac [`aid`, `off`, `sz`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!n b sz i. _` irule >>
    simp[] >> metis_tac[]) >>
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> metis_tac[]
QED

Theorem return_default_alloc_run_step:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r ==>
  step_inst_base (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString a.cs_next_var)]) s = OK r /\
  b.cs_current_bb = a.cs_current_bb /\
  buf.buf_operand = Var (STRING #"%" (toString a.cs_next_var)) /\
  a.cs_next_var <= b.cs_next_var
Proof
  gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
    emit_def, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
    run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def, AllCaseEqs()]
QED

Theorem return_default_alloc_control:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK r /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  r.vs_halted = s.vs_halted /\ r.vs_current_bb = s.vs_current_bb /\
  r.vs_returndata = s.vs_returndata /\
  allocas_from lo r /\ lo <= r.vs_alloca_next
Proof
  strip_tac >>
  `allocas_from lo r /\ lo <= r.vs_alloca_next` by
    (irule ptrSafetyTransportTheory.step_inst_allocas_from >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ctx`, `0`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  simp[] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def]
QED

Theorem return_default_prefix_joint:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  emit_op RETURNDATASIZE [] b = (rds,b1) /\
  emit_op ISZERO [rds] b1 = (test,b2) /\
  fresh_label "extcall_default" b2 = (dl,b3) /\
  fresh_label "extcall_decode" b3 = (cl,b4) /\
  fresh_label "extcall_exit" b4 = (xl,b5) /\
  emit_inst JNZ [test;Label dl;Label cl] [] b5 = ((),b6) /\
  fn_has_code a b func /\ fn_has_code b b2 func /\ fn_has_code b5 b6 func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?u Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tm)) /\
    Gf = DRESTRICT (DRESTRICT
      (step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) r)
      (COMPL {STRING #"%" (toString b.cs_next_var)}))
      (COMPL {STRING #"%" (toString b1.cs_next_var)}) /\
    tm = (step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString a.cs_next_var)]) s r tn) with t_var :=
      (((step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) s r tn).t_var |+
        (STRING #"%" (toString b.cs_next_var),{})) |+
        (STRING #"%" (toString b1.cs_next_var),{})) /\
    u = jump_to (if s.vs_returndata = [] then dl else cl)
      ((update_var (STRING #"%" (toString b1.cs_next_var))
        (if s.vs_returndata = [] then 1w else 0w)
        (update_var (STRING #"%" (toString b.cs_next_var))
          (n2w (LENGTH s.vs_returndata))
          (r with vs_inst_idx := LENGTH b.cs_current_insts)))
        with vs_inst_idx := LENGTH b2.cs_current_insts)
Proof
  strip_tac >> drule_all return_default_alloc_run_step >> strip_tac >>
  drule_all return_default_alloc_control >> strip_tac >>
  qabbrev_tac `ar = r with vs_inst_idx := LENGTH b.cs_current_insts` >>
  qabbrev_tac `AG = step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString a.cs_next_var)]) r` >>
  qabbrev_tac `atn = step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString a.cs_next_var)]) s r tn` >>
  `~ar.vs_halted /\ allocas_from lo ar /\
   ar.vs_current_bb = b.cs_current_bb /\
   ar.vs_inst_idx = LENGTH b.cs_current_insts /\
   LENGTH ar.vs_returndata < dimword (:256)` by
    simp[Abbr `ar`, allocas_from_def] >>
  drule_all return_default_shell_joint >>
  disch_then (qspecl_then [`atn`, `explicit`, `PG`, `AG`] strip_assume_tac) >>
  qexistsl_tac [`u`, `H`, `tm`] >>
  conj_tac >- suspend "path" >>
  gvs[Abbr `AG`, Abbr `atn`, Abbr `ar`]
QED
Resume return_default_prefix_joint[path]:
  gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK ar,AG,atn)` by
    (simp[Abbr `ar`, Abbr `AG`, Abbr `atn`] >>
     irule return_default_alloc_joint >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` assume_tac) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >> gvs[]
QED
Finalise return_default_prefix_joint

(* Resource transport is conditional on each entry horizon, on the supplied run. *)
Theorem return_default_alloc_resources:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv a /\ n < dimword (:256) ==>
  !H. stmt_state_rel H ctx func cenv cx ee s ==>
    stmt_state_rel H ctx func cenv cx ee r /\
    (?w. eval_operand buf.buf_operand r = SOME w /\
      FLOOKUP r.vs_allocas a.cs_next_id = SOME (w2n w,n) /\
      w2n w + n < dimword (:256) /\
      (!aid off sz. aid < a.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
        regions_disjoint (w2n w) n off sz) /\
      (!name off sz. local_region cenv ee.scopes r name off sz ==>
        regions_disjoint (w2n w) n off sz)) /\
    r.vs_memory = s.vs_memory /\
    (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP r.vs_allocas aid = SOME entry)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem return_default_alloc_ghost_resources:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  fn_has_code a b func /\ local_ptrs_reserved cenv a /\
  n < dimword (:256) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) ==>
  !H D lo d. stmt_state_rel H ctx func cenv cx ee s /\
    ghost_inv_at D lo d cenv cx ee G tn s ==>
    ghost_inv_at D lo d cenv cx ee
      (step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) r)
      (step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) s r tn) r /\
    ptr_covers
      (step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) r)
      (step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) s r tn)
      (STRING #"%" (toString a.cs_next_var)) r n /\
    ghost_kept_at lo cenv ee a G tn s
      (step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) r)
      (step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) s r tn)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all return_default_alloc_run_step >> strip_tac >>
  `~not_fresh_at a (STRING #"%" (toString a.cs_next_var))` by
    simp[not_fresh_at_def] >>
  conj_tac >- (irule return_default_alloc_ghost_inv_at >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac >- (drule_all alloca_step_ptr_covers >> simp[]) >>
  irule return_default_alloc_ghost_kept_at >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[ghost_inv_at_def] >> metis_tac[]
QED

Theorem return_default_assert_reject_joint:
  emit_void ASSERT [arg] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand arg s = SOME 0w /\ op_taint tn arg = {} ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort Revert_abort (revert_state (set_returndata [] s)),G,tn)
Proof
  strip_tac >> gen_tac >>
  `emit_inst ASSERT [arg] [] a = ((),b)` by
    gvs[emit_void_def, emit_inst_def] >>
  drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `step_inst_base (mk_inst a.cs_next_id ASSERT [arg] []) s =
    Abort Revert_abort (revert_state (set_returndata [] s))` by
    simp[step_ASSERT_revert] >>
  irule fragGasEmitCtrlTheory.exit_inst_origin_ptr >>
  simp[exit_result_def] >>
  qexists_tac `mk_inst a.cs_next_id ASSERT [arg] []` >>
  simp[gasEventsTheory.gas_events_step_def,
    gasCountTheory.gas_count_step_def, is_terminator_def,
    step_inst_non_invoke, exit_result_def, mk_inst_def,
    memSafeRunTheory.mem_safe_step_non_invoke,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    memSafeRunTheory.inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[mk_inst_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    GSYM op_taint_def] >>
  rpt strip_tac >> gvs[GSYM mk_inst_def, step_inst_non_invoke]
QED

Theorem return_default_codesize_joint:
  emit_op EXTCODESIZE [addr] a = (out,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} ==>
  ?u G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1)) /\
    u = (update_var (STRING #"%" (toString a.cs_next_var))
      (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s)
      with vs_inst_idx := LENGTH b.cs_current_insts /\
    G1 = DRESTRICT G (COMPL {STRING #"%" (toString a.cs_next_var)}) /\
    tn1 = tn with t_var := tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{}) /\
    eval_operand out u = SOME (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) /\
    op_taint tn1 out = {}
Proof
  strip_tac >>
  drule_all extCallCodeCheckTheory.extcall_extcodesize_exact_edge >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `cw:bytes32 = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)` >>
  `out = Var x /\ b.cs_current_bb = a.cs_current_bb /\
    b.cs_current_insts = a.cs_current_insts ++ [mk_inst a.cs_next_id EXTCODESIZE [addr] [x]]` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, Abbr `x`] >>
  `step_inst_base (mk_inst a.cs_next_id EXTCODESIZE [addr] [x]) s = OK (update_var x cw s)` by
    (simp[Abbr `cw`] >> irule exprSimSliceExtcodeTheory.slice_extcodesize_step >> simp[]) >>
  qexistsl_tac [`(update_var x cw s) with vs_inst_idx := LENGTH b.cs_current_insts`,
    `DRESTRICT G (COMPL {x})`, `tn with t_var := tn.t_var |+ (x,{})`] >>
  conj_tac >- suspend "path" >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, op_taint_def]
QED
Resume return_default_codesize_joint[path]:
  gen_tac >>
  `LENGTH b.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `out' = x` by gvs[] >>
  qpat_x_assum `!D lo. _` (qspecl_then [`D`, `lo`] mp_tac) >>
  simp[GSYM mk_inst_def, Abbr `cw`] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
    step_taint_def, out_taint_def, set_var_taint_def, mem_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, adopt_reset_def,
    store_taint_def, imm_taint_def, range_bytes_def, mk_inst_def,
    finite_mapTheory.FLOOKUP_DEF] >>
  simp[update_var_def, source_memory_write_ranges_def] >>
  `({i | ?aid b sz. aid NOTIN FDOM s.vs_allocas /\
      (aid IN FDOM s.vs_allocas /\ s.vs_allocas ' aid = (b,sz)) /\
      b <= i /\ i < b + sz}:num set) = {}` by
    (simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[GSYM taint_component_equality] >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _`
    (mp_then Any mp_tac (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)) >>
  simp[] >> disch_then irule >>
  `<|t_mem := tn.t_mem; t_var := tn.t_var |+ (x,{});
      t_stor := tn.t_stor; t_trans := tn.t_trans; t_imm := tn.t_imm|> =
      (tn with t_var := tn.t_var |+ (x,{}))` by simp[taint_component_equality] >>
  pop_assum SUBST1_TAC >>
  irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]
QED
Finalise return_default_codesize_joint

Theorem return_default_assert_success_joint:
  emit_void ASSERT [arg] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand arg s = SOME w /\ w <> 0w /\ op_taint tn arg = {} ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (s with vs_inst_idx := LENGTH b.cs_current_insts),G,tn)
Proof
  strip_tac >> gen_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
    b.cs_current_insts = a.cs_current_insts ++ [mk_inst a.cs_next_id ASSERT [arg] []]` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  `step_inst_base (mk_inst a.cs_next_id ASSERT [arg] []) s = OK s` by
    simp[step_ASSERT_ok] >>
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  conj_tac >- simp[] >>
  qexistsl_tac [`[mk_inst a.cs_next_id ASSERT [arg] []]`, `a`] >>
  simp[mk_inst_def, is_terminator_def] >>
  conj_tac >- suspend "mem" >>
  simp[run_inst_seq_def, GSYM mk_inst_def, inst_seq_ptr_def] >>
  conj_tac >- suspend "mem2" >>
  simp[step_prov_def, out_prov_def, set_prov_def,
    step_taint_def, out_taint_def, set_var_taint_def, mem_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, adopt_reset_def,
    store_taint_def, imm_taint_def, range_bytes_def, mk_inst_def,
    finite_mapTheory.FLOOKUP_DEF] >>
  suspend "ptr"
QED
Resume return_default_assert_success_joint[mem]:
  simp[run_inst_seq_mem_ok_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    run_inst_seq_def] >> simp[GSYM mk_inst_def]
QED
Resume return_default_assert_success_joint[mem2]:
  simp[run_inst_seq_mem_ok_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    run_inst_seq_def] >> simp[GSYM mk_inst_def]
QED
Resume return_default_assert_success_joint[ptr]:
  simp[finite_mapTheory.DRESTRICT_UNIV, source_memory_write_ranges_def,
    taint_component_equality] >>
  conj_tac >- (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    mk_inst_def, GSYM op_taint_def] >>
    rpt strip_tac >> gvs[GSYM mk_inst_def, step_inst_non_invoke]) >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED
Finalise return_default_assert_success_joint

Theorem return_default_check_joint:
  compile_extcodesize_check addr a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} ==>
  ?u G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      ((if (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code):bytes32) = 0w
        then Abort Revert_abort (revert_state (set_returndata [] u))
        else OK (u with vs_inst_idx := LENGTH b.cs_current_insts)),G1,tn1)) /\
    u = (update_var (STRING #"%" (toString a.cs_next_var))
      (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s)
      with vs_inst_idx := LENGTH a.cs_current_insts + 1 /\
    G1 = DRESTRICT G (COMPL {STRING #"%" (toString a.cs_next_var)}) /\
    tn1 = tn with t_var := tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{})
Proof
  strip_tac >>
  qpat_x_assum `compile_extcodesize_check _ _ = _` mp_tac >>
  simp[exprLoweringTheory.compile_extcodesize_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op EXTCODESIZE [addr] a = (op,m)` >>
  `cs_extends a m /\ cs_extends m b` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code a m func /\ fn_has_code m b func` by
    (conj_tac >> irule fn_has_code_mid >> simp[cs_extends_refl] >>
     qexistsl_tac [`b`, `a`] >> simp[cs_extends_refl]) >>
  drule_all return_default_codesize_joint >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  `m.cs_current_bb = a.cs_current_bb /\
    LENGTH m.cs_current_insts = LENGTH a.cs_current_insts + 1` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  gen_tac >> suspend "compose"
QED
Resume return_default_check_joint[compose]:
  `~u.vs_halted /\ allocas_from lo u /\
    u.vs_current_bb = m.cs_current_bb /\
    u.vs_inst_idx = LENGTH m.cs_current_insts` by
    (gvs[update_var_def, allocas_from_def] >> metis_tac[]) >>
  Cases_on `(n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code):bytes32) = 0w`
  >- (`gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G1,tn1) []
        (Abort Revert_abort (revert_state (set_returndata [] u)),G1,tn1)` by
        (irule return_default_assert_reject_joint >>
         simp[] >> qexistsl_tac [`m`, `op`, `b`] >>
         gvs[eval_operand_def]) >>
      qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
        (qspec_then `D` assume_tac) >>
      qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
        (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
      disch_then assume_tac >> gvs[] >>
      `((n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)):bytes32) = 0w` by
        gvs[wordsTheory.n2w_11] >>
      simp[] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G1,tn1) []
    (OK (u with vs_inst_idx := LENGTH b.cs_current_insts),G1,tn1)` by
    (irule return_default_assert_success_joint >> simp[] >>
     qexistsl_tac [`m`, `op`, `n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)`] >>
     gvs[eval_operand_def]) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` assume_tac) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then assume_tac >> gvs[wordsTheory.n2w_11] >> metis_tac[]
QED
Finalise return_default_check_joint

Theorem return_default_suffix_path_joint:
  (if skip then comp_return () else compile_extcodesize_check addr) a = ((),b) /\
  emit_inst JMP [Label lbl] [] b = ((),j) /\
  fn_has_code a b func /\ fn_has_code b j func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} ==>
  ?r G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G1,tn1)) /\
    (skip ==> r = OK (jump_to lbl s) /\ G1 = G /\ tn1 = tn) /\
    (~skip ==>
      ?u. u = (update_var (STRING #"%" (toString a.cs_next_var))
        (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s)
        with vs_inst_idx := LENGTH a.cs_current_insts + 1 /\
      r = (if (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code):bytes32) = 0w
           then Abort Revert_abort (revert_state (set_returndata [] u))
           else OK (jump_to lbl u)) /\
      G1 = DRESTRICT G (COMPL {STRING #"%" (toString a.cs_next_var)}) /\
      tn1 = tn with t_var := tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{}))
Proof
  strip_tac >> Cases_on `skip`
  >- (gvs[comp_return_def] >>
      gen_tac >> irule return_default_join_joint >> simp[] >>
      qexistsl_tac [`a`, `j`] >> simp[]) >>
  gvs[] >> drule_all return_default_check_joint >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    ((if (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code):bytes32) = 0w
      then Abort Revert_abort (revert_state (set_returndata [] u))
      else OK (jump_to lbl u)),G1,tn1)` suffices_by gvs[] >>
  gen_tac >> Cases_on `(n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code):bytes32) = 0w`
  >- (first_x_assum (qspec_then `D` mp_tac) >>
      pure_asm_rewrite_tac [] >> simp[]) >>
  suspend "join"
QED
Resume return_default_suffix_path_joint[join]:
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[exprLoweringTheory.compile_extcodesize_check_def, comp_bind_def,
      emit_op_def, emit_void_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  `~u.vs_halted /\ allocas_from lo u /\ u.vs_current_bb = b.cs_current_bb` by
    (gvs[update_var_def, allocas_from_def] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := LENGTH b.cs_current_insts,G1,tn1) []
     (OK (jump_to lbl u),G1,tn1)` by
    (`jump_to lbl u = jump_to lbl (u with vs_inst_idx := LENGTH b.cs_current_insts)` by
       simp[jump_to_def] >>
     pop_assum SUBST1_TAC >>
     irule return_default_join_joint >> simp[allocas_from_def] >>
     qexistsl_tac [`b`, `j`] >> simp[]) >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` mp_tac) >>
  pure_asm_rewrite_tac [] >> pure_rewrite_tac [COND_CLAUSES] >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then assume_tac >> pure_asm_rewrite_tac [] >>
  metis_tac[listTheory.APPEND_NIL]
QED
Finalise return_default_suffix_path_joint

(* The optional code check writes one fresh variable, not two. *)
Theorem return_default_suffix_joint_frame:
  sa.cs_next_var <= n /\
  u = jump_to lbl ((update_var (STRING #"%" (toString n)) w s)
        with vs_inst_idx := k) /\
  G1 = DRESTRICT G (COMPL {STRING #"%" (toString n)}) /\
  tn1 = tn with t_var := tn.t_var |+ (STRING #"%" (toString n),{}) ==>
  (!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!lo cenv es sa0 G0 tn0 s0.
    sa0.cs_next_var <= sa.cs_next_var /\
    ghost_kept_at lo cenv es sa0 G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es sa0 G0 tn0 s0 G1 tn1) /\
  (!D lo d cenv cx ee.
    ghost_inv_at D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    ghost_inv_at D lo d cenv cx ee G1 tn1 u) /\
  (!H cenv cx ee.
    local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx ee s ==>
    stmt_state_rel H ctx func cenv cx ee u) /\
  (!cenv es ee sa0 s0.
    sa0.cs_next_var <= sa.cs_next_var /\ wb_frame cenv es ee sa0 s0 s ==>
    wb_frame cenv es ee sa0 s0 u)
Proof
  strip_tac >>
  `u = jump_to lbl ((update_var (STRING #"%" (toString n)) w
      (update_var (STRING #"%" (toString n)) w s)) with vs_inst_idx := k)` by
    simp[update_var_def] >>
  `G1 = DRESTRICT (DRESTRICT G (COMPL {STRING #"%" (toString n)}))
      (COMPL {STRING #"%" (toString n)})` by
    simp[finite_mapTheory.DRESTRICT_DRESTRICT] >>
  `tn1 = tn with t_var := (tn.t_var |+ (STRING #"%" (toString n),{})) |+
      (STRING #"%" (toString n),{})` by simp[] >>
  drule_all return_default_shell_joint_frame >> simp[]
QED


(* Resources on the already selected allocation-and-shell run.  The shell
   indices and label are supplied by the compiler decomposition. *)
Theorem return_default_prefix_store_resources:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv a /\ n < dimword (:256) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  b.cs_next_var <= n1 /\ b.cs_next_var <= n2 /\
  ds.cs_current_bb = dl /\ ds.cs_current_insts = [] /\
  b.cs_next_var <= ds.cs_next_var /\
  AG = step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) r /\
  atn = step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) s r tn /\
  u = jump_to dl ((update_var (STRING #"%" (toString n2)) w2
        (update_var (STRING #"%" (toString n1)) w1
          (r with vs_inst_idx := LENGTH b.cs_current_insts)))
        with vs_inst_idx := k) /\
  Gf = DRESTRICT (DRESTRICT AG (COMPL {STRING #"%" (toString n1)}))
        (COMPL {STRING #"%" (toString n2)}) /\
  tm = atn with t_var := (atn.t_var |+ (STRING #"%" (toString n1),{})) |+
        (STRING #"%" (toString n2),{}) /\
  stmt_state_rel H ctx func cenv cx ee s ==>
  u.vs_current_bb = ds.cs_current_bb /\
  u.vs_inst_idx = LENGTH ds.cs_current_insts /\
  buf.buf_operand = Var (STRING #"%" (toString a.cs_next_var)) /\
  not_fresh_at ds (STRING #"%" (toString a.cs_next_var)) /\
  stmt_state_rel H ctx func cenv cx ee u /\
  u.vs_memory = s.vs_memory /\
  u.vs_allocas = r.vs_allocas /\ u.vs_alloca_next = r.vs_alloca_next /\
  u.vs_halted = s.vs_halted /\
  (!x. not_fresh_at a x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (?w. eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas a.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= u.vs_alloca_next /\
    (!aid off sz. aid < a.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
      regions_disjoint (w2n w) n off sz) /\
    (!name off sz. local_region cenv ee.scopes u name off sz ==>
      regions_disjoint (w2n w) n off sz)) /\
  (!D lo d. ghost_inv_at D lo d cenv cx ee G tn s ==>
    ghost_inv_at D lo d cenv cx ee Gf tm u /\
    ptr_covers Gf tm (STRING #"%" (toString a.cs_next_var)) u n /\
    ghost_kept_at lo cenv ee a G tn s Gf tm) /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!cenv0 es0 ee0 sa0 s0. sa0.cs_next_var <= a.cs_next_var /\
     wb_frame cenv0 es0 ee0 sa0 s0 s ==>
     wb_frame cenv0 es0 ee0 sa0 s0 u) /\
  (!i. i < s.vs_alloca_next ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (alloca_history func s /\ s.vs_current_bb = a.cs_current_bb /\
   s.vs_inst_idx = LENGTH a.cs_current_insts ==> alloca_history func u)
Proof
  strip_tac >>
  drule_all return_default_alloc_run_step >> strip_tac >>
  drule_all return_default_alloc_resources >> strip_tac >>
  qabbrev_tac `ar = r with vs_inst_idx := LENGTH b.cs_current_insts` >>
  drule_all (Q.INST [`sa` |-> `b`, `ctx` |-> `ctx`, `func` |-> `func`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] return_default_shell_joint_frame))) >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  `local_ptrs_reserved cenv b` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `a` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at b x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at b x)` by
    (fs[not_fresh_at_def] >> metis_tac[]) >>
  `not_fresh_at b (STRING #"%" (toString a.cs_next_var))` by
    gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def, not_fresh_at_def] >>
  `stmt_state_rel H ctx func cenv cx ee ar` by
    simp[Abbr `ar`, stmt_state_rel_inst_idx] >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (irule return_default_shell_state >>
     qpat_assum `u = _` (fn th => irule_at Any th) >>
     qexists_tac `b` >> simp[]) >>
  `r.vs_halted = s.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = r.vs_allocas /\
   u.vs_alloca_next = r.vs_alloca_next /\ u.vs_halted = s.vs_halted` by
    gvs[jump_to_def, update_var_def, Abbr `ar`] >>
  `not_fresh_at ds (STRING #"%" (toString a.cs_next_var))` by
    (fs[not_fresh_at_def] >> decide_tac) >>
  `u.vs_current_bb = ds.cs_current_bb /\
   u.vs_inst_idx = LENGTH ds.cs_current_insts` by
    simp[jump_to_def, update_var_def, Abbr `ar`] >>
  ntac 9 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "old" >>
  conj_tac >- suspend "destination" >>
  conj_tac >- suspend "ghost" >>
  suspend "frames"
QED
Resume return_default_prefix_store_resources[old]:
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  rpt strip_tac >>
  `not_fresh_at b x /\ x <> STRING #"%" (toString a.cs_next_var)` by
    (fs[not_fresh_at_def] >> metis_tac[]) >>
  qpat_x_assum `!x. not_fresh_at b x ==> _`
    (qspec_then `x` (drule_all_then strip_assume_tac)) >>
  qpat_x_assum `!p. p <> _ ==> _`
    (qspec_then `x` (drule_all_then strip_assume_tac)) >>
  gvs[Abbr `ar`, lookup_var_def]
QED
Resume return_default_prefix_store_resources[destination]:
  `lookup_var (STRING #"%" (toString a.cs_next_var)) u =
   lookup_var (STRING #"%" (toString a.cs_next_var)) r` by
    (qpat_x_assum `!x. not_fresh_at b x ==> _`
       (qspec_then `STRING #"%" (toString a.cs_next_var)` mp_tac) >>
     simp[Abbr `ar`, lookup_var_def]) >>
  qexists_tac `w` >>
  conj_tac >-
    (qpat_x_assum `eval_operand _ r = SOME w` mp_tac >>
     qpat_assum `buf.buf_operand = _` (fn th => rewrite_tac[th, eval_operand_def]) >>
     qpat_assum `lookup_var _ u = lookup_var _ r`
       (fn th => rewrite_tac[th]) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP r.vs_allocas aid = _ ==> _`
       (qspecl_then [`a.cs_next_id`, `w2n w`, `n`] mp_tac) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!name off sz. local_region cenv ee.scopes u name off sz <=>
                 local_region cenv ee.scopes r name off sz` suffices_by metis_tac[] >>
  irule local_region_lookup_cong >> rpt strip_tac >>
  `not_fresh_at b p` by metis_tac[local_ptrs_reserved_def] >>
  qpat_x_assum `!x. not_fresh_at b x ==> _`
    (qspec_then `p` mp_tac) >>
  simp[Abbr `ar`, lookup_var_def]
QED
Resume return_default_prefix_store_resources[ghost]:
  rpt gen_tac >> disch_tac >>
  `ghost_inv_at D lo d cenv cx ee AG atn r /\
   ptr_covers AG atn (STRING #"%" (toString a.cs_next_var)) r n /\
   ghost_kept_at lo cenv ee a G tn s AG atn` by
    (qpat_assum `AG = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `atn = _` (fn th => rewrite_tac[th]) >>
     irule return_default_alloc_ghost_resources >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`H`, `ctx`, `func`] >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `!D lo d cenv cx ee. _ ==> ghost_inv_at _ _ _ _ _ _ Gf tm u` irule >>
     simp[NoAsms] >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
     goal_assum (drule_at Any) >> qexists_tac `b` >>
     simp[Abbr `ar`, lookup_var_def]) >>
  conj_tac >-
    (fs[ptr_covers_def] >>
     qpat_x_assum `!x. not_fresh_at b x ==> _`
       (qspec_then `STRING #"%" (toString a.cs_next_var)`
         (drule_all_then strip_assume_tac)) >>
     gvs[Abbr `ar`, lookup_var_def]) >>
  qpat_x_assum `!lo cenv es sa0 G0 tn0 s0. _ ==> ghost_kept_at _ _ _ _ _ _ _ Gf tm` irule >>
  simp[]
QED

Resume return_default_prefix_store_resources[frames]:
  conj_tac >-
    (drule_all return_default_allocation_frontier >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "wb" >>
  conj_tac >-
    (drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
     drule_all alloca_step_frame_effects >>
     disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
     gvs[]) >>
  conj_tac >- suspend "taint" >>
  conj_tac >- suspend "taint" >>
  conj_tac >- suspend "taint" >>
  suspend "history"
QED
Resume return_default_prefix_store_resources[wb]:
  rpt gen_tac >> strip_tac >>
  irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
  goal_assum (drule_at Any) >> qexists_tac `a` >>
  simp[NoAsms] >> conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at b z` by (fs[not_fresh_at_def] >> metis_tac[]) >>
     qpat_x_assum `!x. not_fresh_at b x ==> _`
       (qspec_then `z` (drule_all_then strip_assume_tac)) >>
     fs[Abbr `ar`, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED
Resume return_default_prefix_store_resources[taint]:
  markerLib.RESUME_TAC >>
  simp[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def,
       imm_taint_def]
QED
Resume return_default_prefix_store_resources[history]:
  strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func ar` by
    (simp[Abbr `ar`] >> irule emitted_alloca_history >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`emitted_insts a b`, `s`, `a`] >> simp[] >>
     gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, emitted_insts_def, mk_inst_def, is_terminator_def,
       rich_listTheory.DROP_LENGTH_APPEND]) >>
  irule allocaHistoryTheory.alloca_history_jump >>
  conj_tac >- metis_tac[listTheory.LENGTH_NIL] >>
  qexists_tac `ar` >> simp[Abbr `ar`]
QED
Finalise return_default_prefix_store_resources
