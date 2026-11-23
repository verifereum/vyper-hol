(* Counted control edges for the default-return shell. *)
Theory extcallReturnDefaultControlJoint
Ancestors
  extcallReturnDefaultRouting fragGasCopyLoop fragGasCopySeqLiftProps context emitHelper
  emitHelperProps fragExec fragExecPtr fragExecMem venomMemDefs venomState
  venomInst venomExecSemantics ptrDiscipline compileEnv ptrSafeRun
  contextCodegenRel codegenRel list fragGasOriginPtr bodyFullUnwrapRun
  exprLoweringProps fragGasSeqPtr bodyFullGhostFrame bodyPtrDefs
  freshWrites exprSimWordArgs allocaHistory loweringStateRelDefs

Theorem return_default_select_joint[local]:
  emit_inst JNZ [test;Label yes;Label no] [] a = ((),b) /\
  fn_has_code a b func /\ ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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

Theorem return_default_test_joint[local]:
  emit_op RETURNDATASIZE [] a = (rds,m) /\
  emit_op ISZERO [rds] m = (test,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
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
  conj_tac >-
    (rpt strip_tac >>
     `MEM i (pre ++ [i] ++ post)` by simp[] >>
     pop_assum mp_tac >>
     qpat_assum `[_;_] = pre ++ [i] ++ post` (once_rewrite_tac o single o SYM) >>
     simp[] >> strip_tac >>
     simp[memSafeRunTheory.dalloca_no_wrap_non_dalloca, mk_inst_def]) >>
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
  simp[op_taint_def, finite_mapTheory.FLOOKUP_UPDATE, taint_component_equality] >>
  fs[allocas_below_fmp_def, update_var_def] >>
  qpat_assum `ctx_has_dalloca ctx ==> _ /\ _` (fn th =>
    ACCEPT_TAC (DISCH ``ctx_has_dalloca ctx`` (CONJUNCT2 (UNDISCH th))))
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
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
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
  `u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = s.vs_current_bb /\
   u.vs_inst_idx = LENGTH a2.cs_current_insts` by simp[update_var_def] >>
  `allocas_from lo u` by metis_tac[allocas_from_def] >>
  `allocas_below_fmp u = allocas_below_fmp s` by
    (qpat_assum `u = (_ with vs_inst_idx := _)` SUBST1_TAC >>
     simp[allocas_below_fmp_def, update_var_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by simp[] >>
  `a5.cs_current_bb = a.cs_current_bb /\
   a5.cs_current_insts = a2.cs_current_insts` by
    gvs[fresh_label_def, comp_bind_def, comp_return_def,
        emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  `u.vs_current_bb = a5.cs_current_bb /\
   u.vs_inst_idx = LENGTH a5.cs_current_insts` by metis_tac[] >>
  drule_all return_default_select_joint >> strip_tac >>
  simp[] >> gen_tac >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` assume_tac) >>
  drule gas_origin_ptr_path_append >> simp[] >>
  disch_then irule >> gvs[]
QED

(* The branch label and the two scratch outputs do not change live resources. *)
Theorem return_default_shell_joint_frame:
  a.cs_next_var <= n1 /\ a.cs_next_var <= n2 /\
  u = jump_to lbl
    ((update_var (STRING #"%" (toString n2)) w2
       (update_var (STRING #"%" (toString n1)) w1 s))
     with vs_inst_idx := k) /\
  J = DRESTRICT (DRESTRICT G (COMPL {STRING #"%" (toString n1)}))
        (COMPL {STRING #"%" (toString n2)}) /\
  tm = tn with t_var :=
    (tn.t_var |+ (STRING #"%" (toString n1),{})) |+
      (STRING #"%" (toString n2),{}) ==>
  (!x. not_fresh_at a x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP J x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
  u.vs_returndata = s.vs_returndata /\ u.vs_halted = s.vs_halted /\
  u.vs_inst_idx = 0 /\ u.vs_current_bb = lbl /\
  tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (alloca_history func s ==> alloca_history func u) /\
  (!H ctx cenv cx ee.
    local_ptrs_reserved cenv a /\ stmt_state_rel H ctx func cenv cx ee s ==>
    stmt_state_rel H ctx func cenv cx ee u) /\
  (!D lo d cenv cx ee.
    ghost_inv_at D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv a /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) ==>
    ghost_inv_at D lo d cenv cx ee J tm u) /\
  (!lo cenv es sa G0 tn0 s0.
    sa.cs_next_var <= a.cs_next_var /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es sa G0 tn0 s0 J tm) /\
  (!cenv es ee sa s0.
    sa.cs_next_var <= a.cs_next_var /\ wb_frame cenv es ee sa s0 s ==>
    wb_frame cenv es ee sa s0 u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. not_fresh_at a x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP J x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     `x <> STRING #"%" (toString n1) /\ x <> STRING #"%" (toString n2)` by metis_tac[] >>
     simp[jump_to_def, update_var_def, lookup_var_def, op_taint_def,
          finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
   u.vs_returndata = s.vs_returndata /\ u.vs_halted = s.vs_halted /\
   u.vs_inst_idx = 0 /\ u.vs_current_bb = lbl /\
   tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
   tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by
    simp[jump_to_def, update_var_def] >>
  `alloca_history func s ==> alloca_history func u` by
    metis_tac[alloca_history_jump] >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "kept" >>
  suspend "writeback"
QED
Resume return_default_shell_joint_frame[state]:
  rpt strip_tac >>
  simp[stmt_state_rel_jump_to, stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_update_var >>
  conj_tac >- metis_tac[local_ptrs_reserved_fresh] >>
  irule stmt_state_rel_update_var >> simp[] >>
  metis_tac[local_ptrs_reserved_fresh]
QED
Resume return_default_shell_joint_frame[ghost]:
  rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`G`, `ee`, `s`, `tn`] >>
  gvs[jump_to_def, update_var_def, lookup_var_def]
QED
Resume return_default_shell_joint_frame[kept]:
  rpt strip_tac >> irule ghost_kept_at_clean_suffix >>
  goal_assum (drule_at Any) >> reverse conj_tac >- simp[] >>
  qx_gen_tac `x` >> strip_tac >>
  `not_fresh_at a x` by (irule freshWritesTheory.not_fresh_at_mono >> metis_tac[]) >>
  qpat_assum `!x. not_fresh_at a x ==> _` (qspec_then `x` mp_tac) >>
  gvs[jump_to_def, update_var_def, lookup_var_def]
QED
Resume return_default_shell_joint_frame[writeback]:
  rpt strip_tac >> irule wb_frame_readonly_tail >>
  goal_assum (drule_at Any) >> qexists_tac `a` >>
  metis_tac[]
QED
Finalise return_default_shell_joint_frame

(* Expose the chosen block entry with the frame at that same endpoint. *)
Theorem return_default_shell_entry:
  emit_op RETURNDATASIZE [] a = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (test,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [test;Label dl;Label cl] [] a5 = ((),a6) /\
  fn_has_code a a2 func /\ fn_has_code a5 a6 func /\
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?u J tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,J,tm)) /\
    (!x. not_fresh_at a x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP J x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
    u.vs_returndata = s.vs_returndata /\ ~u.vs_halted /\
    u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if s.vs_returndata = [] then dl else cl) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (alloca_history func s ==> alloca_history func u) /\
    (!H cenv cx ee.
      local_ptrs_reserved cenv a /\ stmt_state_rel H ctx func cenv cx ee s ==>
      stmt_state_rel H ctx func cenv cx ee u) /\
    (!D d cenv cx ee.
      ghost_inv_at D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv a /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) ==>
      ghost_inv_at D lo d cenv cx ee J tm u) /\
    (!cenv es sa G0 tn0 s0.
      sa.cs_next_var <= a.cs_next_var /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
      ghost_kept_at lo cenv es sa G0 tn0 s0 J tm) /\
    (!cenv es ee sa s0.
      sa.cs_next_var <= a.cs_next_var /\ wb_frame cenv es ee sa s0 s ==>
      wb_frame cenv es ee sa s0 u)
Proof
  strip_tac >> drule_all return_default_shell_joint >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  `a.cs_next_var <= a1.cs_next_var` by
    (qpat_assum `emit_op RETURNDATASIZE _ _ = _`
       (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >> simp[]) >>
  drule_at (Pat `u = jump_to _ _`) return_default_shell_joint_frame >>
  disch_then (qspecl_then [`tn`, `tm`, `func`, `a`, `H`, `G`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`u`, `H`, `tm`] >> simp[]
QED
