(* Seam 2 joint induction, a family leaf of the call step: pops. *)
Theory bodyIntCallFamCallPop
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore exprSimCopy
  exprSimProps intCallFrame venomState bodyMemPopToplevelSim
  bodyMemPopToplevelPath exprSimPopStorage exprSimTopLevelProps
  exprSimSource exprSimHypsDefs exprSimDefs exprLoweringProps
  exprLowering compileEnv context vyperInterpreter vyperStorageBackend
  vyperStorageLayoutSafety vyperStorage vyperState venomExecSemantics
  venomInst accountsRelProps gasOutcome gasSummary fragGasMode fragGasPathMem
  list words finite_map fragExec bodySimStmtCases exprOpenCases
  supportedExprForms supportedDecls appendStorageSourcePtr fragGasSeq
  fragGasSeqAbort rich_list

(* A storage operation that keeps memory, allocations, and old variables
   transports the joint continuation once its source and state relations
   have been established. *)
Theorem intcall_expr_cont_memory_frame:
  intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env ee /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  sa.cs_next_var <= sb.cs_next_var /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `local_ptrs_reserved ce sa` by fs[intcall_joint_res_def] >>
  `(!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s)` by
    (rpt strip_tac >>
     `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
       metis_tac[intcall_frame_ok_def] >>
     gvs[eval_operand_def] >>
     `not_fresh_at sa x` by metis_tac[intcall_joint_res_def] >> simp[]) >>
  `intcall_joint_res fp ce env ee sb u` by
    (irule intcall_joint_res_frame >>
     simp[] >>
     conj_tac >- (gvs[intcall_joint_res_def, allocas_above_def] >> metis_tac[]) >>
     qexistsl [`es`, `s`, `sa`] >> simp[] >>
     rpt strip_tac >>
     drule_all copy_buffer_local_region_frame >> simp[] >> metis_tac[]) >>
  simp[intcall_expr_cont_def] >>
  irule locals_kept_mem >> simp[]
QED

Theorem intcall_pop_storage_path:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\
  (if tr then tload slot s else sload slot s) <> 0w ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    t.vs_memory = s.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    eval_operand r t = SOME (slot + 1w +
      ((if tr then tload slot s else sload slot s) - 1w) * n2w esz) /\
    t = ((if tr then tstore slot (tload slot s - 1w) s
          else sstore slot (sload slot s - 1w) s)
          with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>)
Proof
  strip_tac >>
  drule dynarray_pop_storage_opcodes >> strip_tac >>
  drule dynarray_pop_storage_shape >> strip_tac >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by fs[ALL_DISTINCT] >>
  drule_all dynarray_pop_storage_run >>
  disch_then (qspecl_then [`sa.cs_next_id`, `esz`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    simp[emitted_insts_def, DROP_APPEND] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all tuple_run_inst_seq_gas_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas /\
   u.vs_memory = s.vs_memory /\ u.vs_halted = s.vs_halted /\
   u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u = _ with vs_vars := _` mp_tac >>
     Cases_on `tr` >> simp[tstore_def, sstore_def, LET_THM] >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `gas_path _ _ _ _ _` mp_tac >>
      Cases_on `tr` >>
      simp[gas_marked_path_def, emitted_insts_def, DROP_APPEND, mk_inst_def]) >>
  simp[eval_operand_def, lookup_var_def] >>
  reverse conj_tac
  >- (qpat_x_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      simp[]) >>
  fs[EVERY_MEM, lookup_var_def] >> metis_tac[]
QED

Theorem intcall_pop_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a tgt. e = Pop a tgt) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
