(* Normal endpoint facts use the same ghosts as the checked prefix. *)
Theory bodyPtrEnvBuiltinsBlockHashPost
Ancestors bodyPtrEnvBuiltinsBlockHashRun bodyPtrEnvBuiltinsBlockHashFrame
  bodyPtrEnvBuiltinsEdges fragGasSeqPtr exprLoweringProps instIdxIndep
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState list fragExec
  bodyPtrDefs compileEnv builtinProps finite_map bodyPtrEnvBuiltinsScalar
  ghostPcTransportPtr stmtSimAppendStorageCompose stateFrame

Theorem checked_sequence_last_post[local]:
  !prefix s t G tn G' tn'.
    EVERY (\i. ~is_terminator i.inst_opcode) (prefix ++ [last]) /\
    inst_seq_ptr D lo ctx fn PG G tn (prefix ++ [last]) s G' tn' /\
    run_inst_seq (prefix ++ [last]) s = OK t /\
    (!u v H q. ptr_inst_ok D lo 0 ctx fn H q last u /\
       step_inst_base last u = OK v ==>
       R (step_prov PG H last v) (step_taint last u v q)) ==>
    R G' tn'
Proof
  Induct
  >- (simp[inst_seq_ptr_def, run_inst_seq_def] >>
      rpt gen_tac >> strip_tac >> Cases_on `step_inst_base last s` >>
      gvs[] >> metis_tac[]) >>
  simp[inst_seq_ptr_def, run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum irule >>
  qexistsl_tac [`step_prov PG G h v`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`, `step_taint h s v tn`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem blockhash_last_output_clean[local]:
  ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id BLOCKHASH [arg] [out]) s ==>
  op_prov (step_prov PG G (mk_inst id BLOCKHASH [arg] [out]) t) (Var out) = NONE /\
  op_taint (step_taint (mk_inst id BLOCKHASH [arg] [out]) s t tn) (Var out) = {}
Proof
  strip_tac >> conj_tac
  >- (irule scalar_builtin_output_no_prov >> simp[]) >>
  irule scalar_builtin_output_clean >> simp[] >>
  gvs[ptr_inst_ok_def, taint_ok_def, mk_inst_def] >> metis_tac[]
QED

Theorem blockhash_compile_last[local]:
  compile_blockhash arg sa = (op,sb) ==>
  ?prefix id out. op = Var out /\
    emitted_insts sa sb = prefix ++ [mk_inst id BLOCKHASH [arg] [out]] /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (prefix ++ [mk_inst id BLOCKHASH [arg] [out]])
Proof
  strip_tac >> drule blockhash_compile_code >> strip_tac >>
  qexistsl_tac [`TAKE 7 (emitted_insts sa sb)`, `sa.cs_next_id+7`, `out`] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem blockhash_checked_output_clean:
  compile_blockhash arg sa = (op,sb) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  op_prov G' op = NONE /\ op_taint tn' op = {}
Proof
  strip_tac >> drule blockhash_compile_last >> strip_tac >> gvs[] >>
  irule (BETA_RULE (Q.INST
    [`R` |-> `\H q. op_prov H (Var out) = NONE /\ op_taint q (Var out) = {}`,
     `last` |-> `mk_inst id BLOCKHASH [arg] [out]`]
    (SPEC_ALL checked_sequence_last_post))) >>
  simp[] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  drule blockhash_last_output_clean >> simp[]
QED

Theorem blockhash_raw_register_frame:
  compile_blockhash arg sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all compile_blockhash_frame >> strip_tac >>
  simp[lookup_var_def]
QED

Theorem blockhash_checked_normal_ghosts:
  compile_blockhash arg sa = (op,sb) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es0 sa G0 tn0 s0 G' tn'
Proof
  strip_tac >> drule_all blockhash_checked_ghost_frame >> strip_tac >>
  drule_all blockhash_raw_register_frame >> strip_tac >>
  conj_tac
  >- (irule ghost_inv_register_transport >>
      qexistsl_tac [`G`, `s`, `sa`, `tn`] >> simp[] >>
      qpat_x_assum `t = _`
        (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_call_ctx,z.vs_accounts,z.vs_transient)`) >>
      simp[]) >>
  irule ghost_kept_clean_suffix >> qexistsl_tac [`G`, `tn`] >> simp[]
QED

Theorem blockhash_checked_state_rel:
  compile_blockhash arg sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  stmt_state_rel ctx fn cenv cx es t
Proof
  strip_tac >> drule_all blockhash_raw_register_frame >> strip_tac >>
  irule stmt_state_rel_reserved_frame >> qexistsl_tac [`s`, `sa`] >>
  conj_tac >- metis_tac[] >> simp[] >>
  qpat_x_assum `t = _` (mp_tac o Q.AP_TERM `state_frame`) >>
  simp[state_frame_def]
QED

Theorem blockhash_counted_normal_post:
  compile_blockhash arg sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sa G0 tn0 s0 G' tn' /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    stmt_state_rel ctx fn cenv cx es t
Proof
  strip_tac >> drule_all blockhash_suffix_code >> strip_tac >>
  `?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn'` by
    (irule blockhash_compile_certificate >> simp[] >>
     qexistsl_tac [`arg`, `op`] >> simp[]) >>
  drule_all blockhash_checked_output_clean >> strip_tac >>
  drule_all blockhash_checked_normal_ghosts >> strip_tac >>
  drule_all blockhash_checked_state_rel >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_ptr >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    fs[FILTER_EQ_NIL, EVERY_MEM] >>
  simp[] >> strip_tac >> qexistsl_tac [`G'`, `tn'`] >> simp[]
QED

Theorem blockhash_normal_suffix_run:
  compile_blockhash arg sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\ eval_operand op u = SOME w /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sa G0 tn0 s0 G' tn' /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    eval_operand op t = SOME w /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all blockhash_counted_normal_post >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all blockhash_raw_register_frame >> strip_tac >>
  drule compile_blockhash_shape >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`, `u with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  qpat_x_assum `u = _`
    (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb,z.vs_memory,z.vs_allocas)`) >>
  simp[] >> gvs[lookup_var_def]
QED
