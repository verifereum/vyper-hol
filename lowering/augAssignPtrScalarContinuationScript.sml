Theory augAssignPtrScalarContinuation
Ancestors augAssignPtrScalarRun augAssignPtrScalarCertificate fragGasFresh
  fragGasSeqPtr fragGasSeqAbort fragGasPathPtr ptrSafeRun
  varsExt freshWrites fragExec exprLoweringProps compileEnv
  venomExecSemantics venomState venomInst venomInstProofs instIdxIndep
  list rich_list pred_set

Theorem straight_fresh_scalar_success_path:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  scalar_code A (emitted_insts sa sb) /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 ==>
  ?t H tm.
    run_inst_seq (emitted_insts sa sb) s = OK t /\ vars_ext t0 t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >>
     simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`, `s`] strip_assume_tac) >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by (fs[EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    metis_tac[writes_fresh_gas_count] >>
  goal_assum (drule_at Any) >> gvs[]
QED

Theorem run_inst_seq_abort_zero_path_ptr:
  !code s t a G tn H tm ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    inst_seq_ptr D lo ctx fn PG G tn code s H tm /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_path_ptr D lo ctx fn PG G tn s 0 H tm
          (Abort a (t with vs_inst_idx := j))
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        (drule_all step_preserves_halted >>
         drule_all step_preserves_control_flow >> simp[]) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >>
      disch_then drule_all >> strip_tac >> qexists `j` >>
      drule_all gas_path_ptr_step >> simp[]) >>
  qexists `t.vs_inst_idx` >> simp[] >>
  drule_all gas_path_ptr_abort >> simp[]
QED

Theorem straight_fresh_scalar_abort_path:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  scalar_code A (emitted_insts sa sb) /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = Abort a t0 ==>
  ?t j H tm.
    run_inst_seq (emitted_insts sa sb) s = Abort a t /\ vars_ext t0 t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >>
     simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`, `s`] strip_assume_tac) >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED
