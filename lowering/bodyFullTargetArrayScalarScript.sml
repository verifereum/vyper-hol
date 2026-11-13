(* The array suffix's raw runs, certified at the same pointer/memory
   endpoint. Safety is explicit: the caller supplies checks for the actual
   emitted code, not an independently chosen target run. *)
Theory bodyFullTargetArrayScalar
Ancestors
  exprSimArrayIndex bodyFullUnwrapRun fragGasSeqPtr fragGasOriginPtr
  fragExecMem fragExec exprLoweringProps compileEnv venomState venomInst
  list rich_list venomExecSemantics venomExecProofs fragGasSeq
  fragGasOrigin gasEvents memSafeRun fragGasSeqAbort venomInstProofs instIdxIndep fragGasPathPtr gasCount ptrSafeRun

Theorem array_bounds_check_joint_ok:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  fresh_vars_wrt sa s /\ idx_in_range sgn i n /\
  fn_has_code sa sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all array_bounds_check_ok >> strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (ss' with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')` by
    (irule emitted_origin_ptr_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> fs[same_blocks_def]) >>
  qexists_tac `ss'` >> simp[]
QED

Theorem array_elem_ptr_joint:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ fn_has_code sa sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  strip_tac >> drule_all array_elem_ptr_run >> strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (ss' with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')` by
    (irule emitted_origin_ptr_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> fs[same_blocks_def]) >>
  qexists_tac `ss'` >> simp[]
QED

(* On ASSERT failure only the executed prefix is certified. The cursor
   of the raw sequence is restored by run_inst_seq, hence the explicit j. *)
Theorem array_abort_joint_run[local]:
  !code s t a G tn G' tn' ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    inst_seq_ptr D lo ctx func PG G tn code s G' tn' /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (Abort a (t with vs_inst_idx := j),G',tn')
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, run_inst_seq_mem_ok_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\ins. ~is_terminator ins.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `step_prov PG G h u`,
        `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `func`, `bb`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      qexists_tac `j` >>
      `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
         step_prov PG G h u, step_taint h s u tn)` by
        (drule_all straight_line_origin_ptr_edge >> simp[]) >>
      drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]) >>
  qexists_tac `t.vs_inst_idx` >> simp[] >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[exit_result_def] >>
  simp[gas_origin_ptr_edge_def] >> conj_tac
  >- (simp[gas_origin_edge_def] >>
      qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_events_step_def,
           mem_safe_step_non_invoke, exit_result_def]) >>
  simp[gas_path_ptr_edge_def] >> qexists_tac `0` >>
  simp[gas_count_step_def, ptr_safe_step_def, step_inst_non_invoke,
       exit_result_def]
QED

Theorem array_bounds_check_joint_abort:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  fresh_vars_wrt sa s /\ ~idx_in_range sgn i n /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  fn_has_code sa sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  ?t j. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := j),G',tn')
Proof
  strip_tac >> drule_all array_bounds_check_oob >> strip_tac >>
  `?j. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (Abort Revert_abort (ss' with vs_inst_idx := j),G',tn')` by
    (irule array_abort_joint_run >> simp[] >>
     fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexistsl_tac [`bb`, `emitted_insts sa sb`] >>
     gvs[IS_PREFIX_APPEND, DROP_APPEND, DROP_LENGTH_NIL,
         APPEND_ASSOC]) >>
  metis_tac[]
QED
