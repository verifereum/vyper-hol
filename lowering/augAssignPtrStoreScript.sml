(* Counted clean scalar stores; source-update invariant transport is separate. *)
Theory augAssignPtrStore
Ancestors
  augAssignPtrLoad typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs venomInst venomState venomExecSemantics ptrSafeRun
  ptrDiscipline emitHelperProps emitHelper compileEnv fragExec
  finite_map words robustCopyTransportPtr valueEncoding valueEncodingProps
  valueEncodingProofs list venomMemProofs

Theorem mstore_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dst; value] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MSTORE [Var dst; value] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  `step_inst_base (mk_inst id MSTORE [Var dst; value] []) s =
    OK (mstore (w2n a) w s)` by
    simp[step_inst_base_def, mk_inst_def, exec_write2_def, eval_operand_def] >>
  mp_tac (Q.INST [`lo` |-> `0`, `u` |-> `mstore (w2n (a:256 word)) w s`,
    `i` |-> `mk_inst id MSTORE [Var dst; value] []`] straight_line_ptr_edge) >>
  gvs[mk_inst_def, is_terminator_def] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[mstore_def]
QED

Theorem emit_mstore_path_ptr:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf = (mstore (w2n a) w s) with vs_inst_idx := LENGTH sb.cs_current_insts /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!p. lookup_var p sf = lookup_var p s)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var dst; value] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id MSTORE [Var dst; value] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] strip_assume_tac) >>
  qexistsl_tac [
    `step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn`,
    `(mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[mstore_def, lookup_var_def, arithmeticTheory.ADD1]
QED

Theorem mstore_robust_exterior:
  val_wf tv v /\
  (!i. p <= i /\ i < p + val_footprint tv v ==> ~(off <= i /\ i < off + 32)) /\
  (!m. mem_agree_outside tainted s.vs_memory m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside (tainted DIFF {i | off <= i /\ i < off + 32})
    (mstore off w s).vs_memory m ==> val_in_memory tv v p m
Proof
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  simp[] >> goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `tainted`, `{i | off <= i /\ i < off + 32}`] >>
  simp[] >> mp_tac (Q.SPECL [`s`, `off`, `w`] mstore_memory_frame) >>
  simp[mem_agree_outside_def]
QED
