Theory fragGasFresh
Ancestors
  freshWrites varsExt fragGasSeq fragGasSeqAbort fragGasMode exprSimProps compileEnv loweringStateRelDefs
  fragExec exprLoweringProps venomInst venomState venomExecSemantics
  venomInstProofs instIdxIndep list rich_list arithmetic

Theorem writes_fresh_path_opcodes:
  writes_fresh sa code ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode) code
Proof
  rw[writes_fresh_def, EVERY_MEM] >>
  first_x_assum drule >>
  simp[fresh_write_op_def] >> rpt strip_tac >>
  gvs[is_terminator_def, is_ext_call_op_def]
QED

Theorem writes_fresh_gas_count:
  writes_fresh sa code ==>
  LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0
Proof
  strip_tac >> drule writes_fresh_path_opcodes >>
  simp[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]
QED

Theorem straight_fresh_code_prefix:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb)
         (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  simp[straight_fresh_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[DROP_APPEND]
QED


Theorem straight_fresh_clean_success_path:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = OK t0 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s0 = OK t /\ vars_ext t0 t /\
      gas_marked_path F ctx func s0 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt strip_tac >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >>
     simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  simp[] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    metis_tac[writes_fresh_gas_count] >>
  simp[gas_marked_path_def] >> disch_then irule >>
  conj_tac >- (fs[EVERY_MEM]) >>
  qexists_tac `bb` >> gvs[]
QED

Theorem straight_fresh_clean_abort_path:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = Abort a t0 ==>
  ?t j. gas_marked_path F ctx func s0 0
      (Abort a (t with vs_inst_idx := j))
Proof
  rpt strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >>
     simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >> metis_tac[]
QED

Theorem straight_fresh_run_post:
  straight_fresh m /\ m sa = (op,sb) /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = OK t0 /\
  eval_operand op t0 = SOME w /\
  run_inst_seq (emitted_insts sa sb) s0 = OK t /\ vars_ext t0 t ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w /\
  (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
    lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas aid = SOME b) /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_memory = s0.vs_memory /\
  ~(t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_halted /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  `writes_fresh sa (emitted_insts sa sb) /\ sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[straight_fresh_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `eval_operand op t = SOME w` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = t0 with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  `stmt_state_rel ctx func cenv cx es (s0 with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[lookup_var_def]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]
QED
