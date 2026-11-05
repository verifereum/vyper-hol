(* Checked interface probes for the membership loader's memory checks. *)
Theory exprSimBopRestWordLoadSafety
Ancestors
  exprSimBopRestWordLoads exprSimBopRestWordStorageLoads
  instMemFrontier fragExecMem memSafeRun emitHelper venomInst
  words arithmetic list finite_map loweringPosts exprLoweringProps compileEnv

Theorem rest_word_load_safety_checks:
  MEM opc [MLOAD; ILOAD; SLOAD; TLOAD; DLOAD] /\
  eval_operand addr s = SOME w ==>
  (run_inst_seq_mem_ok [mk_inst iid opc [addr] outs] s <=>
   ((opc = MLOAD \/ opc = ILOAD) ==> w2n w + 32 <= s.vs_alloca_next) /\
   (opc = DLOAD ==> w2n w <= LENGTH s.vs_data_section))
Proof
  strip_tac >> fs[] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD, below_frontier_ILOAD,
       inst_dload_in_section_def, mk_inst_def] >>
  simp[below_frontier_no_ranges]
QED

Theorem rest_word_immutable_region_bound:
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx ty tv w es s /\
  evaluate_type (get_tenv cx) ty = SOME vt ==>
  w2n w + type_memory_size vt <=
    (if cenv.ce_is_ctor then s.vs_alloca_next else LENGTH s.vs_data_section)
Proof
  strip_tac >>
  qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
  simp[immutable_holds_def] >> strip_tac >>
  `k + type_memory_size vt <= type_memory_size itv` by
    fs[sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  `w2n w = off + k` by simp[] >>
  (Cases_on `cenv.ce_is_ctor`
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
      simp[exprLoweringPropsTheory.stmt_state_rel_def,
           exprLoweringPropsTheory.immutable_alloca_sep_def] >>
      rpt strip_tac >>
      qpat_x_assum `!name tv v off. _` drule_all >> strip_tac >> decide_tac) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def,
       compileEnvTheory.immutables_rel_def] >> rpt strip_tac >>
  qpat_x_assum `!name tv v byte_offset. _` drule_all >> strip_tac >> decide_tac)
QED

(* Constructor staging adds the zero immutable base before the memory load.
   The ADD changes only variables, hence preserves the allocation frontier. *)
Theorem rest_word_staged_load_safety_probe:
  eval_operand addr s = SOME a /\ eval_operand region s = SOME 0w /\
  w2n a + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst iid ADD [addr; region] [tmp];
     mk_inst jid MLOAD [Var tmp] outs] s
Proof
  strip_tac >>
  qspecl_then [`addr`, `region`] mp_tac emitHelperPropsTheory.step_ADD >>
  disch_then (qspecl_then [`a`, `0w`, `iid`, `tmp`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[run_inst_seq_mem_ok_cons, below_frontier_no_ranges,
       inst_dload_in_section_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD,
       inst_dload_in_section_def, mk_inst_def,
       venomStateTheory.update_var_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, FLOOKUP_UPDATE, WORD_ADD_0]
QED
