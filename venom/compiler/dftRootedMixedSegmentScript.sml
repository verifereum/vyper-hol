Theory dftRootedMixedSegment
Ancestors
  dftIndexedFirstShape dftPositionalMixedSegment dftPositionalEdit dftPositionalPhase
  dftOccurrenceMachine dftOpenMachine venomInst list

Theorem dft_pos_rooted_mixed_segment_next:
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  dft_pos_gas_phase C D fi bi pre l r /\
  dft_original_context Corig D /\ ctx_labels_bound Corig L /\ o1_ctx_shape Corig /\
  fi < LENGTH D.ctx_functions /\
  bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
  (EL bi (EL fi D.ctx_functions).fn_blocks).bb_instructions = pre ++ [inst;gas] ++ post /\
  ~is_pseudo inst.inst_opcode /\ MEM rootfn D.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  r = FUNPOW (dft_occ_oracle_next w D) m
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> inst_wf i) /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> i.inst_opcode <> ALLOCA) ==>
  (?a. (a = 1 \/ a = 2) /\
    dft_pos_gas_phase C D fi bi pre
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) a r) /\
    dft_pos_segment_account C D w a a l r) \/
  (?f g bb bb' s ls rs n code t.
    l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
    r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
    dft_pos_slot C D fi bi f g bb bb' /\
    s.vs_inst_idx = LENGTH pre /\ step_inst_base inst s = Abort code t)
Proof
  strip_tac >> irule dft_pos_mixed_segment_next >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      qpat_x_assum `D = _` kall_tac >> fs[dft_pos_slot_def] >>
      irule dft_rooted_indexed_first_no_error >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  asm_rewrite_tac[] >> qexistsl_tac [`gas`, `post`, `v`] >> simp[]
QED
