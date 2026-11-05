Theory dftRootedMixedSegment
Ancestors
  dftIndexedFirstShape dftPositionalMixedSegment dftPositionalEdit dftPositionalPhase
  dftOccurrenceMachine dftOpenMachine dftPositionalSegment
  dftGasOrdinaryTrace dftOccurrenceOrdinaryStop dftOccurrenceGasEdit
  dftOrdinaryEventTrace dftOccurrenceReplay venomInst list arithmetic

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

Theorem dft_pos_mixed_stopped_next[local]:
  dft_gas_ordinary_stopped l r ==>
  dft_gas_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w C) 1 l)
    (FUNPOW (dft_occ_oracle_next w D) 1 r) /\
  dft_pos_segment_account C D w 1 1 l r
Proof
  strip_tac >> fs[dft_gas_ordinary_stopped_def] >>
  ` (dft_occ_oracle_next w C l).dft_occ_core = DftOpen (DftDone (Abort a s)) [] n /\
    (dft_occ_oracle_next w D r).dft_occ_core = DftOpen (DftDone (Abort a t)) [] m` by
    metis_tac[dft_occ_abort_clear] >>
  simp[FUNPOW_1, dft_gas_ordinary_stopped_def] >>
  simp[dft_pos_segment_account_def, FUNPOW_1, dft_occ_count_def,
    dft_done_no_gas_event, dft_open_observe_def]
QED

Definition dft_pos_mixed_exception_def:
  dft_pos_mixed_exception C D w gas inst a b l r <=>
    a = 3 /\ b = 2 /\
    dft_gas_ordinary_stopped
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r) /\
    dft_mixed_segment_events w C D gas inst l r a b /\
    (?f g bb bb' s ls rs n.
      l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
      r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
      dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a l) = SUC n /\
      dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b r) = n) /\
    (!i addr. ((?h. h < a /\ dft_occ_gas_event i addr
        (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
        i = gas /\ addr = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]) /\
      ~(?h. h < b /\ dft_occ_gas_event i addr
        (FUNPOW (dft_occ_oracle_next w D) h r))) /\
    (!j f i t. j < a /\ dft_open_observe f i t
        (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
        inst_mem_ranges i t <> [] ==>
      ?k g u. k < b /\ dft_pos_functions C D f g /\
        dft_open_observe g i u
          (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
        u.vs_memory = t.vs_memory /\ inst_mem_ranges i u = inst_mem_ranges i t) /\
    (!k g i u. k < b /\ dft_open_observe g i u
        (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
        inst_mem_ranges i u <> [] ==>
      ?j f t. j < a /\ dft_pos_functions C D f g /\
        dft_open_observe f i t
          (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
        u.vs_memory = t.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i u)
End

Theorem dft_pos_rooted_mixed_closed_next:
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  (dft_pos_gas_phase C D fi bi pre l r \/ dft_gas_ordinary_stopped l r) /\
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
  ?a b. 0 < a /\ a <= 3 /\ 0 < b /\ b <= 2 /\
    (dft_pos_gas_phase C D fi bi pre
       (FUNPOW (dft_occ_oracle_next w C) a l)
       (FUNPOW (dft_occ_oracle_next w D) b r) \/
     dft_gas_ordinary_stopped
       (FUNPOW (dft_occ_oracle_next w C) a l)
       (FUNPOW (dft_occ_oracle_next w D) b r)) /\
    (dft_pos_segment_account C D w a b l r \/
     dft_pos_mixed_exception C D w gas inst a b l r)
Proof
  strip_tac
  >- ( `(?a. (a = 1 \/ a = 2) /\
         dft_pos_gas_phase C D fi bi pre
           (FUNPOW (dft_occ_oracle_next w C) a l)
           (FUNPOW (dft_occ_oracle_next w D) a r) /\
         dft_pos_segment_account C D w a a l r) \/
       (?f g bb bb' s ls rs n code t.
         l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
         r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
         dft_pos_slot C D fi bi f g bb bb' /\
         s.vs_inst_idx = LENGTH pre /\ step_inst_base inst s = Abort code t)` by
        (irule dft_pos_rooted_mixed_segment_next >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[])
       >- (qexistsl_tac [`a`, `a`] >> simp[] >> decide_tac)
       >- (qexistsl_tac [`a`, `a`] >> simp[] >> decide_tac) >>
       drule_all dft_pos_mixed_pair_abort_closed >>
       disch_then (qspec_then `w` strip_assume_tac) >>
       qexistsl_tac [`3`, `2`] >> simp[dft_pos_mixed_exception_def] >>
       metis_tac[]) >>
  drule dft_pos_mixed_stopped_next >>
  disch_then (qspecl_then [`w`, `D`, `C`] strip_assume_tac) >>
  qexistsl_tac [`1`, `1`] >> simp[]
QED
