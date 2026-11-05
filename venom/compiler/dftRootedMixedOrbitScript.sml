Theory dftRootedMixedOrbit
Ancestors
  dftRootedMixedSegment dftCofinalSegments dftOccurrenceMachine
  dftPositionalPhase dftGasOrdinaryTrace arithmetic

(* Root provenance is retained independently of the current phase. *)
Definition dft_pos_rooted_mixed_phase_def:
  dft_pos_rooted_mixed_phase C D w fi bi pre rootR l r <=>
    (dft_pos_gas_phase C D fi bi pre l r \/ dft_gas_ordinary_stopped l r) /\
    (?m. r = FUNPOW (dft_occ_oracle_next w D) m rootR)
End

Theorem dft_pos_mixed_root_advance:
  (?m. r = FUNPOW R m rootR) ==>
  ?m. FUNPOW R b r = FUNPOW R m rootR
Proof
  strip_tac >> qexists_tac `b + m` >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_rooted_mixed_progress:
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  dft_original_context Corig D /\ ctx_labels_bound Corig L /\ o1_ctx_shape Corig /\
  fi < LENGTH D.ctx_functions /\
  bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
  (EL bi (EL fi D.ctx_functions).fn_blocks).bb_instructions = pre ++ [inst;gas] ++ post /\
  ~is_pseudo inst.inst_opcode /\ MEM rootfn D.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  rootR = dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0) /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> inst_wf i) /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> i.inst_opcode <> ALLOCA) /\
  dft_pos_rooted_mixed_phase C D w fi bi pre rootR l r ==>
  ?a b. 0 < a /\ a <= 3 /\ 0 < b /\ b <= 2 /\
    dft_pos_rooted_mixed_phase C D w fi bi pre rootR
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r) /\
    (dft_pos_segment_account C D w a b l r \/
     dft_pos_mixed_exception C D w gas inst a b l r)
Proof
  strip_tac >>
  `?m. r = FUNPOW (dft_occ_oracle_next w D) m rootR` by
    (fs[dft_pos_rooted_mixed_phase_def] >> metis_tac[]) >>
  `?a b. 0 < a /\ a <= 3 /\ 0 < b /\ b <= 2 /\
    (dft_pos_gas_phase C D fi bi pre
       (FUNPOW (dft_occ_oracle_next w C) a l)
       (FUNPOW (dft_occ_oracle_next w D) b r) \/
     dft_gas_ordinary_stopped
       (FUNPOW (dft_occ_oracle_next w C) a l)
       (FUNPOW (dft_occ_oracle_next w D) b r)) /\
    (dft_pos_segment_account C D w a b l r \/
     dft_pos_mixed_exception C D w gas inst a b l r)` by
    (irule dft_pos_rooted_mixed_closed_next >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[dft_pos_rooted_mixed_phase_def] >> metis_tac[]) >>
  qexistsl_tac [`a`, `b`] >>
  simp[dft_pos_rooted_mixed_phase_def] >>
  metis_tac[dft_pos_mixed_root_advance]
QED

Definition dft_pos_mixed_orbit_cuts_def:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B <=>
    A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. dft_pos_gas_phase C D fi bi pre
        (FUNPOW (dft_occ_oracle_next w C) (A n) c)
        (FUNPOW (dft_occ_oracle_next w D) (B n) d) \/
      dft_gas_ordinary_stopped
        (FUNPOW (dft_occ_oracle_next w C) (A n) c)
        (FUNPOW (dft_occ_oracle_next w D) (B n) d)) /\
    (!n. let a = A (SUC n) - A n; b = B (SUC n) - B n;
             l = FUNPOW (dft_occ_oracle_next w C) (A n) c;
             r = FUNPOW (dft_occ_oracle_next w D) (B n) d
         in 0 < a /\ a <= 3 /\ 0 < b /\ b <= 2 /\
           (dft_pos_segment_account C D w a b l r \/
            dft_pos_mixed_exception C D w gas inst a b l r))
End

Theorem dft_pos_rooted_mixed_orbit_segments:
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  (dft_pos_gas_phase C D fi bi pre c d \/ dft_gas_ordinary_stopped c d) /\
  dft_original_context Corig D /\ ctx_labels_bound Corig L /\ o1_ctx_shape Corig /\
  fi < LENGTH D.ctx_functions /\
  bi < LENGTH (EL fi D.ctx_functions).fn_blocks /\
  (EL bi (EL fi D.ctx_functions).fn_blocks).bb_instructions = pre ++ [inst;gas] ++ post /\
  ~is_pseudo inst.inst_opcode /\ MEM rootfn D.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  rootR = dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0) /\
  d = FUNPOW (dft_occ_oracle_next w D) m rootR /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> inst_wf i) /\
  (!fn i. MEM fn Corig.ctx_functions /\ MEM i (fn_insts fn) ==> i.inst_opcode <> ALLOCA) ==>
  ?A B. dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B
Proof
  strip_tac >>
  qabbrev_tac `P = dft_pos_rooted_mixed_phase C D w fi bi pre rootR` >>
  qabbrev_tac `H = \a b l r.
    0 < a /\ a <= 3 /\ 0 < b /\ b <= 2 /\
    (dft_pos_segment_account C D w a b l r \/
     dft_pos_mixed_exception C D w gas inst a b l r)` >>
  `P c d` by
    (simp[Abbr `P`, dft_pos_rooted_mixed_phase_def] >> metis_tac[]) >>
  `!l r. P l r ==> ?a b. 0 < a /\ 0 < b /\
    P (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r) /\ H a b l r` by
    (rpt gen_tac >> strip_tac >>
     `?a b. 0 < a /\ a <= 3 /\ 0 < b /\ b <= 2 /\
       P (FUNPOW (dft_occ_oracle_next w C) a l)
         (FUNPOW (dft_occ_oracle_next w D) b r) /\
       (dft_pos_segment_account C D w a b l r \/
        dft_pos_mixed_exception C D w gas inst a b l r)` by
       (simp[Abbr `P`] >> irule dft_pos_rooted_mixed_progress >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     qexistsl_tac [`a`, `b`] >> simp[Abbr `H`] >> metis_tac[]) >>
  drule_all dft_cofinal_segments >> strip_tac >>
  qexistsl_tac [`A`, `B`] >>
  simp[dft_pos_mixed_orbit_cuts_def, LET_THM] >>
  fs[Abbr `H`, Abbr `P`, dft_pos_rooted_mixed_phase_def] >> metis_tac[]
QED
