(* Own-code opcode facts at arbitrary label offsets. *)
Theory asmSymOwnStep
Ancestors
  asmSymBridge asmSymOwnCode asmSymSem asmSem asmWf symbolResolve
  vfmTypes list finite_map words spillWordBounds asmToBytecodeProofs

Theorem sym_codesize_own_sim:
  asm_sym_rel_own lo p env own cs ss ⇒
  ∃cs' ss'.
    sym_step_op_own p env own "CODESIZE" ss = SymOK ss' ∧
    asm_step_op otp "CODESIZE" cs = AsmOK cs' ∧
    asm_sym_rel_own lo p env own cs' ss'
Proof
  strip_tac >>
  simp[sym_step_op_own_def, sym_set_stack_def,
       asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def, asm_step_copy_def, asm_step_context_def,
       asm_push_val_def] >>
  gvs[asm_sym_rel_own_def, asm_next_def, sval_conc_def] >>
  conj_tac
  >- (rename1 `LENGTH memory = LENGTH cs.as_memory` >>
      qexists_tac `memory` >> simp[]) >> metis_tac[]
QED

Theorem asm_data_env_lo_ok_canonical:
  asm_static_wf p ⇒
  (asm_data_env_lo_ok (SND (compute_label_offsets p)) p env code ⇔
   asm_data_env_ok p env code)
Proof
  strip_tac >>
  `∀l. MEM (AsmDataHeader l) p ⇒
       ∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off ∧
             off < dimword (:256) DIV 2` by
    (rpt strip_tac >>
     `l ∈ FDOM (SND (compute_label_offsets p))` by
       (simp[compute_label_offsets_def, clo_step_eq] >>
        irule clo_FDOM >> simp[]) >>
     `∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off` by
       gvs[FLOOKUP_DEF] >>
     qexists_tac `off` >> simp[] >>
     `off < 65536` by
       (fs[asm_static_wf_def, asm_encoding_wf_def, pairTheory.UNCURRY] >>
        qpat_x_assum `∀lbl off. FLOOKUP _ lbl = SOME off ⇒ _` drule >>
        simp[symbol_size_def] >> strip_tac >>
        drule encode_num_bytes_length_bound >> simp[]) >>
     simp[dimword_def] >> decide_tac) >>
  simp[asm_data_env_lo_ok_def, asm_data_env_ok_def, sym_data_label_def] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem asm_sym_rel_own_canonical:
  asm_static_wf p ⇒
  (asm_sym_rel_own (SND (compute_label_offsets p)) p env own cs ss ⇔
   asm_sym_rel p env cs ss ∧ cs.as_code = own)
Proof
  strip_tac >> Cases_on `cs.as_code = own` >>
  gvs[asm_sym_rel_own_def, asm_sym_rel_def, asm_data_env_lo_ok_canonical]
QED
