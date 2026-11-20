(* Successful legacy boundary runs at arbitrary label offsets. *)
Theory symFrameBoundaryPairing
Ancestors arithmetic[qualified,ignore_grammar] option[qualified,ignore_grammar]
  codegenSymRel asmSymOwnStep fnPlanPlaceRevertPostamble
  asmSymForwardOwn asmSymBridge asmSymSem asmSem asmWf
  symbolResolve list finite_map words asmOptimizer asmSymRelocLabelsOwn asmSymModeOwn

Theorem sym_frame_inv_canonical_own:
  !p env own ctx cp fn ret srest labs0 ps cs ss.
  asm_static_wf p ==>
  (sym_frame_inv_own (SND (compute_label_offsets p)) p env own ctx cp fn ret srest labs0 ps cs ss <=>
   sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\ cs.as_code = own)
Proof
  simp[sym_frame_inv_own_def, sym_frame_inv_def, asm_sym_rel_own_canonical] >>
  metis_tac[]
QED

Theorem boundary_label_ref_defined:
  !p lo env own cs ss l d.
  asm_static_wf p /\ code_labels_agree p lo /\
  asm_sym_rel_own lo p env own cs ss /\
  (MEM (AsmPushLabel l) p \/ MEM (AsmPushOfst l d) p) ==>
  ?off. FLOOKUP lo l = SOME off
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `asm_data_env_lo_ok lo p env own` by fs[asm_sym_rel_own_def] >>
  metis_tac[asm_push_label_lookup_reloc]
QED

Theorem boundary_jump_dest_conc:
  !p lo dest i w.
  asm_static_wf p /\ code_labels_agree p lo /\
  sym_jump_dest p dest = SOME i /\ sval_conc lo dest = SOME w ==>
  FLOOKUP (build_offset_to_pc p) (w2n w) = SOME i
Proof
  rpt gen_tac >> MATCH_ACCEPT_TAC sym_jump_dest_conc_reloc
QED

Theorem asm_sym_legacy_step_own:
  !p lo env own cs ss out.
  asm_static_wf p /\ code_labels_agree p lo /\
  asm_sym_rel_own lo p env own cs ss /\ cs.as_pc < LENGTH p /\
  sym_step p env (EL cs.as_pc p) ss = SymOK out ==>
  ?cs'. asm_step lo (build_offset_to_pc p) (EL cs.as_pc p) cs = AsmOK cs' /\
    asm_sym_rel_own lo p env own cs' out
Proof
  rpt strip_tac >>
  `MEM (EL cs.as_pc p) p` by simp[EL_MEM] >>
  drule_all (Q.INST [`allow_own` |-> `F`, `ai` |-> `EL cs.as_pc p`]
    asm_sym_inst_step_mode) >>
  simp[]
QED

Theorem asm_sym_legacy_steps_own:
  !p lo env own.
  asm_static_wf p /\ code_labels_agree p lo ==>
  !n cs ss out.
  asm_sym_rel_own lo p env own cs ss /\ sym_steps p env n ss = SymOK out ==>
  ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
    asm_sym_rel_own lo p env own cs' out
Proof
  rpt strip_tac >>
  drule_all (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`] asm_sym_steps_mode_sim)) >>
  simp[]
QED

Theorem sym_frame_inv_same_count_own:
  !lo o2pc prog env own ctx cp fn ret srest labs0 ps cs ss n cs' ss' ps'.
  code_labels_agree prog lo /\
  o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps cs ss /\
  asm_steps lo o2pc prog n cs = AsmOK cs' /\
  sym_steps prog env n ss = SymOK ss' /\
  sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
     FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rpt strip_tac >>
  `asm_sym_rel_own lo prog env own cs ss` by fs[sym_frame_inv_own_def] >>
  drule_all asm_sym_legacy_steps_own >> (gvs[codegenSymRelTheory.sym_frame_inv_own_def])
QED
