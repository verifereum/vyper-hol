(* Code-label lookup and jump concretization at supplied label offsets. *)
Theory asmSymRelocLabelsOwn
Ancestors asmSymBridge fnPlanPlaceRevertPostamble asmSymSem asmOptimizer
  list finite_map words

Theorem asm_push_label_lookup_reloc:
  asm_static_wf p /\ code_labels_agree p lo /\
  asm_data_env_lo_ok lo p env own /\
  (MEM (AsmPushLabel l) p \/ (?d. MEM (AsmPushOfst l d) p)) ==>
  ?off. FLOOKUP lo l = SOME off
Proof
  strip_tac >> (
  `MEM l (asm_label_refs p)` by
    (fs[asm_label_refs_def, MEM_FLAT, MEM_MAP] >>
     qexists_tac `[l]` >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `MEM (AsmLabel l) p`
  >- (`?i. INDEX_OF (AsmLabel l) p = SOME i` by
        (Cases_on `INDEX_OF (AsmLabel l) p` >>
         gvs[INDEX_OF_eq_NONE]) >>
      drule_all asm_static_wf_code_label >> strip_tac >>
      fs[code_labels_agree_def] >> metis_tac[]) >>
  `MEM (AsmDataHeader l) p` by metis_tac[asm_static_wf_def] >>
  fs[asm_data_env_lo_ok_def] >> metis_tac[])
QED

Theorem sym_jump_dest_conc_reloc:
  asm_static_wf p /\ code_labels_agree p lo /\
  sym_jump_dest p dest = SOME i /\ sval_conc lo dest = SOME w ==>
  FLOOKUP (build_offset_to_pc p) (w2n w) = SOME i
Proof
  Cases_on `dest` >> simp[sym_jump_dest_def] >> strip_tac >>
  rename1 `INDEX_OF (AsmLabel l) p = SOME i` >>
  `MEM (AsmLabel l) p` by
    (Cases_on `MEM (AsmLabel l) p` >> gvs[GSYM INDEX_OF_eq_NONE]) >>
  drule_all asm_static_wf_code_label >> strip_tac >>
  `FLOOKUP lo l = SOME off` by fs[code_labels_agree_def] >>
  gvs[sval_conc_def] >>
  `off < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  simp[arithmeticTheory.LESS_MOD]
QED
