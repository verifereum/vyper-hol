Theory fnPlanPlaceRevertPostamble
Ancestors
  codegen asmSem symbolResolve planExec stackPlanGen list
  asmToBytecodeProofs codegenEncodingWf words

Theorem distinct_symbols_no_later_write:
  !prog i lbl.
    ALL_DISTINCT (FLAT (MAP asm_defined_symbols prog)) /\
    i < LENGTH prog /\ EL i prog = AsmLabel lbl ==>
    !j. i < j /\ j < LENGTH prog ==>
      EL j prog <> AsmLabel lbl /\
      (!l. EL j prog = AsmDataHeader l ==> l <> lbl)
Proof
  Induct_on `prog` >- simp[] >>
  rpt gen_tac >> Cases_on `i`
  >- (simp[] >> strip_tac >> gvs[asm_defined_symbols_def] >>
      Cases_on `j` >- simp[] >>
      simp[] >> strip_tac >>
      `MEM (EL n prog) prog` by (simp[MEM_EL] >> metis_tac[]) >>
      gvs[MEM_FLAT, MEM_MAP] >>
      metis_tac[asm_defined_symbols_def, MEM]) >>
  simp[] >> strip_tac >> Cases_on `j` >- simp[] >>
  simp[] >> strip_tac >> gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem labelled_asm_slice_placed:
  !prog pre body post lbl.
    prog = pre ++ (AsmLabel lbl :: body) ++ post /\ asm_symbols_ok prog ==>
    ?off. FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off /\
      off < dimword (:256) /\
      FLOOKUP (build_offset_to_pc prog) off = SOME (LENGTH pre) /\
      asm_block_at prog (LENGTH pre) (AsmLabel lbl :: body)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH pre < LENGTH prog /\ EL (LENGTH pre) prog = AsmLabel lbl`
    by simp[EL_APPEND_EQN] >>
  drule asm_symbols_ok_distinct >> strip_tac >>
  `FLOOKUP (SND (compute_label_offsets prog)) lbl =
     SOME (asm_pc_to_offset prog (LENGTH pre))`
    by (irule label_offset_consistent_proof >>
        metis_tac[distinct_symbols_no_later_write]) >>
  qexists `asm_pc_to_offset prog (LENGTH pre)` >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (drule (cj 2 compute_label_offsets_bound) >> strip_tac >>
      qpat_x_assum `prog = _` kall_tac >>
      gvs[asm_symbols_ok_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  conj_tac
  >- (irule offset_to_pc_inverse_proof >>
      simp[symbolResolveTheory.asm_inst_size_def]) >>
  simp[asm_block_at_def, EL_APPEND_EQN]
QED
