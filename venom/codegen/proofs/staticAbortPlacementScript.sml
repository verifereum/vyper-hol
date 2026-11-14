(* Symbol resolution for generated immediate assertion exits. *)
Theory staticAbortPlacement
Ancestors
  fnPlanPlaceRevertPostamble rich_list list asmSem words

Theorem codegen_revert_placed:
  !rpolicy unit cp prog.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog ==>
    asm_symbols_ok prog /\
    ?off pc.
      FLOOKUP (SND (compute_label_offsets prog)) "revert" = SOME off /\
      off < dimword (:256) /\
      FLOOKUP (build_offset_to_pc prog) off = SOME pc /\
      asm_block_at prog pc (execute_plan cp.cp_initial_fmp revert_postamble)
Proof
  rpt strip_tac >> drule_all codegen_revert_slice >> strip_tac >>
  drule_all labelled_asm_slice_placed >> strip_tac >>
  metis_tac[]
QED

(* Applies to any occurrence of a chunk, not just its original region. *)
Theorem asm_block_label_placed:
  !prog pc code i lbl.
    asm_symbols_ok prog /\ asm_block_at prog pc code /\
    i < LENGTH code /\ EL i code = AsmLabel lbl ==>
    ?off.
      FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off /\
      off < dimword (:256) /\
      FLOOKUP (build_offset_to_pc prog) off = SOME (pc + i)
Proof
  rpt strip_tac >>
  `pc + i < LENGTH prog /\ EL (pc + i) prog = AsmLabel lbl`
    by gvs[asm_block_at_def] >>
  `prog = TAKE (pc + i) prog ++
      (AsmLabel lbl :: DROP (SUC (pc + i)) prog) ++ []`
    by (drule TAKE_DROP_SUC >> simp[]) >>
  drule_all labelled_asm_slice_placed >>
  simp[LENGTH_TAKE] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

Theorem assert_unreachable_end_placed:
  !prog pc lbl.
    asm_symbols_ok prog /\
    asm_block_at prog pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] ==>
    ?off.
      FLOOKUP (SND (compute_label_offsets prog)) lbl = SOME off /\
      off < dimword (:256) /\
      FLOOKUP (build_offset_to_pc prog) off = SOME (pc + 3)
Proof
  rpt strip_tac >> irule asm_block_label_placed >>
  simp[] >> qexists `[AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl]` >>
  simp[]
QED
