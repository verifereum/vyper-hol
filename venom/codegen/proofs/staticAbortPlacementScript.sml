(* Symbol resolution for generated immediate assertion exits. *)
Theory staticAbortPlacement
Ancestors
  fnPlanPlaceRevertPostamble fnBlockBodyHelpers rich_list list asmSem words

Theorem assert_unreachable_end_placed_reloc:
  !prog lo pc lbl.
    asm_symbols_ok prog /\ code_labels_agree prog lo /\
    asm_block_at prog pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] ==>
    ?off.
      FLOOKUP lo lbl = SOME off /\
      off < dimword (:256) /\
      FLOOKUP (build_offset_to_pc prog) off = SOME (pc + 3)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`prog`, `lo`, `build_offset_to_pc prog`, `pc`,
    `[AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl]`]
    mp_tac asm_block_labels_reloc >> simp[] >>
  disch_then (qspecl_then [`lbl`, `3`] mp_tac) >> simp[]
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
  rpt gen_tac >> strip_tac >>
  qspecl_then [`prog`, `SND (compute_label_offsets prog)`, `pc`, `lbl`]
    mp_tac assert_unreachable_end_placed_reloc >> simp[]
QED
