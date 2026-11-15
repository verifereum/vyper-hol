(* Symbol resolution for generated immediate assertion exits. *)
Theory staticAbortPlacement
Ancestors
  fnPlanPlaceRevertPostamble fnBlockBodyHelpers rich_list list asmSem words

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
  rpt strip_tac >> drule asm_block_labels >> disch_then drule >>
  simp[] >> disch_then (qspecl_then [`lbl`, `3`] mp_tac) >> simp[]
QED
