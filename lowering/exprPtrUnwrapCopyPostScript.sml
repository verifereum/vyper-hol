Theory exprPtrUnwrapCopyPost
Ancestors
  exprPtrUnwrapLoopInvariant slotCopyExecution fragGasPathPtr fragGasSeqPtr
  ptrDiscipline bodyPtrDefs valueEncoding byte list rich_list

(* Runtime and ghost prefix projections are kept independent of execution. *)
Theorem copy_prefix_words:
  slot_copy_inv cs load original p d n regions i s ==>
  !j. j < i ==>
    mem_word_at (w2n d + 32*j) s.vs_memory =
      slot_copy_word load original (p+n2w j)
Proof
  simp[slot_copy_inv_def, slot_copy_prefix_def] >> strip_tac >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!j. j < i ==> _` drule >> strip_tac >>
  `32 <= LENGTH (DROP (32*j + w2n d) s.vs_memory)` by simp[] >>
  pure_rewrite_tac[mem_word_at_def] >>
  `w2n d+32*j = 32*j+w2n d` by decide_tac >>
  qpat_x_assum `w2n d+32*j = _` (fn th => pure_rewrite_tac[th]) >>
  `32 - LENGTH (DROP (32*j + w2n d) s.vs_memory) = 0` by decide_tac >>
  pure_asm_rewrite_tac[TAKE_APPEND, TAKE_0, APPEND_NIL] >>
  simp[word_of_bytes_word_to_bytes, dividesTheory.divides_def]
QED

Theorem copy_prefix_taint:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s ==>
  !j b. j < i /\ b < 32 /\ w2n d+32*j+b IN tn.t_mem ==>
    b IN key_taint (if load=SLOAD then tn0.t_stor else tn0.t_trans) (p+n2w j)
Proof
  simp[slot_copy_ghost_inv_def]
QED
