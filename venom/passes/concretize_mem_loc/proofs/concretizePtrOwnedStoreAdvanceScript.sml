Theory concretizePtrOwnedStoreAdvance
Ancestors concretizePtrMatchedStore concretizePtrDeletedGapHistory
  concretizePtrLedgerAlignment concretizePtrSourceOwnership concretizePtrPrefixLedger
  concretizePtrLedgerProbe concretizePtrChronologicalHistory
  concretizePtrActivationChronology contextCodegenRel ptrDiscipline
  venomExecSemantics venomState venomInst list arithmetic

Theorem ptr_owned_mstore_advance:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  MEM sb a.po_fn.fn_blocks /\ sb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx sb.bb_instructions /\
  MEM tb b.po_fn.fn_blocks /\ tb.bb_label = b.po_state.vs_current_bb /\
  b.po_inst = EL b.po_state.vs_inst_idx tb.bb_instructions /\
  ptr_ledger_block_alignment positions sb.bb_instructions tb.bb_instructions indices /\
  SUC j < LENGTH indices /\ a.po_state.vs_inst_idx = EL j indices /\
  b.po_state.vs_inst_idx = j /\
  (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP positions (Allocation i.inst_id) = SOME p) /\
  a.po_inst.inst_opcode = MSTORE /\ b.po_inst.inst_opcode = MSTORE /\
  a.po_inst.inst_operands = [sa;sv] /\ b.po_inst.inst_operands = [ta;tv] /\
  eval_operand sa a.po_state = SOME x /\ eval_operand sv a.po_state = SOME v /\
  eval_operand ta b.po_state = SOME y /\ eval_operand tv b.po_state = SOME vt /\
  word_agree_except (op_taint a.po_taint sv) v vt /\
  (!i:num. reloc i = w2n y + (i - w2n x)) ==>
  ?z w c delta tokens' registry' births' PT' TG' saved'.
    ptr_ledger_write_pair C Ct reloc a z b w /\
    (?gap. delta = z :: gap) /\
    LENGTH delta = EL (SUC j) indices - EL j indices /\
    ptr_source_ownership vs0 C (h ++ delta) c tokens' registry' births' PT' TG' saved' /\
    c.po_fn = a.po_fn /\ c.po_stack = a.po_stack /\ c.po_params = a.po_params /\
    c.po_state = (mstore (w2n x) v a.po_state with vs_inst_idx := EL (SUC j) indices) /\
    c.po_inst = EL (EL (SUC j) indices) sb.bb_instructions /\
    w.po_state = (mstore (w2n y) vt b.po_state with vs_inst_idx := SUC j) /\
    w.po_inst = EL (SUC j) tb.bb_instructions /\
    z = ptr_ledger_next a (EL (SUC (EL j indices)) sb.bb_instructions)
      (mstore (w2n x) v a.po_state) /\
    w = ptr_ledger_next b (EL (SUC j) tb.bb_instructions)
      (mstore (w2n y) vt b.po_state) /\
    c = ptr_gap_scan sb (EL (SUC j) indices - SUC (EL j indices)) z
Proof
  strip_tac >>
  `j < LENGTH indices` by decide_tac >>
  `EL j indices < EL (SUC j) indices` by
    (irule ptr_ledger_alignment_order >> metis_tac[prim_recTheory.LESS_SUC_REFL]) >>
  `LENGTH tb.bb_instructions = LENGTH indices /\
    EL j indices < LENGTH sb.bb_instructions /\
    EL (SUC j) indices < LENGTH sb.bb_instructions` by
    (drule ptr_ledger_alignment_cursor >> metis_tac[]) >>
  `SUC (EL j indices) < LENGTH sb.bb_instructions` by decide_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (simp[active_inst_def] >> qexists_tac `sb` >> simp[]) >>
  `active_inst b.po_fn b.po_inst b.po_state` by
    (simp[active_inst_def] >> qexists_tac `tb` >> simp[]) >>
  `active_inst a.po_fn (EL (SUC (EL j indices)) sb.bb_instructions)
    (mstore (w2n x) v a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (simp[active_inst_def, mstore_def] >> qexists_tac `sb` >> simp[]) >>
  `active_inst b.po_fn (EL (SUC j) tb.bb_instructions)
    (mstore (w2n y) vt b.po_state with vs_inst_idx := SUC b.po_state.vs_inst_idx)` by
    (simp[active_inst_def, mstore_def] >> qexists_tac `tb` >> simp[]) >>
  drule_all ptr_mstore_matched_events >>
  disch_then (qspecl_then [`Ct`,`C`] strip_assume_tac) >>
  `ptr_chrono_step C a z` by
    metis_tac[ptr_ledger_write_pair_def] >>
  `LENGTH saved = LENGTH a.po_stack` by
    metis_tac[ptr_source_ownership_stack_length] >>
  drule ptr_tagged_chrono_step_total >>
  disch_then (qspecl_then [`HD tokens`,`PT`,`TG`,`saved`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all (cj 2 ptr_source_ownership_rules) >> strip_tac >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ptr_chrono_step _ _ _` kall_tac >>
  qpat_x_assum `ptr_source_ownership _ _ h _ _ _ _ _ _ _` kall_tac >>
  `z.po_fn = a.po_fn /\ z.po_stack = a.po_stack /\
   z.po_params = a.po_params /\
   z.po_state = (mstore (w2n x) v a.po_state with vs_inst_idx := SUC (EL j indices)) /\
   z.po_inst = EL (SUC (EL j indices)) sb.bb_instructions` by
    simp[ptr_ledger_next_def, ptr_observe_def] >>
  `z.po_state.vs_inst_idx = SUC (EL j indices) /\
   z.po_state.vs_current_bb = a.po_state.vs_current_bb` by simp[mstore_def] >>
  `?gap c. LENGTH gap = EL (SUC j) indices - SUC (EL j indices) /\
    c = ptr_gap_scan sb (EL (SUC j) indices - SUC (EL j indices)) z /\
    (?ts rg bs ps gs ss. ptr_source_ownership vs0 C ((h ++ [z]) ++ gap) c ts rg bs ps gs ss) /\
    c.po_fn = z.po_fn /\ c.po_stack = z.po_stack /\ c.po_params = z.po_params /\
    c.po_inst = EL (EL (SUC j) indices) sb.bb_instructions /\
    c.po_state = (z.po_state with vs_inst_idx := EL (SUC j) indices)` by
    (drule ptr_gap_ownership_aligned >>
     disch_then (qspecl_then [`tb.bb_instructions`,`positions`,`SUC j`,`indices`,`sb`] mp_tac) >>
     simp[IgnAsm `z = _`, IgnAsm `z.po_state = _`] >>
     metis_tac[]) >>
  qexistsl_tac [`z`,`w`,`c`,`z::gap`,`ts`,`rg`,`bs`,`ps`,`gs`,`ss`] >>
  `LENGTH (z::gap) = EL (SUC j) indices - EL j indices` by
    (simp[] >> decide_tac) >>
  qpat_x_assum `ptr_source_ownership _ _ ((h ++ _) ++ gap) _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> strip_tac >>
  simp[IgnAsm `z = _`, IgnAsm `c = _`, ptr_ledger_next_def, ptr_observe_def] >>
  metis_tac[ptr_ledger_next_def, ptr_observe_def]
QED
