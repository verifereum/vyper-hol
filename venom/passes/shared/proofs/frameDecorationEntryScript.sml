Theory frameDecorationEntry
Ancestors frameFiniteJointDecoration contextCodegenRel venomExecProofs
  venomExecSemantics venomInst

Theorem decoration_entry_instruction:
  decoration_entry fn s q /\ ALL_DISTINCT (fn_labels fn) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  decoration_at fn i s q
Proof
  Cases_on `q` >>
  simp[decoration_entry_def, decoration_at_def] >> strip_tac >>
  fs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> gvs[fn_labels_def]) >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  simp[active_inst_def] >> metis_tac[]
QED

val _ = export_theory();
