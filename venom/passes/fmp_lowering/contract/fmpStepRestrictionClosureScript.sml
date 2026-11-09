(* Local closure interfaces for pointwise structural restrictions. *)
Theory fmpStepRestrictionClosure
Ancestors
  fmpStepPredicateTransport fmpStepLayout fmpStepRewrite fmpLowerDefs fmpLowerProps
  o1PassContract venomInst list rich_list

Theorem fmp_lower_inst_invoke_head:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\j. j.inst_opcode = INVOKE ==>
    ?target. fmp_inst_invokes target j) out
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[fmp_inst_invokes_def]
QED

Theorem fmp_lower_inst_label_refs:
  (!l. MEM (Label l) inst.inst_operands /\ inst.inst_opcode <> INVOKE ==>
    MEM l labels \/ reserved_label l) /\
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\j. !l. MEM (Label l) j.inst_operands /\ j.inst_opcode <> INVOKE ==>
    MEM l labels \/ reserved_label l) out
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all fmp_lower_inst_label_origin >> metis_tac[]
QED

Theorem fmp_lower_inst_invoke_ok:
  (inst.inst_opcode = INVOKE ==>
    ?lbl rest. inst.inst_operands = Label lbl::rest /\ MEM lbl names) /\
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\j. j.inst_opcode = INVOKE ==>
    ?lbl rest. j.inst_operands = Label lbl::rest /\ MEM lbl names) out
Proof
  strip_tac >> drule fmp_lower_inst_invoke_head >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule_all fmp_lower_inst_invokes >>
  gvs[fmp_inst_invokes_def] >> strip_tac >> gvs[]
QED

Theorem fmp_emit_restores_restrictions:
  fmp_emit_restores runner s bases = (out,s') ==>
  EVERY (\j. j.inst_opcode <> INVOKE /\
    (!l. ~MEM (Label l) j.inst_operands) /\
    ~MEM j.inst_opcode [RET; RETFMP; DRET; STOP; RETURN] /\
    ~is_param_opcode j.inst_opcode) out
Proof
  strip_tac >> drule_at (Pat `fmp_emit_restores _ _ _ = _`) fmp_emit_restores_every >>
  disch_then irule >> simp[mk_inst_def, is_param_opcode_def]
QED

Theorem fmp_lower_inst_no_return:
  ~MEM inst.inst_opcode [RET; RETFMP; DRET] /\
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\j. ~MEM j.inst_opcode [RET; RETFMP; DRET]) out
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]
QED

Theorem fmp_lower_inst_no_params:
  ~is_param_opcode inst.inst_opcode /\
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\j. ~is_param_opcode j.inst_opcode) out
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def, is_param_opcode_def]
QED

Theorem fmp_lower_inst_no_halt:
  ~MEM inst.inst_opcode [STOP; RETURN] /\
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\j. ~MEM j.inst_opcode [STOP; RETURN]) out
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]
QED

Theorem split_fmp_entry_from_retpc_operands:
  split_fmp_entry_from k users insts =
    SOME (FmpEntryLayout users' (SOME pc) tail) ==>
  ?w. pc.inst_operands = [Lit w]
Proof
  map_every qid_spec_tac [`k`,`users`,`users'`,`pc`,`tail`] >>
  Induct_on `insts` >> simp[split_fmp_entry_from_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[callLayoutDefsTheory.param_inst_at_def] >> metis_tac[]
QED

Theorem split_fmp_entry_retpc_operands:
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME pc) tail) ==>
  ?w. pc.inst_operands = [Lit w]
Proof
  simp[split_fmp_entry_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[split_fmp_entry_from_retpc_operands]
QED

Theorem split_fmp_entry_retpc_restrictions:
  split_fmp_entry fn = SOME (FmpEntryLayout users pc tail) ==>
  EVERY (\j. j.inst_opcode = RETPC_PARAM /\
    (!l. ~MEM (Label l) j.inst_operands)) (OPTION_TO_LIST pc)
Proof
  Cases_on `pc` >> simp[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  strip_tac >> drule split_fmp_entry_retpc_opcode >> strip_tac >>
  drule split_fmp_entry_retpc_operands >> strip_tac >> simp[]
QED

Theorem fmp_make_root_layout_restrictions:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root pc s') ==>
  EVERY (\j. j.inst_opcode <> INVOKE /\
    (!l. ~MEM (Label l) j.inst_operands) /\
    ~MEM j.inst_opcode [RET; RETFMP; DRET; STOP; RETURN])
    (OPTION_TO_LIST root ++ OPTION_TO_LIST pc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_inst_def, set_param_index_def, callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  drule split_fmp_entry_retpc_restrictions >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem split_fmp_entry_no_params_retpc:
  entry_fn_no_params fn /\
  split_fmp_entry fn = SOME (FmpEntryLayout users pc tail) ==> pc = NONE
Proof
  Cases_on `pc` >> simp[] >> strip_tac >>
  drule split_fmp_entry_retpc_opcode >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  gvs[entry_fn_no_params_def, fn_insts_def, fn_insts_blocks_def,
      EVERY_APPEND, is_param_opcode_def]
QED

Theorem fmp_make_root_layout_entry_no_params:
  fn_is_context_entry ctx fn /\ entry_fn_no_params fn /\
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root pc s') ==>
  EVERY (\j. ~is_param_opcode j.inst_opcode)
    (OPTION_TO_LIST root ++ OPTION_TO_LIST pc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_inst_def, callLayoutDefsTheory.OPTION_TO_LIST_def, is_param_opcode_def] >>
  drule_all split_fmp_entry_no_params_retpc >> strip_tac >>
  gvs[mk_inst_def, callLayoutDefsTheory.OPTION_TO_LIST_def, is_param_opcode_def]
QED
