Theory o1LabelFlowSimplifyChain
Ancestors
  o1LabelFlowLateSimplify simplifyCfgRetpc simplifyCfgWfssa
  simplifyCfgBypassShape venomWf venomInst cfgTransform codegenSymRel
  simplifyCfgDefs simplifyCfgStruct simplifyCfgChainDataflow list unitShapeDefs

Theorem chain_nonphi_output_member:
  wf_function f /\ fn_inst_wf f /\ MEM a f.fn_blocks /\
  MEM b f.fn_blocks /\ can_merge_blocks f a b /\
  i.inst_opcode <> PHI /\ MEM x i.inst_outputs ==>
  (MEM i (fn_insts (f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b)))) <=>
   MEM i (fn_insts f))
Proof
  strip_tac >>
  `lookup_block a.bb_label f.fn_blocks = SOME a /\
   lookup_block b.bb_label f.fn_blocks = SOME b` by
    (fs[wf_function_def, fn_labels_def] >> metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  mp_tac (Q.INST [`P` |-> `\j. j = i`] retpc_chain_exists) >>
  simp[] >> disch_then irule >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> eq_tac >> strip_tac >> gvs[subst_label_inst_def] >>
      metis_tac[]) >>
  metis_tac[MEM]
QED

Theorem chain_code_end_forward:
  !f x. code_end_var f x ==> !a b.
  wf_function f /\ fn_inst_wf f /\ MEM a f.fn_blocks /\
  MEM b f.fn_blocks /\ can_merge_blocks f a b ==>
  code_end_var (f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b))) x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all chain_nonphi_output_member >> strip_tac >>
  metis_tac[code_end_var_rules]
QED

Theorem chain_code_end_backward:
  !g x. code_end_var g x ==> !f a b.
  wf_function f /\ fn_inst_wf f /\ MEM a f.fn_blocks /\
  MEM b f.fn_blocks /\ can_merge_blocks f a b /\
  g = (f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b))) ==>
  code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >> gvs[] >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all chain_nonphi_output_member >> strip_tac >>
  metis_tac[code_end_var_rules]
QED

Theorem chain_nonphi_source:
  wf_function f /\ MEM a f.fn_blocks /\ MEM b f.fn_blocks /\
  can_merge_blocks f a b /\
  MEM i (fn_insts (f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b)))) /\
  i.inst_opcode <> PHI ==> MEM i (fn_insts f)
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> strip_tac >>
  drule_all chain_merge_ordinary_use_source >> strip_tac >>
  metis_tac[]
QED

Theorem chain_phi_var_source:
  wf_function f /\ MEM a f.fn_blocks /\ MEM b f.fn_blocks /\
  can_merge_blocks f a b /\
  MEM i (fn_insts (f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b)))) /\
  i.inst_opcode = PHI /\ MEM (Var x) i.inst_operands ==>
  ?j. MEM j (fn_insts f) /\ j.inst_opcode = PHI /\ MEM (Var x) j.inst_operands
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> strip_tac >>
  drule_all chain_merge_phi_source_exact >> strip_tac >>
  qexists `inst` >> simp[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `i = _` mp_tac >> IF_CASES_TAC >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem simplify_chain_merge_label_flow:
  wf_function f /\ fn_inst_wf f /\
  label_flow_ok (ctx with ctx_functions := [f]) /\
  MEM a f.fn_blocks /\ MEM b f.fn_blocks /\ can_merge_blocks f a b ==>
  label_flow_ok (ctx with ctx_functions :=
    [f with fn_blocks :=
      update_succ_phi_labels b.bb_label a.bb_label
        (replace_block a.bb_label (merge_blocks a b)
          (remove_block b.bb_label f.fn_blocks)) (bb_succs (merge_blocks a b))])
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `label_flow_ok (ctx with ctx_functions := [g])` >>
  `!x. code_end_var g x <=> code_end_var f x` by
    (gen_tac >> eq_tac >> strip_tac
     >- (irule chain_code_end_backward >> metis_tac[]) >>
     simp[Abbr `g`] >> irule chain_code_end_forward >> simp[]) >>
  simp[label_flow_ok_def] >> gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (simp[] >> gen_tac >> spose_not_then strip_assume_tac >>
      `?j. MEM j (fn_insts f) /\ j.inst_opcode = PHI /\
           MEM (Var x) j.inst_operands` by
        (irule chain_phi_var_source >> simp[] >> qexistsl [`a`, `b`, `inst`] >>
         gvs[Abbr `g`]) >>
      fs[label_flow_ok_def] >>
      qpat_x_assum `!inst'. MEM inst' (fn_insts f) ==> _`
        (qspec_then `j` mp_tac) >> simp[] >> metis_tac[]) >>
  `MEM inst (fn_insts f)` by
    (irule chain_nonphi_source >> simp[] >> qexistsl [`a`, `b`] >> gvs[Abbr `g`]) >>
  qpat_x_assum `label_flow_ok _` mp_tac >>
  simp[label_flow_ok_def] >> disch_then (qspec_then `inst` mp_tac) >>
  simp[]
QED
