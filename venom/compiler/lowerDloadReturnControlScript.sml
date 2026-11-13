(* Source entry success from the unchanged transformed PHI prefix. *)
Theory lowerDloadReturnControl
Ancestors
  lowerDloadConfiguredOrigins lowerDloadSafetyPhiEffects lowerDloadSafetyRelation
  lowerDloadSafetyAmbient contextCodegenRel lowerDloadDefs venomExecSemantics
  venomInst list

Theorem ld_related_transformed_entry:
  ld_vars P A f /\ s = f.lf_src /\ t = f.lf_tgt /\
  s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb /\
  s.vs_current_bb = t.vs_current_bb /\
  lower_dload_function_supply u f.lf_fn = (fn',v) /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  eval_phis t bb'.bb_instructions = OK tp ==>
  ?bb sp. lookup_block s.vs_current_bb f.lf_fn.fn_blocks = SOME bb /\
    eval_phis t bb.bb_instructions = OK tp /\
    eval_phis s bb.bb_instructions = OK sp /\
    phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
    enters_block f.lf_fn s
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    enters_block fn' t
      (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
Proof
  strip_tac >>
  `enters_block fn' t (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
  drule_all lower_dload_blocks_supply_lookup_origin >> strip_tac >>
  drule lower_dload_insts_supply_eval_phis >>
  disch_then (qspec_then `f.lf_tgt` assume_tac) >>
  drule lower_dload_insts_supply_phi_length >> strip_tac >>
  gvs[] >>
  `EVERY (\i. MEM i (fn_insts f.lf_fn)) b.bb_instructions` by
    (drule venomExecProofsTheory.lookup_block_MEM >>
     simp[EVERY_MEM, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  drule_all ld_phis_source_success >> strip_tac >>
  goal_assum (drule_at Any) >> simp[enters_block_def] >> metis_tac[]
QED

val _ = if null (hyp ld_related_transformed_entry) then ()
  else raise Fail "related entry boundary has hypotheses";
