Theory makeSsaCurrentForwardReadiness
Ancestors
  makeSsaCurrentWfSsa makeSsaCurrentLockstepShape
  makeSsaCurrentPhiBatchRuntime makeSsaCurrentDefs
  venomExecProofs venomExecSemantics venomState venomInst list finite_map

Theorem current_phi_batch_output_defined:
  eval_phis st xs = OK post /\
  MEM inst (TAKE (phi_prefix_length xs) xs) /\
  MEM out inst.inst_outputs ==>
  IS_SOME (lookup_var out post)
Proof
  strip_tac >> drule_all eval_phis_outputs_in_fdom_mem >>
  simp[lookup_var_def, FLOOKUP_DEF]
QED

Theorem current_retained_parts_member:
  !xs phis ord r.
  simplify_current_phi_prefix_parts xs = (phis,ord) /\
  r < LENGTH xs /\ (EL r xs).inst_opcode = PHI /\
  (!i. i < r ==> (EL i xs).inst_opcode = PHI) /\
  simplify_current_phi (EL r xs) = EL r xs ==>
  MEM (EL r xs) phis
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `r`
  >- (gvs[simplify_current_phi_prefix_parts_def] >>
      Cases_on `simplify_current_phi_prefix_parts xs` >> gvs[]) >>
  `h.inst_opcode = PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  Cases_on `simplify_current_phi_prefix_parts xs` >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
  gvs[simplify_current_phi_prefix_parts_def] >>
  `!i. i < n ==> (EL i xs).inst_opcode = PHI` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem current_exceptional_copy_source_defined:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  k < LENGTH old.bb_instructions /\ (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [v] /\
  simplify_current_phi_prefix_parts new.bb_instructions = (phis,ord) /\
  eval_phis st phis = OK post ==>
  ?src. simplify_current_phi (EL q new.bb_instructions) =
    (EL q new.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
    IS_SOME (lookup_var src post)
Proof
  strip_tac >> drule_all current_wf_exceptional_inserted_copy >> strip_tac >>
  `r < LENGTH new.bb_instructions /\
   (EL r new.bb_instructions).inst_opcode = PHI` by
    (gvs[current_wf_original_phi_at_def] >> metis_tac[]) >>
  `!i. i < r ==> (EL i new.bb_instructions).inst_opcode = PHI` by
    (drule current_wf_phi_context_prefix_order >> simp[] >> metis_tac[]) >>
  `MEM (EL r new.bb_instructions) phis` by
    (irule current_retained_parts_member >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode = PHI) phis` by
    metis_tac[simplify_current_phi_prefix_partition] >>
  qexists_tac `n` >> simp[] >>
  irule current_phi_batch_output_defined >>
  qexistsl_tac [`EL r new.bb_instructions`, `st`, `phis`] >>
  `phi_prefix_length (phis ++ []) = LENGTH phis + phi_prefix_length []` by
    (irule phi_prefix_length_prepend >> simp[]) >>
  gvs[phi_prefix_length_def]
QED
