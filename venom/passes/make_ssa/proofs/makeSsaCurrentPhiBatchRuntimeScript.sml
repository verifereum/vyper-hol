Theory makeSsaCurrentPhiBatchRuntime
Ancestors
  o1FrameLockstep venomExecSemantics venomExecProps venomExecProofs
  venomInst venomState stateFrame list finite_map

Theorem current_phi_batch_success:
  !insts. (!inst. MEM inst (TAKE (phi_prefix_length insts) insts) ==>
    IS_SOME (eval_one_phi s inst)) ==>
  ?post. eval_phis s insts = OK post
Proof
  Induct >> simp[eval_phis_def, phi_prefix_length_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >>
  `IS_SOME (eval_one_phi s h)` by simp[] >>
  Cases_on `eval_one_phi s h` >> gvs[] >> PairCases_on `x` >>
  simp[]
QED

Theorem current_phi_batch_lookup:
  !insts post. eval_phis s insts = OK post ==>
  lookup_var x post =
    case phi_eff s.vs_prev_bb x insts of
      NONE => NONE
    | SOME op => eval_operand op s
Proof
  Induct
  >- (simp[eval_phis_def, phi_eff_def, phi_read_def, eval_operand_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (Cases_on `eval_one_phi s h`
      >- simp[eval_phis_def] >>
      rename1 `eval_one_phi s h = SOME pair` >> PairCases_on `pair` >>
      Cases_on `eval_phis s insts` >> simp[eval_phis_def] >>
      strip_tac >> gvs[] >>
      `h.inst_outputs = [pair0] /\
       ?prev op. s.vs_prev_bb = SOME prev /\
         resolve_phi prev h.inst_operands = SOME op /\
         eval_operand op s = SOME pair1` by
        (qpat_x_assum `eval_one_phi s h = _` mp_tac >>
         simp[eval_one_phi_def, AllCaseEqs()] >> metis_tac[]) >>
      Cases_on `x = pair0` >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          phi_eff_def, phi_read_def]) >>
  simp[eval_phis_def, phi_eff_def, phi_read_def, eval_operand_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem current_phi_batch_frame:
  eval_phis s insts = OK post ==>
  execution_frame post = execution_frame s
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem current_phi_batch_vars_rel:
  vars_rel sg s s' /\ s'.vs_labels = s.vs_labels /\
  phis_rename_ok prev sg insts insts' sg' /\
  s.vs_prev_bb = prev /\ s'.vs_prev_bb = prev /\
  eval_phis s insts = OK post /\ eval_phis s' insts' = OK post' ==>
  vars_rel sg' post post'
Proof
  rpt strip_tac >> simp[vars_rel_def] >> rpt strip_tac >>
  `OPTREL (op_rename sg) (phi_eff prev x insts) (phi_eff prev x' insts')` by
    metis_tac[phis_rename_ok_def] >>
  dxrule current_phi_batch_lookup >> strip_tac >>
  dxrule current_phi_batch_lookup >> strip_tac >>
  simp[] >>
  Cases_on `phi_eff prev x insts` >>
  Cases_on `phi_eff prev x' insts'` >> gvs[] >>
  irule op_rename_eval >> simp[] >> qexists_tac `sg` >> simp[]
QED

Theorem current_phi_batch_state_rel:
  state_rel sg s s' /\
  phis_rename_ok sg_prev sg insts insts' sg' /\
  s.vs_prev_bb = sg_prev /\
  eval_phis s insts = OK post /\ eval_phis s' insts' = OK post' ==>
  state_rel sg' post post'
Proof
  strip_tac >>
  `post = s with vs_vars := post.vs_vars /\
   post' = s' with vs_vars := post'.vs_vars` by
    metis_tac[eval_phis_only_updates_vs_vars] >>
  `vars_rel sg' post post'` by
    (irule current_phi_batch_vars_rel >> fs[state_rel_def] >>
     `s'.vs_labels = s.vs_labels` by
       metis_tac[execution_frame_def, venom_state_component_equality] >>
     metis_tac[]) >>
  qpat_x_assum `post = _` SUBST_ALL_TAC >>
  qpat_x_assum `post' = _` SUBST_ALL_TAC >> fs[state_rel_def]
QED

Theorem current_phi_batch_success_all:
  !insts. (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
    IS_SOME (eval_one_phi s inst)) ==>
  ?post. eval_phis s insts = OK post
Proof
  Induct >> simp[eval_phis_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >>
  `IS_SOME (eval_one_phi s h)` by simp[] >>
  Cases_on `eval_one_phi s h` >> gvs[] >> PairCases_on `x` >> simp[]
QED
