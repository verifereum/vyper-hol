Theory makeSsaCurrentConditionalReadiness
Ancestors
  makeSsaCurrentDominanceAvailability makeSsaCurrentForwardReadiness
  makeSsaCurrentPrefixCopyOccurrence makeSsaCurrentPrefixPayload
  makeSsaCurrentCopyPrefixRuntime makeSsaCurrentCleanupBoundary
  makeSsaCurrentLockstepShape makeSsaCurrentWfSsa makeSsaCurrentDefs
  venomExecProofs venomExecSemantics venomState list pred_set

Theorem current_copy_prefix_ready_from_sources:
  !xs D. EVERY (\i.
    (i.inst_opcode = NOP /\ i.inst_outputs = [] /\ i.inst_operands = []) \/
    (?dst src. i.inst_opcode = ASSIGN /\ i.inst_outputs = [dst] /\
      i.inst_operands = [Var src] /\ src IN D)) xs ==>
    current_copy_prefix_ready D xs
Proof
  Induct >> simp[current_copy_prefix_ready_def] >> rpt strip_tac
  >- metis_tac[] >>
  disj2_tac >> qexistsl [`dst`, `src`] >> simp[] >>
  first_x_assum irule >>
  gvs[EVERY_MEM] >> metis_tac[IN_INSERT]
QED

Theorem current_retained_cleaned_output_defined:
  simplify_current_phi_prefix_parts new.bb_instructions = (phis,ord) /\
  MEM inst phis /\ MEM src inst.inst_outputs /\
  bb = simplify_current_phi_block new /\
  eval_phis st bb.bb_instructions = OK post ==>
  IS_SOME (lookup_var src post)
Proof
  strip_tac >>
  `?k. k < LENGTH phis /\ EL k phis = inst` by metis_tac[MEM_EL] >>
  `?first rest. new.bb_instructions = first::rest /\ first.inst_opcode = PHI` by
    (Cases_on `new.bb_instructions` >>
     gvs[simplify_current_phi_prefix_parts_def] >>
     Cases_on `h.inst_opcode = PHI` >>
     gvs[simplify_current_phi_prefix_parts_def]) >>
  `bb.bb_instructions = reassign_current_inst_ids
    (MAP instruction_inst_id new.bb_instructions) (phis ++ ord)` by
    simp[simplify_current_phi_block_def, simplify_current_phi_prefix_def, ETA_THM] >>
  `phi_prefix_length bb.bb_instructions = LENGTH phis` by
    metis_tac[reassign_current_inst_ids_phi_prefix, simplify_current_phi_parts_prefix] >>
  `MEM src (EL k bb.bb_instructions).inst_outputs` by
    (mp_tac (Q.SPECL [`MAP instruction_inst_id new.bb_instructions`, `phis ++ ord`, `k`]
      current_reassign_content) >> simp[EL_APPEND_EQN]) >>
  irule current_phi_batch_output_defined >>
  qexistsl [`EL k bb.bb_instructions`, `st`, `bb.bb_instructions`] >>
  simp[MEM_EL] >> qexists `k` >> simp[] >>
  sym_tac >> irule EL_TAKE >> simp[]
QED

Theorem current_cleaned_copy_source_defined:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ bb = simplify_current_phi_block new /\
  final = fn with fn_blocks := simplify_current_phis_if T renamed /\
  eval_phis st bb.bb_instructions = OK post /\ post.vs_current_bb = h /\
  strict_dom_vars_defined final post /\
  phi_prefix_length bb.bb_instructions <= k /\
  k < phi_prefix_length new.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = ASSIGN /\
  (EL k bb.bb_instructions).inst_outputs = [d] /\
  (EL k bb.bb_instructions).inst_operands = [Var src] ==>
  IS_SOME (lookup_var src post)
Proof
  strip_tac >>
  `new.bb_label = h` by metis_tac[lookup_block_label] >>
  drule_all current_prefix_cleaned_copy_source_cases >> strip_tac
  >- (`?v. lookup_var src post = SOME v` by
        (irule current_context_external_producer_lookup >> metis_tac[]) >> simp[]) >>
  `r < LENGTH new.bb_instructions /\
   (EL r new.bb_instructions).inst_opcode = PHI` by
    (gvs[current_wf_original_phi_at_def] >> metis_tac[]) >>
  `!i. i < r ==> (EL i new.bb_instructions).inst_opcode = PHI` by
    (drule current_wf_phi_context_prefix_order >> simp[] >> metis_tac[]) >>
  Cases_on `simplify_current_phi_prefix_parts new.bb_instructions` >>
  `MEM (EL r new.bb_instructions) q'` by
    (irule current_retained_parts_member >> metis_tac[]) >>
  irule current_retained_cleaned_output_defined >> metis_tac[]
QED

Theorem current_cleaned_copy_prefix_ready:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ bb = simplify_current_phi_block new /\
  final = fn with fn_blocks := simplify_current_phis_if T renamed /\
  eval_phis st bb.bb_instructions = OK post /\ post.vs_current_bb = h /\
  strict_dom_vars_defined final post /\
  copies = TAKE (phi_prefix_length new.bb_instructions - phi_prefix_length bb.bb_instructions)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) ==>
  current_copy_prefix_ready {x | IS_SOME (lookup_var x post)} copies
Proof
  strip_tac >> irule current_copy_prefix_ready_from_sources >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `?j. j < LENGTH copies /\ EL j copies = i` by metis_tac[MEM_EL] >>
  `j < phi_prefix_length new.bb_instructions - phi_prefix_length bb.bb_instructions /\
   j < LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions` by
    (gvs[LENGTH_TAKE_EQ, LENGTH_DROP, arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `i = EL (j + phi_prefix_length bb.bb_instructions) bb.bb_instructions` by
    (gvs[] >> simp[EL_TAKE, EL_DROP]) >>
  `current_copy_payload i` by
    (qpat_assum `i = EL _ _` SUBST1_TAC >>
     irule current_prefix_cleaned_payload >> simp[] >> qexists `new` >> gvs[] >> decide_tac) >>
  `phi_prefix_length bb.bb_instructions <= j + phi_prefix_length bb.bb_instructions /\
   j + phi_prefix_length bb.bb_instructions < phi_prefix_length new.bb_instructions` by
    decide_tac >>
  fs[current_copy_payload_def] >>
  `phi_prefix_length bb.bb_instructions <= j + phi_prefix_length bb.bb_instructions` by simp[] >>
  qpat_x_assum `i = EL _ _` SUBST_ALL_TAC >>
  drule_all current_cleaned_copy_source_defined >> simp[]
QED

Theorem current_cleaned_copy_prefix_total:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ bb = simplify_current_phi_block new /\
  final = fn with fn_blocks := simplify_current_phis_if T renamed /\
  eval_phis st bb.bb_instructions = OK post /\ post.vs_current_bb = h /\
  strict_dom_vars_defined final post /\
  copies = TAKE (phi_prefix_length new.bb_instructions - phi_prefix_length bb.bb_instructions)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) ==>
  ?done. current_prefix_steps fuel C copies post done /\
    execution_frame done = execution_frame post /\
    done.vs_current_bb = post.vs_current_bb /\
    done.vs_prev_bb = post.vs_prev_bb /\
    (!x. x IN {x | IS_SOME (lookup_var x post)} UNION
      set (FLAT (MAP (\inst. inst.inst_outputs) copies)) ==>
      IS_SOME (lookup_var x done))
Proof
  strip_tac >> drule_all current_cleaned_copy_prefix_ready >> strip_tac >>
  irule current_copy_prefix_total >> simp[] >>
  qexists `{x | IS_SOME (lookup_var x post)}` >> simp[]
QED
