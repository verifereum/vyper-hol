Theory lowerDloadAllocationOwner
Ancestors
  lowerDloadOrdinaryAllocation lowerDloadOwnerTransport lowerDloadOwnership
  lowerDloadFrameCertificate lowerDloadPairedBoundary lowerDloadLifetime
  venomExecSemantics venomState venomInst finite_map pred_set list
  ptrDiscipline lowerDloadRelocation words

Theorem ld_alloca_preserves_entry:
  i.inst_opcode = ALLOCA /\ step_inst fuel C i s = OK s' /\
  FLOOKUP s.vs_allocas id = SOME p ==>
  FLOOKUP s'.vs_allocas id = SOME p
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[]
QED

Theorem ld_alloca_owner_extension:
  i.inst_opcode = ALLOCA /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_frame_embedding E L H s t /\
  step_inst fuelS CS i s = OK s' /\ step_inst fuelT CT i t = OK t' /\
  FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
  FLOOKUP t'.vs_allocas i.inst_id = SOME (bt,sz) ==>
  let E' = if FLOOKUP L i.inst_id = NONE
           then E |+ ((0,k),(bs,bt,sz)) else E in
  ?k' L' H'.
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    ld_frame_embedding E' L' H' s' t' /\
    (!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
      FLOOKUP E' owner = FLOOKUP E owner)
Proof
  strip_tac >> simp[] >>
  `!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
    FLOOKUP (E |+ ((0,k),(bs,bt,sz))) owner = FLOOKUP E owner` by
    (rpt strip_tac >> drule_all ld_annotated_serial >> simp[] >>
     strip_tac >> `owner <> (0,k)` by (strip_tac >> gvs[]) >>
     simp[FLOOKUP_UPDATE]) >>
  `ld_erase (SND (ld_select_alloca k L i s')) = s'.vs_allocas` by
    (`ld_erase L = s.vs_allocas` by metis_tac[ld_frame_embedding_source] >>
     `i.inst_opcode <> INVOKE` by simp[] >>
     drule_all ld_select_alloca_erase >> simp[]) >>
  Cases_on `FLOOKUP L i.inst_id`
  >- suspend "fresh"
  >> suspend "cached"
QED

Resume ld_alloca_owner_extension[fresh]:
  `FLOOKUP H i.inst_id = NONE` by
    (drule ld_frame_embedding_selection >>
     disch_then (qspec_then `i.inst_id` mp_tac) >>
     simp[ld_owned_selection_def]) >>
  `ld_frame_embedding (E |+ ((0,k),(bs,bt,sz))) L H s t` by
    (irule ld_frame_embedding_support >> qexists `E` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  gvs[ld_select_alloca_def] >>
  conj_tac
  >- (simp[ld_frame_embedding_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (gen_tac >> Cases_on `i.inst_id = id`
          >- simp[ld_owned_selection_def, ld_site_entry_def, FLOOKUP_UPDATE] >>
          simp[] >> metis_tac[ld_frame_embedding_selection]) >>
      rpt gen_tac >> Cases_on `i.inst_id = id` >- (strip_tac >> gvs[]) >>
      simp[] >> strip_tac >>
      `FLOOKUP t.vs_allocas id = SOME (bt',sz')` by
        metis_tac[ld_frame_embedding_target] >>
      drule_all ld_alloca_preserves_entry >> simp[]) >>
  metis_tac[]
QED

Resume ld_alloca_owner_extension[cached]:
  `FLOOKUP H i.inst_id <> NONE` by
    (drule ld_frame_embedding_selection >>
     disch_then (qspec_then `i.inst_id` mp_tac) >>
     simp[ld_owned_selection_def] >> strip_tac >> gvs[]) >>
  gvs[ld_select_alloca_def] >>
  simp[ld_frame_embedding_def] >> conj_tac
  >- metis_tac[ld_frame_embedding_selection] >>
  rpt strip_tac >>
  `FLOOKUP t.vs_allocas id = SOME (bt',sz')` by
    metis_tac[ld_frame_embedding_target] >>
  drule_all ld_alloca_preserves_entry >> simp[]
QED

Finalise ld_alloca_owner_extension

Theorem ld_alloca_other_vars[local]:
  i.inst_opcode = ALLOCA /\ i.inst_outputs = [out] /\
  step_inst fuel C i s = OK s' ==>
  s'.vs_labels = s.vs_labels /\
  (!v. v <> out ==> lookup_var v s' = lookup_var v s)
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, lookup_var_def,
      FLOOKUP_UPDATE] >> strip_tac >> gvs[]
QED

Theorem ld_alloca_owned_vars[local]:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ ld_owned_vars V E AG AH tn un s t /\
  step_inst fuelS CS i s = OK s' /\ step_inst fuelT CT i t = OK t' /\
  ld_frame_embedding E L H s' t' /\
  FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
  lookup_var out s' = SOME (n2w bs) /\
  lookup_var out t' = SOME (n2w bt) /\
  FLOOKUP t'.vs_allocas i.inst_id = SOME (bt,sz) ==>
  ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `s'.vs_labels = s.vs_labels /\
   (!v. v <> out ==> lookup_var v s' = lookup_var v s)` by
    metis_tac[ld_alloca_other_vars] >>
  `t'.vs_labels = t.vs_labels /\
   (!v. v <> out ==> lookup_var v t' = lookup_var v t)` by
    metis_tac[ld_alloca_other_vars] >>
  `ld_owned_selection E (FLOOKUP L i.inst_id) (FLOOKUP H i.inst_id)` by
    metis_tac[ld_frame_embedding_selection] >>
  `OPTION_MAP SND (FLOOKUP L i.inst_id) = SOME (bs,sz)` by
    metis_tac[ld_frame_embedding_source, ld_erase_lookup] >>
  gvs[ld_owned_selection_def] >>
  `FLOOKUP t'.vs_allocas i.inst_id = SOME (bt',sz)` by
    metis_tac[ld_frame_embedding_target] >>
  gvs[] >>
  simp[ld_owned_vars_def] >> conj_tac
  >- gvs[ld_owned_vars_def] >>
  gen_tac >> strip_tac >> Cases_on `v = out`
  >- (`ld_ptr_rel bs bt (n2w bs) (n2w bt)` by
        (pure_rewrite_tac[ld_ptr_rel_def] >>
         qabbrev_tac `sw = (n2w bs:bytes32)` >>
         qabbrev_tac `tw = (n2w bt:bytes32)` >>
         CONV_TAC wordsLib.WORD_ARITH_CONV) >>
      gvs[ld_step_prov_def, ld_set_prov_def, ld_out_prov_def,
          FLOOKUP_UPDATE, step_taint_def, set_var_taint_def, op_taint_def,
          out_taint_def, ld_owned_value_def] >>
      Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >> simp[]) >>
  gvs[ld_step_prov_def, ld_set_prov_def, ld_out_prov_def,
      FLOOKUP_UPDATE, step_taint_def, set_var_taint_def, op_taint_def] >>
  gvs[ld_owned_vars_def, op_taint_def] >> metis_tac[]
QED

Theorem ld_owned_alloca_transition_backward:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  ld_alloc_account keys d0 A s t /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. op = Var v ==> v IN V) /\ ld_op_prov AG op = NONE /\
  op_taint tn op = {} /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_frame_embedding E L H s t /\ step_inst fuelT CT i t = OK t' ==>
  ?s' n bs bt sz E' k' L' H'.
    step_inst fuelS CS i s = OK s' /\ ld_alloc_account keys d0 A s' t' /\
    eval_operand op s = SOME n /\ eval_operand op t = SOME n /\
    FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
    FLOOKUP t'.vs_allocas i.inst_id = SOME (bt,sz) /\
    lookup_var out s' = SOME (n2w bs) /\
    lookup_var out t' = SOME (n2w bt) /\
    bs <= bt /\ bt <= bs + d0 + 32 * CARD A /\
    E' = (if FLOOKUP L i.inst_id = NONE
          then E |+ ((0,k),(bs,bt,sz)) else E) /\
    ld_select_alloca k L i s' = (k',L') /\
    ld_select_alloca k H i t' = (k',H') /\
    ld_frame_embedding E' L' H' s' t' /\
    (!owner b n. ld_live astk L AP AG (owner,(b,n)) ==>
      FLOOKUP E' owner = FLOOKUP E owner) /\
    ld_owned_vars V E' (ld_step_prov AP AG L' i) (ld_step_prov AQ AH H' i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >> drule_all ld_owned_alloca_witness_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`] strip_assume_tac) >>
  drule_all ld_alloca_owner_extension >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ld_frame_embedding E' L' H' s' t'` >>
  `ld_owned_vars V E' AG AH tn un s t` by
    (irule ld_owned_vars_support >> qexists `E` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  `ld_owned_vars V E' (ld_step_prov AP AG L' i) (ld_step_prov AQ AH H' i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (drule_all ld_alloca_owned_vars >> simp[]) >>
  qexistsl [`k'`, `L'`, `H'`] >>
  simp[Abbr `E'`] >> metis_tac[]
QED
