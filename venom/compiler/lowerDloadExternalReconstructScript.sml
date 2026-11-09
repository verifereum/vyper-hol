Theory lowerDloadExternalReconstruct
Ancestors
  lowerDloadExternalEffects lowerDloadNormalData lowerDloadOpaqueExecution
  lowerDloadCoverageInvariant lowerDloadFrameCertificate lowerDloadOwnership
  lowerDloadPairedBoundary lowerDloadAllocation lowerDloadMaskBounds lowerDloadOperand
  ptrDiscipline venomState venomExecSemantics finite_map pred_set list words

Theorem ld_external_normal_reconstruct:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  i.inst_outputs = [out] /\
  rS.vs_vars = s.vs_vars /\ rT.vs_vars = t.vs_vars /\
  rS.vs_labels = s.vs_labels /\ rT.vs_labels = t.vs_labels /\
  rS.vs_params = s.vs_params /\ rT.vs_params = t.vs_params /\
  rS.vs_allocas = s.vs_allocas /\ rT.vs_allocas = t.vs_allocas /\
  rS.vs_alloca_next = s.vs_alloca_next /\ rT.vs_alloca_next = t.vs_alloca_next /\
  rS.vs_fmp = s.vs_fmp /\ rT.vs_fmp = t.vs_fmp /\
  rS.vs_call_entry_fmp = s.vs_call_entry_fmp /\
  rT.vs_call_entry_fmp = t.vs_call_entry_fmp /\
  rS.vs_initial_fmp = s.vs_initial_fmp /\
  rT.vs_initial_fmp = t.vs_initial_fmp /\
  rS.vs_call_ctx = s.vs_call_ctx /\ rT.vs_call_ctx = t.vs_call_ctx /\
  rS.vs_gas_readings = s.vs_gas_readings /\
  rT.vs_gas_readings = t.vs_gas_readings /\
  s' = update_var out w rS /\ t' = update_var out w rT /\
  tn' = step_taint i s s' tn /\ un' = step_taint i t t' un /\
  ld_shared_state tn' un' s' t' /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn'.t_mem un'.t_mem (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
  un'.t_stor SUBSET tn'.t_stor /\ un'.t_trans SUBSET tn'.t_trans /\
  un'.t_imm SUBSET tn'.t_imm /\
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    (s'.vs_accounts a).storage = (t'.vs_accounts a).storage) /\
  (!a. a <> s'.vs_call_ctx.cc_address ==> s'.vs_transient a = t'.vs_transient a) ==>
  ld_normal_data CS fn V U lo E L H AP BP
    (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    tn' un' s' t' astk live keys d A suspended gstk f
Proof
  strip_tac >>
  drule_all ld_external_clean_output >> strip_tac >>
  `ld_frame_data V U E L H AP BP AG BH tn un s t` by
    (drule ld_normal_data_frame >> simp[]) >>
  `ld_owned_vars U E AG BH tn un rS rT` by
    (drule ld_frame_data_vars >>
     simp[ld_owned_vars_def, lookup_var_def]) >>
  `ld_owned_vars U E (ld_set_prov AG [out] NONE) (ld_set_prov BH [out] NONE)
     tn' un' s' t'` by
    (asm_rewrite_tac[] >> irule ld_owned_vars_update_supported >>
     qexistsl_tac [`{}`,`{}`,`tn`,`un`] >>
     simp[ld_owned_value_def, ld_mask_word_identity] >> metis_tac[]) >>
  `ld_frame_data V U E L H AP BP (ld_step_prov AP AG L i)
     (ld_step_prov BP BH H i) tn' un' s' t'` by
    (qpat_x_assum `ld_frame_data _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ld_frame_data_def, ld_frame_embedding_def, update_var_def,
          ld_set_prov_def] >> strip_tac >>
     conj_tac
     >- (gen_tac >> Cases_on `v = out` >>
         simp[FLOOKUP_DRESTRICT, ld_owned_selection_def] >>
         qpat_x_assum `!v. ld_owned_selection E (FLOOKUP AG v) _`
           (qspec_then `v` mp_tac) >> simp[ld_owned_selection_def]) >>
     conj_tac
     >- (qpat_x_assum `ld_owned_vars _ _ (ld_set_prov _ _ _) _ _ _ _ _` mp_tac >>
         simp[ld_set_prov_def, update_var_def]) >>
     simp[lookup_var_def, FLOOKUP_UPDATE] >>
     qpat_x_assum `!v. v IN V ==> _` mp_tac >>
     simp[lookup_var_def] >> metis_tac[]) >>
  drule ld_normal_data_geometry >> strip_tac >>
  drule ld_normal_data_masks >> strip_tac >>
  drule ld_normal_data_envelope >> disch_tac >>
  drule ld_normal_data_companions >> strip_tac >>
  simp[ld_normal_data_def] >>
  conj_tac
  >- (simp[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `ld_alloc_account _ _ _ _ _` mp_tac >>
      simp[ld_alloc_account_def, update_var_def]) >>
  conj_tac >- (irule ld_frame_bound_restrict >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `allocas_from f t` mp_tac >>
      simp[allocas_from_def, update_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `ld_live astk L AP AG (owner,bs,sz)` by
        (qpat_x_assum `ld_live _ _ _ (DRESTRICT _ _) _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[ld_live_def] >> metis_tac[ld_restrict_selected]) >>
      metis_tac[]) >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >> irule ld_step_taint_bound >> simp[]
QED
