Theory concretizePtrTaggedOrigins
Ancestors concretizePtrSourceOwnership concretizePtrRuntimeOrigins
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrChronologicalHistory
  concretizePtrActivationSupport pointerClosure pointerConfinedDefs
  ptrDiscipline venomInst finite_map pred_set list

Definition ptr_tag_roots_def:
  ptr_tag_roots fn tok PT tag =
    {v | ?i. MEM i (fn_insts fn) /\ MEM v i.inst_outputs /\
      ((i.inst_opcode = ALLOCA /\ tag = (tok,i.inst_id)) \/
       (i.inst_opcode = PARAM /\ ?idx. i.inst_operands = [Lit idx] /\
         w2n idx < LENGTH PT /\ EL (w2n idx) PT = SOME tag))}
End

Theorem ptr_tag_roots_finite:
  FINITE (ptr_tag_roots fn tok PT tag)
Proof
  irule SUBSET_FINITE_I >>
  qexists `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  simp[SUBSET_DEF, ptr_tag_roots_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem ptr_tag_roots_step:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_tag_roots fn tok PT tag)) TG tag /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> DALLOCA ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_tag_roots fn tok PT tag))
    (ptr_tagged_step tok PT TG inst s') tag
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (simp[ptr_tagged_step_def] >>
      Cases_on `FLOOKUP s'.vs_allocas inst.inst_id` >>
      Cases_on `inst.inst_outputs` >> simp[set_prov_def, ptr_site_supported_def,
        FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> rpt strip_tac >>
      gvs[ptr_site_supported_def] >>
      Cases_on `t` >> gvs[set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      gvs[AllCaseEqs()] >>
      irule (pointer_derived_vars_roots |> REWRITE_RULE [SUBSET_DEF]) >>
      simp[ptr_tag_roots_finite, ptr_tag_roots_def] >>
      qexists `inst` >> simp[]) >>
  simp[ptr_tagged_step_def] >> irule ptr_site_step >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      irule (pointer_derived_vars_roots |> REWRITE_RULE [SUBSET_DEF]) >>
      simp[ptr_tag_roots_finite, ptr_tag_roots_def] >>
      gvs[out_prov_def, AllCaseEqs()] >> metis_tac[]) >>
  qexists `fn` >> simp[] >>
  rpt strip_tac >> irule pointer_derived_vars_closed >>
  simp[ptr_tag_roots_finite] >> metis_tac[]
QED

Theorem ptr_tag_roots_entry:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_tag_roots fn tok PT tag)) TG tag ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_tag_roots fn tok PT tag))
    (entry_prov fn s TG) tag
Proof
  strip_tac >> irule ptr_site_entry >> simp[] >>
  rpt strip_tac >> irule pointer_derived_vars_closed >>
  simp[ptr_tag_roots_finite] >> metis_tac[]
QED

Theorem ptr_source_tag_roots_support[local]:
  !vs C h a tokens registry births PT TG saved.
  ptr_source_ownership vs C h a tokens registry births PT TG saved ==>
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  (EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  (!tag. ptr_site_supported
    (pointer_derived_vars a.po_fn (ptr_tag_roots a.po_fn (HD tokens) PT tag)) TG tag) /\
  (!n tag. n < LENGTH a.po_stack ==>
    ptr_site_supported
      (pointer_derived_vars (EL n a.po_stack).cf_fn
        (ptr_tag_roots (EL n a.po_stack).cf_fn (EL (SUC n) tokens)
          (FST (EL n saved)) tag)) (SND (EL n saved)) tag))
Proof
  ho_match_mp_tac ptr_source_ownership_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[ptr_source_ownership_rules] >>
      simp[ptr_site_supported_def]) >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- metis_tac[ptr_source_ownership_rules] >> strip_tac >>
  `ptr_source_birth_caches vs C h a tokens registry births` by
    metis_tac[ptr_source_ownership_caches] >>
  `ptr_ledger_source_activations vs C h a tokens registry` by
    metis_tac[ptr_source_birth_caches_activations] >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by
    metis_tac[ptr_source_activations_length] >>
  `LENGTH saved = LENGTH a.po_stack` by
    metis_tac[ptr_source_ownership_stack_length] >>
  `a.po_inst.inst_opcode <> DALLOCA` by
    metis_tac[ptr_source_activations_sound, ptr_birth_reachable_no_dalloca] >>
  qpat_x_assum `EVERY _ _ ==> _` (fn th => mp_tac th) >> simp[] >> strip_tac >>
  rpt (qhdtm_x_assum `ptr_source_ownership` kall_tac) >>
  qhdtm_x_assum `ptr_source_birth_caches` kall_tac >>
  qhdtm_x_assum `ptr_ledger_source_activations` kall_tac >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_tagged_chrono_step_cases] >> strip_tac >>
  gvs[ptr_observe_def, ptr_activation_tokens_def]
  >- (gen_tac >> irule ptr_tag_roots_step >> simp[] >>
      gvs[contextCodegenRelTheory.active_inst_def, fn_insts_def,
        removeUnusedSsaProofsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
      metis_tac[MEM_EL])
  >- metis_tac[ptr_tag_roots_entry]
  >- (conj_tac >- simp[ptr_site_supported_def] >>
      rpt gen_tac >> Cases_on `n` >> simp[] >> metis_tac[HD])
  >> Cases_on `tokens` >> gvs[] >> Cases_on `t` >> gvs[] >>
  conj_tac
  >- (gen_tac >> irule ptr_site_support_restrict >>
      qpat_x_assum `!n tag. _` (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> qpat_x_assum `!n tag. _` (qspec_then `SUC n` mp_tac) >> simp[]
QED

Theorem ptr_source_tag_roots_current:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  ptr_site_supported
    (pointer_derived_vars a.po_fn
      (ptr_tag_roots a.po_fn (HD tokens) PT tag)) TG tag
Proof
  metis_tac[ptr_source_tag_roots_support]
QED

Theorem ptr_source_tag_roots_saved:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH a.po_stack ==>
  ptr_site_supported
    (pointer_derived_vars (EL n a.po_stack).cf_fn
      (ptr_tag_roots (EL n a.po_stack).cf_fn (EL (SUC n) tokens)
        (FST (EL n saved)) tag)) (SND (EL n saved)) tag
Proof
  metis_tac[ptr_source_tag_roots_support]
QED
