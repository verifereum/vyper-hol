Theory concretizePtrTaggedOrigins
Ancestors concretizePtrSourceOwnership concretizePtrRuntimeOrigins
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrChronologicalHistory
  concretizePtrActivationSupport pointerClosure pointerConfinedDefs
  ptrDiscipline venomInst venomWf concretizePtrBPOrigins While finite_map pred_set list

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
        venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
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

Theorem pointer_derived_vars_empty[simp]:
  pointer_derived_vars fn {} = {}
Proof
  `pointer_use_step fn [] = []` by
    (Cases_on `pointer_use_step fn []` >> simp[] >>
     metis_tac[pointer_use_step_membership, MEM]) >>
  simp[pointer_derived_vars_def, pointer_use_vars_def, SET_TO_LIST_EMPTY,
    pointer_use_step_step_def, Once OWHILE_THM] >>
  simp[Once OWHILE_THM]
QED

Theorem ptr_tag_roots_local:
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
    LENGTH i.inst_outputs = 1) /\
  ~(?i idx v. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
    MEM v i.inst_outputs /\ i.inst_operands = [Lit idx] /\
    w2n idx < LENGTH PT /\ EL (w2n idx) PT = SOME (tok,aid)) ==>
  ptr_tag_roots fn tok PT (tok,aid) = ptr_bp_alloc_roots fn aid
Proof
  strip_tac >> simp[EXTENSION, ptr_tag_roots_def, ptr_bp_alloc_roots_def] >>
  gen_tac >> eq_tac
  >- (strip_tac
      >- (`LENGTH i.inst_outputs = 1` by metis_tac[] >>
          qpat_x_assum `!i. _` kall_tac >>
          qpat_x_assum `~(?i idx v. _)` kall_tac >>
          qexists `i` >> gvs[] >>
          Cases_on `i.inst_outputs` >> gvs[inst_output_def]) >>
      metis_tac[]) >>
  strip_tac >> qexists `inst` >> simp[] >>
  gvs[inst_output_def, AllCaseEqs()] >> simp[]
QED

Theorem ptr_tag_roots_foreign_param:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_tag_roots fn tok PT (owner,aid))) TG (owner,aid) /\
  FLOOKUP TG v = SOME (owner,aid) /\ owner <> tok ==>
  ?i idx out. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
    MEM out i.inst_outputs /\ i.inst_operands = [Lit idx] /\
    w2n idx < LENGTH PT /\ EL (w2n idx) PT = SOME (owner,aid)
Proof
  strip_tac >> spose_not_then assume_tac >>
  `ptr_tag_roots fn tok PT (owner,aid) = {}` by
    (simp[EXTENSION, ptr_tag_roots_def] >> metis_tac[]) >>
  gvs[ptr_site_supported_def]
QED

Theorem ptr_tag_roots_local_supported:
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
    LENGTH i.inst_outputs = 1) /\
  ~(?i idx out. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
    MEM out i.inst_outputs /\ i.inst_operands = [Lit idx] /\
    w2n idx < LENGTH PT /\ EL (w2n idx) PT = SOME (tok,aid)) /\
  ptr_site_supported
    (pointer_derived_vars fn (ptr_tag_roots fn tok PT (tok,aid))) TG (tok,aid) /\
  FLOOKUP TG v = SOME (tok,aid) ==>
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)
Proof
  strip_tac >> drule_all ptr_tag_roots_local >> strip_tac >>
  gvs[ptr_site_supported_def] >> metis_tac[]
QED

Theorem ptr_tag_roots_local_wf:
  fn_inst_wf fn /\
  ~(?i idx out. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
    MEM out i.inst_outputs /\ i.inst_operands = [Lit idx] /\
    w2n idx < LENGTH PT /\ EL (w2n idx) PT = SOME (tok,aid)) /\
  ptr_site_supported
    (pointer_derived_vars fn (ptr_tag_roots fn tok PT (tok,aid))) TG (tok,aid) /\
  FLOOKUP TG v = SOME (tok,aid) ==>
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)
Proof
  strip_tac >> irule ptr_tag_roots_local_supported >>
  conj_tac
  >- (rpt strip_tac >>
      `inst_wf i` by
        (gvs[fn_inst_wf_def, fn_insts_def,
          venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[]) >>
      gvs[inst_wf_def]) >>
  qexistsl [`PT`, `TG`, `tok`] >> simp[] >> metis_tac[]
QED

Theorem ptr_source_tag_roots_current_foreign_param:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  FLOOKUP TG v = SOME (owner,aid) /\ owner <> HD tokens ==>
  ?i idx out. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = PARAM /\
    MEM out i.inst_outputs /\ i.inst_operands = [Lit idx] /\
    w2n idx < LENGTH PT /\ EL (w2n idx) PT = SOME (owner,aid)
Proof
  strip_tac >> irule ptr_tag_roots_foreign_param >>
  qexistsl [`TG`, `HD tokens`, `v`] >> simp[] >>
  metis_tac[ptr_source_tag_roots_current]
QED

Theorem ptr_source_tag_roots_saved_foreign_param:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH a.po_stack /\
  FLOOKUP (SND (EL n saved)) v = SOME (owner,aid) /\
  owner <> EL (SUC n) tokens ==>
  ?i idx out. MEM i (fn_insts (EL n a.po_stack).cf_fn) /\
    i.inst_opcode = PARAM /\ MEM out i.inst_outputs /\
    i.inst_operands = [Lit idx] /\ w2n idx < LENGTH (FST (EL n saved)) /\
    EL (w2n idx) (FST (EL n saved)) = SOME (owner,aid)
Proof
  strip_tac >> irule ptr_tag_roots_foreign_param >>
  qexistsl [`SND (EL n saved)`, `EL (SUC n) tokens`, `v`] >> simp[] >>
  metis_tac[ptr_source_tag_roots_saved]
QED

Theorem ptr_source_tag_history_bound[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  FLOOKUP TG v = SOME (owner,aid) ==> owner < LENGTH h
Proof
  strip_tac >>
  `MEM owner tokens` by metis_tac[ptr_source_ownership_live_prov] >>
  `ptr_ledger_source_activations vs C h a tokens registry` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations] >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by
    metis_tac[ptr_source_activations_length] >>
  gvs[MEM_EL] >>
  `n <= LENGTH a.po_stack` by decide_tac >>
  drule ptr_source_activations_owner_lookup >>
  disch_then (qspec_then `LENGTH a.po_stack - n` mp_tac) >> simp[] >>
  `LENGTH a.po_stack - (LENGTH a.po_stack - n) = n` by decide_tac >>
  simp[] >> strip_tac >> irule ptr_source_activations_registry_bound >>
  goal_assum (drule_at Any) >> gvs[FLOOKUP_DEF, AllCaseEqs()]
QED

Theorem ptr_source_params_fresh_invariant[local]:
  !vs C h a tokens registry births PT TG saved.
  ptr_source_ownership vs C h a tokens registry births PT TG saved ==>
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  (EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
    (!owner aid. MEM (SOME (owner,aid)) PT ==> owner < HD tokens) /\
    (!n owner aid. n < LENGTH saved /\
      MEM (SOME (owner,aid)) (FST (EL n saved)) ==>
      owner < EL (SUC n) tokens))
Proof
  ho_match_mp_tac ptr_source_ownership_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[ptr_source_ownership_rules] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- metis_tac[ptr_source_ownership_rules] >> strip_tac >>
  `!v owner aid. FLOOKUP TG v = SOME (owner,aid) ==> owner < LENGTH h` by
    metis_tac[ptr_source_tag_history_bound] >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations,
      ptr_source_activations_length] >>
  qpat_x_assum `EVERY _ _ ==> _` mp_tac >> simp[] >> strip_tac >>
  rpt (qhdtm_x_assum `ptr_source_ownership` kall_tac) >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_tagged_chrono_step_cases] >> strip_tac >>
  gvs[ptr_observe_def, ptr_activation_tokens_def]
  >- metis_tac[]
  >- metis_tac[]
  >- (conj_tac
      >- (simp[MEM_MAP] >> rpt strip_tac >> Cases_on `y` >> gvs[op_prov_def] >> metis_tac[]) >>
      rpt gen_tac >> Cases_on `n` >> simp[] >> metis_tac[HD]) >>
  Cases_on `tokens` >> gvs[] >> Cases_on `t` >> gvs[] >>
  conj_tac
  >- (qpat_x_assum `!n owner aid. _` (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> qpat_x_assum `!n owner aid. _` (qspec_then `SUC n` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ptr_source_params_fresh_current:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  MEM (SOME (owner,aid)) PT ==> owner < HD tokens
Proof
  metis_tac[ptr_source_params_fresh_invariant]
QED

Theorem ptr_source_params_fresh_saved:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH saved /\ MEM (SOME (owner,aid)) (FST (EL n saved)) ==>
  owner < EL (SUC n) tokens
Proof
  metis_tac[ptr_source_params_fresh_invariant]
QED
