Theory concretizePtrTaggedCallOrigins
Ancestors concretizePtrTaggedOrigins concretizePtrSourceOwnership
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrChronologicalHistory concretizePtrCallAncestry arithmetic
  ptrDiscipline venomExecSemantics venomInst list rich_list finite_map

Theorem ptr_source_tagged_call_edges:
  !vs C h a tokens registry births PT TG saved.
  ptr_source_ownership vs C h a tokens registry births PT TG saved ==>
  !n site. n < LENGTH a.po_stack /\
    MEM (SOME site) (if n = 0 then PT else FST (EL (n-1) saved)) ==>
    ?u. MEM (Var u) (EL n a.po_stack).cf_inst.inst_operands /\
      FLOOKUP (SND (EL n saved)) u = SOME site
Proof
  ho_match_mp_tac ptr_source_ownership_ind >> conj_tac
  >- simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_tagged_chrono_step_cases] >> strip_tac >>
  gvs[ptr_observe_def]
  >- (gen_tac >> Cases_on `n` >> simp[]
      >- metis_tac[ptr_invoke_imported_provenance] >>
      Cases_on `n'` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC n` mp_tac) >>
  Cases_on `n` >> gvs[] >> metis_tac[]
QED

Theorem ptr_source_tagged_call_traverse[local]:
  !n vs C h a tokens registry births PT TG saved owner aid v.
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH a.po_stack /\ FLOOKUP TG v = SOME (owner,aid) /\
  owner <> HD tokens /\ (!k. k < n ==> owner <> EL (SUC k) tokens) ==>
  ?u. MEM (Var u) (EL n a.po_stack).cf_inst.inst_operands /\
    FLOOKUP (SND (EL n saved)) u = SOME (owner,aid)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (drule_all ptr_source_tag_roots_current_foreign_param >> strip_tac >>
      drule ptr_source_tagged_call_edges >>
      disch_then (qspec_then `0` mp_tac) >> simp[] >>
      disch_then irule >> simp[] >>
      metis_tac[MEM_EL]) >>
  `?u. MEM (Var u) (EL n a.po_stack).cf_inst.inst_operands /\
    FLOOKUP (SND (EL n saved)) u = SOME (owner,aid)` by
    (first_x_assum irule >> conj_tac >- decide_tac >>
     goal_assum (drule_at (Pat `ptr_source_ownership _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `owner <> EL (SUC n) tokens` by
    (qpat_x_assum `!k. _` (qspec_then `n` mp_tac) >> simp[]) >>
  `n < LENGTH a.po_stack` by decide_tac >>
  drule_all ptr_source_tag_roots_saved_foreign_param >> strip_tac >>
  drule ptr_source_tagged_call_edges >>
  disch_then (qspec_then `SUC n` mp_tac) >> simp[] >>
  disch_then irule >> simp[] >> metis_tac[MEM_EL]
QED

Theorem ptr_source_tagged_owner_call_operand:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH a.po_stack /\ EL (SUC n) tokens = owner /\
  FLOOKUP TG v = SOME (owner,aid) /\ fn_inst_wf (EL n a.po_stack).cf_fn ==>
  ?u. MEM (Var u) (EL n a.po_stack).cf_inst.inst_operands /\
      FLOOKUP (SND (EL n saved)) u = SOME (owner,aid) /\
      u IN pointer_derived_vars (EL n a.po_stack).cf_fn
        (ptr_bp_alloc_roots (EL n a.po_stack).cf_fn aid)
Proof
  strip_tac >>
  `ptr_ledger_source_activations vs C h a tokens registry` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations] >>
  `ALL_DISTINCT tokens` by metis_tac[ptr_source_activations_distinct] >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by
    metis_tac[ptr_source_activations_length] >>
  `SUC n < LENGTH tokens` by decide_tac >>
  `!k. k < SUC n ==> owner <> EL k tokens` by
    (rpt strip_tac >> `k < LENGTH tokens` by decide_tac >>
     spose_not_then assume_tac >>
     `SUC n = k` by metis_tac[ALL_DISTINCT_EL_IMP] >> decide_tac) >>
  `owner <> HD tokens` by
    (qpat_x_assum `!k. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `!k. k < n ==> owner <> EL (SUC k) tokens` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!k. _` (qspec_then `SUC k` mp_tac) >> simp[]) >>
  drule_all ptr_source_tagged_call_traverse >> strip_tac >>
  qexists `u` >> simp[] >>
  irule (INST_TYPE [alpha |-> ``:num``] ptr_tag_roots_local_wf) >>
  `n < LENGTH saved` by metis_tac[ptr_source_ownership_stack_length] >>
  `!idx. idx < LENGTH (FST (EL n saved)) ==>
      EL idx (FST (EL n saved)) <> SOME (owner,aid)` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `MEM (SOME (owner,aid)) (FST (EL n saved))` by metis_tac[MEM_EL] >>
     `owner < EL (SUC n) tokens` by metis_tac[ptr_source_params_fresh_saved] >>
     gvs[]) >>
  conj_tac >- simp[] >>
  qexistsl [`FST (EL n saved)`, `SND (EL n saved)`, `owner`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  metis_tac[ptr_source_tag_roots_saved]
QED
