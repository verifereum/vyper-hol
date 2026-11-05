Theory concretizePtrOwnedAllocationPrefix
Ancestors concretizePtrAllocationTransport concretizePtrOwnedAffinePrefix
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrLedgerProbe concretizePtrChronologicalHistory
  concretizePtrValueTransport concretizeMemLocDefs ptrDiscipline
  contextCodegenRel venomExecSemantics venomState venomInst finite_map words list pred_set arithmetic

Theorem ptr_owned_alloca_prefix_back_next:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
  a.po_inst.inst_opcode = ALLOCA /\ a.po_inst.inst_operands = [Lit sz] /\
  a.po_inst.inst_outputs = [out] /\
  FLOOKUP layout (Allocation a.po_inst.inst_id) = SOME pos /\
  FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (pos,w2n sz) /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  (!base size. FLOOKUP a.po_state.vs_allocas a.po_inst.inst_id = SOME (base,size) ==>
    size = w2n sz) /\
  step_inst 0 C' (concretize_inst_with_positions layout a.po_inst) t = OK post ==>
  ?b births' TG'.
    ptr_source_ownership vs0 C (h ++ [b]) b tokens registry births' PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL b.po_state.vs_inst_idx bb.bb_instructions /\
    b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    births' = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) /\
    ptr_vars_transport births' positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[] >> decide_tac) >>
  drule_all ptr_alloca_transport >>
  disch_then (qspecl_then [`HD tokens`,`0`,`PT`] mp_tac) >>
  disch_then (qspecl_then [`C'`,`C`] strip_assume_tac) >>
  qpat_x_assum `!base size. FLOOKUP a.po_state.vs_allocas _ = _ ==> _` kall_tac >>
  `active_inst a.po_fn (EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions)
     (s' with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[]) >>
  qabbrev_tac `b = ptr_ledger_next a
    (EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions) s'` >>
  `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT
      (ptr_tagged_step (HD tokens) PT TG a.po_inst s') saved` by
    (simp[Abbr `b`, ptr_ledger_next_def] >>
     `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
        a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     drule_all (cj 1 ptr_tagged_chrono_step_rules) >> simp[] >> metis_tac[]) >>
  `ptr_activation_tokens h a b tokens = tokens /\
   ptr_activation_registry h a b registry = registry` by
    simp[Abbr `b`, ptr_ledger_next_def, ptr_observe_def,
      ptr_activation_tokens_def, ptr_activation_registry_def] >>
  drule_all (cj 2 ptr_source_ownership_rules) >> simp[] >> strip_tac >>
  `ptr_source_birth_caches vs0 C h a tokens registry births` by
    metis_tac[ptr_source_ownership_caches] >>
  `ptr_chrono_step C a b` by metis_tac[ptr_tagged_chrono_step_projection] >>
  drule ptr_source_birth_caches_snoc_retained >>
  simp[] >> disch_then (drule_at Any) >> strip_tac >>
  qpat_x_assum `!key site. _` (assume_tac o SRULE []) >>
  `ptr_source_birth_caches vs0 C (h ++ [b]) b tokens registry
    (ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births)` by
    metis_tac[ptr_source_ownership_caches] >>
  drule_all ptr_source_birth_caches_active_lookup >>
  disch_then (qspec_then `a.po_inst.inst_id` assume_tac) >>
  `!base size. FLOOKUP s'.vs_allocas a.po_inst.inst_id = SOME (base,size) ==>
    FLOOKUP (ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births)
      (HD tokens,a.po_inst.inst_id) = SOME (base,size)` by
    (`b.po_state.vs_allocas = s'.vs_allocas` by
       simp[NoAsms, Abbr `b`, ptr_ledger_next_def, ptr_observe_def] >>
     metis_tac[]) >>
  qpat_x_assum `!births' t'. _`
    (qspecl_then [`ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births`,`post`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  qexistsl_tac [`b`,`ptr_tagged_step (HD tokens) PT TG a.po_inst s'`] >>
  simp[] >>
  `post = update_var out (n2w pos) t` by
    (qpat_x_assum `a.po_inst = EL _ _` kall_tac >>
     qpat_x_assum `step_inst 0 C' _ t = OK post` mp_tac >>
     simp[concretize_inst_with_positions_def, passSharedDefsTheory.mk_assign_inst_def] >>
     simp[step_inst_non_invoke] >>
     pure_once_rewrite_tac [step_inst_base_def] >>
     simp[eval_operand_def]) >>
  gvs[Abbr `b`, ptr_ledger_next_def, ptr_observe_def, ptr_vars_transport_def,
      lookup_var_def, update_var_def]
QED
