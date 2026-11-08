Theory concretizePtrOwnedAllocationPrefix
Ancestors concretizePtrAllocationTransport concretizePtrOwnedAffinePrefix
  concretizePtrAllocationSize o1PassContract venomWf o1PassLift removeUnusedSsaProofs
  concretizePtrOwnedAssignPrefix concretizePtrDeletedGapHistory concretizePtrLedgerAlignment
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

Theorem ptr_owned_alloca_prefix_aligned_next:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  o1_run_state_ok vs0 /\ o1_ctx_shape C /\
  ~ctx_has_dalloca C /\
  fn_inst_wf a.po_fn /\ MEM sb a.po_fn.fn_blocks /\
  sb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL (EL j indices) sb.bb_instructions /\
  a.po_state.vs_inst_idx = EL j indices /\ t.vs_inst_idx = j /\
  (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP layout (Allocation i.inst_id) = SOME p) /\
  ptr_ledger_block_alignment layout sb.bb_instructions tb.bb_instructions indices /\
  SUC j < LENGTH indices /\
  a.po_inst.inst_opcode = ALLOCA /\ a.po_inst.inst_operands = [Lit sz] /\
  a.po_inst.inst_outputs = [out] /\
  FLOOKUP layout (Allocation a.po_inst.inst_id) = SOME pos /\
  FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (pos,w2n sz) /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  step_inst 0 C' (EL j tb.bb_instructions) t = OK post ==>
  ?delta b births' TG'. LENGTH delta = EL (SUC j) indices - EL j indices /\
    ptr_source_ownership vs0 C (h ++ delta) b tokens registry births' PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL (EL (SUC j) indices) sb.bb_instructions /\
    b.po_state.vs_inst_idx = EL (SUC j) indices /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) /\
    ptr_vars_transport births' positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC j)
Proof
  strip_tac >>
  `EL j indices < EL (SUC j) indices` by
    (irule ptr_ledger_alignment_order >> simp[] >>
     qexistsl_tac [`layout`,`sb.bb_instructions`,`tb.bb_instructions`] >> simp[]) >>
  `LENGTH tb.bb_instructions = LENGTH indices /\
    EL (SUC j) indices < LENGTH sb.bb_instructions /\
    EL j tb.bb_instructions = concretize_inst_with_positions layout a.po_inst` by
    (drule ptr_ledger_alignment_cursor >> strip_tac >>
     first_assum (qspec_then `SUC j` mp_tac) >>
     first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (simp[active_inst_def] >> qexists_tac `sb` >> simp[] >> decide_tac) >>
  `frame_reachable vs0 C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions /\ fn_inst_ids_distinct a.po_fn` by
    (drule_all ptr_frame_sizes >> strip_tac >>
     gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[MEM_EL]) >>
  `!base size. FLOOKUP a.po_state.vs_allocas a.po_inst.inst_id = SOME (base,size) ==>
    size = w2n sz` by
    (rpt strip_tac >> drule_all ptr_frame_current_allocation_size >>
     drule_all ptr_alloca_inst_size >> simp[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (qpat_x_assum `~ctx_has_dalloca C` mp_tac >>
     simp[NoAsms, ctx_has_dalloca_def, EVERY_MEM]) >>
  `SUC a.po_state.vs_inst_idx < LENGTH sb.bb_instructions` by decide_tac >>
  `?b births' TG'.
    ptr_source_ownership vs0 C (h ++ [b]) b tokens registry births' PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL b.po_state.vs_inst_idx sb.bb_instructions /\
    b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    births' = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) /\
    ptr_vars_transport births' positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ptr_owned_alloca_prefix_back_next >>
     rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  qpat_x_assum `!base size. FLOOKUP a.po_state.vs_allocas _ = _ ==> _` kall_tac >>
  rename1 `ptr_source_ownership vs0 C (h ++ [b0]) b0 _ _ births0 _ TG0 _` >>
  `?delta b. LENGTH delta = EL (SUC j) indices - b0.po_state.vs_inst_idx /\
    ptr_source_ownership vs0 C ((h ++ [b0]) ++ delta) b tokens registry births0 PT TG0 saved /\
    b.po_fn = b0.po_fn /\ b.po_stack = b0.po_stack /\ b.po_params = b0.po_params /\
    b.po_inst = EL (EL (SUC j) indices) sb.bb_instructions /\
    b.po_state = (b0.po_state with vs_inst_idx := EL (SUC j) indices) /\
    ptr_vars_transport births0 positions TG0 b.po_taint b.po_state
      (post with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ptr_assign_prefix_gap_aligned >>
     rpt (goal_assum (drule_at Any)) >> gvs[] >>
     qexistsl_tac [`layout`,`tb.bb_instructions`] >> simp[]) >>
  qexistsl_tac [`b0::delta`,`b`,`births0`,`TG0`] >>
  qpat_x_assum `ptr_source_ownership _ _ ((h ++ [b0]) ++ delta) _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  simp[] >> strip_tac >> simp[] >>
  qpat_x_assum `ptr_vars_transport _ _ _ b.po_taint _ _` mp_tac >> simp[]
QED

Theorem ptr_allocating_affine_owned_prefix:
  !n a h births TG j t u.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  o1_run_state_ok vs0 /\ o1_ctx_shape C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  ~ctx_has_dalloca C /\
  (!stk PG G tn fn inst s. frame_reachable vs0 C stk PG G tn fn inst s ==>
    taint_ok fn tn inst s) /\
  fn_inst_wf a.po_fn /\ MEM sb a.po_fn.fn_blocks /\
  sb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL (EL j indices) sb.bb_instructions /\
  a.po_state.vs_inst_idx = EL j indices /\ t.vs_inst_idx = j /\
  (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP layout (Allocation i.inst_id) = SOME p) /\
  (!i sz. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit sz] ==>
    ?p. FLOOKUP layout (Allocation i.inst_id) = SOME p /\
        FLOOKUP positions (Allocation i.inst_id) = SOME (p,w2n sz)) /\
  ptr_ledger_block_alignment layout sb.bb_instructions tb.bb_instructions indices /\
  j+n < LENGTH indices /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  (!k. j <= k /\ k < j+n ==>
    (?op out. (EL (EL k indices) sb.bb_instructions).inst_opcode = ASSIGN /\
      (EL (EL k indices) sb.bb_instructions).inst_operands = [op] /\
      (EL (EL k indices) sb.bb_instructions).inst_outputs = [out]) \/
    (?x y out. ((EL (EL k indices) sb.bb_instructions).inst_opcode = ADD \/
               (EL (EL k indices) sb.bb_instructions).inst_opcode = SUB) /\
      (EL (EL k indices) sb.bb_instructions).inst_operands = [x;y] /\
      (EL (EL k indices) sb.bb_instructions).inst_outputs = [out]) \/
    (?sz out. (EL (EL k indices) sb.bb_instructions).inst_opcode = ALLOCA /\
      (EL (EL k indices) sb.bb_instructions).inst_operands = [Lit sz] /\
      (EL (EL k indices) sb.bb_instructions).inst_outputs = [out])) /\
  ptr_assign_target_segment C' tb n t u ==>
  ?delta b births' TG'. LENGTH delta = EL (j+n) indices - EL j indices /\
    ptr_source_ownership vs0 C (h ++ delta) b tokens registry births' PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL (EL (j+n) indices) sb.bb_instructions /\
    b.po_state.vs_inst_idx = EL (j+n) indices /\ u.vs_inst_idx = j+n /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = u.vs_labels /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) /\
    ptr_vars_transport births' positions TG' b.po_taint b.po_state u
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`[]`,`a`,`births`,`TG`] >>
      gvs[ptr_assign_target_segment_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_assign_target_segment _ _ (SUC n) _ _` mp_tac >>
  simp[Once ptr_assign_target_segment_def] >> strip_tac >>
  `SUC j < LENGTH indices` by decide_tac >>
  `?delta b births' TG'. LENGTH delta = EL (SUC j) indices - EL j indices /\
    ptr_source_ownership vs0 C (h ++ delta) b tokens registry births' PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL (EL (SUC j) indices) sb.bb_instructions /\
    b.po_state.vs_inst_idx = EL (SUC j) indices /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) /\
    ptr_vars_transport births' positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC j)` by
    (qpat_x_assum `!a h births TG j t u. ptr_source_ownership _ _ _ _ _ _ _ _ _ _ /\ _ ==> _` kall_tac >>
     qpat_assum `!k. _` (qspec_then `j` mp_tac) >>
     (impl_tac >- simp[]) >>
     qpat_assum `a.po_inst = _` (fn th =>
       disch_then (assume_tac o PURE_REWRITE_RULE [GSYM th])) >>
     Cases_on `a.po_inst.inst_opcode = ALLOCA`
     >- (`?sz out. a.po_inst.inst_operands = [Lit sz] /\ a.po_inst.inst_outputs = [out]` by
           (qpat_x_assum `(?op out. _) \/ _` mp_tac >> simp[]) >>
         `EL j indices < LENGTH sb.bb_instructions` by
           (drule ptr_ledger_alignment_cursor >> strip_tac >>
            first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
         `MEM a.po_inst (fn_insts a.po_fn)` by
           (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
            qexists_tac `sb.bb_instructions` >> conj_tac
            >- (qexists_tac `sb` >> simp[]) >> metis_tac[MEM_EL]) >>
         `?p. FLOOKUP layout (Allocation a.po_inst.inst_id) = SOME p /\
              FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (p,w2n sz)` by
           metis_tac[] >>
         drule_all ptr_owned_alloca_prefix_aligned_next >> disch_then ACCEPT_TAC) >>
     drule ptr_affine_prefix_aligned_next >>
     disch_then (drule_at (Pat `ptr_ledger_block_alignment _ _ _ _`)) >>
     disch_then (drule_at (Pat `ptr_vars_transport _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
     disch_then drule >>
     simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
     qexistsl_tac [`delta`,`b`,`births`,`TG'`] >> simp[]) >>
  first_x_assum (qspec_then `b` mp_tac) >>
  disch_then drule >>
  disch_then (qspecl_then [`SUC j`,`post with vs_inst_idx := SUC j`,`u`] mp_tac) >>
  simp[ADD_CLAUSES] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `EL j indices < EL (SUC j) indices` by
    (irule ptr_ledger_alignment_order >> simp[] >>
     qexistsl_tac [`layout`,`sb.bb_instructions`,`tb.bb_instructions`] >> simp[]) >>
  `EL (SUC j) indices <= EL (SUC (j+n)) indices` by
    (Cases_on `n = 0` >- simp[] >>
     `SUC j < SUC (j+n) /\ SUC (j+n) < LENGTH indices` by decide_tac >>
     drule_all ptr_ledger_alignment_order >> decide_tac) >>
  qexistsl_tac [`delta ++ delta'`,`b'`,`births''`,`TG''`] >>
  simp[APPEND_ASSOC] >> metis_tac[]
QED
