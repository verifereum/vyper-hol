Theory concretizePtrActivationBirths
Ancestors
  concretizePtrActivationChronology concretizePtrActivationSupport
  concretizePtrChronologicalHistory concretizePtrOwnerPath venomInst
  venomExecSemantics venomMemProps ptrDiscipline ptrDisciplineEmptyTaint
  finite_map list rich_list pred_set

Definition ptr_birth_lift_def:
  ptr_birth_lift token (A : (num,num # num) fmap) =
    FUN_FMAP (\key. A ' (SND key)) (IMAGE (\aid. (token,aid)) (FDOM A))
End

Definition ptr_birth_overlay_def:
  ptr_birth_overlay token A births = FUNION (ptr_birth_lift token A) births
End

Theorem ptr_birth_lift_lookup:
  FLOOKUP (ptr_birth_lift token A) (t,aid) =
    if t = token then FLOOKUP A aid else NONE
Proof
  simp[ptr_birth_lift_def, FLOOKUP_FUN_FMAP] >>
  Cases_on `t = token` >> simp[] >> simp[FLOOKUP_DEF]
QED

Theorem ptr_birth_overlay_lookup:
  FLOOKUP (ptr_birth_overlay token A births) (t,aid) =
    if t = token then
      (case FLOOKUP A aid of NONE => FLOOKUP births (t,aid) | SOME site => SOME site)
    else FLOOKUP births (t,aid)
Proof
  simp[ptr_birth_overlay_def, FLOOKUP_FUNION, ptr_birth_lift_lookup] >>
  Cases_on `t = token` >> simp[] >> Cases_on `FLOOKUP A aid` >> simp[]
QED

Definition ptr_birth_slices_def:
  ptr_birth_slices a tokens births <=>
    !d aid. d <= LENGTH a.po_stack ==>
      FLOOKUP births (EL (LENGTH a.po_stack - d) tokens,aid) =
      FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid
End

Definition ptr_birth_token_bound_def:
  ptr_birth_token_bound (h : ptr_observation list) births <=>
    !t aid. (t,aid) IN FDOM births ==> t < LENGTH h
End

Inductive ptr_source_birth_caches:
[~root:]
  (!vs0 C a. ptr_chrono_history vs0 C [a] a /\ a.po_stack = [] ==>
    ptr_source_birth_caches vs0 C [a] a [0] (FEMPTY |+ (0,a.po_fn))
      (ptr_birth_lift 0 a.po_state.vs_allocas))
[~snoc:]
  (!vs0 C h a tokens registry births b.
    ptr_source_birth_caches vs0 C h a tokens registry births /\ ptr_chrono_step C a b ==>
    ptr_source_birth_caches vs0 C (h ++ [b]) b
      (ptr_activation_tokens h a b tokens)
      (ptr_activation_registry h a b registry)
      (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births))
End

Theorem ptr_source_birth_caches_total:
  !vs0 C h a tokens registry.
  ptr_ledger_source_activations vs0 C h a tokens registry ==>
  ?births. ptr_source_birth_caches vs0 C h a tokens registry births
Proof
  ho_match_mp_tac ptr_ledger_source_activations_ind >>
  metis_tac[ptr_source_birth_caches_rules]
QED

Theorem ptr_source_birth_caches_activations:
  !vs0 C h a tokens registry births.
  ptr_source_birth_caches vs0 C h a tokens registry births ==>
  ptr_ledger_source_activations vs0 C h a tokens registry
Proof
  ho_match_mp_tac ptr_source_birth_caches_ind >>
  metis_tac[ptr_ledger_source_activations_rules]
QED

Theorem ptr_birth_overlay_retains[local]:
  (!aid site. FLOOKUP births (token,aid) = SOME site ==> FLOOKUP A aid = SOME site) ==>
  !key site. FLOOKUP births key = SOME site ==>
    FLOOKUP (ptr_birth_overlay token A births) key = SOME site
Proof
  strip_tac >> rpt gen_tac >> PairCases_on `key` >>
  simp[ptr_birth_overlay_lookup] >> rpt strip_tac >>
  Cases_on `key0 = token` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem ptr_birth_overlay_exact[local]:
  (!aid site. FLOOKUP births (token,aid) = SOME site ==> FLOOKUP A aid = SOME site) ==>
  !aid. FLOOKUP (ptr_birth_overlay token A births) (token,aid) = FLOOKUP A aid
Proof
  strip_tac >> simp[ptr_birth_overlay_lookup] >> gen_tac >>
  Cases_on `FLOOKUP A aid` >> simp[] >>
  Cases_on `FLOOKUP births (token,aid)` >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem ptr_birth_overlay_bound[local]:
  ptr_birth_token_bound h births /\ token < LENGTH (h ++ [b]) ==>
  ptr_birth_token_bound (h ++ [b]) (ptr_birth_overlay token A births)
Proof
  simp[ptr_birth_token_bound_def, ptr_birth_overlay_def, ptr_birth_lift_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> decide_tac
QED

Theorem ptr_birth_reachable_no_dalloca:
  ptr_chrono_history vs0 C h a /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  a.po_inst.inst_opcode <> DALLOCA
Proof
  strip_tac >> drule ptr_chrono_history_reachable >> strip_tac >>
  gvs[ptr_observation_reachable_def] >>
  drule ptr_frame_table_support_invariant >> simp[] >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    metis_tac[ptr_owner_frame_active] >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (gvs[contextCodegenRelTheory.active_inst_def, fn_insts_def,
      venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[MEM_EL]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_birth_step_tables[local]:
  ptr_chrono_step C a b /\ a.po_inst.inst_opcode <> DALLOCA ==>
  (LENGTH b.po_stack = LENGTH a.po_stack ==>
    (!aid site. FLOOKUP a.po_state.vs_allocas aid = SOME site ==>
      FLOOKUP b.po_state.vs_allocas aid = SOME site) /\
    (!d. d < LENGTH b.po_stack ==>
      (ptr_owner_view d b).cf_state.vs_allocas = (ptr_owner_view d a).cf_state.vs_allocas)) /\
  (LENGTH b.po_stack = SUC (LENGTH a.po_stack) ==>
    b.po_state.vs_allocas = FEMPTY /\
    (!d. d <= LENGTH a.po_stack ==>
      (ptr_owner_view d b).cf_state.vs_allocas = (ptr_owner_view d a).cf_state.vs_allocas)) /\
  (LENGTH a.po_stack = SUC (LENGTH b.po_stack) ==>
    !d. d <= LENGTH b.po_stack ==>
      (ptr_owner_view d b).cf_state.vs_allocas = (ptr_owner_view d a).cf_state.vs_allocas)
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def]
  >- metis_tac[ptr_step_allocas_extend]
  >- simp[ptr_owner_view_def]
  >- (`~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, is_alloca_op_def]) >>
      `s'.vs_allocas = s.vs_allocas` by metis_tac[step_inst_non_alloca_preserves_allocas] >>
      `s1.vs_allocas = s'.vs_allocas` by metis_tac[enters_block_allocas] >> simp[]) 
  >- simp[ptr_owner_view_def]
  >- (drule enters_block_allocas >>
      gvs[setup_callee_def, AllCaseEqs()])
  >- (Cases_on `d = LENGTH stk` >> gvs[ptr_owner_view_def] >>
      `SUC (LENGTH stk) - (d + 1) = SUC (LENGTH stk - (d + 1))` by decide_tac >>
      simp[EL]) >>
  `s'.vs_allocas = f.cf_state.vs_allocas` by metis_tac[ptr_return_allocas] >>
  Cases_on `d = LENGTH stk` >> gvs[ptr_owner_view_def] >>
  `SUC (LENGTH stk) - (d + 1) = SUC (LENGTH stk - (d + 1))` by decide_tac >> simp[EL]
QED

Theorem ptr_birth_token_geometry[local]:
  ptr_ledger_source_activations vs0 C h a tokens registry ==>
  LENGTH tokens = SUC (LENGTH a.po_stack) /\ ALL_DISTINCT tokens /\
  EVERY (\t. t < LENGTH h) tokens
Proof
  strip_tac >> conj_tac >- metis_tac[ptr_source_activations_length] >>
  conj_tac >- metis_tac[ptr_source_activations_distinct] >>
  simp[EVERY_EL] >> rpt strip_tac >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by metis_tac[ptr_source_activations_length] >>
  `n <= LENGTH a.po_stack` by decide_tac >>
  `LENGTH a.po_stack - (LENGTH a.po_stack - n) = n` by decide_tac >>
  drule ptr_source_activations_owner_lookup >>
  disch_then (qspec_then `LENGTH a.po_stack - n` mp_tac) >> simp[] >> strip_tac >>
  irule ptr_source_activations_registry_bound >>
  metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]
QED

Theorem ptr_birth_step_compatible[local]:
  ptr_chrono_step C a b /\ a.po_inst.inst_opcode <> DALLOCA /\
  LENGTH tokens = SUC (LENGTH a.po_stack) /\
  ptr_birth_slices a tokens births /\ ptr_birth_token_bound h births ==>
  !aid site.
    FLOOKUP births (HD (ptr_activation_tokens h a b tokens),aid) = SOME site ==>
    FLOOKUP b.po_state.vs_allocas aid = SOME site
Proof
  strip_tac >> drule ptr_activation_step_lengths >> strip_tac
  >- (gvs[ptr_activation_tokens_def] >> rpt strip_tac >>
      `FLOOKUP births (HD tokens,aid) = FLOOKUP a.po_state.vs_allocas aid` by
        (qpat_x_assum `ptr_birth_slices _ _ _` mp_tac >>
         simp[ptr_birth_slices_def] >> disch_then (qspec_then `LENGTH a.po_stack` mp_tac) >>
         Cases_on `tokens` >> gvs[ptr_owner_view_def] >> metis_tac[]) >>
      drule_all ptr_birth_step_tables >> metis_tac[])
  >- (gvs[ptr_activation_tokens_def, ptr_birth_token_bound_def, FLOOKUP_DEF] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  gvs[ptr_activation_tokens_def] >> rpt strip_tac >>
  `LENGTH a.po_stack - LENGTH b.po_stack = 1` by decide_tac >>
  `FLOOKUP births (HD (TL tokens),aid) =
    FLOOKUP (ptr_owner_view (LENGTH b.po_stack) a).cf_state.vs_allocas aid` by
    (qpat_x_assum `ptr_birth_slices _ _ _` mp_tac >>
     simp[ptr_birth_slices_def] >>
     disch_then (qspec_then `LENGTH b.po_stack` mp_tac) >>
     Cases_on `tokens` >> gvs[] >> Cases_on `t` >> gvs[] >> metis_tac[]) >>
  drule_all ptr_birth_step_tables >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `LENGTH b.po_stack` mp_tac) >>
  simp[ptr_owner_view_def] >> gvs[ptr_owner_view_def]
QED

Theorem ptr_birth_step_passive[local]:
  ptr_chrono_step C a b /\ a.po_inst.inst_opcode <> DALLOCA /\
  LENGTH tokens = SUC (LENGTH a.po_stack) /\
  ptr_birth_slices a tokens births ==>
  !d aid. d < LENGTH b.po_stack ==>
    FLOOKUP births
      (EL (LENGTH b.po_stack - d) (ptr_activation_tokens h a b tokens),aid) =
    FLOOKUP (ptr_owner_view d b).cf_state.vs_allocas aid
Proof
  strip_tac >> drule ptr_activation_step_lengths >> strip_tac
  >- (simp[ptr_activation_tokens_def] >> rpt strip_tac >>
      drule_all ptr_birth_step_tables >> simp[] >> strip_tac >>
      gvs[ptr_birth_slices_def] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ])
  >- (simp[ptr_activation_tokens_def] >> rpt strip_tac >>
      `d <= LENGTH a.po_stack /\
       SUC (LENGTH a.po_stack) - d = SUC (LENGTH a.po_stack - d)` by decide_tac >>
      simp[EL] >> drule_all ptr_birth_step_tables >> simp[] >> strip_tac >>
      gvs[ptr_birth_slices_def] >> metis_tac[]) >>
  simp[ptr_activation_tokens_def] >> rpt strip_tac >>
  `d <= LENGTH a.po_stack /\
   SUC (LENGTH b.po_stack) - d = SUC (LENGTH b.po_stack - d)` by decide_tac >>
  drule_all ptr_birth_step_tables >> simp[] >> strip_tac >>
  qpat_x_assum `ptr_birth_slices _ _ _` mp_tac >>
  simp[ptr_birth_slices_def] >> disch_then (qspec_then `d` mp_tac) >>
  Cases_on `tokens` >> gvs[EL, TL] >>
  `SUC (LENGTH b.po_stack) - d = SUC (LENGTH b.po_stack - d)` by decide_tac >>
  simp[EL]
QED

Theorem ptr_birth_distinct_head[local]:
  ALL_DISTINCT tokens /\ n < LENGTH tokens /\ n <> 0 ==>
  EL n tokens <> HD tokens
Proof
  Cases_on `tokens` >> simp[] >> strip_tac >>
  Cases_on `n` >> gvs[EL] >> metis_tac[MEM_EL]
QED

Theorem ptr_birth_step_slices[local]:
  ptr_chrono_step C a b /\ a.po_inst.inst_opcode <> DALLOCA /\
  LENGTH tokens = SUC (LENGTH a.po_stack) /\
  ALL_DISTINCT (ptr_activation_tokens h a b tokens) /\
  LENGTH (ptr_activation_tokens h a b tokens) = SUC (LENGTH b.po_stack) /\
  ptr_birth_slices a tokens births /\ ptr_birth_token_bound h births ==>
  ptr_birth_slices b (ptr_activation_tokens h a b tokens)
    (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births)
Proof
  strip_tac >> simp[ptr_birth_slices_def] >> rpt strip_tac >>
  Cases_on `d = LENGTH b.po_stack`
  >- (simp[ptr_owner_view_def] >>
      `EL 0 (ptr_activation_tokens h a b tokens) = HD (ptr_activation_tokens h a b tokens)` by
        (Cases_on `ptr_activation_tokens h a b tokens` >> gvs[]) >>
      simp[] >> irule ptr_birth_overlay_exact >>
      rpt strip_tac >> irule ptr_birth_step_compatible >> metis_tac[]) >>
  `d < LENGTH b.po_stack` by decide_tac >>
  `EL (LENGTH b.po_stack - d) (ptr_activation_tokens h a b tokens) <>
   HD (ptr_activation_tokens h a b tokens)` by
    (irule ptr_birth_distinct_head >> simp[] >> decide_tac) >>
  simp[ptr_birth_overlay_lookup] >> irule ptr_birth_step_passive >> metis_tac[]
QED

Theorem ptr_source_birth_caches_invariant[local]:
  !vs0 C h a tokens registry births.
  ptr_source_birth_caches vs0 C h a tokens registry births ==>
  ptr_ledger_source_activations vs0 C h a tokens registry /\
  (EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
    ptr_birth_slices a tokens births /\ ptr_birth_token_bound h births)
Proof
  ho_match_mp_tac ptr_source_birth_caches_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[ptr_ledger_source_activations_rules] >>
      simp[ptr_birth_slices_def, ptr_birth_token_bound_def,
        ptr_birth_lift_def, ptr_owner_view_def, FLOOKUP_FUN_FMAP] >>
      rpt strip_tac >> simp[FLOOKUP_DEF]) >>
  rpt gen_tac >> strip_tac >> rename1 `ptr_chrono_step C a b` >>
  `ptr_ledger_source_activations vs0 C (h ++ [b]) b
    (ptr_activation_tokens h a b tokens) (ptr_activation_registry h a b registry)` by
    metis_tac[ptr_ledger_source_activations_rules] >>
  conj_tac >- simp[] >> strip_tac >>
  `ptr_birth_slices a tokens births /\ ptr_birth_token_bound h births` by metis_tac[] >>
  `a.po_inst.inst_opcode <> DALLOCA` by
    metis_tac[ptr_source_activations_sound, ptr_birth_reachable_no_dalloca] >>
  qpat_assum `ptr_ledger_source_activations _ _ h a tokens _`
    (mp_then Any strip_assume_tac ptr_birth_token_geometry) >>
  qpat_assum `ptr_ledger_source_activations _ _ (h ++ [b]) _ _ _`
    (mp_then Any strip_assume_tac ptr_birth_token_geometry) >>
  conj_tac >- (irule ptr_birth_step_slices >> metis_tac[]) >>
  irule ptr_birth_overlay_bound >> simp[] >>
  Cases_on `ptr_activation_tokens h a b tokens` >> gvs[]
QED

Theorem ptr_source_birth_caches_slices:
  ptr_source_birth_caches vs0 C h a tokens registry births /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  ptr_birth_slices a tokens births
Proof
  metis_tac[ptr_source_birth_caches_invariant]
QED

Theorem ptr_source_birth_caches_token_bound:
  ptr_source_birth_caches vs0 C h a tokens registry births /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  ptr_birth_token_bound h births
Proof
  metis_tac[ptr_source_birth_caches_invariant]
QED

Theorem ptr_source_birth_caches_active_lookup:
  ptr_source_birth_caches vs0 C h a tokens registry births /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  !aid. FLOOKUP births (HD tokens,aid) = FLOOKUP a.po_state.vs_allocas aid
Proof
  strip_tac >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by
    metis_tac[ptr_source_birth_caches_activations, ptr_source_activations_length] >>
  drule_all ptr_source_birth_caches_slices >>
  simp[ptr_birth_slices_def] >> disch_then (qspec_then `LENGTH a.po_stack` mp_tac) >>
  Cases_on `tokens` >> gvs[ptr_owner_view_def]
QED

Theorem ptr_source_birth_caches_snoc_retained:
  ptr_source_birth_caches vs0 C h a tokens registry births /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  ptr_chrono_step C a b ==>
  !key site. FLOOKUP births key = SOME site ==>
    FLOOKUP (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens))
      b.po_state.vs_allocas births) key = SOME site
Proof
  strip_tac >>
  drule ptr_source_birth_caches_invariant >> simp[] >> strip_tac >>
  drule ptr_birth_token_geometry >> strip_tac >>
  `a.po_inst.inst_opcode <> DALLOCA` by
    metis_tac[ptr_source_activations_sound, ptr_birth_reachable_no_dalloca] >>
  rpt gen_tac >> strip_tac >> irule ptr_birth_overlay_retains >> conj_tac
  >- (rpt strip_tac >> irule ptr_birth_step_compatible >> metis_tac[]) >> simp[]
QED
