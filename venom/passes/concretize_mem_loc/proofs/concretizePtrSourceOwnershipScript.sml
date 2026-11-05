Theory concretizePtrSourceOwnership
Ancestors
  concretizePtrActivationBirths concretizePtrOwnershipErasure
  concretizePtrActivationChronology concretizePtrChronologicalHistory
  ptrDiscipline venomExecSemantics venomInst finite_map list pred_set arithmetic

(* Only allocation creates a tag. All other instructions use the already
   checked, polymorphic copying operations. The post-cache lookup covers
   both first execution and reuse of a cached ALLOCA. *)
Definition ptr_tagged_step_def:
  ptr_tagged_step token PT TG inst s =
    if inst.inst_opcode = ALLOCA then
      set_prov TG inst.inst_outputs
        (case FLOOKUP s.vs_allocas inst.inst_id of
           NONE => NONE | SOME site => SOME (token,inst.inst_id))
    else step_prov PT TG inst s
End

Inductive ptr_tagged_chrono_step:
[~next:]
  (!C stk PG G tn fn inst inst' s s' fuel token PT TG saved.
    active_inst fn inst s /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel C inst s = OK s' /\
    active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
    ptr_tagged_chrono_step C token
      (ptr_observe stk PG G tn fn inst s)
      (ptr_observe stk PG (step_prov PG G inst s')
        (step_taint inst s s' tn) fn inst'
        (s' with vs_inst_idx := SUC s.vs_inst_idx))
      PT TG saved PT (ptr_tagged_step token PT TG inst s') saved)
[~block:]
  (!C stk PG G tn fn inst inst' s s' s1 fuel token PT TG saved.
    active_inst fn inst s /\ is_terminator inst.inst_opcode /\
    step_inst fuel C inst s = OK s' /\ ~s'.vs_halted /\
    enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
    ptr_tagged_chrono_step C token
      (ptr_observe stk PG G tn fn inst s)
      (ptr_observe stk PG (entry_prov fn s' G)
        (entry_taint_vars fn s' tn) fn inst' s1)
      PT TG saved PT (entry_prov fn s' TG) saved)
[~call:]
  (!C stk PG G tn caller inv s nm ops callee args cs s1 inst token PT TG saved.
    active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
    decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    ptr_tagged_chrono_step C token
      (ptr_observe stk PG G tn caller inv s)
      (ptr_observe
        (<| cf_fn := caller; cf_inst := inv; cf_state := s;
            cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
        (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1)
      PT TG saved (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved))
[~ret:]
  (!C f stk PG G tn fn rinst s ret s_end s' inst' fuel token PT TG RPT RTG saved.
    active_inst fn rinst s /\
    step_inst fuel C rinst s = IntRet ret s_end /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
    active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
    ptr_tagged_chrono_step C token
      (ptr_observe (f::stk) PG G tn fn rinst s)
      (ptr_observe stk f.cf_params
        (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
        (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
        f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
      PT TG ((RPT,RTG)::saved) RPT
        (DRESTRICT RTG (COMPL (set f.cf_inst.inst_outputs))) saved)
End

Theorem ptr_tagged_chrono_step_projection:
  !C token a b PT TG saved PT' TG' saved'.
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' ==>
  ptr_chrono_step C a b
Proof
  ho_match_mp_tac ptr_tagged_chrono_step_ind >>
  metis_tac[ptr_chrono_step_rules]
QED

Theorem ptr_tagged_chrono_step_length:
  !C token a b PT TG saved PT' TG' saved'.
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' ==>
  LENGTH saved = LENGTH a.po_stack ==> LENGTH saved' = LENGTH b.po_stack
Proof
  ho_match_mp_tac ptr_tagged_chrono_step_ind >> simp[ptr_observe_def]
QED

Theorem ptr_tagged_chrono_step_total:
  !C a b. ptr_chrono_step C a b ==>
  !token PT TG saved.
  LENGTH saved = LENGTH a.po_stack ==>
  ?PT' TG' saved'. ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved'
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac
  >- metis_tac[ptr_tagged_chrono_step_rules]
  >- metis_tac[ptr_tagged_chrono_step_rules]
  >- metis_tac[ptr_tagged_chrono_step_rules] >>
  Cases_on `saved` >> gvs[ptr_observe_def] >> PairCases_on `h` >>
  metis_tac[ptr_tagged_chrono_step_rules, ptr_observe_def]
QED

Inductive ptr_source_ownership:
[~root:]
  (!vs0 C a. ptr_chrono_history vs0 C [a] a /\ a.po_stack = [] ==>
    ptr_source_ownership vs0 C [a] a [0] (FEMPTY |+ (0,a.po_fn))
      (ptr_birth_lift 0 a.po_state.vs_allocas) [] FEMPTY [])
[~snoc:]
  (!vs0 C h a tokens registry births PT TG saved b PT' TG' saved'.
    ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved' ==>
    ptr_source_ownership vs0 C (h ++ [b]) b
      (ptr_activation_tokens h a b tokens) (ptr_activation_registry h a b registry)
      (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births)
      PT' TG' saved')
End

Theorem ptr_source_ownership_caches:
  !vs0 C h a tokens registry births PT TG saved.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved ==>
  ptr_source_birth_caches vs0 C h a tokens registry births
Proof
  ho_match_mp_tac ptr_source_ownership_ind >>
  metis_tac[ptr_source_birth_caches_rules, ptr_tagged_chrono_step_projection]
QED

Theorem ptr_source_ownership_stack_length:
  !vs0 C h a tokens registry births PT TG saved.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved ==>
  LENGTH saved = LENGTH a.po_stack
Proof
  ho_match_mp_tac ptr_source_ownership_ind >> simp[] >>
  metis_tac[ptr_tagged_chrono_step_length]
QED

Theorem ptr_source_ownership_total:
  !vs0 C h a tokens registry births.
  ptr_source_birth_caches vs0 C h a tokens registry births ==>
  ?PT TG saved. ptr_source_ownership vs0 C h a tokens registry births PT TG saved
Proof
  ho_match_mp_tac ptr_source_birth_caches_ind >> conj_tac
  >- metis_tac[ptr_source_ownership_rules] >>
  rpt gen_tac >> strip_tac >> rename1 `ptr_chrono_step C a b` >>
  `?PT TG saved. ptr_source_ownership vs0 C h a tokens registry births PT TG saved` by metis_tac[] >>
  `LENGTH saved = LENGTH a.po_stack` by metis_tac[ptr_source_ownership_stack_length] >>
  drule ptr_tagged_chrono_step_total >>
  disch_then (qspecl_then [`HD tokens`,`PT`,`TG`,`saved`] mp_tac) >> simp[] >> strip_tac >>
  metis_tac[ptr_source_ownership_rules]
QED

Theorem ptr_owner_restrict_projection[local]:
  ptr_ledger_erases births TG G ==>
  ptr_ledger_erases births (DRESTRICT TG keep) (DRESTRICT G keep)
Proof
  simp[concretizePtrPrefixLedgerTheory.ptr_ledger_erases_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ptr_tagged_step_projection[local]:
  ptr_ledger_erases births TG G /\ ptr_params_erases births PT PG /\
  inst.inst_opcode <> DALLOCA /\
  (!aid. FLOOKUP births (token,aid) = FLOOKUP s.vs_allocas aid) ==>
  ptr_ledger_erases births (ptr_tagged_step token PT TG inst s) (step_prov PG G inst s)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (simp[ptr_tagged_step_def, step_prov_def, out_prov_def] >>
      Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
      >- (simp[] >>
          irule (SRULE [ptr_owner_project_def]
            (Q.INST [`p` |-> `NONE`] ptr_owner_set_projection)) >> simp[]) >>
      simp[] >>
      `SOME x = ptr_owner_project births (SOME (token,inst.inst_id))` by
        simp[ptr_owner_project_def] >>
      pop_assum SUBST1_TAC >> irule ptr_owner_set_projection >> simp[] >>
      metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  simp[ptr_tagged_step_def] >> irule ptr_owner_step_projection >> simp[]
QED

Definition ptr_saved_erases_def:
  ptr_saved_erases births saved stk <=>
    LENGTH saved = LENGTH stk /\
    !n. n < LENGTH saved ==>
      ptr_params_erases births (FST (EL n saved)) (EL n stk).cf_params /\
      ptr_ledger_erases births (SND (EL n saved)) (EL n stk).cf_prov
End

Theorem ptr_saved_erases_nil[local]:
  ptr_saved_erases births [] []
Proof
  simp[ptr_saved_erases_def]
QED

Theorem ptr_saved_erases_cons[local]:
  ptr_saved_erases births ((PT,TG)::saved) (f::stk) <=>
  ptr_params_erases births PT f.cf_params /\
  ptr_ledger_erases births TG f.cf_prov /\ ptr_saved_erases births saved stk
Proof
  simp[ptr_saved_erases_def] >> eq_tac
  >- (strip_tac >>
      `ptr_params_erases births PT f.cf_params /\
       ptr_ledger_erases births TG f.cf_prov` by
        (qpat_assum `!n. n < SUC _ ==> _` (qspec_then `0` mp_tac) >> simp[NoAsms, EL]) >>
      simp[] >> rpt strip_tac >>
      first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]) >>
  strip_tac >> simp[] >> gen_tac >> Cases_on `n` >> simp[]
QED

Theorem ptr_saved_erases_extend[local]:
  ptr_saved_erases births saved stk /\
  (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) ==>
  ptr_saved_erases births' saved stk
Proof
  simp[ptr_saved_erases_def] >> rpt strip_tac >>
  metis_tac[ptr_params_erases_extend, ptr_ledger_erases_extend]
QED

Theorem ptr_tagged_chrono_step_erasure[local]:
  !C token a b PT TG saved PT' TG' saved'.
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' ==>
  !births.
  a.po_inst.inst_opcode <> DALLOCA /\
  ptr_params_erases births PT a.po_params /\
  ptr_ledger_erases births TG a.po_prov /\
  ptr_saved_erases births saved a.po_stack /\
  (LENGTH b.po_stack = LENGTH a.po_stack ==>
    !aid. FLOOKUP births (token,aid) = FLOOKUP b.po_state.vs_allocas aid) ==>
  ptr_params_erases births PT' b.po_params /\
  ptr_ledger_erases births TG' b.po_prov /\
  ptr_saved_erases births saved' b.po_stack
Proof
  ho_match_mp_tac ptr_tagged_chrono_step_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  simp[ptr_observe_def] >> strip_tac
  >- (simp[] >> irule ptr_tagged_step_projection >> simp[])
  >- (simp[] >> irule ptr_owner_entry_projection >> simp[])
  >- (`ptr_ledger_erases births FEMPTY FEMPTY` by
        simp[concretizePtrPrefixLedgerTheory.ptr_ledger_erases_def] >>
      simp[ptr_saved_erases_cons] >> irule ptr_owner_call_params >> simp[]) >>
  gvs[ptr_saved_erases_cons] >> irule ptr_owner_restrict_projection >> simp[]
QED

Theorem ptr_chrono_singleton_empty[local]:
  ptr_chrono_history vs0 C [a] a ==>
  a.po_params = [] /\ a.po_prov = FEMPTY
Proof
  simp[Once ptr_chrono_history_cases] >> rpt strip_tac >> gvs[ptr_observe_def] >>
  drule ptr_chrono_history_end >> strip_tac >>
  `LENGTH h + 1 = 1` by metis_tac[LENGTH_APPEND, LENGTH] >>
  Cases_on `h` >> gvs[]
QED

Theorem ptr_source_ownership_erasure_invariant[local]:
  !vs0 C h a tokens registry births PT TG saved.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved ==>
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  (EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
    ptr_params_erases births PT a.po_params /\
    ptr_ledger_erases births TG a.po_prov /\ ptr_saved_erases births saved a.po_stack)
Proof
  ho_match_mp_tac ptr_source_ownership_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[ptr_source_ownership_rules] >>
      drule ptr_chrono_singleton_empty >> strip_tac >>
      simp[ptr_params_erases_def,
        concretizePtrPrefixLedgerTheory.ptr_ledger_erases_def, ptr_saved_erases_nil]) >>
  rpt gen_tac >> strip_tac >> rename1 `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved'` >>
  conj_asm1_tac >- metis_tac[ptr_source_ownership_rules] >> strip_tac >>
  `ptr_chrono_step C a b` by metis_tac[ptr_tagged_chrono_step_projection] >>
  `ptr_source_birth_caches vs0 C h a tokens registry births` by
    metis_tac[ptr_source_ownership_caches] >>
  `a.po_inst.inst_opcode <> DALLOCA` by
    metis_tac[ptr_source_birth_caches_activations, ptr_source_activations_sound,
      ptr_birth_reachable_no_dalloca] >>
  qmatch_goalsub_abbrev_tac `ptr_params_erases births' _ _` >>
  `!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site` by
    (simp[Abbr `births'`] >> rpt strip_tac >>
     irule ptr_source_birth_caches_snoc_retained >> metis_tac[]) >>
  `ptr_params_erases births' PT a.po_params /\
   ptr_ledger_erases births' TG a.po_prov /\ ptr_saved_erases births' saved a.po_stack` by
    metis_tac[ptr_params_erases_extend, ptr_ledger_erases_extend, ptr_saved_erases_extend] >>
  drule ptr_tagged_chrono_step_erasure >> disch_then (qspec_then `births'` mp_tac) >>
  simp[] >> disch_then irule >> strip_tac >>
  `ptr_source_birth_caches vs0 C (h ++ [b]) b
    (ptr_activation_tokens h a b tokens) (ptr_activation_registry h a b registry) births'` by
    metis_tac[ptr_source_ownership_caches] >>
  drule_all ptr_source_birth_caches_active_lookup >>
  simp[ptr_activation_tokens_def]
QED

Theorem ptr_source_ownership_params_erases:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  ptr_params_erases births PT a.po_params
Proof
  metis_tac[ptr_source_ownership_erasure_invariant]
QED

Theorem ptr_source_ownership_prov_erases:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  ptr_ledger_erases births TG a.po_prov
Proof
  metis_tac[ptr_source_ownership_erasure_invariant]
QED

Theorem ptr_source_ownership_saved_erases:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  ptr_saved_erases births saved a.po_stack
Proof
  metis_tac[ptr_source_ownership_erasure_invariant]
QED

Theorem ptr_source_ownership_saved_params:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH saved ==>
  ptr_params_erases births (FST (EL n saved)) (EL n a.po_stack).cf_params
Proof
  metis_tac[ptr_source_ownership_saved_erases, ptr_saved_erases_def]
QED

Theorem ptr_source_ownership_saved_prov:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH saved ==>
  ptr_ledger_erases births (SND (EL n saved)) (EL n a.po_stack).cf_prov
Proof
  metis_tac[ptr_source_ownership_saved_erases, ptr_saved_erases_def]
QED

(* Operational tag support is distinct from persistent birth-table support:
   retired births remain recorded but cannot appear in a live frame's tags. *)
Definition ptr_tag_live_def:
  ptr_tag_live (tokens:num list) (p:(num # num) option) <=>
    case p of NONE => T | SOME owner => MEM (FST owner) tokens
End

Definition ptr_tags_live_def:
  ptr_tags_live tokens PT (TG:(string,num # num) fmap) <=>
    EVERY (ptr_tag_live tokens) PT /\
    !v. ptr_tag_live tokens (FLOOKUP TG v)
End

Definition ptr_saved_live_def:
  ptr_saved_live tokens saved <=>
    !n. n < LENGTH saved ==>
      ptr_tags_live (DROP (SUC n) tokens) (FST (EL n saved)) (SND (EL n saved))
End

Theorem ptr_live_op[local]:
  (!v. ptr_tag_live tokens (FLOOKUP TG v)) ==>
  ptr_tag_live tokens (op_prov TG op)
Proof
  Cases_on `op` >> simp[op_prov_def, ptr_tag_live_def]
QED

Theorem ptr_live_first[local]:
  (!v. ptr_tag_live tokens (FLOOKUP TG v)) ==>
  ptr_tag_live tokens (first_prov TG ops)
Proof
  Induct_on `ops`
  >- simp[first_prov_def, ptr_tag_live_def] >>
  strip_tac >> strip_tac >> simp[first_prov_def] >>
  drule ptr_live_op >> disch_then (qspec_then `h` mp_tac) >>
  Cases_on `op_prov TG h` >> gvs[ptr_tag_live_def]
QED

Theorem ptr_live_set[local]:
  (!v. ptr_tag_live tokens (FLOOKUP TG v)) /\ ptr_tag_live tokens p ==>
  !v. ptr_tag_live tokens (FLOOKUP (set_prov TG outs p) v)
Proof
  strip_tac >>
  `!keep v. ptr_tag_live tokens (FLOOKUP (DRESTRICT TG keep) v)` by
    (simp[FLOOKUP_DRESTRICT] >> rpt gen_tac >>
     Cases_on `v IN keep` >> simp[ptr_tag_live_def] >>
     metis_tac[ptr_tag_live_def]) >>
  Cases_on `outs` >- simp[set_prov_def] >>
  Cases_on `t` >- (Cases_on `p` >> simp[set_prov_def, FLOOKUP_UPDATE] >>
    gen_tac >> Cases_on `h = v` >> gvs[]) >>
  Cases_on `p` >> simp[set_prov_def]
QED

Theorem ptr_live_tagged_step[local]:
  ptr_tags_live tokens PT TG /\ MEM token tokens /\
  inst.inst_opcode <> DALLOCA ==>
  ptr_tags_live tokens PT (ptr_tagged_step token PT TG inst s)
Proof
  strip_tac >> gvs[ptr_tags_live_def] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (simp[ptr_tagged_step_def] >> irule ptr_live_set >> simp[] >>
      Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[ptr_tag_live_def]) >>
  simp[ptr_tagged_step_def, step_prov_def] >> irule ptr_live_set >> simp[] >>
  simp[out_prov_def] >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (simp[] >> Cases_on `inst.inst_operands` >>
      simp[ptr_tag_live_def] >> Cases_on `t` >> simp[ptr_tag_live_def] >>
      Cases_on `h` >> simp[ptr_tag_live_def] >>
      IF_CASES_TAC >> simp[ptr_tag_live_def] >>
      metis_tac[EVERY_EL, ptr_tag_live_def]) >>
  simp[] >> IF_CASES_TAC >> simp[ptr_tag_live_def, ptr_live_first]
QED

Theorem ptr_live_entry[local]:
  (!v. ptr_tag_live tokens (FLOOKUP TG v)) ==>
  !v. ptr_tag_live tokens (FLOOKUP (entry_prov fn s TG) v)
Proof
  strip_tac >>
  `!inst. ptr_tag_live tokens (phi_prov s.vs_prev_bb TG inst)` by
    (gen_tac >> simp[phi_prov_def] >> Cases_on `s.vs_prev_bb` >>
     simp[ptr_tag_live_def] >>
     Cases_on `resolve_phi x inst.inst_operands` >>
     simp[ptr_tag_live_def] >> metis_tac[ptr_live_op, ptr_tag_live_def]) >>
  `!is. !v. ptr_tag_live tokens (FLOOKUP (phis_prov s.vs_prev_bb TG is) v)` by
    (Induct >> simp[phis_prov_def] >> rpt gen_tac >> IF_CASES_TAC >> simp[] >>
     irule ptr_live_set >> simp[]) >>
  simp[entry_prov_def] >> Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
QED

Theorem ptr_live_restrict[local]:
  ptr_tags_live tokens PT TG ==>
  ptr_tags_live tokens PT (DRESTRICT TG keep)
Proof
  simp[ptr_tags_live_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  Cases_on `v IN keep` >> simp[ptr_tag_live_def] >>
  metis_tac[ptr_tag_live_def]
QED

Theorem ptr_live_mono[local]:
  ptr_tags_live tokens PT TG /\
  (!t. MEM t tokens ==> MEM t tokens') ==>
  ptr_tags_live tokens' PT TG
Proof
  simp[ptr_tags_live_def, EVERY_MEM] >> rpt strip_tac
  >- (first_x_assum drule >> Cases_on `e` >> simp[ptr_tag_live_def] >> metis_tac[]) >>
  first_x_assum (qspec_then `v` mp_tac) >>
  Cases_on `FLOOKUP TG v` >> simp[ptr_tag_live_def] >> metis_tac[]
QED

Theorem ptr_saved_live_cons[local]:
  ptr_saved_live tokens ((PT,TG)::saved) <=>
  ptr_tags_live (TL tokens) PT TG /\ ptr_saved_live (TL tokens) saved
Proof
  Cases_on `tokens` >> simp[ptr_saved_live_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      rpt strip_tac >> first_x_assum (qspec_then `SUC n` mp_tac) >> simp[])
  >- (strip_tac >> gen_tac >> Cases_on `n` >> simp[])
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      rpt strip_tac >> first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]) >>
  strip_tac >> gen_tac >> Cases_on `n` >> simp[]
QED

Theorem ptr_tagged_chrono_step_live[local]:
  !C token a b PT TG saved PT' TG' saved'.
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' ==>
  !(h:ptr_observation list) tokens.
  LENGTH tokens = SUC (LENGTH a.po_stack) /\ token = HD tokens /\
  a.po_inst.inst_opcode <> DALLOCA /\
  ptr_tags_live tokens PT TG /\ ptr_saved_live tokens saved ==>
  ptr_tags_live (ptr_activation_tokens h a b tokens) PT' TG' /\
  ptr_saved_live (ptr_activation_tokens h a b tokens) saved'
Proof
  ho_match_mp_tac ptr_tagged_chrono_step_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[ptr_observe_def, ptr_activation_tokens_def] >> strip_tac
  >- (irule ptr_live_tagged_step >> simp[] >> Cases_on `tokens` >> gvs[])
  >- (gvs[ptr_tags_live_def] >> metis_tac[ptr_live_entry])
  >- (simp[ptr_saved_live_cons] >>
      `ptr_tags_live tokens (MAP (op_prov TG) ops) FEMPTY` by
        (gvs[ptr_tags_live_def, EVERY_MAP, EVERY_MEM, ptr_tag_live_def] >>
         metis_tac[ptr_live_op, ptr_tag_live_def]) >>
      irule ptr_live_mono >> qexists_tac `tokens` >> simp[])
  >> gvs[ptr_saved_live_cons] >> irule ptr_live_restrict >> simp[]
QED

Theorem ptr_source_ownership_live_invariant[local]:
  !vs0 C h a tokens registry births PT TG saved.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved ==>
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  (EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
    ptr_tags_live tokens PT TG /\ ptr_saved_live tokens saved)
Proof
  ho_match_mp_tac ptr_source_ownership_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[ptr_source_ownership_rules] >>
      simp[ptr_tags_live_def, ptr_saved_live_def, ptr_tag_live_def]) >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- metis_tac[ptr_source_ownership_rules] >> strip_tac >>
  `ptr_source_birth_caches vs0 C h a tokens registry births` by
    metis_tac[ptr_source_ownership_caches] >>
  `ptr_ledger_source_activations vs0 C h a tokens registry` by
    metis_tac[ptr_source_birth_caches_activations] >>
  `a.po_inst.inst_opcode <> DALLOCA` by
    metis_tac[ptr_source_activations_sound, ptr_birth_reachable_no_dalloca] >>
  drule ptr_tagged_chrono_step_live >>
  disch_then (qspecl_then [`h`,`tokens`] mp_tac) >>
  simp[] >> metis_tac[ptr_source_activations_length]
QED

Theorem ptr_source_ownership_live:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  ptr_tags_live tokens PT TG
Proof
  metis_tac[ptr_source_ownership_live_invariant]
QED

Theorem ptr_source_ownership_saved_live:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions ==>
  ptr_saved_live tokens saved
Proof
  metis_tac[ptr_source_ownership_live_invariant]
QED

Theorem ptr_source_ownership_live_prov:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  FLOOKUP TG v = SOME (token,aid) ==> MEM token tokens
Proof
  strip_tac >> drule_all ptr_source_ownership_live >>
  simp[ptr_tags_live_def] >> strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[ptr_tag_live_def]
QED

Theorem ptr_source_ownership_live_param:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  MEM (SOME (token,aid)) PT ==> MEM token tokens
Proof
  strip_tac >> drule_all ptr_source_ownership_live >>
  simp[ptr_tags_live_def, EVERY_MEM] >>
  strip_tac >> first_x_assum (qspec_then `SOME (token,aid)` mp_tac) >>
  simp[ptr_tag_live_def]
QED

Theorem ptr_source_ownership_saved_live_prov:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH saved /\ FLOOKUP (SND (EL n saved)) v = SOME (token,aid) ==>
  MEM token (DROP (SUC n) tokens)
Proof
  strip_tac >> drule_all ptr_source_ownership_saved_live >>
  simp[ptr_saved_live_def] >> disch_then (qspec_then `n` mp_tac) >>
  simp[ptr_tags_live_def] >> strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[ptr_tag_live_def]
QED

Theorem ptr_source_ownership_saved_live_param:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH saved /\ MEM (SOME (token,aid)) (FST (EL n saved)) ==>
  MEM token (DROP (SUC n) tokens)
Proof
  strip_tac >> drule_all ptr_source_ownership_saved_live >>
  simp[ptr_saved_live_def] >> disch_then (qspec_then `n` mp_tac) >>
  simp[ptr_tags_live_def, EVERY_MEM] >>
  strip_tac >> first_x_assum (qspec_then `SOME (token,aid)` mp_tac) >>
  simp[ptr_tag_live_def]
QED

Theorem ptr_source_ownership_live_cache:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP a.po_prov v = SOME (srcbase,sz) ==>
  ?d. d <= LENGTH a.po_stack /\
      EL (LENGTH a.po_stack - d) tokens = token /\
      FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (srcbase,sz)
Proof
  strip_tac >>
  `MEM token tokens` by metis_tac[ptr_source_ownership_live_prov] >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations,
      ptr_source_activations_length] >>
  `FLOOKUP births (token,aid) = SOME (srcbase,sz)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[concretizePtrPrefixLedgerTheory.ptr_ledger_erases_def] >> strip_tac >>
     qpat_x_assum `!v. FLOOKUP a.po_prov v = _`
       (qspec_then `v` mp_tac) >> simp[ptr_owner_project_def]) >>
  `ptr_birth_slices a tokens births` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_slices] >>
  gvs[MEM_EL] >> rename1 `n < SUC (LENGTH a.po_stack)` >>
  qexists_tac `LENGTH a.po_stack - n` >>
  `LENGTH a.po_stack - (LENGTH a.po_stack - n) = n` by decide_tac >>
  simp[] >> gvs[ptr_birth_slices_def] >>
  first_x_assum (qspecl_then [`LENGTH a.po_stack - n`,`aid`] mp_tac) >> simp[]
QED
