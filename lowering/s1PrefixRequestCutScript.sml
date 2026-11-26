(* Request-cut safety from a checked path to the issuing instruction. *)
Theory s1PrefixRequestCut
Ancestors
  s1PrefixDefs loweringJointPrefixHistory loweringCallBudgetHistory
  loweringBudgetStoreRecorder fragGasOriginPtrSafeUpto loweringMemCorrect
  lowerDloadDefs contextRawReachable ptrDiscipline unitMemInv o1PassContract
  venomInst venomState venomExecSemantics e2eRequestCutDefs words list finite_map
  s1PrefixIssueHistory s1PrefixIssueChecks s1PrefixIssueReach
  s1PrefixRawRequestSafety fragExec contextCodegenRel

Theorem request_site_raw_safe_rq_upto:
  request_site (D, 0, explicit, ctx, func, []) cx H
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY, entry_taint) k rq outcome /\
  ctx.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" ctx.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" /\
  ~vs.vs_halted /\
  (!f. MEM f ctx.ctx_functions ==>
    ALL_DISTINCT (fn_labels f) /\
    !bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  EVERY (\f. fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f)) ctx.ctx_functions /\
  reserved_intervals_wf ctx.ctx_global_reserved /\
  EVERY (\f. f.fn_eom = NONE) ctx.ctx_functions /\
  fmp_free_ctx ctx /\ fixed_region_reserved 0 ctx /\
  mem_inv dload_headroom_ok ctx vs /\
  w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
  code_layout_valid vs ==>
  raw_safe_rq_upto D 0 k ctx vs /\
  ?fn inst s fuel s'.
    raw_reachable vs ctx fn inst s /\ inst.inst_opcode <> INVOKE /\
    LENGTH s.vs_requests = k /\ step_inst fuel ctx inst s = OK s' /\
    k < LENGTH s'.vs_requests /\
    request_agree H cx.txn.target rq (EL k s'.vs_requests) /\
    outcome = (if s.vs_outcomes = [] then failed_outcome rq else HD s.vs_outcomes)
Proof
  suspend "proof"
QED

Resume request_site_raw_safe_rq_upto[proof]:
  strip_tac >>
  qpat_x_assum `request_site _ _ _ _ _ _ _` mp_tac >>
  simp[request_site_def] >> strip_tac >>
  rename1 `active_inst leaf issue end_state` >>
  `MEM func ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  qabbrev_tac `entry = vs with <|vs_prev_bb := NONE;
                          vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  qabbrev_tac `root = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
                      bp_taint := entry_taint; bp_fn := func; bp_state := entry |>` >>
  `?h. lower_budget_certificate (D,0,explicit,ctx) root h left
        (INL (leaf,leaf_pg,G',tn',end_state))` by
    (irule gas_origin_ptr_focus_certificate >> simp[Abbr `root`] >>
     metis_tac[]) >>
  qpat_x_assum `lower_budget_certificate _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [lower_budget_certificate_def]) >>
  reverse conj_tac
  >- (qexistsl [`leaf`, `issue`, `end_state`, `fuel`, `t'`] >> simp[] >>
      gs[Abbr `root`, Abbr `entry`] >>
      qpat_assum `lower_budget_path T _ _ _ _ _`
        (mp_then Any mp_tac issue_history_endpoint_raw) >>
      simp[] >> metis_tac[]) >>
  irule raw_safe_rq_upto_intro >> simp[] >> reverse conj_tac
  >- (qexists_tac `P` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `active_inst fn inst s` by
    (qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_once_rewrite_tac[frame_reachable_cases] >> metis_tac[]) >>
  drule lower_budget_frame_history >>
  disch_then (qspecl_then [`D`, `0`, `explicit`] mp_tac) >> simp[] >> strip_tac >>
  `entered = entry` by
    (qpat_x_assum `enters_block _ _ _` mp_tac >>
     simp[enters_block_def, Abbr `entry`] >> strip_tac >>
     `phi_prefix_length bb.bb_instructions = 0` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
     gvs[eval_phis_no_phi, venom_state_fupdfupds]) >>
  qpat_x_assum `entered = entry` SUBST_ALL_TAC >>
  gs[Abbr `root`] >>
  `LENGTH h' <= LENGTH h` by
    (qpat_assum `lower_budget_path T _ _ _ _ _`
       (mp_then Any (fn th => qpat_assum `lower_budget_path F _ _ _ _ _`
         (mp_then Any mp_tac th)) issue_history_bounds_frame_history) >>
     simp[] >> metis_tac[]) >>
  qpat_assum `lower_budget_path T _ _ _ _ _`
    (mp_then Any (fn th => qpat_assum `lower_budget_path F _ _ _ _ _`
      (mp_then Any mp_tac th)) issue_prefix_frame_checks) >>
  simp[] >> metis_tac[]
QED

Finalise request_site_raw_safe_rq_upto
