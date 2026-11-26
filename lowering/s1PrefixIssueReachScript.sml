(* Realize the issuing point of the recorder as a raw reachable state. *)
Theory s1PrefixIssueReach
Ancestors
  loweringCallBudgetHistory lowerDloadPtrRawReachable contextRawReachable
  contextCodegenRel venomInst venomState venomExecProofs venomExecSemantics
  fragExec ptrDiscipline finite_map list

Theorem issue_stack_next[local]:
  ALL_DISTINCT (fn_labels fn) /\
  frame_stack_prefix vs ctx stk fn s /\ active_inst fn i s /\
  ~is_terminator i.inst_opcode /\ step_inst fuel ctx i s = OK t ==>
  frame_stack_prefix vs ctx stk fn (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  Cases_on `stk` >> simp[frame_stack_prefix_def] >> rpt strip_tac >>
  drule_all active_inst_block_lookup >> strip_tac >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
  qexistsl [`nm`, `ops`, `args`, `cs`] >> simp[] >>
  irule frame_prefix_next >> simp[] >> metis_tac[]
QED

Theorem issue_history_raw_ind[local]:
  !checked cfg root h marks p.
    lower_budget_path checked cfg root h marks p ==>
    !ctx vs. SND (SND (SND cfg)) = ctx /\
      (!f. MEM f ctx.ctx_functions ==> ALL_DISTINCT (fn_labels f)) /\
      MEM root.bp_fn ctx.ctx_functions /\
      frame_stack_prefix vs ctx root.bp_stack root.bp_fn root.bp_state /\
      (!i. active_inst root.bp_fn i root.bp_state ==>
        raw_reachable vs ctx root.bp_fn i root.bp_state) ==>
      MEM p.bp_fn ctx.ctx_functions /\
      frame_stack_prefix vs ctx p.bp_stack p.bp_fn p.bp_state /\
      (!i. active_inst p.bp_fn i p.bp_state ==>
        raw_reachable vs ctx p.bp_fn i p.bp_state)
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- simp[] >>
  gvs[] >>
  qpat_x_assum `!v. frame_stack_prefix v _ _ _ _ /\ _ ==> _`
    (qspec_then `vs` mp_tac) >> simp[] >> strip_tac >> simp[]
  >- (conj_tac
      >- (irule issue_stack_next >> metis_tac[]) >>
      metis_tac[raw_reachable_next])
  >- (conj_tac
      >- (Cases_on `p.bp_stack` >> fs[frame_stack_prefix_def] >>
          irule frame_prefix_block >>
          metis_tac[active_inst_block_lookup]) >>
      metis_tac[raw_reachable_block])
  >- (conj_tac >- metis_tac[lookup_function_MEM] >>
      conj_tac
      >- (simp[frame_stack_prefix_def] >>
          metis_tac[frame_prefix_entry, lookup_function_MEM]) >>
      metis_tac[raw_reachable_callee]) >>
  gvs[frame_stack_prefix_def] >>
  `?call_fuel. run_blocks call_fuel ctx p.bp_fn cs = IntRet ret s_end` by
    (irule frame_prefix_return >> metis_tac[active_inst_block_lookup]) >>
  conj_tac
  >- (irule issue_stack_next >> simp[] >>
      rename1 `run_blocks call_fuel _ _ _ = IntRet _ _` >>
      qexistsl [`call_fuel`, `f.cf_inst`] >> simp[is_terminator_def] >>
      simp[Once step_inst_def]) >>
  metis_tac[raw_reachable_completed_invoke]
QED

Theorem issue_history_endpoint_raw:
  ctx.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" ctx.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" /\
  (!f. MEM f ctx.ctx_functions ==>
    ALL_DISTINCT (fn_labels f) /\
    !bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  lower_budget_path checked (D,lo,explicit,ctx)
    <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
       bp_taint := entry_taint; bp_fn := func;
       bp_state := vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0|> |> h marks p /\
  active_inst p.bp_fn inst p.bp_state ==>
  raw_reachable vs ctx p.bp_fn inst p.bp_state
Proof
  strip_tac >>
  drule issue_history_raw_ind >>
  disch_then (qspecl_then [`ctx`, `vs`] mp_tac) >>
  simp[frame_stack_prefix_def] >>
  `MEM func ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  simp[] >> impl_tac
  >- (rpt strip_tac >>
      `ALL_DISTINCT (fn_labels func)` by metis_tac[] >>
      drule_all active_inst_block_lookup >> simp[] >> strip_tac >>
      `phi_prefix_length bb.bb_instructions = 0` by
        metis_tac[lookup_block_MEM] >>
      qmatch_asmsub_abbrev_tac `active_inst func i entry` >>
      `enters_block func entry entry` by
        (simp[enters_block_def, Abbr `entry`, eval_phis_no_phi,
              venom_state_fupdfupds] >> metis_tac[]) >>
      metis_tac[raw_reachable_entry]) >>
  metis_tac[]
QED
