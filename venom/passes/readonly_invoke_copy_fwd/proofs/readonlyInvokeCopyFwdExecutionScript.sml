(* Actual source execution and opaque relational observations are separate. *)
Theory readonlyInvokeCopyFwdExecution
Ancestors
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdOpaqueReturn frameViewFacts frameRel unitShapeDefs o1PassContract
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHeterogeneousSupport
  readonlyInvokeCopyFwdHeterogeneousMapOrigins readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdGlobalSupport readonlyInvokeCopyFwdOperationalPositiveCopy
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdOperationalSupport
  o1LowerDloadOccurrence taintAgree o1LowerDloadShared internalReturnCopyFwdSim
  contextCodegenRel venomExecSemantics venomState venomInst ptrDiscipline
  finite_map list pred_set

Definition ricf_execution_invariant_def:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt <=>
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G rt s t /\
  ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) rt maps stk targets s t /\
  ircf_cross rt (ricf_phase_ranges 0 ledger) s t /\
  ricf_cert_crosses rt (ricf_phase_stack_ranges stk ledger) stk s t /\
  ricf_heterogeneous_support_origins vs C a fn U stk B E /\
  ricf_support_agree B E rt s t /\
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
  ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn inst s U B maps
End

Theorem ricf_execution_initial:
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s ==>
  ricf_execution_invariant vs C D [] [] FEMPTY entry_taint fn inst s s
    1 0 [] FEMPTY [] FEMPTY [] {} FEMPTY [] [] entry_taint
Proof
  strip_tac >> drule_all ricf_heterogeneous_source_ledger_initial >> strip_tac >>
  simp[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
    ricf_opaque_live_stack_agree_def, ricf_opaque_view_def,
    ricf_visible_prov_def, ricf_visible_params_def, ricf_opaque_params_def,
    ricf_is_zero_prov_def, frame_view_def,
    ricf_frame_agree_identity, ricf_frame_agree_def, ricf_params_agree_def,
    ricf_value_agree_empty, ricf_complete_params_def, taint_agree_def, ld_shared_agree_refl,
    word_agree_except_def, venom_state_component_equality,
    ircf_cross_def, ricf_phase_stack_ranges_def, ricf_cert_crosses_def,
    ricf_heterogeneous_support_empty, ricf_support_agree_def]
QED



(* The opcode proves relational transport.  This rule advances all actual
   source histories once, including fresh/cached allocation bookkeeping. *)
Theorem ricf_execution_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  ricf_opaque_frame_agree fn D
    (ircf_dead (ricf_original_copy_ids C) u stk) sites
    (ricf_complete_params PG u.vs_params) (step_prov PG G inst u)
    (step_taint inst s u rt) u v /\
  ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    (step_taint inst s u rt) maps stk targets u v /\
  ircf_cross (step_taint inst s u rt) (ricf_phase_ranges 0 ledger) u v /\
  ricf_cert_crosses (step_taint inst s u rt)
    (ricf_phase_stack_ranges stk ledger) stk u v /\
  ricf_support_agree (occurrence_sites_step a B inst u) E
    (step_taint inst s u rt) u v ==>
  ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx)
    (v with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst u) HP
    (occurrence_step a HP H inst u) ledger E sites maps targets
    (step_taint inst s u rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_heterogeneous_source_ledger_def] >>
  `ricf_heterogeneous_source_ledger vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst u) HP
    (occurrence_step a HP H inst u) ledger` by
    (irule ricf_heterogeneous_source_ledger_actual_next >> metis_tac[]) >>
  `ricf_heterogeneous_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U (occurrence_sites_step a B inst u) sites` by
    (`ricf_heterogeneous_map_origins vs C stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
      U B sites` by
       (irule ricf_heterogeneous_map_origins_next >> metis_tac[]) >>
     Cases_on `inst.inst_opcode = ALLOCA`
     >- (irule ricf_heterogeneous_map_origins_sites_step >>
         drule occ_frame_reachable_annotation >>
         fs[ricf_heterogeneous_source_ledger_def, occurrence_annotation_ok_def] >>
         metis_tac[]) >>
     fs[occurrence_sites_step_def]) >>
  `ricf_heterogeneous_saved_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U (occurrence_sites_step a B inst u) maps` by
    (`ricf_heterogeneous_saved_map_origins vs C stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
      U B maps` by
       (irule ricf_heterogeneous_saved_map_origins_next >> metis_tac[]) >>
     Cases_on `inst.inst_opcode = ALLOCA`
     >- (irule ricf_heterogeneous_saved_map_origins_sites_step >>
         drule occ_frame_reachable_annotation >>
         fs[ricf_heterogeneous_source_ledger_def, occurrence_annotation_ok_def] >>
         metis_tac[]) >>
     fs[occurrence_sites_step_def]) >>
  `ricf_heterogeneous_support_origins vs C a fn U stk
    (occurrence_sites_step a B inst u) E` by
    (irule ricf_heterogeneous_support_actual_next >>
     fs[ricf_heterogeneous_source_ledger_def] >> metis_tac[]) >>
  simp[] >> rpt conj_tac
  >- (irule ricf_opaque_frame_inst_idx >> fs[ircf_dead_def])
  >- (qpat_x_assum `ricf_opaque_live_stack_agree _ _ _ _ _ _ u v` mp_tac >>
      simp[ricf_opaque_live_stack_agree_def, merge_callee_state_def])
  >- (qpat_x_assum `ircf_cross _ _ u v` mp_tac >> simp[ircf_cross_def])
  >- (qpat_x_assum `ricf_cert_crosses _ _ _ u v` mp_tac >>
      simp[ricf_cert_crosses_def, ircf_cross_def])
  >> qpat_x_assum `ricf_support_agree _ _ _ u v` mp_tac >>
     simp[ricf_support_agree_def]
QED

Theorem ricf_execution_bind_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK (update_var out x s) /\
  step_inst fuel Ct inst t = OK (update_var out y t) /\
  active_inst fn next ((update_var out x s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  ricf_opaque_value_agree sites p m
    (if retpc_var fn out then 0w else x)
    (if retpc_var fn out then 0w else y) /\
  step_prov PG G inst (update_var out x s) = set_prov G [out] p /\
  step_taint inst s (update_var out x s) rt =
    (rt with t_var := set_var_taint rt.t_var [out] m) /\
  occurrence_sites_step a B inst (update_var out x s) = B ==>
  ricf_execution_invariant vs C D stk PG
    (step_prov PG G inst (update_var out x s))
    (step_taint inst s (update_var out x s) tn) fn next
    ((update_var out x s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((update_var out y t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst (update_var out x s)) HP
    (occurrence_step a HP H inst (update_var out x s))
    ledger E sites maps targets
    (step_taint inst s (update_var out x s) rt)
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G rt s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) rt maps stk targets s t /\
   ircf_cross rt (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses rt (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E rt s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all ricf_opaque_frame_bind >> strip_tac >>
  irule ricf_execution_next >>
  simp[Once ircf_dead_def, update_var_def] >>
  fs[ircf_dead_def, ricf_opaque_live_stack_agree_def,
    merge_callee_state_def, ircf_cross_def, ricf_cert_crosses_def,
    ricf_support_agree_def, update_var_def] >>
  rpt conj_tac
  >- (qexists_tac `fuel` >> asm_rewrite_tac[])
  >- (qpat_x_assum `!db sb sz k. _` ACCEPT_TAC) >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem ricf_execution_assign_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ssa_form fn /\
  active_inst fn inst s /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  strip_tac >>
  `?x. eval_operand op s = SOME x /\ u = update_var out x s` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G rt s t` by
    fs[ricf_execution_invariant_def] >>
  `?y. eval_operand op t = SOME y` by
    (drule ricf_opaque_frame_operand_defined >> disch_then (qspec_then `op` mp_tac) >>
     simp[] >> Cases_on `eval_operand op t` >> simp[]) >>
  `(!v. op <> Var v) ==> ~retpc_var fn out` by
    (strip_tac >> mp_tac (Q.INST
       [`fn` |-> `fn`, `inst` |-> `inst`, `x` |-> `out`, `op` |-> `op`]
       (SPEC_ALL assign_nonvar_output_not_retpc)) >> simp[]) >>
  `!v. op = Var v ==> (retpc_var fn out <=> retpc_var fn v)` by
    (rpt strip_tac >> mp_tac (Q.INST
       [`fn` |-> `fn`, `inst` |-> `inst`, `x` |-> `out`, `y` |-> `v`]
       (SPEC_ALL assign_output_retpc)) >> simp[]) >>
  `retpc_var fn out <=> ricf_retpc_operand fn op` by
    (Cases_on `op` >> gvs[ricf_retpc_operand_def]) >>
  `ricf_opaque_value_agree sites (op_prov G op) (op_taint rt op)
    (if retpc_var fn out then 0w else x)
    (if retpc_var fn out then 0w else y)` by
    (drule_all ricf_opaque_frame_operand_masked >> simp[]) >>
  qexists_tac `update_var out y t` >>
  conj_asm1_tac >- simp[step_inst_def, step_inst_base_opcode_eqs] >>
  gvs[] >> irule ricf_execution_bind_next >>
  simp[step_prov_def, out_prov_def, first_prov_def, step_taint_def,
    out_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    codegenRelTheory.source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  conj_tac
  >- (qexistsl_tac [`Ct`,`fuel`] >> fs[update_var_def]) >>
  qexistsl_tac [`op_taint rt op`,`op_prov G op`] >> simp[] >>
  Cases_on `op_prov G op` >> simp[]
QED
