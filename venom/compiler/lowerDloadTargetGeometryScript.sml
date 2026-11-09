Theory lowerDloadTargetGeometry
Ancestors
  lowerDloadAllocationOwner lowerDloadAllocationMemory lowerDloadScratchBudget
  lowerDloadFrameCertificate lowerDloadOwnership lowerDloadPairedBoundary
  venomExecSemantics venomState ptrDiscipline finite_map pred_set list arithmetic

(* Unlike ld_frame_bound_alloca, this does not erase target scratch sites. *)
Theorem ld_embedded_alloca_geometry:
  i.inst_outputs = [out] /\ exec_alloca i t n = OK t' /\
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t /\
  i.inst_id NOTIN keys /\
  ld_select_alloca k H i t' = (k',H') /\ i.inst_opcode = ALLOCA /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next ==>
  ld_frame_bound t'.vs_alloca_next H' BP (ld_step_prov BP BH H' i) /\
  ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next
Proof
  strip_tac >>
  `FLOOKUP H i.inst_id = NONE ==> FLOOKUP t.vs_allocas i.inst_id = NONE` by
    (strip_tac >>
     drule ld_frame_embedding_selection >>
     disch_then (qspec_then `i.inst_id` mp_tac) >>
     simp[ld_owned_selection_def] >> strip_tac >>
     `FLOOKUP s.vs_allocas i.inst_id = NONE` by
       metis_tac[ld_frame_embedding_source, ld_erase_lookup, optionTheory.OPTION_MAP_EQ_NONE] >>
     metis_tac[lowerDloadAllocationTheory.ld_alloc_account_old_absent]) >>
  `t.vs_alloca_next <= t'.vs_alloca_next /\
   (!id site. FLOOKUP H' id = SOME site ==>
     FLOOKUP H id = SOME site \/
     FST (SND site) + SND (SND site) = t'.vs_alloca_next)` by
    (Cases_on `FLOOKUP H i.inst_id` >>
     gvs[exec_alloca_def, update_var_def, AllCaseEqs(),
         ld_select_alloca_def, FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (irule ld_frame_bound_step >> simp[ld_frame_bound_def] >>
      gen_tac >> strip_tac >>
      `ld_selected H BP BH site \/
       FST (SND site) + SND (SND site) = t'.vs_alloca_next` by
        (gvs[ld_selected_def] >> metis_tac[]) >>
      gvs[ld_frame_bound_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[ld_stack_bound_mono, LESS_EQ_TRANS]
QED

Theorem ld_scratch_alloca_geometry:
  i.inst_outputs = [out] /\ exec_alloca i t (32w:bytes32) = OK t' /\
  ld_alloc_account keys d A s t /\ i.inst_id IN keys /\
  d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next ==>
  ld_frame_bound t'.vs_alloca_next H BP BH /\
  ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next /\
  ld_alloc_account keys d (i.inst_id INSERT A) s t' /\
  t'.vs_alloca_next = s.vs_alloca_next +
    32 * SUM (MAP CARD ((i.inst_id INSERT A)::suspended))
Proof
  strip_tac >>
  `t.vs_alloca_next <= t'.vs_alloca_next` by
    (gvs[exec_alloca_def, update_var_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  drule_all lowerDloadAllocationTheory.ld_alloc_account_scratch >> strip_tac >>
  drule lowerDloadAllocationTheory.ld_alloc_account_frontier >> strip_tac >>
  simp[LEFT_ADD_DISTRIB] >>
  metis_tac[ld_frame_bound_mono, ld_stack_bound_mono, LESS_EQ_TRANS, ADD_COMM]
QED

Theorem ld_call_geometry:
  setup_callee callee args t = SOME cs /\ enters_block callee cs t1 /\
  setup_callee source sargs s = SOME ss /\ enters_block source ss s1 /\
  ld_alloc_account keys d A s t /\ FINITE child_keys /\
  d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next ==>
  ld_frame_bound t1.vs_alloca_next FEMPTY (MAP (ld_op_prov BH) ops) FEMPTY /\
  ld_stack_bound t1.vs_alloca_next
    (<| lf_fn := caller; lf_inst := ins; lf_state := t;
        lf_params := BP; lf_prov := BH; lf_tvar := un.t_var;
        lf_local := H |> :: gstk) /\ lo <= t1.vs_alloca_next /\
  ld_alloc_account child_keys (32 * SUM (MAP CARD (A::suspended))) {} s1 t1 /\
  d + 32 * CARD A = 32 * SUM (MAP CARD (A::suspended))
Proof
  strip_tac >>
  `ld_alloc_account child_keys (d + 32 * CARD A) {} ss cs` by
    (irule lowerDloadAllocationTheory.ld_alloc_account_enter >> metis_tac[]) >>
  `cs.vs_alloca_next = t.vs_alloca_next` by
    metis_tac[calleeTransportTheory.setup_callee_shared_fields] >>
  `t1.vs_allocas = cs.vs_allocas /\ t1.vs_alloca_next = cs.vs_alloca_next` by
    metis_tac[ld_enters_block_allocation_fields] >>
  `s1.vs_allocas = ss.vs_allocas /\ s1.vs_alloca_next = ss.vs_alloca_next` by
    metis_tac[ld_enters_block_allocation_fields] >>
  `ld_alloc_account child_keys (d + 32 * CARD A) {} s1 t1` by
    (irule lowerDloadAllocationTheory.ld_alloc_account_transport >> metis_tac[]) >>
  gvs[ld_stack_bound_def, LEFT_ADD_DISTRIB] >>
  metis_tac[ld_frame_bound_call, ADD_COMM]
QED

Theorem ld_return_geometry:
  ld_stack_bound n (g::gstk) /\ lo <= g.lf_state.vs_alloca_next /\
  ld_saved_embedded V E keys d A f g /\
  d = 32 * SUM (MAP CARD suspended) /\
  bind_outputs f.lf_inst.inst_outputs sret.iret_values
    (adopt_return_fmp sret (merge_callee_state f.lf_state s_end)) = SOME s' /\
  bind_outputs g.lf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.lf_state t_end)) = SOME t' ==>
  ld_frame_bound t'.vs_alloca_next g.lf_local g.lf_params
    (DRESTRICT g.lf_prov (COMPL (set g.lf_inst.inst_outputs))) /\
  ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next /\
  ld_alloc_account keys d A s' t' /\
  t'.vs_alloca_next = s'.vs_alloca_next + 32 * SUM (MAP CARD (A::suspended))
Proof
  strip_tac >>
  `s'.vs_allocas = f.lf_state.vs_allocas /\
   s'.vs_alloca_next = f.lf_state.vs_alloca_next` by
    (rev_drule ld_bind_outputs_allocas >> strip_tac >>
     rev_drule calleeTransportTheory.bind_outputs_shared_fields >> strip_tac >>
     gvs[adopt_return_fmp_allocas, merge_callee_state_def]) >>
  `t'.vs_allocas = g.lf_state.vs_allocas /\
   t'.vs_alloca_next = g.lf_state.vs_alloca_next` by
    (drule ld_bind_outputs_allocas >> strip_tac >>
     drule calleeTransportTheory.bind_outputs_shared_fields >> strip_tac >>
     gvs[adopt_return_fmp_allocas, merge_callee_state_def]) >>
  `ld_alloc_account keys d A s' t'` by
    (irule lowerDloadAllocationTheory.ld_alloc_account_transport >>
     metis_tac[ld_saved_embedded_account]) >>
  drule lowerDloadAllocationTheory.ld_alloc_account_frontier >> strip_tac >>
  gvs[ld_stack_bound_def, LEFT_ADD_DISTRIB] >>
  metis_tac[ld_frame_bound_restrict, ADD_COMM]
QED

Theorem ld_paired_selected_geometry[local]:
  (!id. ld_owned_selection E (FLOOKUP L id) (FLOOKUP H id)) /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  ld_selected L AP AG (owner,(bs,sz)) /\
  ld_site_entry E owner bs bt sz ==>
  ld_selected H BP BH (owner,(bt,sz))
Proof
  strip_tac >>
  `!ps. MEM ps AP ==> ?pt. MEM pt BP /\ ld_owned_selection E ps pt` by
    (gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  qpat_x_assum `ld_selected _ _ _ _` mp_tac >>
  simp[ld_selected_def] >> strip_tac
  >- (qpat_x_assum `!id. _` (qspec_then `id` mp_tac) >>
      gvs[ld_owned_selection_def, lowerDloadLifetimeTheory.ld_site_entry_def] >>
      metis_tac[])
  >- (first_x_assum drule >>
      gvs[ld_owned_selection_def, lowerDloadLifetimeTheory.ld_site_entry_def] >>
      metis_tac[]) >>
  qpat_x_assum `!v. _` (qspec_then `v` mp_tac) >>
  gvs[ld_owned_selection_def, lowerDloadLifetimeTheory.ld_site_entry_def] >>
  metis_tac[]
QED

Theorem ld_paired_live_endpoints:
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) astk gstk /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk ==>
  !owner bs bt sz. ld_live astk L AP AG (owner,(bs,sz)) /\
    ld_site_entry E owner bs bt sz ==> bt + sz <= t.vs_alloca_next
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `!f. MEM f astk ==> ?g. MEM g gstk /\
      (?V keys d A. ld_saved_embedded V E keys d A f g)` by
    (gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  qpat_x_assum `ld_live _ _ _ _ _` mp_tac >>
  simp[ld_live_def] >> strip_tac
  >- (`ld_selected H BP BH (owner,(bt,sz))` by
        (irule ld_paired_selected_geometry >>
         metis_tac[ld_frame_embedding_selection]) >>
      gvs[ld_frame_bound_def] >>
      first_x_assum (qspec_then `(owner,(bt,sz))` mp_tac) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  `ld_selected g.lf_local g.lf_params g.lf_prov (owner,(bt,sz))` by
    (irule ld_paired_selected_geometry >>
     metis_tac[ld_saved_embedded_params, ld_saved_embedded_prov,
               ld_saved_embedded_layout, ld_frame_embedding_selection]) >>
  drule_all ld_stack_bound_member >> strip_tac >>
  gvs[ld_frame_bound_def] >>
  first_x_assum (qspec_then `(owner,(bt,sz))` mp_tac) >> simp[]
QED

Theorem ld_geometry_initial_charge:
  s.vs_allocas = FEMPTY /\ FINITE keys /\ lo <= s.vs_alloca_next ==>
  ld_alloc_account keys 0 {} s s /\
  ld_frame_bound s.vs_alloca_next FEMPTY [] FEMPTY /\
  ld_stack_bound s.vs_alloca_next [] /\ lo <= s.vs_alloca_next
Proof
  simp[lowerDloadAllocationTheory.ld_alloc_account_init,
       ld_frame_bound_def, ld_selected_def, ld_stack_bound_def]
QED

Theorem ld_charged_frontier_budget:
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn :: MAP (\f. f.cf_fn) stk) /\
  ld_alloc_account keys d A s t /\ d = 32 * SUM (MAP CARD suspended) /\
  dload_headroom_ok C fn inst s ==>
  t.vs_alloca_next <= s.vs_alloca_next + 32 * ctx_dload_count C /\
  t.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule_all ld_stack_scratch_budget >>
  simp[LEFT_ADD_DISTRIB] >> strip_tac >>
  `d + 32 * CARD A <= 32 * ctx_dload_count C` by decide_tac >>
  conj_tac
  >- (drule lowerDloadAllocationTheory.ld_alloc_account_frontier >> decide_tac) >>
  irule lowerDloadAllocationTheory.ld_alloc_account_nowrap >> metis_tac[]
QED
