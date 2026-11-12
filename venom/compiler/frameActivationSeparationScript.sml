Theory frameActivationSeparation
Ancestors
  frameActivationCache frameJointTransition frameOriginCache frameOriginHistory
  ptrDiscipline venomMemProps venomMemDefs venomExecSemantics venomState venomInstProofs1
  finite_map list arithmetic venomInst

(* Adjacent frontiers separate the current cache from every saved cache.
   Returns remove the top component instead of requiring frontier monotonicity. *)
Definition frame_cache_separated_def:
  (frame_cache_separated [] s <=> alloca_inv s) /\
  (frame_cache_separated (f::stk) s <=>
    alloca_inv s /\ frame_cache_separated stk f.cf_state /\
    f.cf_state.vs_alloca_next <= s.vs_alloca_next /\
    allocas_from f.cf_state.vs_alloca_next s)
End

Theorem alloca_inv_byte_unique:
  alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  FLOOKUP s.vs_allocas aid' = SOME (b',sz') /\
  b <= byte /\ byte < b + sz /\ b' <= byte /\ byte < b' + sz' ==>
  aid = aid' /\ b = b' /\ sz = sz'
Proof
  strip_tac >>
  `aid = aid'` by
    (spose_not_then assume_tac >>
     fs[alloca_inv_def, allocas_non_overlapping_def] >>
     first_x_assum drule_all >> decide_tac) >> gvs[]
QED

Theorem allocas_from_exec_alloca:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ exec_alloca inst s n = OK s' ==>
  allocas_from lo s'
Proof
  rw[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  gvs[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `aid = inst.inst_id` >> gvs[] >> metis_tac[]
QED

Theorem allocas_from_step:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode <> INVOKE ==>
  allocas_from lo s'
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >>
      metis_tac[allocas_from_exec_alloca]) >>
  `s'.vs_allocas = s.vs_allocas` by metis_tac[step_inst_base_preserves_allocas] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem noninvoke_frontier_mono:
  step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode <> INVOKE ==>
  s.vs_alloca_next <= s'.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
      metis_tac[exec_alloca_alloca_next_mono]) >>
  gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_preserves_alloca_next, LESS_EQ_REFL]
QED

Theorem frame_cache_separated_step:
  frame_cache_separated stk s /\ step_inst fuel ctx inst s = OK s' /\
  inst.inst_opcode <> INVOKE ==> frame_cache_separated stk s'
Proof
  Cases_on `stk` >> simp[frame_cache_separated_def] >> strip_tac
  >- metis_tac[alloca_inv_step_inst] >>
  drule_all noninvoke_frontier_mono >> strip_tac >>
  drule_all allocas_from_step >> strip_tac >>
  simp[] >> metis_tac[alloca_inv_step_inst, LESS_EQ_TRANS]
QED

Theorem frame_cache_separated_transport:
  frame_cache_separated stk s /\ s'.vs_allocas = s.vs_allocas /\
  s'.vs_alloca_next = s.vs_alloca_next ==> frame_cache_separated stk s'
Proof
  Cases_on `stk` >> strip_tac >>
  gvs[frame_cache_separated_def, alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def, allocas_from_def] >> metis_tac[]
QED

Theorem enters_block_allocation_frame:
  enters_block fn s s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >>
  drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem frame_cache_separated_entry:
  frame_cache_separated stk s /\ enters_block fn s s' ==>
  frame_cache_separated stk s'
Proof
  metis_tac[frame_cache_separated_transport, enters_block_allocation_frame]
QED

Theorem frame_cache_separated_push:
  frame_cache_separated stk f.cf_state /\ s.vs_allocas = FEMPTY /\
  s.vs_alloca_next = f.cf_state.vs_alloca_next ==>
  frame_cache_separated (f::stk) s
Proof
  simp[frame_cache_separated_def, allocas_from_def] >>
  metis_tac[alloca_inv_empty]
QED

Theorem frame_cache_separated_pop:
  frame_cache_separated (f::stk) s /\ s'.vs_allocas = f.cf_state.vs_allocas /\
  s'.vs_alloca_next = f.cf_state.vs_alloca_next ==>
  frame_cache_separated stk s'
Proof
  simp[frame_cache_separated_def] >> metis_tac[frame_cache_separated_transport]
QED

Theorem setup_callee_allocation_frame:
  setup_callee fn args s = SOME cs ==>
  cs.vs_allocas = FEMPTY /\ cs.vs_alloca_next = s.vs_alloca_next
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem return_bind_allocation_frame:
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME s' ==>
  s'.vs_allocas = caller.vs_allocas /\ s'.vs_alloca_next = caller.vs_alloca_next
Proof
  strip_tac >>
  `s'.vs_allocas = (adopt_return_fmp ret (merge_callee_state caller callee)).vs_allocas` by
    (drule (bind_outputs_preserves |> Q.ISPEC `\s. s.vs_allocas` |> SIMP_RULE (srw_ss()) [update_var_def]) >> simp[]) >>
  `s'.vs_alloca_next = (adopt_return_fmp ret (merge_callee_state caller callee)).vs_alloca_next` by
    (drule (bind_outputs_preserves |> Q.ISPEC `\s. s.vs_alloca_next` |> SIMP_RULE (srw_ss()) [update_var_def]) >> simp[]) >>
  Cases_on `ret.iret_adopt_fmp` >> gvs[merge_callee_state_def, adopt_return_fmp_def]
QED

Theorem frame_cache_separated_idx:
  frame_cache_separated stk (s with vs_inst_idx := idx) <=>
  frame_cache_separated stk s
Proof
  Cases_on `stk` >>
  simp[frame_cache_separated_def, alloca_inv_def, alloca_next_valid_def,
       allocas_non_overlapping_def, allocas_from_def]
QED

Theorem frame_cache_separated_transition:
  frame_cache_separated stk s /\
  joint_transition ctx (JointConfig stk PG G tn fn inst s oms om hs h) ev
    (JointConfig stk' PG' G' tn' fn' inst' s' oms' om' hs' h') ==>
  frame_cache_separated stk' s'
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[]
  >- metis_tac[frame_cache_separated_step, frame_cache_separated_idx]
  >- (`inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      metis_tac[frame_cache_separated_step, frame_cache_separated_entry])
  >- (drule setup_callee_allocation_frame >> strip_tac >>
      irule frame_cache_separated_entry >> goal_assum (drule_at Any) >>
      irule frame_cache_separated_push >> simp[])
  >> drule return_bind_allocation_frame >> strip_tac >>
  simp[frame_cache_separated_idx] >> metis_tac[frame_cache_separated_pop]
QED

Theorem joint_history_cache_separated:
  !vs0 ctx stk PG G tn fn inst s oms om hs h.
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
  vs0.vs_allocas = FEMPTY ==> frame_cache_separated stk s
Proof
  ho_match_mp_tac joint_origin_history_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- (strip_tac >> simp[frame_cache_separated_def] >>
      irule alloca_inv_empty >>
      drule enters_block_allocation_frame >> simp[]) >>
  strip_tac >> res_tac >> irule frame_cache_separated_transition >>
  goal_assum (drule_at (Pat `frame_cache_separated _ _`)) >>
  metis_tac[joint_transition_rules]
QED

Theorem joint_reachable_cache_separated:
  joint_config_reachable vs0 ctx (JointConfig stk PG G tn fn inst s oms om hs h) /\
  vs0.vs_allocas = FEMPTY ==> frame_cache_separated stk s
Proof
  simp[joint_config_reachable_def] >> metis_tac[joint_history_cache_separated]
QED

Theorem frame_cache_separated_local:
  frame_cache_separated stk s ==> alloca_inv s
Proof
  Cases_on `stk` >> simp[frame_cache_separated_def]
QED

Theorem frame_cache_saved_bound:
  !stk s k aid b sz.
  frame_cache_separated stk s /\ k < LENGTH stk /\
  FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME (b,sz) ==>
  b + sz <= s.vs_alloca_next
Proof
  Induct >> simp[frame_cache_separated_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `k` >> gvs[]
  >- (drule frame_cache_separated_local >>
      simp[alloca_inv_def, alloca_next_valid_def] >>
      metis_tac[LESS_EQ_TRANS]) >>
  first_x_assum drule_all >> decide_tac
QED

Theorem frame_cache_current_saved_disjoint:
  frame_cache_separated stk s /\ k < LENGTH stk /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  FLOOKUP (EL k stk).cf_state.vs_allocas aid' = SOME (b',sz') ==>
  b' + sz' <= b
Proof
  Cases_on `stk` >> simp[frame_cache_separated_def] >> strip_tac >>
  `h.cf_state.vs_alloca_next <= b` by metis_tac[allocas_from_def] >>
  Cases_on `k` >> gvs[]
  >- (drule frame_cache_separated_local >>
      simp[alloca_inv_def, alloca_next_valid_def] >>
      metis_tac[LESS_EQ_TRANS]) >>
  drule_all frame_cache_saved_bound >> decide_tac
QED

Theorem activation_cache_cons_saved:
  d <= LENGTH stk ==>
  (activation_cache (JointConfig (f::stk) PG G tn current inst s oms om hs hist)
      d owner aid site <=>
   activation_cache (JointConfig stk PG G tn f.cf_fn inst f.cf_state oms om hs hist)
      d owner aid site)
Proof
  strip_tac >> Cases_on `d = LENGTH stk` >>
  simp[activation_cache_def] >>
  `LENGTH stk - d = SUC (LENGTH stk - SUC d)` by decide_tac >>
  simp[]
QED

Theorem frame_cache_activation_current_unique:
  frame_cache_separated stk s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  activation_cache (JointConfig stk PG G tn fn inst s oms om hs h) d owner aid' (b',sz') /\
  b <= byte /\ byte < b + sz /\ b' <= byte /\ byte < b' + sz' ==>
  d = LENGTH stk /\ owner = fn /\ aid = aid' /\ b = b' /\ sz = sz'
Proof
  simp[activation_cache_def] >> strip_tac
  >- metis_tac[frame_cache_separated_local, alloca_inv_byte_unique] >>
  `LENGTH stk - SUC d < LENGTH stk` by decide_tac >>
  drule_all frame_cache_current_saved_disjoint >> strip_tac >> fs[]
QED

Theorem frame_cache_activation_byte_unique:
  !stk s PG G tn fn inst oms om hs h d owner aid b sz d' owner' aid' b' sz' byte.
  frame_cache_separated stk s /\
  activation_cache (JointConfig stk PG G tn fn inst s oms om hs h) d owner aid (b,sz) /\
  activation_cache (JointConfig stk PG G tn fn inst s oms om hs h) d' owner' aid' (b',sz') /\
  b <= byte /\ byte < b + sz /\ b' <= byte /\ byte < b' + sz' ==>
  d = d' /\ owner = owner' /\ aid = aid' /\ b = b' /\ sz = sz'
Proof
  Induct
  >- (simp[activation_cache_def, frame_cache_separated_def] >>
      metis_tac[alloca_inv_byte_unique]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `d = LENGTH (h::stk)`
  >- (gvs[] >> qpat_x_assum `activation_cache _ (SUC (LENGTH stk)) _ _ _` mp_tac >>
      simp[NoAsms, activation_cache_def] >> rpt strip_tac >> gvs[] >>
      drule_all frame_cache_activation_current_unique >> simp[]) >>
  Cases_on `d' = LENGTH (h::stk)`
  >- (gvs[] >> qpat_x_assum `activation_cache _ (SUC (LENGTH stk)) _ _ _` mp_tac >>
      simp[NoAsms, activation_cache_def] >> rpt strip_tac >> gvs[] >>
      drule_all frame_cache_activation_current_unique >> simp[]) >>
  `d <= LENGTH stk /\ d' <= LENGTH stk` by
    (imp_res_tac activation_cache_depth >> fs[activation_depth_def] >> decide_tac) >>
  fs[activation_cache_cons_saved, frame_cache_separated_def] >>
  first_x_assum irule >>
  (conj_tac >- (qexists_tac `byte` >> simp[])) >>
  goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >> simp[]
QED

Theorem joint_activation_cache_byte_unique:
  joint_config_reachable vs0 ctx q /\ vs0.vs_allocas = FEMPTY /\
  activation_cache q d owner aid (b,sz) /\
  activation_cache q d' owner' aid' (b',sz') /\
  b <= byte /\ byte < b + sz /\ b' <= byte /\ byte < b' + sz' ==>
  d = d' /\ owner = owner' /\ aid = aid' /\ b = b' /\ sz = sz'
Proof
  Cases_on `q` >> strip_tac >>
  drule_all joint_reachable_cache_separated >> strip_tac >>
  irule frame_cache_activation_byte_unique >>
  (conj_tac >- (qexists_tac `byte` >> simp[])) >>
  goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >> simp[]
QED
