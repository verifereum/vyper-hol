Theory frameAllocationOwnership
Ancestors
  frameOriginCache frameOriginHistory frameOriginUpdates frameOriginReachable
  ptrDiscipline venomExecSemantics venomState venomMemProps
  ptrDisciplineEmptyTaint contextCodegenRel removeUnusedSsaProofs
  venomInst venomWf finite_map list

Definition cache_has_site_def:
  cache_has_site s site <=> ?aid. FLOOKUP s.vs_allocas aid = SOME site
End

Definition saved_has_site_def:
  saved_has_site stk site <=>
    ?k aid. k < LENGTH stk /\
      FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME site
End

Definition prov_sites_def:
  prov_sites P G <=> !v site. FLOOKUP G v = SOME site ==> P site
End

Definition param_sites_def:
  param_sites P PG <=> !site. MEM (SOME site) PG ==> P site
End

(* A site that a DALLOCA allocated: at or above the initial free memory
   pointer, so above every ALLOCA site. *)
Definition dyn_site_def:
  dyn_site ctx (vs0:venom_state) (site:num # num) <=>
    ctx_has_dalloca ctx /\ w2n vs0.vs_initial_fmp <= FST site
End

Definition frame_sites_def:
  frame_sites D stk PG G s <=>
    param_sites (\site. saved_has_site stk site \/ D site) PG /\
    prov_sites (\site. cache_has_site s site \/ saved_has_site stk site \/ D site) G
End

Definition saved_sites_def:
  (saved_sites D [] <=> T) /\
  (saved_sites D (f::stk) <=>
    frame_sites D stk f.cf_params f.cf_prov f.cf_state /\ saved_sites D stk)
End

Theorem saved_has_site_cons:
  saved_has_site (f::stk) site <=>
    cache_has_site f.cf_state site \/ saved_has_site stk site
Proof
  simp[saved_has_site_def, cache_has_site_def] >> eq_tac
  >- (rpt strip_tac >> Cases_on `k` >> gvs[] >> metis_tac[]) >>
  strip_tac
  >- (qexists_tac `0` >> simp[] >> metis_tac[]) >>
  qexists_tac `SUC k` >> simp[] >> metis_tac[]
QED

Theorem prov_sites_mono:
  prov_sites P G /\ (!site. P site ==> Q site) ==> prov_sites Q G
Proof
  simp[prov_sites_def] >> metis_tac[]
QED

Theorem prov_sites_restrict:
  prov_sites P G ==> prov_sites P (DRESTRICT G keys)
Proof
  simp[prov_sites_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem prov_sites_op:
  prov_sites P G /\ op_prov G op = SOME site ==> P site
Proof
  Cases_on `op` >> simp[op_prov_def, prov_sites_def] >> metis_tac[]
QED

Theorem prov_sites_first:
  !ops. prov_sites P G /\ first_prov G ops = SOME site ==> P site
Proof
  Induct >> simp[first_prov_def] >> rpt strip_tac >>
  Cases_on `op_prov G h` >> gvs[] >> metis_tac[prov_sites_op]
QED

Theorem prov_sites_set:
  prov_sites P G /\ (!site. p = SOME site ==> P site) ==>
  prov_sites P (set_prov G outs p)
Proof
  Cases_on `outs` >> Cases_on `p` >>
  simp[set_prov_def, prov_sites_restrict] >>
  Cases_on `t` >> simp[set_prov_def, prov_sites_restrict] >>
  simp[prov_sites_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem prov_sites_phi:
  prov_sites P G /\ phi_prov prev G inst = SOME site ==> P site
Proof
  simp[phi_prov_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[prov_sites_op]
QED

Theorem prov_sites_phis:
  !insts. prov_sites P G ==> prov_sites P (phis_prov prev G insts)
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[] >> irule prov_sites_set >>
  simp[] >> metis_tac[prov_sites_phi]
QED

Theorem prov_sites_entry:
  prov_sites P G ==> prov_sites P (entry_prov fn s G)
Proof
  simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[prov_sites_phis]
QED

Theorem frame_sites_step:
  frame_sites D stk PG G s /\ step_inst fuel ctx inst s = OK s' /\
  inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode = DALLOCA ==>
    !site. out_prov PG G inst s' = SOME site ==> D site) ==>
  frame_sites D stk PG (step_prov PG G inst s')
    (s' with vs_inst_idx := idx)
Proof
  strip_tac >> fs[frame_sites_def] >>
  `prov_sites (\site. cache_has_site s' site \/ saved_has_site stk site \/ D site) G` by
    (irule prov_sites_mono >>
     qexists_tac `\site. cache_has_site s site \/ saved_has_site stk site \/ D site` >>
     simp[] >> metis_tac[cache_has_site_def, step_inst_cache_preserved]) >>
  simp[frame_sites_def, step_prov_def, cache_has_site_def] >>
  irule prov_sites_set >> simp[GSYM cache_has_site_def] >>
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = DALLOCA` >- metis_tac[] >>
  qpat_x_assum `out_prov _ _ _ _ = _` mp_tac >> simp[out_prov_def] >> strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[] >> metis_tac[cache_has_site_def]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[AllCaseEqs(), param_sites_def] >> metis_tac[MEM_EL]) >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `prov_sites (\site. cache_has_site s site \/ _) G` kall_tac >>
  drule_all prov_sites_first >> simp[]
QED

Theorem frame_sites_transport:
  frame_sites D stk PG G s /\ s'.vs_allocas = s.vs_allocas ==>
  frame_sites D stk PG G s'
Proof
  simp[frame_sites_def, prov_sites_def, cache_has_site_def] >> metis_tac[]
QED

Theorem frame_sites_entry:
  frame_sites D stk PG G s /\ enters_block fn s s1 ==>
  frame_sites D stk PG (entry_prov fn s G) s1
Proof
  strip_tac >> drule enters_block_allocas >> strip_tac >>
  `frame_sites D stk PG G s1` by metis_tac[frame_sites_transport] >>
  fs[frame_sites_def] >> simp[frame_sites_def, prov_sites_entry]
QED

Theorem frame_sites_call:
  frame_sites D stk PG G s ==>
  frame_sites D
    (<|cf_fn := fn; cf_inst := inst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)
    (MAP (op_prov G) ops) FEMPTY s1
Proof
  simp[frame_sites_def, prov_sites_def, param_sites_def,
       saved_has_site_cons, MEM_MAP] >> rpt strip_tac >>
  Cases_on `y` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem frame_sites_return:
  frame_sites D stk PG G caller /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME s' ==>
  frame_sites D stk PG (DRESTRICT G (COMPL (set outs)))
    (s' with vs_inst_idx := idx)
Proof
  strip_tac >> drule return_bind_cache >> strip_tac >>
  fs[frame_sites_def] >> simp[frame_sites_def, cache_has_site_def] >>
  irule prov_sites_restrict >> gvs[cache_has_site_def]
QED

(* A frame is suspended in the state it was reachable in, so a property
   every reachable state has holds of every saved frame too. *)
Theorem frame_reachable_saved_below_fmp:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    (!stk PG G tn fn inst s. frame_reachable vs0 ctx stk PG G tn fn inst s ==>
       allocas_below_fmp s) ==>
    EVERY (\f. allocas_below_fmp f.cf_state) stk
Proof
  ho_match_mp_tac frame_reachable_strongind >> rw[] >> metis_tac[]
QED

Theorem frame_reachable_initial_fmp:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    s.vs_initial_fmp = vs0.vs_initial_fmp /\
    EVERY (\f. f.cf_state.vs_initial_fmp = vs0.vs_initial_fmp) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rw[] >>
  imp_res_tac ctxLookupAgreeHelpersTheory.enters_block_initial_fmp >> imp_res_tac ctxLookupAgreeHelpersTheory.step_inst_initial_fmp >>
  imp_res_tac ctxLookupAgreeHelpersTheory.setup_callee_initial_fmp >> imp_res_tac ctxLookupAgreeHelpersTheory.bind_outputs_initial_fmp >>
  gvs[]
QED

(* With DALLOCA, every cache of a reachable frame and its callers lies below
   the dynamic region. *)
Theorem frame_reachable_caches_below:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ ptr_discipline lo ctx vs0 /\
  ctx_has_dalloca ctx ==>
  !k aid b sz.
    k < LENGTH ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk) /\
    FLOOKUP (SND (EL k ((fn,s.vs_allocas)::
      MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk))) aid = SOME (b,sz) ==>
    b + sz <= w2n s.vs_initial_fmp
Proof
  strip_tac >>
  `!stk PG G tn fn inst s. frame_reachable vs0 ctx stk PG G tn fn inst s ==>
     allocas_below_fmp s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `allocas_below_fmp s` by metis_tac[] >>
  drule_all frame_reachable_saved_below_fmp >> strip_tac >>
  drule frame_reachable_initial_fmp >> strip_tac >>
  qpat_x_assum `!stk PG G tn fn inst s. _` kall_tac >>
  rpt gen_tac >> Cases_on `k` >> simp[]
  >- (fs[allocas_below_fmp_def] >> metis_tac[]) >>
  strip_tac >>
  `allocas_below_fmp (EL n stk).cf_state /\
   (EL n stk).cf_state.vs_initial_fmp = vs0.vs_initial_fmp` by fs[EVERY_EL] >>
  fs[allocas_below_fmp_def] >>
  `FLOOKUP (EL n stk).cf_state.vs_allocas aid = SOME (b,sz)` by gvs[EL_MAP] >>
  metis_tac[]
QED

Theorem resolved_dalloca_output:
  inst.inst_opcode = DALLOCA /\ step_inst fuel ctx inst s = OK post /\
  inst.inst_outputs = [out] /\ lookup_var out post = SOME b ==> b = s.vs_fmp
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem frame_reachable_functions_member:
  !vs ctx ds PH H un g j t.
    frame_reachable vs ctx ds PH H un g j t ==>
    MEM g ctx.ctx_functions /\ EVERY (\d. MEM d.cf_fn ctx.ctx_functions) ds
Proof
  ho_match_mp_tac frame_reachable_ind >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[lookup_function_MEM]
QED

(* A reachable DALLOCA is an instruction of the program. *)
Theorem frame_reachable_dalloca:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx
Proof
  strip_tac >> drule frame_reachable_functions_member >> strip_tac >>
  simp[ctx_has_dalloca_def, EXISTS_MEM] >> qexists_tac `fn` >> simp[] >>
  gvs[active_inst_def, fn_insts_def,
      venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_EL]
QED

(* DALLOCA allocates at the free memory pointer, which a disciplined run
   keeps at or above the initial one. *)
Theorem frame_dalloca_floor:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ ptr_discipline lo ctx vs0 /\
  ctx_has_dalloca ctx /\ inst.inst_opcode = DALLOCA /\
  step_inst fuel ctx inst s = OK s' /\ inst.inst_outputs = [out] /\
  lookup_var out s' = SOME b ==>
  w2n vs0.vs_initial_fmp <= w2n b
Proof
  strip_tac >>
  `b = s.vs_fmp` by metis_tac[resolved_dalloca_output] >>
  `allocas_below_fmp s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `s.vs_initial_fmp = vs0.vs_initial_fmp` by metis_tac[frame_reachable_initial_fmp] >>
  gvs[allocas_below_fmp_def]
QED

Theorem frame_allocation_ownership:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    (ctx_has_dalloca ctx ==> ptr_discipline lo ctx vs0) ==>
    frame_sites (dyn_site ctx vs0) stk PG G s /\ saved_sites (dyn_site ctx vs0) stk
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- (rpt strip_tac >> simp[frame_sites_def, param_sites_def,
                           prov_sites_def, saved_sites_def])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_allocation_ownership[next]:
  rpt strip_tac >> gvs[] >>
  `inst.inst_opcode = DALLOCA ==>
   !site. out_prov PG G inst s' = SOME site ==> dyn_site ctx vs0 site` by
    (rpt strip_tac >>
     `ctx_has_dalloca ctx` by metis_tac[frame_reachable_dalloca] >>
     qpat_x_assum `out_prov _ _ _ _ = _` mp_tac >>
     simp[out_prov_def, dyn_site_def] >> rpt CASE_TAC >> rw[] >>
     `ptr_discipline lo ctx vs0` by metis_tac[] >>
     drule_all frame_dalloca_floor >> simp[]) >>
  metis_tac[frame_sites_step]
QED

Resume frame_allocation_ownership[block]:
  rpt strip_tac >> gvs[] >> simp[] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `s'.vs_allocas = s.vs_allocas` by
    (gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_preserves_allocas]) >>
  metis_tac[frame_sites_transport, frame_sites_entry]
QED

Resume frame_allocation_ownership[call]:
  rpt strip_tac >> gvs[] >> simp[saved_sites_def] >>
  metis_tac[frame_sites_call]
QED

Resume frame_allocation_ownership[ret]:
  rpt strip_tac >> gvs[saved_sites_def] >> simp[] >>
  metis_tac[frame_sites_return]
QED

Finalise frame_allocation_ownership

Theorem frame_parameter_owner:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  (ctx_has_dalloca ctx ==> ptr_discipline lo ctx vs0) /\
  (ctx_has_dalloca ctx ==> FST site < w2n vs0.vs_initial_fmp) /\
  MEM (SOME site) PG ==> saved_has_site stk site
Proof
  strip_tac >> drule_all frame_allocation_ownership >>
  simp[frame_sites_def, param_sites_def, dyn_site_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem frame_provenance_owner:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  (ctx_has_dalloca ctx ==> ptr_discipline lo ctx vs0) /\
  (ctx_has_dalloca ctx ==> FST site < w2n vs0.vs_initial_fmp) /\
  FLOOKUP G v = SOME site ==>
  cache_has_site s site \/ saved_has_site stk site
Proof
  strip_tac >> drule_all frame_allocation_ownership >>
  simp[frame_sites_def, prov_sites_def, dyn_site_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem saved_sites_suffix:
  !stk n. saved_sites D stk /\ n < LENGTH stk ==>
    frame_sites D (DROP (SUC n) stk) (EL n stk).cf_params
      (EL n stk).cf_prov (EL n stk).cf_state
Proof
  Induct >> simp[saved_sites_def] >> Cases_on `n` >> simp[]
QED

Theorem frame_saved_owners:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  (ctx_has_dalloca ctx ==> ptr_discipline lo ctx vs0) /\ n < LENGTH stk ==>
  frame_sites (dyn_site ctx vs0) (DROP (SUC n) stk) (EL n stk).cf_params
    (EL n stk).cf_prov (EL n stk).cf_state
Proof
  metis_tac[frame_allocation_ownership, saved_sites_suffix]
QED

(* A parameter tag is preserved by copying but never by ALLOCA.  This is
   a semantic fact: it needs no SSA or static pointer-analysis hypotheses. *)
Definition parameter_origin_sites_def:
  parameter_origin_sites PG om <=>
    !v k site. FLOOKUP om v = SOME (OriginParameter k,site) ==>
      MEM (SOME site) PG
End

Theorem parameter_origin_sites_restrict:
  parameter_origin_sites PG om ==>
  parameter_origin_sites PG (DRESTRICT om keys)
Proof
  simp[parameter_origin_sites_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem parameter_origin_sites_out:
  parameter_origin_sites PG om /\
  origin_out PG om inst s = SOME (OriginParameter k,site) ==>
  MEM (SOME site) PG
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- gvs[origin_out_alloca] >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- gvs[origin_out_dalloca] >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[origin_out_param] >> metis_tac[MEM_EL]) >>
  drule_all origin_out_inherited >> strip_tac >>
  gvs[origin_op_some, parameter_origin_sites_def] >> metis_tac[]
QED

Theorem parameter_origin_sites_step:
  parameter_origin_sites PG om ==>
  parameter_origin_sites PG (origin_step PG om inst s)
Proof
  simp[parameter_origin_sites_def] >> rpt strip_tac >>
  drule origin_step_lookup >> strip_tac
  >- metis_tac[] >>
  metis_tac[parameter_origin_sites_out, parameter_origin_sites_def]
QED

Theorem parameter_origin_sites_entry:
  parameter_origin_sites PG om ==>
  parameter_origin_sites PG (origin_entry fn s om)
Proof
  simp[origin_entry_def] >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  simp[parameter_origin_sites_def] >> rpt strip_tac >>
  drule origin_phis_lookup >> strip_tac
  >- (gvs[parameter_origin_sites_def] >> metis_tac[]) >>
  gvs[origin_phi_some, origin_op_some, parameter_origin_sites_def] >> metis_tac[]
QED

Theorem frame_parameter_origin_sites:
  !vs0 ctx stk PG G tn fn inst s oms om.
    origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
    parameter_origin_sites PG om /\
    LIST_REL (\f m. parameter_origin_sites f.cf_params m) stk oms
Proof
  ho_match_mp_tac origin_frame_reachable_ind >> rpt conj_tac
  >- simp[parameter_origin_sites_def]
  >- (rpt strip_tac >> simp[] >> metis_tac[parameter_origin_sites_step])
  >- (rpt strip_tac >> simp[] >> metis_tac[parameter_origin_sites_entry])
  >- (rpt strip_tac >> fs[parameter_origin_sites_def] >> metis_tac[])
  >> rpt strip_tac >> gvs[] >> metis_tac[parameter_origin_sites_restrict]
QED

Theorem joint_incoming_allocation_owner:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  (ctx_has_dalloca ctx ==> ptr_discipline lo ctx vs0) /\
  (ctx_has_dalloca ctx ==> FST site < w2n vs0.vs_initial_fmp) /\
  FLOOKUP om v = SOME (OriginParameter p,site) ==>
  ?k aid. k < LENGTH stk /\
    FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME site
Proof
  strip_tac >> drule joint_origin_history_erasure >> strip_tac >>
  drule frame_parameter_origin_sites >> strip_tac >>
  `MEM (SOME site) PG` by metis_tac[parameter_origin_sites_def] >>
  metis_tac[frame_parameter_owner, origin_frame_erasure, saved_has_site_def]
QED
