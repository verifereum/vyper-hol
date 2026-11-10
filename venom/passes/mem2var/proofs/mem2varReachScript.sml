(* Facts about source states actually reached from the pipeline entry. *)
Theory mem2varReach
Ancestors
  venomFnInstsProofs mem2varInvariant mem2varDefs mem2varProofs ptrDiscipline unitTransformDefs
  venomWf venomMemDefs venomMemProps venomExecSemantics venomState
  pointerConfinedDefs pointerConfinedProps contextCodegenRel
  ctxLookupAgreeHelpers contextCodegenRelProps venomExecProofs
  finite_map list words dfgAnalysisProps passSharedDefs execEquivParamBase

Theorem m2v_call_free_reachable[local]:
  !vs ctx stk PG G tn current inst s.
    frame_reachable vs ctx stk PG G tn current inst s ==>
    !name fn.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) ==>
      stk = [] /\ PG = [] /\ current = fn /\ active_inst fn inst s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[]
  >- (drule_all EVERY_active_inst >> simp[])
  >> gvs[EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem m2v_call_free_invariant[local]:
  !vs ctx stk PG G tn current inst s.
    frame_reachable vs ctx stk PG G tn current inst s ==>
    !name fn Inv.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
      codegen_reachability_package Inv ctx vs ==>
      stk = [] /\ PG = [] /\ current = fn /\ Inv ctx fn inst s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[]
  >- (qpat_x_assum `codegen_reachability_package _ _ _` mp_tac >>
      simp[codegen_reachability_package_def] >> strip_tac >>
      gvs[fn_entry_inv_def] >> metis_tac[])
  >- (first_x_assum (qspec_then `Inv` assume_tac) >> gvs[] >>
      qpat_x_assum `codegen_reachability_package _ _ _` mp_tac >>
      simp[codegen_reachability_package_def] >> strip_tac >>
      drule_all reachability_closed_next >> simp[])
  >- (first_x_assum (qspec_then `Inv` assume_tac) >> gvs[] >>
      qpat_x_assum `codegen_reachability_package _ _ _` mp_tac >>
      simp[codegen_reachability_package_def] >> strip_tac >>
      drule_all reachability_closed_block >> simp[])
  >- (first_x_assum (qspec_then `Inv` assume_tac) >> gvs[] >> drule_all EVERY_active_inst >> simp[])
  >> first_x_assum (qspec_then `Inv` assume_tac) >>
  gvs[EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem m2v_enters_block_alloca_inv[local]:
  enters_block fn s s' /\ alloca_inv s ==> alloca_inv s'
Proof
  rw[enters_block_def] >>
  drule_then strip_assume_tac eval_phis_preserves_alloca_fields >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem m2v_call_free_alloca_inv[local]:
  !vs ctx stk PG G tn current inst s.
    frame_reachable vs ctx stk PG G tn current inst s ==>
    !name fn.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
      o1_initial_state_ok vs ==>
      stk = [] /\ PG = [] /\ current = fn /\ alloca_inv s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (irule m2v_enters_block_alloca_inv >> goal_assum (drule_at Any) >>
      irule alloca_inv_empty >> gvs[o1_initial_state_ok_def])
  >- (drule_all alloca_inv_step_inst >> strip_tac >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (irule m2v_enters_block_alloca_inv >> goal_assum (drule_at Any) >>
      drule_all alloca_inv_step_inst >> simp[])
  >- (drule_all EVERY_active_inst >> simp[])
  >> gvs[EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem m2v_reachable_raw_bound[local]:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
  raw_unit_memory_ok ctx vs /\
  frame_reachable vs ctx [] [] G tn fn inst s ==>
  s.vs_alloca_next < dimword (:256) /\ inst_mem_ok_in_fn fn inst s
Proof
  strip_tac >> drule raw_unit_memory_ok_invariant >> strip_tac >>
  drule m2v_call_free_invariant >>
  disch_then (qspecl_then [`name`, `fn`, `Inv`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem m2v_enters_block_fresh[local]:
  enters_block fn s s' /\ m2v_fresh_names_disjoint fn /\
  m2v_fresh_undef fn s ==> m2v_fresh_undef fn s'
Proof
  rw[enters_block_def, m2v_fresh_undef_def] >>
  drule_then strip_assume_tac venomInstTheory.selected_block_mem >>
  `FLOOKUP s_phi.vs_vars v = FLOOKUP s.vs_vars v` by
    (irule eval_phis_flookup_not_phi_output >>
     goal_assum (drule_at Any) >>
     gvs[m2v_fresh_names_disjoint_def] >> metis_tac[MEM_fn_insts]) >>
  gvs[lookup_var_def]
QED

Theorem m2v_enters_block_bridge[local]:
  enters_block fn s s' /\ wf_function fn /\ wf_ssa fn /\
  alloca_bridge fn s ==> alloca_bridge fn s'
Proof
  rw[enters_block_def] >>
  drule_then strip_assume_tac venomInstTheory.selected_block_mem >>
  drule_then strip_assume_tac eval_phis_preserves_alloca_fields >>
  simp[alloca_bridge_def] >> rpt strip_tac >>
  `lookup_var ao s_phi = lookup_var ao s` by
    (simp[lookup_var_def] >>
     irule eval_phis_flookup_not_phi_output >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     rename1 `MEM phi bb.bb_instructions` >>
     `MEM phi (fn_insts fn)` by metis_tac[MEM_fn_insts] >>
     `phi = inst` by
       (irule ssa_alloca_output_unique >>
        conj_tac
        >- (qexists `fn` >> gvs[wf_ssa_def]) >>
        qexists `ao` >> simp[]) >> gvs[]) >>
  gvs[lookup_var_def, alloca_bridge_def] >> metis_tac[]
QED

Theorem m2v_call_free_bridge_fresh[local]:
  !vs ctx stk PG G tn current inst s.
    frame_reachable vs ctx stk PG G tn current inst s ==>
    !name fn.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
      wf_function fn /\ wf_ssa fn /\ o1_initial_state_ok vs /\
      raw_unit_memory_ok ctx vs /\ m2v_fresh_names_disjoint fn ==>
      stk = [] /\ PG = [] /\ current = fn /\
      alloca_bridge fn s /\ m2v_fresh_undef fn s
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (conj_tac
      >- (irule m2v_enters_block_bridge >>
          simp[] >> goal_assum (drule_at Any) >> simp[] >>
          irule alloca_bridge_undef >>
          gvs[o1_initial_state_ok_def, lookup_var_def]) >>
      irule m2v_enters_block_fresh >> simp[] >>
      goal_assum (drule_at Any) >>
      gvs[o1_initial_state_ok_def, m2v_fresh_undef_def, lookup_var_def])
  >- (drule_all m2v_reachable_raw_bound >> strip_tac >>
      drule m2v_call_free_alloca_inv >> simp[] >> strip_tac >>
      `MEM inst (fn_insts current)` by
        (gvs[active_inst_def] >> metis_tac[MEM_fn_insts, EL_MEM]) >>
      gvs[wf_ssa_def] >> drule_all alloca_bridge_step >> strip_tac >>
      drule_all m2v_fresh_undef_preserved_step >>
      simp[vs_inst_idx_update_transparent_export])
  >- (`MEM inst (fn_insts current)` by
        (gvs[active_inst_def] >> metis_tac[MEM_fn_insts, EL_MEM]) >>
      `inst.inst_opcode <> INVOKE` by gvs[EVERY_MEM] >>
      drule_all m2v_reachable_raw_bound >> strip_tac >>
      drule m2v_call_free_alloca_inv >> simp[] >> strip_tac >>
      `alloca_bridge current s'` by
        (gvs[wf_ssa_def] >> drule_all alloca_bridge_step >> simp[]) >>
      `m2v_fresh_undef current s'` by
        (drule_all m2v_fresh_undef_preserved_step >> simp[]) >>
      conj_tac
      >- (drule_all m2v_enters_block_bridge >> simp[]) >>
      drule_all m2v_enters_block_fresh >> simp[])
  >- (drule_all EVERY_active_inst >> simp[])
  >> gvs[EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem m2v_root_use[local]:
  m2v_can_promote_alloca v (dfg_get_uses (dfg_build_function fn) v) /\
  MEM i (fn_insts fn) /\ MEM (Var v) i.inst_operands ==>
  m2v_is_pointer_use v i
Proof
  strip_tac >>
  `MEM i (dfg_get_uses (dfg_build_function fn) v)` by
    (irule dfg_build_function_uses_complete >>
     simp[] >> qpat_x_assum `MEM (Var v) _` mp_tac >>
     qspec_tac (`i.inst_operands`, `ops`) >>
     Induct >> simp[dfgDefsTheory.operand_vars_def] >>
     Cases_on `h` >> simp[dfgDefsTheory.operand_var_def] >> metis_tac[]) >>
  gvs[m2v_can_promote_alloca_def, EVERY_MEM]
QED

Theorem m2v_root_no_propagating_use[local]:
  m2v_can_promote_alloca v (dfg_get_uses (dfg_build_function fn) v) /\
  MEM i (fn_insts fn) /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB \/
   i.inst_opcode = ASSIGN \/ i.inst_opcode = PHI) ==>
  ~MEM (Var v) i.inst_operands
Proof
  strip_tac >> strip_tac >> drule_all m2v_root_use >>
  gvs[m2v_is_pointer_use_def]
QED

Theorem m2v_scan_contains_root[local]:
  !xs dfg ctr ps fresh a v w.
    ((?p sz. MEM (v,p,sz) ps) \/
     (MEM a xs /\ a.inst_outputs = [v] /\ a.inst_operands = [Lit w] /\
      m2v_can_promote_alloca v (dfg_get_uses dfg v))) ==>
    ?p sz. MEM (v,p,sz)
      (FST (SND (FOLDL (m2v_scan_step dfg) (ctr,ps,fresh) xs)))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `m2v_scan_step dfg (ctr,ps,fresh) h` >>
  PairCases_on `r` >> simp[] >> first_x_assum irule >>
  gvs[m2v_scan_step_def, m2v_can_promote_alloca_def, AllCaseEqs()] >>
  metis_tac[EXISTS_MEM, NOT_CONS_NIL]
QED

Theorem m2v_root_in_promo_list[local]:
  fn_inst_wf fn /\ MEM a (fn_insts fn) /\ a.inst_opcode = ALLOCA /\
  a.inst_outputs = [v] /\
  m2v_can_promote_alloca v (dfg_get_uses (dfg_build_function fn) v) ==>
  ?p sz. MEM (v,p,sz) (m2v_promo_list fn)
Proof
  strip_tac >> drule_all fn_inst_wf_MEM >>
  simp[inst_wf_def] >> strip_tac >>
  simp[m2v_promo_list_def, m2v_scan_def] >>
  irule m2v_scan_contains_root >> simp[MEM_FILTER] >>
  metis_tac[]
QED

Theorem m2v_promoted_id_root[local]:
  wf_function fn /\ MEM a (fn_insts fn) /\
  a.inst_id IN m2v_promoted_ids fn ==>
  a.inst_opcode = ALLOCA /\
  ?v. a.inst_outputs = [v] /\
      m2v_can_promote_alloca v (dfg_get_uses (dfg_build_function fn) v)
Proof
  rw[m2v_promoted_ids_def] >>
  `a = inst` by metis_tac[wf_fn_inst_id_inj] >> gvs[]
QED

Theorem m2v_find_no32_excludes_root[local]:
  wf_function fn /\ fn_inst_wf fn /\ MEM i (fn_insts fn) /\
  MEM a (fn_insts fn) /\
  a.inst_id IN m2v_promoted_ids fn /\ a.inst_outputs = [v] /\
  alloca_bridge fn s /\ FLOOKUP s.vs_allocas a.inst_id = SOME (b,32) /\
  ~(?ao p. FIND (\(ao,p,sz). MEM (Var ao) i.inst_operands)
    (m2v_promo_list fn) = SOME (ao,p,32)) ==>
  ~MEM (Var v) i.inst_operands
Proof
  strip_tac >> strip_tac >>
  drule_all m2v_promoted_id_root >> strip_tac >> gvs[] >>
  drule_all m2v_root_in_promo_list >> strip_tac >>
  `!ao p sz. MEM (ao,p,sz) (m2v_promo_list fn) /\
    MEM (Var ao) i.inst_operands ==> sz = 32` by
    (rpt strip_tac >>
     drule_all m2v_root_use >> strip_tac >>
     drule m2v_promo_list_can_promote >> strip_tac >>
     `m2v_is_pointer_use ao i` by metis_tac[m2v_root_use] >>
     `ao = v` by
       (`inst_wf i` by metis_tac[fn_inst_wf_MEM] >>
        gvs[m2v_is_pointer_use_def, inst_wf_def, AllCaseEqs()] >>
        Cases_on `i.inst_operands` >> gvs[] >>
        Cases_on `t` >> gvs[] >> metis_tac[]) >>
     gvs[] >> drule_all alloca_bridge_entry_sz >> simp[]) >>
  qpat_x_assum `!ao p. FIND _ _ <> _` mp_tac >>
  qpat_x_assum `!ao p sz. _` mp_tac >>
  qpat_x_assum `MEM (v,p,sz) _` mp_tac >>
  qpat_x_assum `MEM (Var v) _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  qspec_tac (`m2v_promo_list fn`, `ps`) >>
  Induct >- simp[] >>
  gen_tac >> PairCases_on `h` >>
  pure_rewrite_tac[FIND_thm, MEM, pairTheory.UNCURRY_DEF,
    pairTheory.FST, pairTheory.SND] >>
  Cases_on `MEM (Var h0) i.inst_operands` >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  pure_asm_rewrite_tac[COND_CLAUSES] >> rpt strip_tac >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Theorem m2v_step_alloca_record[local]:
  step_inst fuel ctx i s = OK s' /\ i.inst_opcode <> INVOKE /\
  FLOOKUP s.vs_allocas aid = SOME site ==>
  FLOOKUP s'.vs_allocas aid = SOME site
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (gvs[Once step_inst_base_def, exec_alloca_def, AllCaseEqs(),
          update_var_def, FLOOKUP_UPDATE] >> strip_tac >> gvs[]) >>
  drule_all step_inst_base_ok_preserves_allocas >> simp[]
QED

Theorem m2v_enters_block_alloca_record[local]:
  enters_block fn s s' /\ FLOOKUP s.vs_allocas aid = SOME site ==>
  FLOOKUP s'.vs_allocas aid = SOME site
Proof
  rw[enters_block_def] >>
  drule_then strip_assume_tac eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem m2v_dalloca_origin_base[local]:
  i.inst_opcode = DALLOCA /\ step_inst fuel ctx i s = OK s' /\
  out_prov [] G i s' = SOME (b,sz) ==> b = w2n s.vs_fmp
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, out_prov_def, AllCaseEqs()] >>
  gvs[Once step_inst_base_def, AllCaseEqs(), update_var_def,
      lookup_var_def, FLOOKUP_UPDATE]
QED

Definition m2v_static_origin_def:
  m2v_static_origin fn s v b sz <=>
    ?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      (aid IN m2v_promoted_ids fn ==>
       ?a. MEM a (fn_insts fn) /\ a.inst_id = aid /\
           a.inst_opcode = ALLOCA /\ a.inst_outputs = [v])
End

Definition m2v_prov_origins_def:
  m2v_prov_origins H ctx fn G s <=>
    !v b sz. FLOOKUP G v = SOME (b,sz) ==>
      m2v_static_origin fn s v b sz \/ (ctx_has_dalloca ctx /\ H <= b)
End

Theorem m2v_prov_origins_empty[local]:
  m2v_prov_origins H ctx fn FEMPTY s
Proof
  simp[m2v_prov_origins_def]
QED

Theorem m2v_prov_origins_idx[local]:
  m2v_prov_origins H ctx fn G (s with vs_inst_idx := idx) <=>
  m2v_prov_origins H ctx fn G s
Proof
  simp[m2v_prov_origins_def, m2v_static_origin_def]
QED

Theorem m2v_static_origin_step[local]:
  step_inst fuel ctx i s = OK s' /\ i.inst_opcode <> INVOKE /\
  m2v_static_origin fn s v b sz ==> m2v_static_origin fn s' v b sz
Proof
  rw[m2v_static_origin_def] >> qexists `aid` >> simp[] >>
  metis_tac[m2v_step_alloca_record]
QED

Theorem m2v_propagated_origin[local]:
  wf_function fn /\ MEM i (fn_insts fn) /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB \/
   i.inst_opcode = ASSIGN \/ i.inst_opcode = PHI) /\
  MEM (Var v) i.inst_operands /\ m2v_static_origin fn s v b sz ==>
  m2v_static_origin fn s out b sz
Proof
  rw[m2v_static_origin_def] >> qexists `aid` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule_all m2v_promoted_id_root >> strip_tac >> gvs[] >>
  metis_tac[m2v_root_no_propagating_use]
QED

Theorem m2v_out_prov_origin[local]:
  wf_function fn /\ fn_inst_wf fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode <> INVOKE /\ step_inst fuel ctx i s = OK s' /\
  m2v_prov_origins H ctx fn G s /\
  (i.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx /\ H <= w2n s.vs_fmp) /\
  i.inst_outputs = [out] /\ out_prov [] G i s' = SOME (b,sz) ==>
  m2v_static_origin fn s' out b sz \/ (ctx_has_dalloca ctx /\ H <= b)
Proof
  strip_tac >> Cases_on `i.inst_opcode = ALLOCA`
  >- (disj1_tac >> gvs[out_prov_def, m2v_static_origin_def] >>
      qexists `i.inst_id` >> simp[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DALLOCA`
  >- (disj2_tac >> drule_all m2v_dalloca_origin_base >> simp[]) >>
  gvs[out_prov_def, AllCaseEqs()] >>
  drule first_prov_origin >> strip_tac >>
  qpat_x_assum `m2v_prov_origins _ _ _ _ _` mp_tac >>
  simp[m2v_prov_origins_def] >>
  disch_then (drule_then strip_assume_tac) >> simp[] >>
  disj1_tac >>
  `m2v_static_origin fn s out b sz` by
    (irule m2v_propagated_origin >> metis_tac[]) >>
  irule m2v_static_origin_step >>
  qexistsl [`ctx`, `fuel`, `i`, `s`] >> simp[]
QED

Theorem m2v_prov_origins_step[local]:
  wf_function fn /\ fn_inst_wf fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode <> INVOKE /\ step_inst fuel ctx i s = OK s' /\
  m2v_prov_origins H ctx fn G s /\
  (i.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx /\ H <= w2n s.vs_fmp) ==>
  m2v_prov_origins H ctx fn (step_prov [] G i s') s'
Proof
  strip_tac >>
  `!v b sz. FLOOKUP G v = SOME (b,sz) ==>
     m2v_static_origin fn s' v b sz \/ (ctx_has_dalloca ctx /\ H <= b)` by
    (rpt strip_tac >>
     qpat_x_assum `m2v_prov_origins _ _ _ _ _` mp_tac >>
     simp[m2v_prov_origins_def] >>
     disch_then (drule_then strip_assume_tac) >> simp[] >>
     disj1_tac >> irule m2v_static_origin_step >>
     qexistsl [`ctx`, `fuel`, `i`, `s`] >> simp[]) >>
  simp[step_prov_def] >>
  Cases_on `i.inst_outputs`
  >- simp[set_prov_def, m2v_prov_origins_def, DRESTRICT_UNIV] >>
  Cases_on `t`
  >- (Cases_on `out_prov [] G i s'` >>
      gvs[set_prov_def, m2v_prov_origins_def, FLOOKUP_DRESTRICT,
          FLOOKUP_UPDATE] >> rpt strip_tac >>
      Cases_on `h = v` >> gvs[] >>
      irule m2v_out_prov_origin >> simp[] >>
      qexistsl [`G`, `fuel`, `i`, `s`] >>
      simp[m2v_prov_origins_def]) >>
  simp[set_prov_def, m2v_prov_origins_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> first_x_assum irule >>
  Cases_on `out_prov [] G i s'` >> gvs[FLOOKUP_DRESTRICT, AllCaseEqs()]
QED

Theorem m2v_phi_prov_origin[local]:
  wf_function fn /\ MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
  m2v_prov_origins H ctx fn G s /\ phi_prov prev G i = SOME (b,sz) ==>
  m2v_static_origin fn s out b sz \/ (ctx_has_dalloca ctx /\ H <= b)
Proof
  strip_tac >> gvs[phi_prov_def, AllCaseEqs()] >>
  Cases_on `op` >> gvs[op_prov_def] >>
  drule resolve_phi_MEM >> strip_tac >>
  qpat_x_assum `m2v_prov_origins _ _ _ _ _` mp_tac >>
  simp[m2v_prov_origins_def] >>
  disch_then (drule_then strip_assume_tac) >> simp[] >>
  disj1_tac >> irule m2v_propagated_origin >> metis_tac[]
QED

Theorem m2v_phis_prov_origins[local]:
  !insts. wf_function fn /\ EVERY (\i. MEM i (fn_insts fn)) insts /\
  m2v_prov_origins H ctx fn G0 s ==>
  m2v_prov_origins H ctx fn (phis_prov prev G0 insts) s
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  `m2v_prov_origins H ctx fn (phis_prov prev G0 insts) s` by metis_tac[] >>
  Cases_on `h.inst_outputs`
  >- simp[set_prov_def, DRESTRICT_UNIV] >>
  Cases_on `t`
  >- (Cases_on `phi_prov prev G0 h` >>
      gvs[set_prov_def, m2v_prov_origins_def, FLOOKUP_DRESTRICT,
          FLOOKUP_UPDATE] >> rpt strip_tac >>
      Cases_on `h' = v` >> gvs[] >>
      irule m2v_phi_prov_origin >> simp[] >>
      qexistsl [`G0`, `h`, `prev`] >> simp[m2v_prov_origins_def]) >>
  Cases_on `phi_prov prev G0 h` >>
  gvs[set_prov_def, m2v_prov_origins_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> first_x_assum irule >> gvs[AllCaseEqs()]
QED

Theorem m2v_prov_origins_allocas[local]:
  s'.vs_allocas = s.vs_allocas /\ m2v_prov_origins H ctx fn G s ==>
  m2v_prov_origins H ctx fn G s'
Proof
  simp[m2v_prov_origins_def, m2v_static_origin_def]
QED

Theorem m2v_entry_prov_origins[local]:
  wf_function fn /\ enters_block fn s s' /\ m2v_prov_origins H ctx fn G s ==>
  m2v_prov_origins H ctx fn (entry_prov fn s G) s'
Proof
  strip_tac >> irule m2v_prov_origins_allocas >> qexists `s` >>
  conj_tac
  >- (gvs[enters_block_def] >>
      drule_then strip_assume_tac eval_phis_preserves_alloca_fields >> simp[]) >>
  simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule m2v_phis_prov_origins >> simp[EVERY_MEM] >>
  drule venomInstTheory.selected_block_mem >>
  metis_tac[MEM_fn_insts]
QED

Theorem m2v_call_free_origins[local]:
  !vs ctx stk PG G tn current inst s.
    frame_reachable vs ctx stk PG G tn current inst s ==>
    !name fn.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
      wf_function fn /\ fn_inst_wf fn /\
      ptr_discipline vs.vs_alloca_next ctx vs ==>
      stk = [] /\ PG = [] /\ current = fn /\
      s.vs_initial_fmp = vs.vs_initial_fmp /\
      m2v_prov_origins (w2n vs.vs_initial_fmp) ctx fn G s
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (simp[m2v_prov_origins_empty] >>
      drule enters_block_initial_fmp >> simp[])
  >- (`MEM inst (fn_insts current)` by
        (gvs[active_inst_def] >> metis_tac[MEM_fn_insts, EL_MEM]) >>
      conj_tac
      >- (drule_all step_inst_initial_fmp >> simp[]) >>
      simp[m2v_prov_origins_idx] >> irule m2v_prov_origins_step >>
      simp[] >> qexistsl [`fuel`, `s`] >> simp[] >> strip_tac >>
      `ctx_has_dalloca ctx` by
        (drule venomInstTheory.lookup_function_MEM >>
         simp[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
      simp[] >> qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
      simp[ptr_discipline_def] >> strip_tac >>
      first_x_assum drule >> simp[allocas_below_fmp_def])
  >- (`MEM inst (fn_insts current)` by
        (gvs[active_inst_def] >> metis_tac[MEM_fn_insts, EL_MEM]) >>
      `inst.inst_opcode <> INVOKE` by gvs[EVERY_MEM] >>
      `s'.vs_initial_fmp = s.vs_initial_fmp` by
        (drule_all step_inst_initial_fmp >> simp[]) >>
      conj_tac
      >- (drule enters_block_initial_fmp >> simp[]) >>
      irule m2v_entry_prov_origins >> simp[] >>
      irule m2v_prov_origins_allocas >> qexists `s` >> simp[] >>
      `inst.inst_opcode <> ALLOCA` by
        (strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
      irule step_inst_base_ok_preserves_allocas >> qexists `inst` >>
      gvs[step_inst_non_invoke])
  >- (drule_all EVERY_active_inst >> simp[])
  >> gvs[EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem m2v_origins_access_safe[local]:
  wf_function fn /\ fn_inst_wf fn /\ MEM inst (fn_insts fn) /\
  alloca_inv s /\ alloca_bridge fn s /\
  access_ok lo G fn inst s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  m2v_prov_origins (w2n s.vs_initial_fmp) ctx fn G s /\
  ~in_revert_forward fn s ==> m2v_access_safe fn inst s
Proof
  pure_rewrite_tac[m2v_access_safe_def] >> rpt strip_tac >>
  qpat_x_assum `in_promoted_region _ _ _` mp_tac >>
  pure_rewrite_tac[in_promoted_region_def] >> strip_tac >>
  Cases_on `off + len <= lo`
  >- (gvs[allocas_from_def] >>
      first_x_assum drule >> simp[]) >>
  `len <> 0 /\ lo < off + len` by decide_tac >>
  `?ops v b sz.
     (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
     ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b,sz) /\
     b <= off /\ off + len <= b + sz` by
    (fs[access_ok_def] >> metis_tac[]) >>
  `MEM (Var v) inst.inst_operands` by
    (qpat_x_assum `ops.iao_ofst = Var v` mp_tac >>
     qpat_x_assum `_ inst = SOME ops` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `inst.inst_opcode` >>
     gvs[memLocDefsTheory.mem_read_ops_def, memLocDefsTheory.mem_write_ops_def,
         AllCaseEqs()] >> metis_tac[MEM_REVERSE, MEM]) >>
  (qpat_x_assum `m2v_prov_origins _ _ _ _ _` mp_tac >>
   pure_rewrite_tac[m2v_prov_origins_def] >>
   disch_then drule >> strip_tac
   >- (qpat_x_assum `m2v_static_origin _ _ _ _ _` mp_tac >>
       pure_rewrite_tac[m2v_static_origin_def] >> strip_tac >>
       Cases_on `aid' = aid`
       >- (fs[] >> metis_tac[m2v_find_no32_excludes_root]) >>
       qpat_x_assum `alloca_inv s` mp_tac >>
       pure_rewrite_tac[alloca_inv_def, allocas_non_overlapping_def] >>
       strip_tac >>
       first_x_assum (qspecl_then [`aid'`, `aid`] mp_tac) >>
       disch_then drule_all >> decide_tac) >>
   fs[allocas_below_fmp_def] >>
   qpat_x_assum `!aid b sz. _` (qspec_then `aid` mp_tac) >>
   disch_then drule >> decide_tac)
QED

Theorem m2v_reachable_access_safe[local]:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
  wf_function fn /\ fn_inst_wf fn /\ o1_initial_state_ok vs /\
  ptr_discipline vs.vs_alloca_next ctx vs /\ alloca_bridge fn s /\
  frame_reachable vs ctx [] [] G tn fn inst s ==>
  (~in_revert_forward fn s ==> m2v_access_safe fn inst s)
Proof
  strip_tac >>
  drule m2v_call_free_origins >> simp[] >> strip_tac >>
  drule m2v_call_free_alloca_inv >> simp[] >> strip_tac >>
  drule m2v_call_free_reachable >> simp[] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def] >> metis_tac[MEM_fn_insts, EL_MEM]) >>
  qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
  simp[ptr_discipline_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> strip_tac >>
  irule m2v_origins_access_safe >> simp[] >>
  qexistsl [`G`, `ctx`, `vs.vs_alloca_next`] >> simp[]
QED

(* The pointer-use guard isolates a promoted root: its address cannot flow
   to another variable. Other accesses are confined to their own provenance
   sites or the fixed prefix. Revert forwarding is simulated as a segment
   instead, since its copy may overwrite a promoted site before aborting. *)
Theorem m2v_reachable_memory_safety:
  !ctx name fn vs G tn inst s.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    o1_initial_state_ok vs /\
    ptr_discipline vs.vs_alloca_next ctx vs /\
    raw_unit_memory_ok ctx vs /\
    m2v_fresh_names_disjoint fn /\
    EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn) /\
    frame_reachable vs ctx [] [] G tn fn inst s ==>
    alloca_inv s /\ alloca_bridge fn s /\ m2v_fresh_undef fn s /\
    s.vs_alloca_next < dimword (:256) /\
    (~in_revert_forward fn s ==> m2v_access_safe fn inst s)
Proof
  rpt strip_tac >>
  drule m2v_call_free_alloca_inv >> simp[] >> strip_tac >>
  drule m2v_call_free_bridge_fresh >> simp[] >> strip_tac >>
  drule_all m2v_reachable_raw_bound >> strip_tac >>
  drule_all m2v_reachable_access_safe >> simp[]
QED
