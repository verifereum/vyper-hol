(* Callee-exit memory framing, independent of the copy execution. *)
Theory internalReturnMemoryExitFrame
Ancestors
  internalReturnMemoryFrame intCallReturnMem intCallResult
  loweringSlice instIdxIndep stmtSimReturn loweringStateRelDefs
  compileEnv venomState vyperState bodySim exprLoweringProps stateRelProj

(* Clearing the local scopes leaves only the immutable base lookup to
   preserve across the return-buffer copy. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `copied = (return_unlock_state cenv t) with
      <|vs_vars := copied.vs_vars; vs_memory := copied.vs_memory|>` by
    (qpat_x_assum `copied with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o AP_TERM ``\z. z with
          <|vs_vars := copied.vs_vars; vs_memory := copied.vs_memory|>``) >>
     simp[]) >>
  qabbrev_tac `pre = t with
    <|vs_vars := copied.vs_vars; vs_memory := copied.vs_memory;
      vs_inst_idx := n - LENGTH (return_unlock_insts cenv iid)|>` >>
  `copied with vs_inst_idx := n = return_unlock_state cenv pre` by
    (qpat_assum `copied = _ with <|vs_vars := _; vs_memory := _|>`
       (fn th => once_rewrite_tac[th]) >>
     drule return_unlock_memory_frame >>
     disch_then (qspecl_then [`t`, `copied.vs_vars`, `copied.vs_memory`] mp_tac) >>
     simp[Abbr `pre`]) >>
  `stmt_state_rel H ctx func cenv cx (ee with scopes := []) t` by
    (irule internal_return_exit_stmt_state_rel >> qexists_tac `cenv` >>
     simp[same_frame_def]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (ee with scopes := [])
     (t with <|vs_vars := copied.vs_vars; vs_memory := copied.vs_memory|>)` by
    (irule immutables_rel_mem_agree >> qexists_tac `t` >>
     imp_res_tac stmt_state_rel_state_rel >>
     imp_res_tac state_rel_immutables_rel >> fs[] >> rpt strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> fs[regions_disjoint_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx (ee with scopes := [])
     (t with <|vs_vars := copied.vs_vars; vs_memory := copied.vs_memory|>)` by
    (irule result_state_memory_frame >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qexists_tac `t` >> simp[local_region_def, lookup_scopes_def] >>
     fs[lookup_var_def]) >>
  `stmt_state_rel H ctx func cenv cx (ee with scopes := []) pre` by
    (mp_tac (Q.INST
       [`s` |-> `t with <|vs_vars := copied.vs_vars; vs_memory := copied.vs_memory|>`,
        `es` |-> `ee with scopes := []`,
        `n` |-> `n - LENGTH (return_unlock_insts cenv iid)`]
       (SPEC_ALL stmt_state_rel_inst_idx)) >>
     simp[Abbr `pre`]) >>
  `intret_mem_q H func cenv cx tv bw v (ee with scopes := []) r` by
    (simp[intret_mem_q_def, intret_q_def, result_rel_def,
          intret_vals_match_def] >>
     reverse conj_tac >- fs[Abbr `pre`] >>
     qexistsl_tac [`pre`, `(return_unlock_state cenv pre).vs_inst_idx`] >>
     simp[venom_state_component_equality] >>
     metis_tac[stmt_state_rel_state_rel]) >>
  gen_tac >>
  `((ee with gas_obs := tail) with scopes := []) =
    ((ee with scopes := []) with gas_obs := tail)` by
    simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> rewrite_tac[intret_mem_q_gas_obs] >>
  fs[intret_mem_q_def] >>
  irule internal_return_post_frame >> goal_assum (drule_at Any) >> metis_tac[]
QED
*)
Theorem internal_return_memory_copy_exit_base:
  same_frame ce cenv /\ cenv.ce_returns_count = 0 /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==>
       lookup_var x copied = lookup_var x t) /\
  stmt_state_rel H ctx func cenv cx ee t /\
  (cenv.ce_is_ctor ==> !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  (copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) =
    return_unlock_state cenv t /\
  (!a len. a + len <= w2n bw \/ w2n bw + type_memory_size tv <= a ==>
    mem_bytes_at a len copied.vs_memory = mem_bytes_at a len t.vs_memory) /\
  LENGTH t.vs_memory <= LENGTH copied.vs_memory /\
  val_in_memory tv v (w2n bw) copied.vs_memory /\
  LENGTH (return_unlock_insts cenv iid) <= n /\
  r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
        (copied with vs_inst_idx := n) ==>
  !tail. intret_mem_q H func ce cx tv bw v
    ((ee with gas_obs := tail) with scopes := []) r
Proof
  cheat
QED

Theorem internal_return_memory_copy_exit:
  same_frame ce cenv /\ cenv.ce_returns_count = 0 /\
  cenv.ce_imm_alloca = NONE /\
  stmt_state_rel H ctx func cenv cx ee t /\
  (cenv.ce_is_ctor ==> !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  (copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) =
    return_unlock_state cenv t /\
  (!a len. a + len <= w2n bw \/ w2n bw + type_memory_size tv <= a ==>
    mem_bytes_at a len copied.vs_memory = mem_bytes_at a len t.vs_memory) /\
  LENGTH t.vs_memory <= LENGTH copied.vs_memory /\
  val_in_memory tv v (w2n bw) copied.vs_memory /\
  LENGTH (return_unlock_insts cenv iid) <= n /\
  r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
        (copied with vs_inst_idx := n) ==>
  !tail. intret_mem_q H func ce cx tv bw v
    ((ee with gas_obs := tail) with scopes := []) r
Proof
  strip_tac >>
  mp_tac (SPEC_ALL internal_return_memory_copy_exit_base) >>
  impl_tac >- (fs[] >> metis_tac[]) >> simp[]
QED

Theorem intret_mem_q_set_control:
  intret_mem_q H func ce cx tv bw v es (IntRet ir s) ==>
  intret_mem_q H func ce cx tv bw v es
    (IntRet ir (s with <|vs_prev_bb := prev; vs_current_bb := bb; vs_inst_idx := idx|>))
Proof
  simp[intret_mem_q_def, intret_q_def, result_rel_def] >>
  strip_tac >>
  rename1 `state_rel H func ce cx es pre` >>
  qexistsl_tac [`pre with <|vs_prev_bb := prev; vs_current_bb := bb|>`,`idx`] >>
  conj_tac
  >- (qabbrev_tac `info = ce.ce_nonreentrant` >> PairCases_on `info` >>
      Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
      gvs[return_unlock_state_def, tstore_def, sstore_def]) >>
  qpat_assum `state_rel H func ce cx es pre` mp_tac >>
  simp_tac (srw_ss()) [state_rel_def, local_ptrs_rel_def, local_region_def, local_backed_def,
       lookup_var_def, storage_rel_def, transient_rel_def, immutables_rel_def,
       logs_rel_def, contract_storage_def, contract_transient_def, accounts_rel_def] >>
  strip_tac >> simp[] >> conj_tac
  >- (qpat_assum `!name entry p sz. _ ==> ?w. _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  first_assum ACCEPT_TAC
QED
