(* Package one selected IntRet for the caller, with the same source release
   and the same protected path at every valid horizon. *)
Theory bodySelectedReturningExitPostMods
Ancestors
  bodyFullShadowBodyInv bodyFullPostsMods bodyInvCodeProps bodyInvMetadataProps
  stateRelProj stmtSimReturn fragGasOriginPtrInvoke gasSummary
  externalBodySupport vyperImmutableMetadataFrame vyperStatePreservation
  vyperInterpreter vyperStorageFootprint vyperState vyperAST
  loweringStateRelDefs bodyInvSplit compileEnv bodyPtrDefs valueEncodingDefs
  venomState venomExecSemantics finite_map words alist list
Libs monadsyntax

val selected_source = ``do lock_if_nr cx nr (is_view_mut mut);
  try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
           return NoneV od) handle_function od``;

Theorem selected_return_release_immutables[local]:
  unlock_if_nr cx nr iv ee = (INL (),out) ==>
  out.immutables = ee.immutables
Proof
  Cases_on `nr /\ ~iv` >> simp[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[return_def] >>
  metis_tac[release_nonreentrant_lock_immutables]
QED

Theorem selected_return_metadata[local]:
  (^selected_source) (es1 with gas_obs := readings) =
    (INL v,ee with gas_obs := []) /\
  unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out) ==>
  immutable_metadata_frame es1 out
Proof
  strip_tac >> drule_then assume_tac selected_return_release_immutables >>
  qpat_x_assum `unlock_if_nr _ _ _ _ = _` kall_tac >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := readings)` >>
  Cases_on `q` >> gvs[ignore_bind_def, bind_def, Excl "lock_if_nr_def"] >>
  drule_then strip_assume_tac external_body_lock_frame >>
  rename1 `lock_if_nr _ _ _ _ = (INL (),locked)` >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (src,name)) ss locked` >>
  rename1 `eval_stmts _ _ _ = (res,last)` >>
  drule_then assume_tac (cj 2 eval_metadata_frame_mutual) >>
  `last.immutables = out.immutables` by
    (Cases_on `res` >> gvs[try_def, ignore_bind_def, bind_def, return_def, raise_def] >>
     rename1 `eval_stmts _ _ _ = (INR err,last)` >>
     Cases_on `err` >> gvs[handle_function_def, return_def, raise_def]) >>
  qpat_x_assum `immutable_metadata_frame locked last` mp_tac >>
  `locked.immutables = es1.immutables` by fs[] >>
  simp[immutable_metadata_frame_def] >> metis_tac[]
QED

Theorem selected_return_physical[local]:
  contract_inv mods exps ctx cenv cx /\
  contract_inv mods exps ctx body_ce (cx with stk updated_by CONS key) /\
  IS_SOME (ALOOKUP mods cenv.ce_module) /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  state_rel H callee body_ce (cx with stk updated_by CONS key) (out with scopes := []) cs /\
  immutable_frame_mods callee body_ce (cx with stk updated_by CONS key) (ee with scopes := []) cs /\
  out.immutables = ee.immutables ==>
  state_rel H func cenv cx (out with scopes := []) cs /\
  immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor out cs
Proof
  strip_tac >>
  `cenv.ce_modules = mods /\ body_ce.ce_modules = mods` by
    metis_tac[contract_inv_cenv_modules] >>
  `cenv.ce_is_ctor = body_ce.ce_is_ctor` by
    (imp_res_tac contract_inv_constructor >> fs[]) >>
  `cenv.ce_module_vars = body_ce.ce_module_vars` by
    (fs[contract_inv_def, cenv_module_pins_mods_def]) >>
  `immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor out cs` by
    (qpat_assum `immutable_frame_mods _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [immutable_frame_mods_def]) >>
     qpat_x_assum `immutables_rel_mods body_ce _ _ _ _` mp_tac >>
     simp[immutables_rel_mods_def, immutables_rel_def]) >>
  simp[] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor (out with scopes := []) cs` by
    (qpat_x_assum `immutables_rel_mods cenv _ _ _ _`
       (assume_tac o PURE_REWRITE_RULE [immutables_rel_mods_def]) >>
     Cases_on `ALOOKUP mods cenv.ce_module` >> gvs[] >>
     qpat_assum `!src tops. ALOOKUP _ src = _ ==> _` (drule_then mp_tac) >>
     simp[NoAsms, immutables_rel_def]) >>
  `!src tops. ALOOKUP mods src = SOME tops ==>
     immutables_rel cenv cx.txn.target src cenv.ce_is_ctor
       (out with scopes := []) cs` by
    (rpt gen_tac >> disch_tac >>
     `ALOOKUP cenv.ce_modules src = SOME tops` by fs[] >>
     qpat_assum `immutables_rel_mods cenv _ _ _ _`
       (qspecl_then [`src`,`tops`] (drule_then mp_tac) o
        PURE_REWRITE_RULE [immutables_rel_mods_def]) >>
     simp[immutables_rel_def]) >>
  qpat_x_assum `state_rel H callee body_ce _ _ _` mp_tac >>
  simp[state_rel_def, local_ptrs_rel_def, local_region_def, lookup_scopes_def,
       accounts_rel_def, logs_rel_def, listTheory.LIST_REL_EL_EQN, log_entry_equiv_def]
QED

(* The conditional protector is used only on the composed entered-to-RET
   path. All endpoint data are fixed before specializing the horizon. *)
Theorem selected_returning_exit_post_mods:
  !rc rbs.
  let X = gas_explicit_sites ctx shadow_ctx in
  let PGc = MAP (op_prov G) arg_ops in
  let rb = if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE in
  let p = cx with stk updated_by CONS (src,name) in
  let n = sa.cs_next_id in
  let m = sm.cs_next_id in
    contract_inv mods exps ctx cenv cx /\ contract_inv mods exps ctx body_ce p /\
    IS_SOME (ALOOKUP mods cenv.ce_module) /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    gas_invoke_entry (ctx,func) t callee entered /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
    (!setup. setup_callee callee argv t = SOME setup ==> fmp_room ctx callee setup) /\
    (!b sz. MEM (SOME (b,sz)) PGc ==>
      ?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ n <= aid /\ aid < m) /\
    (!tail. (^selected_source)
        (es1 with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
    unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out) /\
    LENGTH ir.iret_values = rc /\
    (0 < rc \/ 0 < rbs ==> ret_tv = rtv) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,X,ctx,callee,PGc)
        (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,J,tc) /\
      result_rel H callee ret_tv body_ce p
        (INR (ReturnException v),out with scopes := []) (IntRet ir cs) /\
      immutable_frame_mods callee body_ce p (ee with scopes := []) cs /\
      storage_well_formed_on cx out (FST H) /\
      stor_taint_ok_at (DF H) tc cs /\
      (!i. i < lo /\ i IN tc.t_mem ==>
           imm_section_dead_mods body_ce (mem_bytes_at 0 lo cs.vs_memory) i) /\
      (!w. rb = SOME w ==>
        !mem. mem_agree_outside tc.t_mem cs.vs_memory mem ==>
              val_in_memory ret_tv v (w2n w) mem)) /\
    (!H. contract_inv mods exps ctx cenv cx /\ contract_inv mods exps ctx body_ce p /\
      dead_lo_ok_mods H (DF H) lo cenv cx /\
      gas_invoke_entry (ctx,func) t callee entered /\
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
      (!setup. setup_callee callee argv t = SOME setup ==> fmp_room ctx callee setup) /\
      (!b sz. MEM (SOME (b,sz)) PGc ==>
        ?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ n <= aid /\ aid < m) /\
      gas_origin_ptr_path (DF H,lo,X,ctx,callee,PGc)
        (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,J,tc) /\
      stor_taint_ok_at (DF H) tc cs /\
      (!i. i < lo /\ i IN tc.t_mem ==>
           imm_section_dead_mods body_ce (mem_bytes_at 0 lo cs.vs_memory) i) ==>
      (!b sz. (cenv.ce_is_ctor ==> imm_len_mods mods <= b) /\
         b + sz <= t.vs_alloca_next /\
         (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
            n <= aid /\ aid < m ==> regions_disjoint b sz a cap) ==>
         mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
      stor_taint_ok_at (DF H) tc cs /\
      (!i. i < lo /\ i IN tc.t_mem ==>
           imm_section_dead_mods cenv (mem_bytes_at 0 lo cs.vs_memory) i) /\
      (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN tc.t_mem /\
         (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
            n <= aid /\ aid < m ==> i < a \/ a + cap <= i) ==> i IN tn.t_mem)) ==>
    ?out'. unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out') /\
      immutable_metadata_frame es1 out' /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
      state_rel H func cenv cx (out' with scopes := []) cs /\
      immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor out' cs /\
      storage_well_formed_on cx out' (FST H) /\
      intret_vals_match rtv v ir.iret_values /\
      LENGTH ir.iret_values = rc /\ ir.iret_adopt_fmp = NONE /\
      stor_taint_ok_at (DF H) tc cs /\
      (!i. i < lo /\ i IN tc.t_mem ==>
           imm_section_dead_mods cenv (mem_bytes_at 0 lo cs.vs_memory) i) /\
      (!b sz. lo <= b /\ b + sz <= t.vs_alloca_next /\
         (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
            n <= aid /\ aid < m ==> regions_disjoint b sz a cap) ==>
         mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
      (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN tc.t_mem /\
         (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
            n <= aid /\ aid < m ==> i < a \/ a + cap <= i) ==> i IN tn.t_mem) /\
      (!w. rb = SOME w ==>
        !mem. mem_agree_outside tc.t_mem cs.vs_memory mem ==>
              val_in_memory rtv v (w2n w) mem)
Proof
  rpt gen_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `out` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `!tail. (^selected_source) _ = _`
        (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
      drule_all_then ACCEPT_TAC selected_return_metadata) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. contract_inv _ _ _ _ _ /\ _ ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `result_rel _ _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [result_rel_def]) >>
  `out.immutables = ee.immutables` by
    (drule_then mp_tac selected_return_release_immutables >> simp[]) >>
  drule_all_then strip_assume_tac selected_return_physical >>
  rename1 `LENGTH ir.iret_values = nret` >>
  asm_rewrite_tac[] >> conj_tac
  >- (Cases_on `nret = 0`
      >- (`ir.iret_values = []` by fs[LENGTH_NIL] >> simp[intret_vals_match_def]) >>
      `ret_tv = rtv` by simp[] >> fs[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!b sz. (cenv.ce_is_ctor ==> _) /\ _ ==> _` irule >>
      asm_rewrite_tac[] >> disch_tac >>
      qpat_assum `contract_inv _ _ _ cenv cx`
        (assume_tac o MATCH_MP contract_inv_cenv_modules) >>
      qpat_x_assum `!H. dead_lo_ok_mods H _ _ _ _` (qspec_then `H` mp_tac) >>
      simp[dead_lo_ok_mods_def] >> strip_tac >> fs[]) >>
  Cases_on `nret = 0 /\ 0 < rbs` >> simp[] >>
  `ret_tv = rtv` by fs[] >>
  qpat_x_assum `!w. (if _ then _ else _) = SOME w ==> _`
    (qspec_then `HD argv` mp_tac) >> simp[]
QED
