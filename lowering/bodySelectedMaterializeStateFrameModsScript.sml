Theory bodySelectedMaterializeStateFrameMods
Ancestors
  bodyInvSplit intCallCallee exprLoweringProps localPtrsProps loweringSlice
  loweringStateRelDefs vyperState venomState vyperStorageFootprint
  vyperFiniteStoragePreservation vyperTypeEvalProofs vyperTypeInvariants

(* The allocation added by scratch has no memory write and preserves the
   bindings of the locals materialized in the preceding interval. *)
Theorem materialize_scratch_locals[local]:
  mat_inv callee mat_ce penv materialized mat_state f0 mr /\
  body_ce.ce_vars = mat_ce.ce_vars /\
  es1.scopes = [penv] /\
  at_mat = mat_state with vs_inst_idx := idx /\
  (!n v sz. FLOOKUP mat_ce.ce_vars n = SOME (PtrVar (Var v) sz) ==>
            not_fresh_at materialized v) /\
  (!v. not_fresh_at materialized v ==> lookup_var v at_pro = lookup_var v at_mat) /\
  (!aid r. FLOOKUP at_mat.vs_allocas aid = SOME r ==>
           FLOOKUP at_pro.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP at_pro.vs_allocas aid = SOME (b,sz) /\
              FLOOKUP at_mat.vs_allocas aid = NONE ==> at_mat.vs_alloca_next <= b) /\
  at_mat.vs_alloca_next <= at_pro.vs_alloca_next /\
  at_pro.vs_memory = at_mat.vs_memory ==>
  local_ptrs_rel callee body_ce es1.scopes at_pro
Proof
  strip_tac >>
  qpat_assum `mat_inv _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
  `local_ptrs_rel callee mat_ce es1.scopes at_mat` by
    simp[local_ptrs_rel_inst_idx] >>
  irule local_ptrs_rel_cenv_cong >> qexists_tac `mat_ce` >>
  conj_tac >- simp[] >>
  irule local_ptrs_rel_mem_agree >> qexists_tac `at_mat` >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!n v sz. FLOOKUP mat_ce.ce_vars n = _ ==> _` (drule_then assume_tac) >>
  qpat_assum `!v. not_fresh_at materialized v ==> _` (drule_then mp_tac) >>
  simp[]
QED

(* Use the unit floor, not the active module's immutable length, to show that
   every initialized constructor slot lies below the materialization writes. *)
Theorem materialize_qualified_immutable_values[local]:
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es1 at_reserve /\
  ce.ce_modules = body_ce.ce_modules /\
  ce.ce_module_vars = body_ce.ce_module_vars /\
  ce.ce_is_ctor = body_ce.ce_is_ctor /\
  (body_ce.ce_is_ctor ==>
   !src tops name tv v off.
     ALOOKUP body_ce.ce_modules src = SOME tops /\
     FLOOKUP body_ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables src imms)
             name = SOME (tv,v) ==> off + type_memory_size tv <= lo) /\
  lo <= at_reserve.vs_alloca_next /\
  mat_frame reserved at_reserve mat_state /\
  at_pro.vs_memory = mat_state.vs_memory /\
  at_pro.vs_data_section = at_reserve.vs_data_section ==>
  immutables_rel_mods body_ce cx.txn.target body_ce.ce_is_ctor es1 at_pro
Proof
  simp[immutables_rel_mods_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule immutables_rel_mem_agree >> qexists_tac `at_reserve` >>
  qpat_assum `mat_frame _ _ _` (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
  qpat_x_assum `mat_state = at_reserve with <|vs_vars := _; vs_memory := _;
                                             vs_allocas := _; vs_alloca_next := _|>` kall_tac >>
  simp[] >> conj_tac
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_assum `!b n. b + n <= at_reserve.vs_alloca_next ==> _` irule >>
      qpat_assum `body_ce.ce_is_ctor ==> _` (drule_then assume_tac) >>
      `off + type_memory_size tv <= lo` by
        (qpat_assum `!src tops name tv v off. _ ==> off + type_memory_size tv <= lo`
           (drule_all_then ACCEPT_TAC)) >>
      irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `lo` >> simp[]) >>
  qpat_x_assum `!src tops. ALOOKUP ce.ce_modules src = _ ==> _`
    (qspecl_then [`src`,`tops`] mp_tac) >> simp[immutables_rel_def]
QED

Theorem materialize_state_rel_push[local]:
  state_rel H callee ce (cx with stk updated_by CONS key) es s <=>
  state_rel H callee ce cx es s
Proof
  simp[state_rel_def, accounts_rel_def, storage_vars_rel_def,
       transient_vars_rel_def, get_module_code_stk_irrelevant,
       lookup_var_slot_from_layout_context, get_tenv_stk_irrelevant]
QED

(* The reserve and scratch record equations describe the physical prefix,
   without choosing another execution at any horizon. *)
Theorem selected_materialize_state_frame_mods:
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
       state_rel H callee ce cx (es1 with scopes := []) t) /\
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es1 at_reserve /\
  ce.ce_modules = body_ce.ce_modules /\
  ce.ce_module_vars = body_ce.ce_module_vars /\
  ce.ce_module = body_ce.ce_module /\
  ce.ce_is_ctor = body_ce.ce_is_ctor /\
  ALOOKUP body_ce.ce_modules body_ce.ce_module = SOME tops /\
  (body_ce.ce_is_ctor ==>
   !src m name tv v off.
     ALOOKUP body_ce.ce_modules src = SOME m /\
     FLOOKUP body_ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables src imms)
             name = SOME (tv,v) ==> off + type_memory_size tv <= lo) /\
  lo <= at_reserve.vs_alloca_next /\
  at_reserve = t with <|vs_vars := at_reserve.vs_vars;
                        vs_params := at_reserve.vs_params;
                        vs_current_bb := at_reserve.vs_current_bb;
                        vs_inst_idx := at_reserve.vs_inst_idx;
                        vs_prev_bb := at_reserve.vs_prev_bb;
                        vs_halted := at_reserve.vs_halted;
                        vs_allocas := at_reserve.vs_allocas;
                        vs_call_entry_fmp := at_reserve.vs_call_entry_fmp;
                        vs_return_pc_token := at_reserve.vs_return_pc_token|> /\
  mat_frame reserved at_reserve mat_state /\
  mat_inv callee mat_ce penv materialized mat_state f0 mr /\
  body_ce.ce_vars = mat_ce.ce_vars /\
  es1.scopes = [penv] /\
  at_mat = mat_state with vs_inst_idx := idx /\
  at_pro with <|vs_vars := at_mat.vs_vars; vs_allocas := at_mat.vs_allocas;
                vs_alloca_next := at_mat.vs_alloca_next; vs_inst_idx := at_mat.vs_inst_idx|> = at_mat /\
  (!n v sz. FLOOKUP mat_ce.ce_vars n = SOME (PtrVar (Var v) sz) ==>
            not_fresh_at materialized v) /\
  (!v. not_fresh_at materialized v ==> lookup_var v at_pro = lookup_var v at_mat) /\
  (!aid r. FLOOKUP at_mat.vs_allocas aid = SOME r ==>
           FLOOKUP at_pro.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP at_pro.vs_allocas aid = SOME (b,sz) /\
              FLOOKUP at_mat.vs_allocas aid = NONE ==> at_mat.vs_alloca_next <= b) /\
  at_mat.vs_alloca_next <= at_pro.vs_alloca_next ==>
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
       state_rel H callee body_ce cx es1 at_pro) /\
  (!key H. valid_horizon (cx with stk updated_by CONS key) st0 H es1.storage_trace ==>
       state_rel H callee body_ce (cx with stk updated_by CONS key) es1 at_pro) /\
  immutables_rel_mods body_ce cx.txn.target body_ce.ce_is_ctor es1 at_pro /\
  at_pro.vs_transient = t.vs_transient /\
  at_pro.vs_accounts = t.vs_accounts /\
  at_pro.vs_call_ctx = t.vs_call_ctx /\
  at_pro.vs_tx_ctx = t.vs_tx_ctx /\
  at_pro.vs_block_ctx = t.vs_block_ctx
Proof
  strip_tac >>
  qpat_x_assum `at_reserve = t with <|vs_vars := _; vs_params := _;
        vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _; vs_halted := _;
        vs_allocas := _; vs_call_entry_fmp := _; vs_return_pc_token := _|>`
    (strip_assume_tac o SRULE [NoAsms, venom_state_component_equality]) >>
  qpat_x_assum `at_pro with <|vs_vars := _; vs_allocas := _;
                             vs_alloca_next := _; vs_inst_idx := _|> = at_mat`
    (strip_assume_tac o SRULE [NoAsms, venom_state_component_equality]) >>
  qpat_assum `mat_frame _ _ _` (strip_assume_tac o REWRITE_RULE [mat_frame_def]) >>
  qpat_x_assum `mat_state = at_reserve with <|vs_vars := _; vs_memory := _;
                                             vs_allocas := _; vs_alloca_next := _|>`
    (strip_assume_tac o SRULE [NoAsms, venom_state_component_equality]) >>
  `local_ptrs_rel callee body_ce es1.scopes at_pro` by
    (irule materialize_scratch_locals >>
     qexistsl_tac [`at_mat`,`f0`,`idx`,`mat_ce`,`mat_state`,`materialized`,`mr`,`penv`] >>
     asm_rewrite_tac[]) >>
  `immutables_rel_mods body_ce cx.txn.target body_ce.ce_is_ctor es1 at_pro` by
    (irule materialize_qualified_immutable_values >>
     qexistsl_tac [`at_reserve`,`ce`,`lo`,`mat_state`,`reserved`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
       state_rel H callee body_ce cx es1 at_pro` suffices_by
    simp[materialize_state_rel_push, valid_horizon_def,
         storage_well_formed_on_stk, storage_observations_ok_stk] >>
  gen_tac >> strip_tac >>
  `state_rel H callee body_ce cx (es1 with scopes := []) t` by
    (irule state_rel_cenv_cong >> qexists_tac `ce` >>
     simp[lookup_scopes_def]) >>
  irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`es1 with scopes := []`,`t`] >> simp[evaluation_state_component_equality] >>
  qpat_assum `immutables_rel_mods body_ce _ _ _ at_pro`
    (drule_then mp_tac o REWRITE_RULE [immutables_rel_mods_def]) >>
  simp[immutables_rel_def]
QED
