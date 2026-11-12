(* Counted MSTORE path for a live local. *)
Theory stmtSimAssignPath
Ancestors
  stmtSimAssignStore stmtSimAssignSource stmtSimDeclPath stmtSimProps
  stmtSimDefs exprSimDefs loweringPosts gasSummary
  venomState compileEnv loweringStateRelDefs valueEncoding list finite_map stmtLowering
  emitHelper emitHelperProps exprLoweringProps fragGasPath fragGasMode vyperLookup
Libs monadsyntax

Theorem assign_local_word_store_path:
  !ctx func cenv cx es s id p sz pre env entry rest v etv op st st'.
    emit_void MSTORE [Var p; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME (typed_val_to_w256 etv v) /\
    stmt_state_rel H ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    store_lays_out etv entry.type v ==>
    ?t. stmt_state_rel H ctx func cenv cx
          (es with scopes :=
            pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        (!w. lookup_var p s = SOME w ==>
             t.vs_memory = (mstore (w2n w) (typed_val_to_w256 etv v) s).vs_memory) /\
        (!w. lookup_var p s = SOME w ==>
             t = mstore (w2n w) (typed_val_to_w256 etv v) s with
                   vs_inst_idx := SUC s.vs_inst_idx) /\
        gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  drule_all emit_mstore_marked_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `st'.cs_current_bb = st.cs_current_bb /\
   LENGTH st'.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexists `mstore (w2n w) (typed_val_to_w256 etv v) s with
    vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def, mstore_def, LET_THM]
QED

Theorem assign_local_normal_continuation:
  !ctx func cenv cx st0 lctx id e es etv sa sb sf s0 marks v ee s op p sz.
    gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
      (stmt_res_ok lctx) es /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!gs v es1 entry. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       store_lays_out etv entry.type v) /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    ~block_is_terminated sf /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s0) marks (INL v) ee (OK s) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         expr_post H ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es s0) /\ local_ptrs_reserved cenv sa /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?ff u. gas_marked_exec F (ctx,func) (write_place cx (MemoryPlace id []) v)
      (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
      !H. valid_horizon cx st0 H ff.storage_trace ==>
        stmt_post H ctx func cx lctx cenv cenv sa sf es s0 (INL ()) ff u
Proof
  rpt gen_tac >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                          gas_marked_exec_valid_prefix)) >>
     impl_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     simp[]) >>
  `expr_post H ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s /\
   stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id ee.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `store_lays_out etv entry.type v` by
    (qpat_x_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs v es1 entry. _` irule >>
     qexistsl [`ee with gas_obs := []`,
       `gas_explicit marks s0.vs_gas_readings ++ []`] >> simp[]) >>
  `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule eval_read_preserves_scopes_dom >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) s` by
    (drule_all expr_post_alloca_frame >> simp[]) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `eval_operand op s = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by
    (qpat_assum `stmt_state_rel H _ _ _ _ (ee with gas_obs := []) s` mp_tac >>
     match_mp_tac EQ_IMPLIES >>
     simp_tac (srw_ss()) [stmt_state_rel_def, state_rel_gas_obs,
                          immutable_alloca_sep_def]) >>
  drule_all assign_local_word_store_path >> strip_tac >>
  `local_ptrs_rel func cenv ee.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `?w. lookup_var p s = SOME w /\ 32 <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     rewrite_tac[local_ptrs_rel_def] >> strip_tac >>
     qpat_x_assum `!name entry p sz. lookup_scopes _ _ = _ /\ _ ==> _`
       (qspecl_then [`id`, `entry`, `p`, `sz`] mp_tac) >>
     simp[] >> strip_tac >> fs[stmtSimDeclStoreTheory.store_lays_out_def]) >>
  `ee.scopes = pre ++ env :: rest /\ id IN FDOM env` by
    (drule vyperLookupTheory.find_containing_scope_structure >>
     simp[finite_mapTheory.FLOOKUP_DEF]) >>
  `local_region cenv ee.scopes s id (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `!ad len. ad + len <= w2n w \/ w2n w + 32 <= ad ==>
     mem_bytes_at ad len t.vs_memory = mem_bytes_at ad len s.vs_memory` by
    (rpt strip_tac >>
     `t.vs_memory = (mstore (w2n w) (typed_val_to_w256 etv v) s).vs_memory` by
       (qpat_assum `!w. lookup_var p s = SOME w ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `t.vs_memory = _` (fn th => REWRITE_TAC [th]) >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     decide_tac) >>
  `alloca_frame cenv es sa s0 cenv (ee with scopes :=
     pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t` by
    (qspecl_then [`H`, `ctx`, `func`, `cx`] mp_tac
       (Q.GENL [`H`, `ctx`, `func`, `cx`]
         (Q.INST [`c` |-> `cenv`, `es1` |-> `ee with gas_obs := []`,
           `b` |-> `w2n (w:bytes32)`, `z` |-> `sz`, `n0` |-> `32`,
           `ee` |-> `ee with scopes :=
              pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest`]
           alloca_frame_local_store)) >>
     impl_tac >- (simp[pred_setTheory.ABSORPTION_RWT] >> rpt conj_tac
       >- (qpat_assum `ee.scopes = _` (fn th =>
             qpat_assum `local_region _ ee.scopes _ _ _ _`
               (mp_tac o REWRITE_RULE [th])) >> simp[])
       >- (qpat_assum `ee.scopes = _` (fn th =>
             qpat_assum `MAP FDOM (ee with gas_obs := []).scopes = _`
               (mp_tac o SIMP_RULE (srw_ss()) [th])) >> simp[])
       >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  qexistsl [`ee with scopes :=
    pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest`, `t`] >>
  conj_tac >- simp[gas_marked_exec_def] >>
  qx_gen_tac `H'` >> simp[] >> strip_tac >>
  `valid_horizon cx st0 H' es.storage_trace` by metis_tac[] >>
  `expr_post H' ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s /\
   stmt_state_rel H' ctx func cenv cx es s0` by metis_tac[] >>
  qpat_x_assum `expr_post H' _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `stmt_state_rel H' ctx func cenv cx ee s` by
    (qpat_assum `stmt_state_rel H' _ _ _ _ (ee with gas_obs := []) s` mp_tac >>
     match_mp_tac EQ_IMPLIES >>
     simp_tac (srw_ss()) [stmt_state_rel_def, state_rel_gas_obs,
                          immutable_alloca_sep_def]) >>
  `storage_well_formed_on cx ee (FST H')` by
    (qpat_assum `storage_well_formed_on cx (ee with gas_obs := []) _` mp_tac >>
     match_mp_tac EQ_IMPLIES >>
     `!b. get_storage cx (ee with gas_obs := []) b = get_storage cx ee b` by
       (Cases >> simp_tac (srw_ss()) [vyperStorageBackendTheory.get_storage_def]) >>
     pop_assum (fn th => simp_tac (srw_ss())
       [vyperStorageFootprintTheory.storage_well_formed_on_def, th])) >>
  `stmt_state_rel H' ctx func cenv cx (ee with scopes :=
     pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t` by
    (`stmt_state_rel H' ctx func cenv cx (ee with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
        (mstore (w2n w) (typed_val_to_w256 etv v) s)` by
       (irule stmt_state_rel_write_local_store >> simp[] >> metis_tac[]) >>
     `t = mstore (w2n w) (typed_val_to_w256 etv v) s with
            vs_inst_idx := SUC s.vs_inst_idx` by
       (qpat_assum `!w. lookup_var p s = SOME w ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     simp[stmt_state_rel_inst_idx]) >>
  `storage_well_formed_on cx (ee with scopes :=
     pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
     (FST H')` by
    fs[vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageBackendTheory.get_storage_scopes] >>
  simp[stmt_post_def, stmt_lands_def] >>
  simp[cenv_top_ext_refl] >> metis_tac[]
QED
