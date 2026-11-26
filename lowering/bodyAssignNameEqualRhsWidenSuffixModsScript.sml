(* Install an equal-layout RHS into a wider local on the typed copy's own run. *)
Theory bodyAssignNameEqualRhsWidenSuffixMods
Ancestors
  bodyAssignLocalInstallMods bodyLocalCopyWritesMods bodyLocalTypedCopyPathMods
  bodyFullPostsMods bodyFullShared bodyMemoryDefs bodyPtrDefs exprSimWordArgs
  fragGasOriginPtr freshWrites gasExplicitSites loweringPosts loweringStateRelDefs
  placeMemoryStateRebuild ptrDiscipline stmtSimDefs typedMemoryCopy
  vyperStorageTrace vyperStorageFootprint vyperState wordArgsPtr
Libs monadsyntax

Theorem assign_name_equal_rhs_widen_suffix_mods:
  lowered_value_type cenv e = expr_type e /\ expr_type e <> ty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  ~is_bytestring_type ty /\ ~is_word_type ty /\ 0 < type_memory_bytes cenv ty /\
  compile_assign_value cenv (Var p) LocMemory (Var xs) F loc ty
    (lowered_value_type cenv e) (type_memory_bytes cenv ty) sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sb /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      len = type_memory_size tv) fields) /\
  opr = Var xs /\ ~is_word_type (lowered_value_type cenv e) /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
  type_memory_bytes cenv ty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sm xs /\ not_fresh_at sm p /\
  lookup_var xs u = SOME sw /\ lookup_var p u = SOME dw /\
  ptr_covers Gi ti xs u (type_memory_size stv) /\ ptr_covers Gi ti p u cap /\
  (!m. mem_agree_outside ti.t_mem u.vs_memory m ==> val_in_memory stv v (w2n sw) m) /\
  local_region cenv mid.scopes u id (w2n dw) cap /\ type_memory_size dtv <= cap /\
  w2n sw + type_memory_size stv <= u.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (loc = SOME LocMemory ==>
    expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v (Var xs) u /\
    ?b len. b <= w2n dw /\ w2n dw + type_memory_size dtv <= b + len /\
      ((?name. local_region cenv mid.scopes u name b len) \/
       ?aid. aid < sm.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,len))) /\
  (loc <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n dw \/ w2n dw + type_memory_size dtv <= w2n sw) /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\ lo <= w2n dw /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  (!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_scopes id mid.scopes = SOME entry /\ entry.type = dtv /\
  value_has_type dtv entry.value /\ well_formed_type_value dtv /\
  (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)) /\
  write_place cx (MemoryPlace id []) v mid = (INL (),ff) /\
  ff.storage_trace = mid.storage_trace /\ mid.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gi ti u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gi ti /\
    (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) u)) ==>
  ?t Gf tf.
    (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
        (INL (),ff with gas_obs := tail)) /\ ff.storage_trace = mid.storage_trace /\
    !H. valid_horizon cx st0 H ff.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gi,ti) [] (OK t,Gf,tf) /\
      ?ce. stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
        (~block_is_terminated sb /\ ce = cenv) /\ cenv_top_ext cenv ce (ff with gas_obs := []).scopes /\
        stmt_state_rel H ctx func ce cx (ff with gas_obs := []) t /\
        immutable_frame_mods func ce cx (ff with gas_obs := []) t /\
        storage_well_formed_on cx (ff with gas_obs := []) (FST H) /\
        return_buf_frame d ce sb t /\ alloca_history func t /\ return_buf_sep d ce (ff with gas_obs := []) t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx (ff with gas_obs := []) Gf tf t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
        (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
        (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 ce (ff with gas_obs := []) t /\
        (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
           (!n b len. local_region cenv es.scopes s0 n b len ==>
              off+sz <= b \/ b+len <= off) /\
           off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `opr = Var xs` SUBST_ALL_TAC >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gen_tac >> strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H0 ctx func cenv cx mid u` by fs[expr_post_mods_def,expr_post_def] >>
  suspend "path"
QED

Resume assign_name_equal_rhs_widen_suffix_mods[path]:
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
    (mp_then (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`) mp_tac
      (Q.INST [`PG` |-> `PG`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
        (SPEC_ALL local_typed_copy_path_mods))) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME sw`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME dw`)) >>
  disch_then (drule_at (Pat `ptr_covers Gi ti p u cap`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME stv`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME dtv`)) >>
  disch_then (drule_at (Pat `local_ptrs_reserved cenv sm`)) >>
  disch_then (qspecl_then [`v`,`sa`,`shadow_ctx`,`lo`,`PG`] mp_tac) >>
  impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, disj2_tac >> first_assum ACCEPT_TAC,
      rpt gen_tac >> strip_tac >> first_assum irule >> first_assum drule >> simp[]]) >>
  disch_then (qx_choosel_then [`snap`,`sc`,`Gs`,`ts`,`t`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >> conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` ACCEPT_TAC)) >>
  suspend "horizon"
QED

Resume assign_name_equal_rhs_widen_suffix_mods[horizon]:
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `ff.storage_trace = mid.storage_trace` (fn eq =>
       qpat_assum `valid_horizon cx st0 H ff.storage_trace`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `ff with gas_obs := [] = ff` by
    (drule write_memory_place_entry_update >> strip_tac >>
     qpat_assum `ff = mid with scopes := _` (once_rewrite_tac o single) >>
     simp[evaluation_state_component_equality]) >>
  pop_assum (once_rewrite_tac o single) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     pop_assum (fn eq => qpat_assum `!tail. bind _ _ _ = _`
        (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind_all,cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then assume_tac) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `stmt_state_rel H ctx func cenv cx mid snap /\ immutable_frame_mods func cenv cx mid snap /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gs ts snap` by
    (rpt conj_tac >> first_assum (irule o SPEC_ALL) >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
   s0.vs_alloca_next <= snap.vs_alloca_next` by
    (rpt conj_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
     FIRST [qexists_tac `sm.cs_next_var` >> conj_tac >> first_assum ACCEPT_TAC,
            qexists_tac `sm.cs_next_id` >> conj_tac >> first_assum ACCEPT_TAC,
            qexists_tac `u.vs_alloca_next` >> conj_tac >> first_assum ACCEPT_TAC]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (gen_tac >> strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x snap = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` (drule_then ACCEPT_TAC)) >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ lookup_var x snap = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> _`
       (drule_all_then assume_tac) >> simp[]) >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP snap.vs_allocas aid = SOME a` by
    (rpt strip_tac >> qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> _`
       (drule_then assume_tac) >>
     qpat_assum `!aid a. FLOOKUP u.vs_allocas aid = SOME a ==> _` (drule_then ACCEPT_TAC)) >>
  `return_buf_frame d cenv sc snap` by
    (irule return_buf_frame_frame >> goal_assum (drule_at (Pat `return_buf_frame _ _ sa s0`)) >>
     pure_rewrite_tac[REFL_CLAUSE,AND_CLAUSES] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_sep d cenv mid snap` by suspend "separation" >>
  `alloca_frame cenv es sa s0 cenv mid snap` by suspend "alloca_frame" >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gs ts` by suspend "kept" >>
  suspend "install"
QED

Resume assign_name_equal_rhs_widen_suffix_mods[separation]:
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> conj_tac
  >- (rpt gen_tac >> disch_tac >> pure_rewrite_tac[allocas_from_def] >> rpt gen_tac >> disch_tac >>
      qpat_assum `!aid off len. FLOOKUP snap.vs_allocas aid = SOME (off,len) ==> _`
        (drule_then strip_assume_tac)
      >- (qpat_assum `!bw capacity. d = SOME (bw,capacity) ==> allocas_from _ u`
            (drule_then (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))) >>
      `w2n bw + capacity <= s0.vs_alloca_next` by
        (qpat_assum `return_buf_frame d cenv sa s0` mp_tac >>
         qpat_assum `d = SOME _` (fn th => pure_rewrite_tac[th,return_buf_frame_def]) >>
         rpt strip_tac >> first_assum ACCEPT_TAC) >>
      irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `s0.vs_alloca_next` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `u.vs_alloca_next` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `return_buf_sep _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ es s0`)) >>
  qexists_tac `sa` >> simp[]
QED

Resume assign_name_equal_rhs_widen_suffix_mods[alloca_frame]:
  irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_expr_prefix) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`mid`,`sm`,`u`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume assign_name_equal_rhs_widen_suffix_mods[kept]:
  `ghost_kept_at lo cenv mid sm Gi ti u Gs ts` by
    (pure_rewrite_tac[ghost_kept_at_def] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, rpt strip_tac >>
        qpat_assum `!x. not_fresh_at sm x ==> _ /\ lookup_var x snap = _ /\ _`
          (drule_then strip_assume_tac) >> simp[]]) >>
  irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gi`,`mid`,`mid`,`u`,`sm`,`ti`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    sym_tac >> first_assum ACCEPT_TAC,
    qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >> drule_then ACCEPT_TAC expr_post_frame]
QED

Resume assign_name_equal_rhs_widen_suffix_mods[install]:
  `mem_path_offset entry.type [] = SOME (0,dtv)` by simp[mem_path_offset_def] >>
  `local_region cenv mid.scopes snap id (w2n dw) cap` by simp[] >>
  `!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sc x` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x len. cenv.ce_return_buf = _ ==> _` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` (drule_then ACCEPT_TAC)) >>
  `!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sc x` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x len. cenv.ce_return_pc = _ ==> _` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` (drule_then ACCEPT_TAC)) >>
  `!x. not_fresh_at sc x ==> FLOOKUP Gf x = FLOOKUP Gs x /\ op_taint tf (Var x) = op_taint ts (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x t = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  irule (REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
    (Q.INST [`k` |-> `0`] (SPEC_ALL
       (INST_TYPE [alpha |-> ``:256``] assign_local_install_post_mods)))) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  goal_assum (drule_at (Pat `lookup_scopes _ _ = SOME _`)) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = SOME _`)) >>
  goal_assum (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, MATCH_ACCEPT_TAC arithmeticTheory.LESS_EQ_REFL,
    qpat_assum `entry.type = dtv` (once_rewrite_tac o single) >> first_assum ACCEPT_TAC,
    disch_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL local_copy_immutable_frame_mods))]
QED

Finalise assign_name_equal_rhs_widen_suffix_mods
