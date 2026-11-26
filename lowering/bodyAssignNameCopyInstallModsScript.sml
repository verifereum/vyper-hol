(* Install the selected local copy after its optional staging. *)
Theory bodyAssignNameCopyInstallMods
Ancestors
  bodyAssignLocalInstallMods bodyLocalCopyWritesMods bodyFullPostsMods bodyFullShared
  bodyMemoryDefs bodyPtrDefs exprSimWordArgs fragGasOriginPtr freshWrites
  loweringPosts loweringStateRelDefs placeMemoryStateRebuild ptrDiscipline
  stmtSimDefs typedMemoryCopy vyperStorageTrace vyperStorageFootprint vyperState
  wordArgsPtr
Libs monadsyntax

Theorem assign_name_copy_install_mods:
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
      (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] /\
  (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)) /\
  write_place cx (MemoryPlace id []) v mid = (INL (),ff) /\
  ff.storage_trace = mid.storage_trace /\
  lookup_scopes id mid.scopes = SOME entry /\ entry.type = tv /\
  value_has_type tv entry.value /\ well_formed_type_value tv /\ value_has_type tv v /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p z = SOME dw /\
  type_memory_size tv <= cap /\ lo <= w2n dw /\
  (!H : (bool # 256 word # type_value) list # num list.
     valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
     ghost_inv_at_mods (DF H) lo d cenv cx mid Gi ti u /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 Gi ti /\ s0.vs_alloca_next <= u.vs_alloca_next) /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw+capacity) u) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sc /\
  (!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  (!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sc.cs_next_var /\
  sc.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sc.cs_next_id /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gi,ti) [] (OK z,Gz,tz)) /\
  (!H : (bool # 256 word # type_value) list # num list.
     stmt_state_rel H ctx func cenv cx mid u ==> stmt_state_rel H ctx func cenv cx mid z) /\
  (immutable_frame_mods func cenv cx mid u ==> immutable_frame_mods func cenv cx mid z) /\
  (!D. ghost_inv_at_mods D lo d cenv cx mid Gi ti u ==>
       ghost_inv_at_mods D lo d cenv cx mid Gz tz z) /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
       FLOOKUP Gz x = FLOOKUP Gi x /\ op_taint tz (Var x) = op_taint ti (Var x)) /\
  (!aid a. FLOOKUP u.vs_allocas aid = SOME a ==> FLOOKUP z.vs_allocas aid = SOME a) /\
  (!aid off len. FLOOKUP z.vs_allocas aid = SOME (off,len) ==>
       FLOOKUP u.vs_allocas aid = SOME (off,len) \/ u.vs_alloca_next <= off) /\
  u.vs_alloca_next <= z.vs_alloca_next /\
  alloca_frame cenv mid sm u cenv mid z /\
  (!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
       (!n b len. local_region cenv mid.scopes u n b len ==> off+sz <= b \/ b+len <= off) /\
       off <= i /\ i < off+sz /\ i IN tz.t_mem ==> i IN ti.t_mem) /\
  (!n b sz i. local_region cenv mid.scopes u n b sz /\
       b <= i /\ i < b+sz /\ i IN tz.t_mem ==> i IN ti.t_mem) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,Gf,tf)) /\
  typed_copy_state_frame sc (w2n dw) bytes z t /\ bytes <= type_memory_size tv /\
  (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory tv v (w2n dw) m) /\
  (!x. not_fresh_at sc x ==> FLOOKUP Gf x = FLOOKUP Gz x /\
       op_taint tf (Var x) = op_taint tz (Var x)) /\
  tf.t_stor = tz.t_stor /\ tf.t_trans = tz.t_trans /\ tf.t_imm = tz.t_imm /\
  (!i. ~(w2n dw <= i /\ i < w2n dw+bytes) ==> (i IN tf.t_mem <=> i IN tz.t_mem)) /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~block_is_terminated sb /\ ~t.vs_halted /\ alloca_history func t ==>
  (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)) /\ ff.storage_trace = mid.storage_trace /\
  !H. valid_horizon cx st0 H ff.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gi,ti) [] (OK t,Gf,tf) /\
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
         (!n b len. local_region cenv es.scopes s0 n b len ==> off+sz <= b \/ b+len <= off) /\
         off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >> conj_tac >- suspend "path" >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `ff.storage_trace = mid.storage_trace` (fn eq =>
       qpat_assum `valid_horizon cx st0 H ff.storage_trace`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `ff with gas_obs := [] = ff` by
    (drule write_memory_place_entry_update >> strip_tac >>
     qpat_assum `ff = mid with scopes := _` (once_rewrite_tac o single) >>
     simp[evaluation_state_component_equality]) >>
  pop_assum (once_rewrite_tac o single) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     pop_assum (fn eq => qpat_assum `!tail. bind _ _ _ = _`
        (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  `valid_horizon cx st0 H es.storage_trace` by suspend "entry_horizon" >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then ACCEPT_TAC)) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_mods_def]) >>
  `stmt_state_rel H ctx func cenv cx mid z` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ u ==> _` irule >>
     drule_then ACCEPT_TAC expr_post_state) >>
  `immutable_frame_mods func cenv cx mid z` by
    (qpat_assum `immutable_frame_mods _ _ _ _ u ==> _` irule >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx mid Gz tz z` by
    (qpat_assum `!D. ghost_inv_at_mods D _ _ _ _ _ _ _ u ==> _` irule >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
   s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x /\ not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w` by suspend "vars" >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP z.vs_allocas aid = SOME a` by suspend "allocas" >>
  `return_buf_frame d cenv sc z` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `return_buf_sep d cenv mid z` by suspend "separation" >>
  `alloca_frame cenv es sa s0 cenv mid z` by suspend "alloca_frame" >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz` by suspend "kept" >>
  suspend "install"
QED

Resume assign_name_copy_install_mods[path]:
  irule (SIMP_RULE (srw_ss()) [] (Q.SPECL [`cfg`,`start`,`[]`] gas_origin_ptr_path_append)) >>
  qexistsl_tac [`Gz`,`z`,`(OK z,Gz,tz)`,`tz`] >> simp[]
QED

Resume assign_name_copy_install_mods[entry_horizon]:
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind_all,cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  drule valid_horizon_frame >> disch_then drule >> simp[]
QED

Resume assign_name_copy_install_mods[vars]:
  rpt strip_tac >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> _`
    (drule_all_then assume_tac) >>
  `not_fresh_at sm x` by
    (qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then (assume_tac o CONJUNCT1)) >>
  simp[]
QED

Resume assign_name_copy_install_mods[allocas]:
  rpt strip_tac >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> _` (drule_then assume_tac) >>
  qpat_assum `!aid a. FLOOKUP u.vs_allocas aid = SOME a ==> _` (drule_then ACCEPT_TAC)
QED

Resume assign_name_copy_install_mods[separation]:
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> conj_tac
  >- (rpt gen_tac >> disch_tac >> pure_rewrite_tac[allocas_from_def] >> rpt gen_tac >> disch_tac >>
      qpat_assum `!aid off len. FLOOKUP z.vs_allocas aid = SOME (off,len) ==> _`
        (drule_then strip_assume_tac)
      >- (qpat_assum `!bw capacity. d = SOME (bw,capacity) ==> allocas_from _ u`
            (drule_then (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))) >>
      `w2n bw + capacity <= s0.vs_alloca_next` by
        (qpat_assum `return_buf_frame d cenv sa s0` mp_tac >>
         qpat_assum `d = SOME _` (fn th => pure_rewrite_tac[th,return_buf_frame_def]) >>
         rpt strip_tac >> first_assum ACCEPT_TAC) >>
      decide_tac) >>
  goal_assum (drule_at (Pat `return_buf_sep _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ es s0`)) >>
  qexists_tac `sa` >> simp[]
QED

Resume assign_name_copy_install_mods[alloca_frame]:
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_expr_prefix) >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`mid`,`sm`,`u`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume assign_name_copy_install_mods[kept]:
  `ghost_kept_at lo cenv mid sm Gi ti u Gz tz` by
    (pure_rewrite_tac[ghost_kept_at_def] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, rpt strip_tac >>
        qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >> simp[]]) >>
  irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gi`,`mid`,`mid`,`u`,`sm`,`ti`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    sym_tac >> first_assum ACCEPT_TAC, drule_then ACCEPT_TAC expr_post_frame]
QED

Resume assign_name_copy_install_mods[install]:
  `mem_path_offset entry.type [] = SOME (0,tv)` by simp[mem_path_offset_def] >>
  `bytes <= cap` by decide_tac >>
  `storage_well_formed_on cx mid (FST H)` by fs[expr_post_def] >>
  `!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sc x` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x len. cenv.ce_return_buf = _ ==> _` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sc x` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x len. cenv.ce_return_pc = _ ==> _` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
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
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qpat_assum `entry.type = tv` (once_rewrite_tac o single) >> first_assum ACCEPT_TAC,
    disch_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL local_copy_immutable_frame_mods))]

QED

Finalise assign_name_copy_install_mods
