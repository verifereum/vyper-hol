(* Recover the slot-copy operands at the actual post-target unwrap cursor. *)
Theory bodySlotCopySavedMods
Ancestors
  bodyWriteTargetStageMods bodyCopyReadPhysicalTypeMods assignBasePtrBoundary
  bodyFullPostsMods exprOperandVar exprLoweringProps freshWrites stateRelProj
  valueCopyBytes bodyPtrDefs loweringPosts venomState words arithmetic ptrDiscipline context
  bodyLocalCopyPhysicalRhsMods bodyCopyMaterializedRhsPostMods
  bodyCopyCtorRhsRunMods bodyCopyRuntimeRhsRunMods bodyFullShadowBodyInv
  vyperStorageFootprint fragGasOriginPtr finite_map valueTypingMemoryProps bodyFullHashKeccakFixed

(* The unwrap supplier fixes z: for StackValue and nonword LocMemory this
   is the identity cut; for LocCode it is the fresh operand produced by the
   counted cut below. The slot is carried across that very same interval. *)
Theorem slot_copy_saved_input_mods:
  expr_body_pre_mods mods cenv cx env e es /\ ~is_word_type (expr_type e) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  write_target_post_mods H D lo d ctx func cenv cx bt mid sm sb s ee
    (PlaceR (StoragePlace tr k dtv)) (Type dty) r G0 tn0 Gu tu u /\
  unwrap_value cenv vv sb = (op,sc) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  expr_post_mods H ctx func cenv cx e ee sa sc u ee v op z /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn z /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G z) /\
  (~is_word_type (post_value_type cenv e) ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
           eval_operand op z = SOME w ==>
           type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  eval_operand (FST r) z = eval_operand (FST r) u /\
  ghost_kept_at lo cenv ee sb Gu tu u G tn ==>
  eval_operand (FST r) z = SOME k /\ op_taint tn (FST r) = {} /\
  op_prov G (FST r) = NONE /\
  FST (SND r) = SOME (slot_loc tr) /\ SND (SND r) = SOME (ValPT dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  (!x. FST r = Var x ==> not_fresh_at sc x) /\
  stmt_state_rel H ctx func cenv cx ee z /\ immutable_frame_mods func cenv cx ee z /\
  ?rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rt /\
    value_has_type rt v /\ eval_operand op z = SOME w /\ op_taint tn op = {} /\
    (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    (!x. op = Var x ==> not_fresh_at sc x) /\
    (0 < type_memory_size rt ==> ?x. op = Var x /\ ptr_covers G tn x z (type_memory_size rt)) /\
    (~is_bytestring_type (lowered_value_type cenv e) ==>
     expr_val_at cenv cx (lowered_value_type cenv e) sa sc ee v op z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac copy_read_physical_type_gas_obs_mods >>
  drule_then strip_assume_tac write_target_storage_view_mods >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  `sb.cs_next_var <= sc.cs_next_var` by metis_tac[ci_mono_unwrap_value, ci_mono_def, pairTheory.SND] >>
  `!x. FST r = Var x ==> not_fresh_at sc x` by metis_tac[not_fresh_at_mono] >>
  `op_taint tn (FST r) = {} /\ op_prov G (FST r) = NONE` by
    (Cases_on `FST r` >> fs[ghost_kept_at_def,op_taint_def,op_prov_def] >> metis_tac[]) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (drule compiler_unwrap_value_var >> Cases_on `vv` >> simp[vv_operand_def]) >>
  qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def, expr_post_def, expr_val_rel_def]) >>
  asm_rewrite_tac[exprLoweringTheory.value_type_place_def] >>
  qexistsl [`rt`,`w`] >> simp[] >>
  `op_taint tn op = {} /\ (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
      val_in_memory pt v (w2n w) mem)` by fs[ptr_val_ok_def, ptr_mem_ok_def] >>
  `(type_memory_size rt <> 0 ==> w2n w + type_memory_size rt <= z.vs_alloca_next)` by metis_tac[] >>
  `!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem` by
    metis_tac[bytestring_val_in_memory_transfer, optionTheory.SOME_11] >>
  `w2n w + type_memory_size rt < dimword (:256)` by
    (Cases_on `type_memory_size rt = 0` >- fs[w2n_lt] >>
     `z.vs_alloca_next < dimword (:256)` by
       (drule_then (mp_tac o MATCH_MP alloca_room_next_lt) stmt_state_rel_alloca_room >> simp[]) >>
     decide_tac) >>
  `(0 < type_memory_size rt ==> ?x. op = Var x /\ ptr_covers G tn x z (type_memory_size rt))` by
    (strip_tac >> irule ptr_buf_ok_read_covers >> simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  `(~is_bytestring_type (lowered_value_type cenv e) ==>
      expr_val_at cenv cx (lowered_value_type cenv e) sa sc ee v op z)` by metis_tac[] >>
  simp[Once ADD_COMM] >> decide_tac
QED

(* A saved LocCode value is still in its owning module's immutable region
   after target evaluation. Run the emitted unwrap at that cursor; only
   the resulting allocation is a slot-copy source in ordinary memory. *)
Theorem slot_copy_saved_code_unwrap_mods:
  p.ptr_location = LocCode /\
  unwrap_value ce (LocatedValue ty p) sm = (op,sc) /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue ty p) ee G tn s /\
  (ce.ce_is_ctor ==> !rt w.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
    eval_operand p.ptr_operand s = SOME w ==>
    w2n w + type_memory_size rt <= lo /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem) /\
  post_value_type ce e = lowered_value_type ce e /\ ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\ value_has_type rt v /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw (LocatedValue ty p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?z Gf tf w.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s.vs_alloca_next <= z.vs_alloca_next /\
    eval_operand op z = SOME w /\
    w2n w + type_memory_size rt <= z.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es sa sc s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\ ptr_buf_ok ce e op Gf z /\
    expr_store_bound cx (post_value_type ce e) v op z /\
    wb_frame ce ee ee sm s z /\ ghost_kept_at lo ce ee sm G tn s Gf tf /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `ce.ce_is_ctor ==> ?val. read_result cx raw ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand p.ptr_operand s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)` by
    (disch_tac >> qexists `v` >> simp[]) >>
  qhdtm_assum `vv_post_mods` (mp_then Any mp_tac local_copy_raw_code_source_mods) >>
  disch_then (qspecl_then [`v`,`tn`,`rt`,`lo`,`G`] mp_tac) >> asm_rewrite_tac[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`owner`,`tops`,`src`] (map_every assume_tac o CONJUNCTS))))) >>
  `w2n src + type_memory_size rt < dimword (:256)` by
    (qhdtm_assum `immutable_holds`
       (strip_assume_tac o REWRITE_RULE [immutable_holds_def,sub_layout_def]) >>
     `rt = tvt` by metis_tac[optionTheory.SOME_11] >>
     `off + k < dimword (:256)` by decide_tac >>
     simp[w2n_n2w,LESS_MOD] >> decide_tac) >>
  `type_memory_size rt < dimword (:256)` by decide_tac >>
  `~is_word_type ty /\ type_memory_bytes ce ty = type_memory_size rt` by metis_tac[] >>
  `val_wf rt v` by simp[value_has_type_memory_wf] >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `stmt_state_rel H0 ctx func ce cx ee s` by fs[vv_post_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  Cases_on `ce.ce_is_ctor` >- suspend "ctor" >> suspend "runtime"
QED

val saved_code_post_tac =
  qpat_x_assum `op = Var root` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es sa sc s0 ee v (Var root) z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z /\
      ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
      ptr_val_ok cx (post_value_type ce e) v (Var root) Gf tf z /\
      ptr_buf_ok ce e (Var root) Gf z /\
      expr_store_bound cx (post_value_type ce e) v (Var root) z /\
      wb_frame ce ee ee sm s z /\ ghost_kept_at lo ce ee sm G tn s Gf tf` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     mp_tac (Q.INST [`sb` |-> `sc`, `nb` |-> `type_memory_size rt`, `D` |-> `DF H`,
                      `vv` |-> `LocatedValue ty p`, `tv` |-> `raw`]
       (INST_TYPE [alpha |-> ``:256``] copy_materialized_rhs_post_mods)) >>
     (impl_tac >- (gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  qexistsl [`z`,`Gf`,`tf`,`w`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  gvs[SF CONJ_ss];

Resume slot_copy_saved_code_unwrap_mods[ctor]:
  qpat_assum `ce.ce_is_ctor ==> w2n src + _ <= lo /\ _` (drule_then strip_assume_tac) >>
  drule_all (Q.INST [`sb` |-> `sm`] copy_ctor_rhs_endpoint_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`] (map_every assume_tac o CONJUNCTS)) >>
  `!j. j < w2n w \/ w2n w+type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem` by
    (rpt gen_tac >> disch_tac >> first_x_assum (drule_then (fn th => simp[th]))) >>
  saved_code_post_tac
QED

Resume slot_copy_saved_code_unwrap_mods[runtime]:
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  qpat_assum `~ce.ce_is_ctor ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_all copy_runtime_rhs_endpoint_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] mp_tac) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`] (map_every assume_tac o CONJUNCTS)) >>
  `!j. j < w2n w \/ w2n w+type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem` by simp[] >>
  saved_code_post_tac
QED

Finalise slot_copy_saved_code_unwrap_mods
