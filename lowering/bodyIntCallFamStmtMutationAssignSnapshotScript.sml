(* Assign's lowered-type capture boundary. *)
Theory bodyIntCallFamStmtMutationAssignSnapshot
Ancestors
  bodyIntCallJointContract bodyIntCallJointAggCore bodyPtrIfExpSourceTyping
  exprPtrUnwrapStorageShape abiEncodeArgsSim abiEncodeMaterialize
  exprSimHyps valueCopyBytes context loweringPosts
  bodyIntCallFamAggSubscriptAllocRun placeMemoryPrimitiveForward loweringHalt
  exprExtRequestOperandSafety exprSafeOperand

Theorem intcall_assign_lowered_value:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  compile_expr ce ty e sa = (vv,sb) /\
  eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx (post_value_type ce e) raw vv ee s ==>
  vv_holds ce cx (lowered_value_type ce e) raw
    (vv_with_type (lowered_value_type ce e) vv) ee s /\
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
       value_has_type tv v
Proof
  strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
        value_has_type tv v` by
    metis_tac[ifexp_source_lowered_typed] >>
  reverse conj_tac >- metis_tac[] >>
  Cases_on `vv`
  >- (gvs[vv_with_type_def, vv_holds_def] >>
      irule abi_args_rel_lowered_transport >> simp[] >>
      metis_tac[memoryValueTypingTheory.value_has_type_val_wf]) >>
  rename1 `LocatedValue ann p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- (Cases_on `is_word_type (expr_type e)`
      >- (`lowered_value_type ce e = expr_type e` by
            (drule expr_body_pre_lowered_fits >>
             qmatch_goalsub_abbrev_tac `lt = et` >>
             Cases_on `lt` >> Cases_on `et` >>
             gvs[vyperTypeSystemTheory.arg_type_fits_def, compileEnvTheory.is_word_type_def] >>
             rpt strip_tac >> Cases_on `b` >> Cases_on `b'` >>
             gvs[vyperTypeSystemTheory.arg_type_fits_def,
                 compileEnvTheory.is_word_type_def] >>
             Cases_on `b` >> Cases_on `b''` >>
             gvs[vyperTypeSystemTheory.arg_type_fits_def,
                 compileEnvTheory.is_word_type_def]) >>
          gvs[vv_holds_def, vv_with_type_def]) >>
      `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
        metis_tac[expr_body_pre_lowered_fits] >>
      drule_all materialize_post_lowered_classify >> strip_tac
      >- gvs[vv_holds_def, vv_with_type_def] >>
      `post_value_type ce e = expr_type e \/
       post_value_type ce e = lowered_value_type ce e` by
        (Cases_on `e` >> simp[post_value_type_def] >>
         rename1 `Call _ ct _ _` >> Cases_on `ct` >>
         simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
         IF_CASES_TAC >> simp[]) >>
      `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
        metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
      gvs[vv_holds_def, vv_with_type_def, is_bytestring_word_type] >>
      rpt strip_tac >>
      irule bytestring_val_in_memory_transfer >> simp[] >>
      qexistsl [`post_value_type ce e`, `lowered_value_type ce e`,
                `get_tenv cx`, `ptv`] >> simp[]) >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[compile_nonmemory_lowered_value_type] >>
  `post_value_type ce e = expr_type e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ ct _ _` >> Cases_on `ct` >>
     simp[post_value_type_def, exprLoweringTheory.lowered_value_type_def,
          vyperASTTheory.expr_type_def] >> metis_tac[]) >>
  gvs[vv_holds_def, vv_with_type_def]
QED

(* Forcing consumes the lowered layout.  In precisely the nonbytes aggregate
   case that requires a producer window, that layout is the producer layout. *)
Theorem intcall_assign_unwrap_type:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  type_alloc_ok ce (lowered_value_type ce e) ==>
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  (~is_word_type (lowered_value_type ce e) /\
   ~is_bytestring_type (lowered_value_type ce e) ==>
   post_value_type ce e = lowered_value_type ce e)
Proof
  strip_tac >>
  conj_tac
  >- (irule expr_sim_inv_memory_size >>
      gvs[exprSimHypsDefsTheory.expr_body_pre_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[allocLimitsTheory.type_alloc_ok_def] >>
      `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by
        (irule expr_sim_inv_memory_size >>
         gvs[exprSimHypsDefsTheory.expr_body_pre_def] >> metis_tac[]) >>
      Cases_on `is_word_type (lowered_value_type ce e)` >> gvs[] >>
      `type_memory_size tv = 32` by
        metis_tac[stmtSimReturnTheory.word_type_sizes] >> simp[]) >>
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type e)` by
    metis_tac[exprSimLayoutTransportTheory.compatible_word_type] >>
  metis_tac[materialize_post_lowered_classify]
QED

Theorem intcall_assign_materialize_prepare:
  compile_materialize_vv ce ty vv sa = (dst,sb) /\ ~is_word_type ty /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  vv_holds ce fp.jc_cx ty r vv es s /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   ?w a k. eval_operand (vv_operand vv) s = SOME w /\
     a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,mid) /\
  unwrap_value ce vv mid = (src,su) /\
  compile_store_memory ce src buf.buf_operand ty ty su = ((),sb) /\
  dst = buf.buf_operand ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es su u /\
    expr_val_rel fp.jc_cx ty v src u /\
    eval_operand dst u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    sa.cs_next_id < su.cs_next_id /\ fp.jc_lo <= w2n w /\
    w2n w + type_memory_size tv < dimword (:256) /\
    (!x. src = Var x ==> not_fresh_at su x) /\
    (!x. dst = Var x ==> not_fresh_at su x) /\
    (!n b k. local_region ce es.scopes s n b k ==>
       regions_disjoint (w2n w) (type_memory_size tv) b k) /\
    (!n b k. local_region ce es.scopes u n b k ==>
       regions_disjoint (w2n w) (type_memory_size tv) b k) /\
    ci_mono sa su /\ ci_mono su sb /\ fn_has_code su sb fp.jc_func /\
    (?i. MEM i (fn_insts fp.jc_func) /\ i.inst_opcode = ALLOCA /\
         i.inst_id = sa.cs_next_id)
Proof
  strip_tac >>
  `ci_mono sa mid /\ ci_mono mid su /\ ci_mono su sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      exprLoweringPropsTheory.ci_mono_unwrap_value,
      exprLoweringPropsTheory.ci_mono_compile_store_memory, pairTheory.SND] >>
  `cs_extends sa mid /\ cs_extends mid su /\ cs_extends su sb` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  `cs_extends mid sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sa mid fp.jc_func /\ fn_has_code mid sb fp.jc_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code mid su fp.jc_func /\ fn_has_code su sb fp.jc_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by
    gvs[intcall_expr_res_def] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq _ s = OK q` >>
  drule_all intcall_alloc_run_cont >> strip_tac >>
  drule_all intcall_alloc_run_frame >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
      (OK (q with vs_inst_idx := LENGTH mid.cs_current_insts))` by
    (irule straight_line_zero_gas_path >>
     simp[] >> qexistsl [`emitted_insts sa mid`, `sa`] >> simp[] >>
     drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
     gvs[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
         venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  `vv_holds ce fp.jc_cx ty r vv es
      (q with vs_inst_idx := LENGTH mid.cs_current_insts)` by
    (irule exprSimVVFrameTheory.vv_holds_vars_frame >> qexists `s` >>
     simp[] >>
     fs[venomStateTheory.venom_state_component_equality,
        venomStateTheory.contract_storage_def,
        venomStateTheory.contract_transient_def] >>
     Cases_on `vv_operand vv` >>
     gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> gvs[exprLoweringPropsTheory.ci_mono_def]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
     eval_operand op (q with vs_inst_idx := LENGTH mid.cs_current_insts) =
     eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >>
     gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
         venomStateTheory.venom_state_component_equality]) >>
  `intcall_expr_res fp ce env es mid
      (q with vs_inst_idx := LENGTH mid.cs_current_insts) /\
   ~(q with vs_inst_idx := LENGTH mid.cs_current_insts).vs_halted /\
   (q with vs_inst_idx := LENGTH mid.cs_current_insts).vs_current_bb = mid.cs_current_bb` by
    gvs[intcall_expr_cont_def] >>
  drule_at (Pat `vv_holds _ _ _ _ _ _ _`) intcall_unwrap_landing >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`v`, `tv`] mp_tac) >>
  (impl_tac >-
    (simp[] >> gvs[])) >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es mid _ es su u` >>
  `intcall_expr_cont fp ce env es sa s es su u` by
    (irule intcall_expr_cont_trans >> simp[] >>
     qexistsl [`es`, `mid`, `q with vs_inst_idx := LENGTH mid.cs_current_insts`] >>
     gvs[exprLoweringPropsTheory.ci_mono_def]) >>
  `eval_operand buf.buf_operand u = SOME w` by
    (gvs[intcall_expr_cont_def, venomStateTheory.eval_operand_def,
         venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv)` by
    (gvs[intcall_expr_cont_def] >> metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
   local_ptrs_reserved ce su /\ ~u.vs_halted /\
   u.vs_current_bb = su.cs_current_bb /\
   u.vs_inst_idx = LENGTH su.cs_current_insts` by
    gvs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `!n b k. local_region ce es.scopes u n b k ==>
     regions_disjoint (w2n w) (type_memory_size tv) b k` by
    (rpt strip_tac >>
     `local_region ce es.scopes q n b k` by
       (irule stmtSimDefsTheory.local_region_kept >>
        reverse conj_tac
        >- (qexistsl [`fp.jc_ctx`, `fp.jc_cx`, `fp.jc_func`] >> simp[]) >>
        qexistsl [`es`, `u`, `mid`] >>
        gvs[intcall_expr_cont_def, intcall_expr_res_def,
            venomStateTheory.lookup_var_def]) >>
     metis_tac[]) >>
  `ci_mono sa su` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  `sa.cs_next_id < su.cs_next_id` by
    (gvs[exprLoweringPropsTheory.ci_mono_def,
         compileEnvTheory.cs_extends_def] >> decide_tac) >>
  `!x. src = Var x ==> not_fresh_at su x` by
    metis_tac[bodyIntCallJointForceTheory.unwrap_value_operand_reserved] >>
  `!x. dst = Var x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `mid` >> gvs[exprLoweringPropsTheory.ci_mono_def]) >>
  `fp.jc_lo <= w2n w` by
    (gvs[intcall_expr_cont_def, intcall_expr_res_def,
         intCallFrameTheory.allocas_above_def] >> metis_tac[]) >>
  `!n b k. local_region ce es.scopes s n b k ==>
     regions_disjoint (w2n w) (type_memory_size tv) b k` by
    (rpt strip_tac >>
     `local_region ce es.scopes q n b k` by
       (gvs[loweringStateRelDefsTheory.local_region_def,
            venomStateTheory.lookup_var_def] >>
        `not_fresh_at sa p'` by
          metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
        simp[]) >>
     metis_tac[]) >>
  qexistsl [`u`, `w`] >> simp[] >>
  rpt conj_tac
  >- metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD]
  >- gvs[]
  >- metis_tac[]
  >- metis_tac[] >>
  qexists `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce ty))]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  simp[venomInstTheory.mk_inst_def]
QED

Theorem intcall_assign_materialize_path:
  compile_materialize_vv ce ty vv sa = (dst,sb) /\ ~is_word_type ty /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  vv_holds ce fp.jc_cx ty r vv es s /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   ?w a k. eval_operand (vv_operand vv) s = SOME w /\
     a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es sa s es sb t /\
    eval_operand dst t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    sa.cs_next_id < sb.cs_next_id /\ fp.jc_lo <= w2n w /\
    w2n w + type_memory_size tv < dimword (:256) /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    (!n b k. local_region ce es.scopes s n b k ==>
       regions_disjoint (w2n w) (type_memory_size tv) b k) /\
    (!n b k. local_region ce es.scopes t n b k ==>
       regions_disjoint (w2n w) (type_memory_size tv) b k)
Proof
  strip_tac >> drule materialize_compile_trace >> strip_tac >>
  drule_all intcall_assign_materialize_prepare >> strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
   local_ptrs_reserved ce su /\ ~u.vs_halted /\
   u.vs_current_bb = su.cs_current_bb /\
   u.vs_inst_idx = LENGTH su.cs_current_insts` by
    gvs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables fp.jc_cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)` by
    (match_mp_tac (GEN_ALL intcall_owned_destination_immutable_clear) >>
     qexists `u` >> qexists `type_memory_size tv` >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists `w2n w` >> simp[] >>
     simp[]) >>
  `?sw. eval_operand src u = SOME sw /\
        val_in_memory tv v (w2n sw) u.vs_memory` by
    gvs[expr_val_rel_def] >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    intcall_compatible_store_effect >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  disch_then (qspecl_then [`v`, `tv`, `w`] mp_tac) >>
  (impl_tac >- (gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[])) >>
  strip_tac >>
  `alloca_inv u` by
    gvs[intcall_expr_cont_def, intcall_expr_res_def,
        exprLoweringPropsTheory.stmt_state_rel_def] >>
  `intcall_expr_cont fp ce env es sa s es sb u'` by
    (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)
       intcall_owned_store_cont >>
     disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
     disch_then (qspecl_then [`type_memory_size tv`, `w2n w`, `sa.cs_next_id`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     gvs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_def,
         loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `eval_operand dst u' = SOME w` by
    metis_tac[bodyIntCallCopySharpDynamicTheory.typed_copy_effect_operand_preserved] >>
  `u'.vs_allocas = u.vs_allocas` by
    metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_allocas] >>
  `!n b k. local_region ce es.scopes u' n b k <=>
           local_region ce es.scopes u n b k` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists `su` >> simp[] >>
     metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_lookup]) >>
  qexistsl [`u'`, `w`] >> simp[] >> rpt conj_tac
  >- metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_path,
       fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD]
  >- (gvs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_def] >>
      decide_tac)
  >- metis_tac[freshWritesTheory.not_fresh_at_mono,
              exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[]
QED

Theorem intcall_assign_snapshot_path:
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es0 /\
  compile_expr ce ety e si = (vv,sa) /\
  eval_expr fp.jc_cx e es0 = (INL raw,es) /\
  read_result fp.jc_cx raw es = (INL v,es) /\
  vv_holds ce fp.jc_cx (post_value_type ce e) raw vv es s /\
  (take ==> type_alloc_ok ce (lowered_value_type ce e)) /\
  (if take then compile_snapshot_vv ce T
       (vv_with_type (lowered_value_type ce e) vv) sa
   else (vv,sa)) = (saved,sb) /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (post_value_type ce e <> NoneT /\
   ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) /\
   (case vv of StackValue _ _ => T
     | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv' ==>
     ?w a k. eval_operand (vv_operand vv) s = SOME w /\
       a <= w2n w /\ w2n w + type_memory_size tv' <= a+k /\
       a+k < dimword (:256) /\
       (fp.jc_lo <= a \/
        ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t tv. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es sa s es sb t /\
    evaluate_type (get_tenv fp.jc_cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\
    (!x. vv_operand saved = Var x ==> not_fresh_at sb x) /\
    (~take ==> saved = vv /\ sb = sa /\ t = s) /\
    (take ==>
      vv_type saved = lowered_value_type ce e /\
      expr_val_rel fp.jc_cx (lowered_value_type ce e) v (vv_operand saved) t /\
      (is_word_type (lowered_value_type ce e) ==>
         saved = StackValue (lowered_value_type ce e) (vv_operand saved)) /\
      (~is_word_type (lowered_value_type ce e) ==>
        saved = LocatedValue (lowered_value_type ce e)
                  (mk_ptr (vv_operand saved) LocMemory) /\
        ?w. eval_operand (vv_operand saved) t = SOME w /\
          val_in_memory tv v (w2n w) t.vs_memory /\
          FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
          sa.cs_next_id < sb.cs_next_id /\ fp.jc_lo <= w2n w /\
          w2n w + type_memory_size tv < dimword (:256) /\
          (!n b k. local_region ce es.scopes t n b k ==>
             regions_disjoint (w2n w) (type_memory_size tv) b k)) /\
      (!ee sc u. intcall_expr_cont fp ce env es sb t ee sc u ==>
         expr_val_rel fp.jc_cx (lowered_value_type ce e) v (vv_operand saved) u))
Proof
  strip_tac >> drule_all intcall_assign_lowered_value >> strip_tac >>
  Cases_on `take`
  >- (gvs[] >>
      drule_all intcall_assign_unwrap_type >> strip_tac >>
      `vv_type (vv_with_type (lowered_value_type ce e) vv) =
         lowered_value_type ce e /\
       vv_operand (vv_with_type (lowered_value_type ce e) vv) = vv_operand vv` by
        (Cases_on `vv` >> simp[vv_with_type_def, vv_type_def, vv_operand_def]) >>
      `lowered_value_type ce e <> NoneT /\
       ~is_word_type (lowered_value_type ce e) /\
       ~is_bytestring_type (lowered_value_type ce e) /\
       (case vv_with_type (lowered_value_type ce e) vv of
          StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
       ?w a k. eval_operand (vv_operand (vv_with_type (lowered_value_type ce e) vv)) s = SOME w /\
         a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
         (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)` by
        (strip_tac >> `post_value_type ce e = lowered_value_type ce e` by metis_tac[] >>
         Cases_on `vv` >> gvs[vv_with_type_def] >> metis_tac[]) >>
      Cases_on `is_word_type (lowered_value_type ce e)`
      >- (gvs[exprLoweringTheory.compile_snapshot_vv_def,
               compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
               AllCaseEqs()] >>
          Cases_on `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) sa` >>
          gvs[] >>
          drule_at (Pat `unwrap_value _ _ _ = _`) intcall_unwrap_landing >>
          disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
          disch_then (qspecl_then [`v`, `tv`, `env`] mp_tac) >>
          (impl_tac >- simp[]) >> strip_tac >>
          `!x. q = Var x ==> not_fresh_at r x` by
            (drule_at (Pat `unwrap_value _ _ _ = _`)
               bodyIntCallJointForceTheory.unwrap_value_operand_reserved >> simp[]) >>
          `!l. vv_operand vv <> Label l` by
            (drule_at (Pat `compile_expr _ _ _ _ = _`)
               (CONJUNCT1 extrequest_compiler_nonlabel) >>
             disch_then (qspec_then `env` mp_tac) >>
             simp[] >>
             gvs[exprSimHypsDefsTheory.expr_body_pre_def,
                 exprSimHypsDefsTheory.expr_sim_inv_def]) >>
          `!l. q <> Label l` by
            (drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_not_label >> simp[]) >>
          qexists_tac `u` >> simp[vv_operand_def, vv_type_def] >>
          rpt strip_tac >>
          gvs[intcall_expr_cont_def, expr_val_rel_def] >>
          Cases_on `q` >> gvs[venomStateTheory.eval_operand_def] >>
          metis_tac[]) >>
      gvs[exprLoweringTheory.compile_snapshot_vv_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
          AllCaseEqs()] >>
      Cases_on `compile_materialize_vv ce (lowered_value_type ce e)
                  (vv_with_type (lowered_value_type ce e) vv) sa` >> gvs[] >>
      drule_at (Pat `compile_materialize_vv _ _ _ _ = _`)
        intcall_assign_materialize_path >>
      disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
      disch_then (qspecl_then [`v`, `tv`, `env`] mp_tac) >>
      (impl_tac >- (simp[] >>
         gvs[wordsTheory.dimword_def] >> metis_tac[])) >> strip_tac >>
      `?x. q = Var x` by
        (drule_at (Pat `compile_materialize_vv _ _ _ _ = _`) materialize_compile_trace >>
         strip_tac >>
         drule bodyPtrMakeArrayAllocBufferTheory.alloc_buffer_emitted >>
         strip_tac >> metis_tac[]) >>
      qexists_tac `t` >>
      simp[vv_operand_def, vv_type_def, contextTheory.mk_ptr_def] >>
      conj_tac >- (simp[expr_val_rel_def] >> metis_tac[]) >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >>
      `eval_operand q u = SOME w` by
        (gvs[intcall_expr_cont_def, venomStateTheory.eval_operand_def] >> metis_tac[]) >>
      `mem_bytes_at (w2n w) (type_memory_size tv) u.vs_memory =
       mem_bytes_at (w2n w) (type_memory_size tv) t.vs_memory` by
        (gvs[intcall_expr_cont_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
         qpat_x_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _` irule >>
         conj_tac >- (rpt gen_tac >> strip_tac >>
           qpat_x_assum `!n b k. local_region ce es.scopes t n b k ==> _` drule >>
           simp[]) >>
         qexists_tac `sa.cs_next_id` >> simp[]) >>
      simp[expr_val_rel_def] >>
      qexists_tac `w` >> gvs[] >>
      irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
      conj_tac >- metis_tac[memoryValueTypingTheory.value_has_type_val_wf] >>
      qexistsl_tac [`type_memory_size tv`, `t.vs_memory`] >>
      simp[memoryValueTypingTheory.value_has_type_val_wf]) >>
  gvs[] >>
  simp[intcall_expr_cont_def] >>
  simp[fragGasModeTheory.gas_marked_path_def, fragGasPathTheory.gas_path_rules]
QED
