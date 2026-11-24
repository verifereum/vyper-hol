(* Dispatch at the successful RHS cut. In the raw branch, the only new
   execution starts at the chosen VV endpoint and emits no GAS marks. *)
Theory bodyCopyReachedRhsMods
Ancestors
  bodyCopyReachedValueMods bodyCopyReachedIdentityMods
  bodyCopyReachedMaterializedMods bodyCopySlotRhsEndpointMods
  bodyCopyRuntimeRhsRunMods bodyCopyCtorRhsRunMods bodyCopyReadPhysicalTypeMods
  exprPtrUnwrapStorageShape exprOperandVar exprSimHyps valueCopyBytes
  fragExec exprSimUnwrap exprLoweringProps gasContext valueTypingMemoryProps
  bodyFullShadowBodyInv bodyFullPostsMods loweringPosts ptrDiscipline
  exprSimMemorySource vyperStorageFootprint vyperState exprLowering compileEnv
  bodyCopyEqualRhsTypeMods
  words arithmetic context bodyLocalCopyPhysicalRhsMods

Theorem reached_located_tag_mods[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv (LocatedValue ty p) s ==>
  p.ptr_location <> LocCalldata /\
  (ty = post_value_type ce e \/
    p.ptr_location = LocMemory /\ is_bytestring_type ty /\
    is_bytestring_type (post_value_type ce e))
Proof
  simp[vv_post_mods_def,vv_holds_mods_def,vv_holds_def] >>
  Cases_on `p.ptr_location` >> simp[] >> metis_tac[]
QED

Theorem reached_immutable_nonwrap[local]:
  immutable_holds ce cx ty tv w ee s /\
  evaluate_type (get_tenv cx) ty = SOME rt ==>
  w2n w + type_memory_size rt < dimword (:256)
Proof
  rw[immutable_holds_def,sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  `rt = tvt` by fs[] >>
  simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem reached_pre_gas_obs[local]:
  expr_body_pre_mods mods ce cx env e es ==>
  !gs. expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)
Proof
  `!gs. expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
        expr_body_pre_mods mods ce cx env e es` by
    simp_tac (srw_ss()) [exprSimHypsDefsTheory.expr_body_pre_mods_def,
                        exprSimHypsDefsTheory.expr_sim_inv_mods_def] >>
  simp[]
QED

(* The post and lowered bytestring tags may differ in capacity but have
   the same footprint for the value that was actually read. *)
Theorem reached_bytes_origin_mods[local]:
  is_bytestring_type pty /\ is_bytestring_type sty /\
  evaluate_type (get_tenv cx) pty = SOME pt /\
  evaluate_type (get_tenv cx) sty = SOME rt /\
  value_has_type pt v /\ value_has_type rt v /\
  expr_val_at ce cx pty sa sb ee v op s ==>
  expr_val_at ce cx sty sa sb ee v op s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_footprint pt v = val_footprint rt v` by
    (drule_all_then ACCEPT_TAC bytestring_val_footprint_eq) >>
  `val_wf rt v` by simp[value_has_type_memory_wf] >>
  `?p r. pt = BaseTV p /\ rt = BaseTV r` by metis_tac[bytestring_type_value] >>
  gvs[expr_val_at_def,is_bytestring_word_type] >>
  metis_tac[exprSimPropsTheory.local_val_at_base,arithmeticTheory.LESS_EQ_REFL]
QED

val raw_rhs_prefix = ``
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!tail. eval_expr cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL tv,ee with gas_obs := tail)) /\
  read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,Gi,ti) marks (OK s,G,tn) /\
     vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!t x. vv = StackValue t x /\ ~is_word_type (post_value_type ce e) ==>
          ptr_buf_ok ce e x G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v'. read_result cx tv ee = (INL v',ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
            eval_operand (vv_operand vv) s = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                   val_in_memory rt v' (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s0.vs_alloca_next <= s.vs_alloca_next``;

val raw_rhs_result = ``
  ?z Gf tf pt rt w.
    lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,Gi,ti) marks (OK z,Gf,tf) /\
      expr_post_mods H ctx func ce cx e es sa sb s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\
    ptr_buf_ok ce e op Gf z /\ expr_store_bound cx (post_value_type ce e) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    ~is_word_type (post_value_type ce e) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
    value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
    eval_operand op z = SOME w /\ op_taint tf op = {} /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op z /\
    (0 < type_memory_size rt ==>
      ?src. op = Var src /\ not_fresh_at sb src /\ ptr_covers Gf tf src z (type_memory_size rt)) /\
    (!dst cap dw aid chunk. not_fresh_at sa dst /\ lookup_var dst s0 = SOME dw /\
       ptr_covers Gi ti dst s0 cap /\ FLOOKUP s0.vs_allocas aid = SOME chunk ==>
       lookup_var dst z = SOME dw /\ ptr_covers Gf tf dst z cap /\ FLOOKUP z.vs_allocas aid = SOME chunk) /\
    ((sb = sm /\ z = s /\ Gf = G /\ tf = tn /\
      vv_at ce cx (post_value_type ce e) sa sb ee tv
        (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) z) \/
     (sm.cs_next_id < sb.cs_next_id /\
      post_value_type ce e = lowered_value_type ce e /\
      FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size rt) /\
      lo <= w2n w /\
      (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size rt) b len) /\
      wb_frame ce ee ee sm s z /\ ghost_kept_at lo ce ee sm G tn s Gf tf))``;

Theorem reached_rhs_raw_mods:
  ^raw_rhs_prefix ==> ^raw_rhs_result
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,ee with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (assume_tac o REWRITE_RULE[listTheory.APPEND_NIL])) >>
     drule read_result_gas_obs >> simp[bind_def]) >>
  drule_all_then
    (fn th => assume_tac (CONJUNCT1 th) >>
      assume_tac (CONJUNCT1 (CONJUNCT2 th))) copy_read_physical_type_gas_obs_mods >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue ty p` >>
  drule_then (CONJUNCTS_THEN2 assume_tac assume_tac) reached_located_tag_mods >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  Cases_on `p.ptr_location = LocMemory`
  >- suspend "memory" >>
  suspend "materialize"
QED

fun finish_identity vvtac =
  mp_tac (vvtac (Q.INST [`a` |-> `sa`,`b` |-> `sb`,`entry` |-> `s0`]
     local_copy_reached_identity_mods)) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then strip_assume_tac >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >>
     qpat_x_assum `post_value_type ce e = lowered_value_type ce e \/ _`
       (DISJ_CASES_THEN2 (SUBST1_TAC o SYM) strip_assume_tac)
     >- first_assum ACCEPT_TAC >>
     qpat_assum `expr_val_at ce cx (post_value_type ce e) _ _ _ _ _ _`
       (mp_then Any mp_tac reached_bytes_origin_mods) >> simp[]) >>
  qexistsl [`s`,`G`,`tn`,`pt`,`rt`,`w`] >> asm_rewrite_tac[];

Resume reached_rhs_raw_mods[stack]:
  rename1 `unwrap_value ce (StackValue ty src) sm = (op,sb)` >>
  `src = op` by fs[unwrap_value_def,comp_return_def] >>
  qpat_x_assum `src = op` SUBST_ALL_TAC >>
  finish_identity (Q.INST [`vv` |-> `StackValue ty op`])
QED

Resume reached_rhs_raw_mods[memory]:
  `p.ptr_operand = op` by fs[unwrap_value_def,comp_return_def] >>
  finish_identity (Q.INST [`vv` |-> `LocatedValue ty p`])
QED

(* Apply the common linked post only after a route has fixed its physical
   allocation and endpoint. Each branch thus preserves a single path. *)
val finish_materialized =
  qpat_x_assum `op = Var root` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`vv` |-> `LocatedValue ty p`, `nb` |-> `type_memory_size rt`]
    local_copy_reached_materialized_mods) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> asm_rewrite_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`z`,`Gf`,`tf`,`rt`,`rt`,`w`] >>
  asm_rewrite_tac[venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> qexists_tac `root` >> simp[];

Resume reached_rhs_raw_mods[materialize]:
  `ty = post_value_type ce e` by metis_tac[] >>
  `lowered_value_type ce e = expr_type e` by
    (drule_all compile_nonmemory_lowered_value_type >> simp[]) >>
  `post_value_type ce e = lowered_value_type ce e` by simp[post_value_type_lowered] >>
  drule reached_pre_gas_obs >>
  disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` assume_tac) >>
  drule_all copy_nonmemory_rhs_type_mods >>
  disch_then (qx_choose_then `rt` (map_every assume_tac o CONJUNCTS)) >>
  `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
   type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
   type_memory_bytes ce ty = type_memory_size rt` by metis_tac[] >>
  `type_memory_size rt < 2 ** 64` by
    (`alloc_limits_expr ce e` by fs[exprSimHypsDefsTheory.expr_body_pre_mods_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[allocLimitsTheory.type_alloc_ok_def] >>
     metis_tac[]) >>
  `val_wf rt v` by simp[value_has_type_memory_wf] >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved ce sm` by (drule_all local_ptrs_reserved_next_var >> simp[]) >>
  `cs_extends sm sb` by (drule unwrap_value_extends >> simp[]) >>
  `fn_has_code sm sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 compiler_compile_var) >> simp[vv_operand_def]) >>
  Cases_on `p.ptr_location = LocCode`
  >- suspend "code" >>
  `(p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  suspend "slot"
QED

Resume reached_rhs_raw_mods[slot]:
  markerLib.RESUME_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func ce cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  mp_tac (Q.INST [`t` |-> `ty`,`sc` |-> `sb`,`entry` |-> `s0`]
    copy_slot_rhs_endpoint_mods) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`root`,`w`,`mid`,`buf`,`u`,`z`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  finish_materialized
QED

Resume reached_rhs_raw_mods[code]:
  `ce.ce_is_ctor ==> ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand p.ptr_operand s = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                    val_in_memory rt val (w2n w) mem)` by
    (qpat_assum `ce.ce_is_ctor /\ vv_location _ = _ ==> _` mp_tac >>
     pure_rewrite_tac[vv_location_def,vv_operand_def] >> asm_rewrite_tac[]) >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`
    (mp_then Any mp_tac local_copy_raw_code_source_mods) >>
  disch_then (qspecl_then [`v`,`tn`,`rt`,`lo`,`G`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`owner`,`tops`,`src`] (map_every assume_tac o CONJUNCTS))))) >>
  `evaluate_type (get_tenv cx) ty = SOME rt` by
    (qpat_assum `ty = post_value_type ce e` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac reached_immutable_nonwrap >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    fs[vv_post_mods_def] >>
  Cases_on `ce.ce_is_ctor`
  >- suspend "ctor" >>
  suspend "runtime"
QED

Resume reached_rhs_raw_mods[ctor]:
  `type_memory_size rt < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
  qpat_assum `ce.ce_is_ctor ==> w2n src + _ <= lo /\ _` (drule_then strip_assume_tac) >>
  drule_all (Q.INST [`sc` |-> `sb`, `sb` |-> `sm`] copy_ctor_rhs_endpoint_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`] (map_every assume_tac o CONJUNCTS)) >>
  `!j. j < w2n w \/ w2n w + type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem` by
    (rpt gen_tac >> strip_tac >> first_x_assum (drule_then (fn th => simp[th]))) >>
  finish_materialized
QED

Resume reached_rhs_raw_mods[runtime]:
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  qpat_assum `~ce.ce_is_ctor ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_all (Q.INST [`sc` |-> `sb`] copy_runtime_rhs_endpoint_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] mp_tac) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`] (map_every assume_tac o CONJUNCTS)) >>
  `!j. j < w2n w \/ w2n w + type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem` by
    simp[] >>
  finish_materialized
QED

Finalise reached_rhs_raw_mods[local]

(* Use the value child for value-width copies, or the raw child when the
   continuation needs allocation origin or the entire staging window. *)
Theorem local_copy_reached_rhs_mods:
  ^(concl local_copy_reached_value_mods) /\
  (^raw_rhs_prefix ==> ^raw_rhs_result)
Proof
  conj_tac
  >- ACCEPT_TAC local_copy_reached_value_mods
  >> ACCEPT_TAC reached_rhs_raw_mods
QED
