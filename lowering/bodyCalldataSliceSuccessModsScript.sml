(* Introduce the successful linked outcome at the single checked copy endpoint. *)
Theory bodyCalldataSliceSuccessMods
Ancestors
  bodyCalldataSliceSuccessResourcesMods bodyCalldataSliceLinkedFrameMods
  bodyCalldataSliceValuePostMods gasOutcomeFullPostMods stateRelProj
  exprSimCalldataSlice exprSimWordArgs bodyFullPostsMods loweringPosts
  vyperContext vyperState vyperInterpreter vyperStorageFootprint
  exprLoweringProps compileEnv context valueTypingMemoryProps vfmConstants words
Libs monadsyntax

val ann = ``BaseT (BytesT (Dynamic m))``;
val E = ``Builtin ^ann (CalldataSlice n) [e]``;
val v = ``BytesV (TAKE n (DROP a cx.txn.calldata))``;
val N = ``type_memory_bytes cenv ^ann``;
val reached = ``
  expr_post_mods (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx e es sa sm s0 mid (IntV (&a)) x t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1``;

Theorem calldata_slice_success_outcome_mods:
  expr_type e = BaseT (UintT 256) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_slice_calldata x (Lit (n2w n)) ^N sm = (out,sb) /\
  vv = LocatedValue ^ann (mk_ptr out LocMemory) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  (!y sz. cenv.ce_return_buf = SOME (PtrVar (Var y) sz) ==> not_fresh_at sm y) /\
  (!y sz. cenv.ce_return_pc = SOME (PtrVar (Var y) sz) ==> not_fresh_at sm y) /\
  0 < n /\ n <= m /\ 32+n <= ^N /\ ^N < dimword (:256) /\
  a < dimword (:256) /\ a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata /\
  context_well_typed cx /\
  eval_operand x t = SOME (n2w a) /\ op_prov G1 x = NONE /\ op_taint tn1 x = {} /\
  (!y. x = Var y ==> not_fresh_at sm y) /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\
  (ctx_has_dalloca ctx ==>
    t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (IntV (&a)),mid with gas_obs := tail)) /\
  mid.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> ^reached) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (\u. ((case builtin_result cx u.accounts ^ann (CalldataSlice n)
                 [expr_type e] [IntV (&a)] of
             INL r => INL (Value r) | INR ex => INR ex),u))
    (mid,t,G1,tn1)
    (\H res ee G tn z. ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx ^E es sa sb s0 ee tv vv z /\
      vv_store_bound cx (post_value_type cenv ^E) (lowered_value_type cenv ^E) ee tv vv z /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn z /\
      ptr_vv_ok cx (post_value_type cenv ^E) tv vv ee G tn z /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv ^E) /\
           ~is_bytestring_type (post_value_type cenv ^E) ==>
           vv_own cenv cx (post_value_type cenv ^E) sa sb ee tv vv z /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv ^E) = SOME rt /\
                    eval_operand (vv_operand vv) z = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv ^E) ==>
               ptr_buf_ok cenv ^E op G z) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok cenv ^E p.ptr_operand G z) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n < dimword (:256)` by decide_tac >>
  `m < dimword (:256)` by
    (`m <= 32 * word_size m` by simp[word_size_capacity] >>
     `^N = 32 + 32 * word_size m` by
       (simp_tac bool_ss [type_memory_bytes_def,word_size_def] >> decide_tac) >>
     decide_tac) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx mid t /\
   t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
   alloca_history func t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ^reached`
       (drule_then strip_assume_tac) >>
     fs[expr_post_mods_def,expr_post_def]) >>
  drule_all_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choose_then `p` (qx_choose_then `w` (qx_choose_then `z`
      (qx_choose_then `HG` (qx_choose_then `tm`
        (map_every assume_tac o CONJUNCTS)))))))
    (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
       (INST_TYPE [``:'b`` |-> ``:256``] calldata_slice_success_resources_mods)) >>
  qpat_x_assum `out = Var p` SUBST_ALL_TAC >>
  irule gas_outcome_full_mods_pure >> (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`HG`,`mid`,`INL (Value ^v)`,`z`,`tm`] >> conj_tac
  >- (simp[builtin_result_def,vyperContextTheory.evaluate_builtin_def,
            evaluate_calldata_slice_uint] >> fs[dimword_def] >> decide_tac) >>
  gen_tac >> disch_tac >> conj_tac >- (first_x_assum irule) >>
  suspend "post"
QED

Resume calldata_slice_success_outcome_mods[post]:
  rename1 `valid_horizon cx st0 H mid.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ^reached`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
       irule >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx mid t /\ immutable_frame_mods func cenv cx mid t` by
    fs[expr_post_mods_def,expr_post_def] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `ghost_inv_at_mods (DF H) lo d cenv cx mid HG tm z /\
   immutable_frame_mods func cenv cx mid z` by
    (irule calldata_slice_linked_frame_mods >> qexistsl_tac [`G1`,`t`,`sm`,`tn1`] >>
     rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL (IntV (&a)),mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
       qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,frame])))) >>
  `!y. not_fresh_at sm y ==> lookup_var y z = lookup_var y t` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `(stmt_state_rel H ctx func cenv cx mid t ==> stmt_state_rel H ctx func cenv cx mid z)` by
    (strip_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `^N = ^N` by REFL_TAC >>
  qhdtm_assum `expr_post_mods`
    (mp_then Any (fn post =>
       qpat_assum `compile_slice_calldata _ _ _ _ = _`
         (mp_then Any (drule_all_then (map_every assume_tac o CONJUNCTS)) post))
       (SIMP_RULE bool_ss [LET_THM] calldata_slice_value_post_mods)) >>
  BETA_TAC >> qexists_tac `Value ^v` >>
  fs[post_value_type_def,vyperASTTheory.expr_type_def,vv_location_def,mk_ptr_def,is_bytestring_type_def]
QED

Finalise calldata_slice_success_outcome_mods
