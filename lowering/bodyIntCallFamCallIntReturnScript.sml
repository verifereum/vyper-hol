(* Nested internal call, return side: from the INVOKE, with the callee's
   run as packaging gives it, to the producer's normal certificate for the
   call (intcall_expr_producer's post at the call's entry s0, es0, sa). *)
Theory bodyIntCallFamCallIntReturn
Ancestors
  bodyIntCallJointContract bodyIntCallSeamDefs
  bodyIntCallFamCallIntReturnDispatch bodyIntCallAssemblySource
  bodyIntCallAssembly bodyIntCallSource bodyIntCallImmutableFrame
  bodyIntCallMetadata bodyIntCallWidenedPost bodyIntCallRestoreResults
  gasSummary gasOutcome fragGasMode gasContext exprSimCopy
  loweringPosts vyperInterpreter vyperState compileEnv venomExecSemantics
  exprSimHypsDefs exprSimDefs bodyIntCallCompletedFacts
  bodyIntCallFamCallIntReturnFrame bodyIntCallFamCallIntReturnResources
  vyperPlaceWriteSoundness vyperImmutableMetadataFrame
  exprLoweringProps stmtSimProps bodyMemoryDefs freshWrites
  bodyIntCallJointCallCore exprOperandVar exprSimSubscriptMap
Libs
  monadsyntax

(* Resource transport uses immutable metadata, not equality of values: a
   constructor call may initialize an immutable without changing its type. *)
Theorem intcall_expr_res_metadata_frame:
  intcall_frame_ok fp /\
  intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env ee /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  allocas_above fp.jc_lo u /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
     lookup_var x u = SOME w) /\
  (!n p k. local_region ce ee.scopes u n p k ==>
     local_region ce es.scopes s n p k) /\
  immutable_metadata_frame es ee ==>
  intcall_expr_res fp ce env ee sb u
Proof
  strip_tac >>
  qpat_x_assum `intcall_expr_res _ _ _ _ _ _` mp_tac >>
  simp[intcall_expr_res_def] >> strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok ce sb u` by
    (irule ret_pc_ok_frame >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  `return_buf_frame fp.jc_rb ce sb u` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  `fp.jc_reserved fp.jc_rpc` by fs[intcall_frame_ok_def] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >>
      qexists `sa` >> simp[])
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  drule immutable_metadata_frame_value_lookup >>
  disch_then (qspecl_then [`fp.jc_cx.txn.target`,`ce.ce_module`,`nm`,`tv`,`iv`]
    mp_tac) >>
  Cases_on `ALOOKUP ee.immutables fp.jc_cx.txn.target` >>
  Cases_on `ALOOKUP es.immutables fp.jc_cx.txn.target` >>
  gvs[vyperStateTheory.get_source_immutables_def] >> metis_tac[]
QED

(* The cleanup outcome carries the spatial facts on its physical witness. *)
Theorem intcall_nested_return_enriched:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function fp.jc_cx.in_deploy name fp.jc_tops =
    SOME (mut,F,args,[],ret,ss) /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) fp.jc_tops /\
  compile_expr ce ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es0 sa s0 /\
  intcall_entry fp.jc_tops fp.jc_ctx fp.jc_func ce fp.jc_cx env name es
    sa sb vv s0 es0 (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  intcall_expr_res fp ce env (es1 with scopes := prev) sa t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rbs,pvs) /\
  (!callee entered bb inst lbl arg_ops argv.
     gas_invoke_entry (fp.jc_ctx,fp.jc_func) t callee entered /\
     lookup_block t.vs_current_bb fp.jc_func.fn_blocks = SOME bb /\
     get_instruction bb t.vs_inst_idx = SOME inst /\
     decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv ==>
     gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,callee)
       (intcall_callee_src fp.jc_cx name ss) (es1,entered) (\res ee r. F)
       (intcall_callee_exit fp.jc_func ce fp.jc_cx rtv rcn
         (if rcn = 0 /\ ce.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT
          then SOME (HD argv) else NONE) sa.cs_next_id sb.cs_next_id t)) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (intcall_rest fp.jc_cx name mut ss prev rtv) (es1,t)
    (\res ee out. ?tv. res = INL tv /\
      vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx
        (Call ann (IntCall (NONE,name)) es dflt) es0 sa sb s0 ee tv vv out /\
      out.vs_current_bb = sb.cs_current_bb /\
      out.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~out.vs_halted /\
      s0.vs_alloca_next <= out.vs_alloca_next /\ intcall_expr_res fp ce env ee sb out /\
      (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt) <> NoneT /\
       ~is_word_type (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) /\
       ~is_bytestring_type (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) ==>
       ?buf aid off. vv = LocatedValue
         (ce.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr buf) /\
         eval_operand buf.buf_operand out = SOME (n2w off) /\
         FLOOKUP out.vs_allocas aid = SOME (off,buf.buf_size) /\
         type_memory_size rtv <= buf.buf_size /\ off + buf.buf_size < dimword (:256)))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `ce.ce_func_return_type (nsid_to_string (NONE,name)) = ret` by
    (drule_all body_internal_decl_return_type >> simp[]) >>
  `rcn = returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ret` by
    (drule_all body_internal_decl_return_count >> simp[]) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv fp.jc_cx)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `wb_frame ce es0 sa s0 t` by
    (qpat_assum `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[intcall_entry_def] >> strip_tac >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!n b sz. local_region ce es0.scopes s0 n b sz ==>
    local_region ce prev t n b sz` by
    (rpt strip_tac >> irule (expr_inv_local_regions_transport
       |> Q.INST [`esB` |-> `es1 with scopes := prev`] |> SRULE []) >>
     qexistsl [`fp.jc_cx`,`env`,`es1`,`es0`,`s0`,`sa`] >>
     fs[intcall_expr_res_def, wb_frame_def]) >>
  qpat_assum `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[intcall_entry_def] >> strip_tac >>
  qpat_x_assum `ce.ce_func_info _ = (rc',rbs',pvs')` mp_tac >>
  qpat_assum `ce.ce_func_info _ = (rcn,rbs,pvs)` (fn th => rewrite_tac[th]) >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `rcn = rc'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `rbs = rbs'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `pvs = pvs'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!callee entered bb inst lbl arg_ops argv. _` drule_all >> strip_tac >>
  rewrite_tac[intcall_rest_def] >> pure_once_rewrite_tac[GSYM intcall_callee_src_def] >>
  irule invoke_cleanup_outcome >>
  conj_tac >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
    rewrite_tac[intcall_rest_def] >> pure_once_rewrite_tac[GSYM intcall_callee_src_def] >> simp[]) >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_invoke_entry _ _ _ _`)) >>
  qexists `\v ee ir cs. intcall_callee_exit fp.jc_func ce fp.jc_cx rtv rcn
    (if rcn = 0 /\ ret <> NoneT then SOME (HD argv) else NONE)
    sa.cs_next_id sb.cs_next_id t (INL v) ee (IntRet ir cs)` >>
  reverse conj_tac >- metis_tac[intcall_callee_exit_def] >>
  rpt strip_tac >> suspend "physical"
QED

Resume intcall_nested_return_enriched[physical]:
  `expr_sim_inv ce fp.jc_cx env (ee with <|scopes := prev; gas_obs := []|>)` by
    (drule_all intcall_entry_marked_restore_inv >> simp[]) >>
  `immutable_metadata_frame es1 ee` by
    (drule_at Any marked_exec_immutable_metadata >>
     metis_tac[intcall_callee_src_metadata]) >>
  `immutable_alloca_sep fp.jc_func ce fp.jc_cx (ee with scopes := prev) t` by
    (`immutable_alloca_sep fp.jc_func ce fp.jc_cx (es1 with scopes := prev) t` by
       (qpat_assum `stmt_state_rel _ _ _ _ (es1 with scopes := prev) t` mp_tac >>
        pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >>
        first_assum ACCEPT_TAC) >>
     irule marked_body_immutable_alloca_sep >> goal_assum (drule_at Any) >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[intcall_callee_src_def] >> strip_tac >> goal_assum (drule_at Any)) >>
  `gas_path fp.jc_ctx callee entered (LENGTH marks) (IntRet ir cs)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `(\v ee ir cs. _) _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [intcall_callee_exit_def, expr_exit_def]) >>
  `local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo t /\
    (!a k. fp.jc_prot a k ==> a + k <= fp.jc_lo)` by
    (qpat_assum `intcall_expr_res _ _ _ _ _ t` mp_tac >>
     qpat_assum `intcall_frame_ok fp` mp_tac >>
     pure_rewrite_tac[intcall_expr_res_def, intcall_frame_ok_def] >>
     rpt strip_tac >> metis_tac[]) >>
  suspend "dispatch"
QED

Resume intcall_nested_return_enriched[dispatch]:
  drule (intcall_physical_return_resources |>
    Q.SPEC `rcn` |>
    Q.INST [`lo` |-> `fp.jc_lo`, `P` |-> `fp.jc_prot`, `cty` |-> `ret`]) >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `gas_path _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `state_rel _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `LENGTH _ = _`)) >>
  disch_then (drule_at (Pat `value_has_type _ _`)) >>
  disch_then (qspecl_then [`HD argv`,`vv`,`ret`,`rbs`,`lbl`,`fp`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> conj_tac
    >- (qpat_assum `rcn = 0 /\ _ ==> st2 = _ /\ _` mp_tac >>
        qpat_assum `ce.ce_func_return_type _ = ret` mp_tac >>
        qpat_assum `rcn = returns_stack_count _ _` mp_tac >>
        qpat_assum `lbl = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
    qpat_assum `0 < rcn \/ _ ==> _` mp_tac >>
    qpat_assum `ce.ce_func_return_type _ = ret` mp_tac >>
    qpat_assum `rcn = returns_stack_count _ _` mp_tac >>
    qpat_assum `lbl = _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
    metis_tac[])) >>
  disch_then (qx_choose_then `k` (qx_choose_then `out` assume_tac)) >>
  qpat_x_assum `gas_path _ _ _ _ _ /\ _`
    (map_every assume_tac o CONJUNCTS) >>
  suspend "endpoint"
QED

Resume intcall_nested_return_enriched[endpoint]:
  `~out.vs_halted` by
    (drule_at Any fragGasPathTheory.gas_path_normal >> simp[]) >>
  `intcall_expr_res fp ce env
     (ee with <|scopes := prev; gas_obs := []|>) sb out` by
    (irule intcall_expr_res_metadata_frame >>
     asm_rewrite_tac[] >>
     qexistsl [`es1 with scopes := prev`, `t`, `sa`] >>
     asm_rewrite_tac[] >>
     reverse (rpt conj_tac)
     >- (qpat_assum `immutable_metadata_frame es1 ee` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[immutable_metadata_frame_def] >>
         metis_tac[])
     >- (drule (cj 1 compile_expr_grows) >> simp[])
     >- (qpat_assum `intcall_expr_res _ _ _ (es1 with scopes := prev) sa t` mp_tac >>
         qpat_assum `intcall_frame_ok fp` mp_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x out = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         pure_rewrite_tac[intcall_frame_ok_def,intcall_expr_res_def] >>
         rpt strip_tac >>
         `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by metis_tac[] >>
         metis_tac[venomStateTheory.eval_operand_def])
     >- (qpat_assum `local_ptrs_reserved ce sa` mp_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x out = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >>
         metis_tac[copy_buffer_local_region_frame]) >>
     rpt strip_tac >> simp[]) >>
  qexistsl [`k`, `out`] >> simp[NoAsms] >>
  conj_tac >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  `s0.vs_alloca_next <= out.vs_alloca_next` by decide_tac >>
  asm_rewrite_tac[] >> suspend "post"
QED

Resume intcall_nested_return_enriched[post]:
  `type_widens_to (get_tenv fp.jc_cx) ret ann` by
    (drule_all body_intcall_source_selection >> strip_tac >>
     `env.type_defs = get_tenv fp.jc_cx` by
       (qpat_assum `expr_sim_inv _ _ env _` mp_tac >>
        disch_then (mp_tac o cj 1 o REWRITE_RULE [expr_sim_inv_def]) >>
        disch_then (mp_tac o cj 1 o REWRITE_RULE
          [vyperTypeInvariantsTheory.env_consistent_def]) >>
        simp[NoAsms, vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     qpat_x_assum `env.type_defs = _` mp_tac >>
     qpat_x_assum `lookup_callable_function _ _ _ = SOME (mut,F,args,[],ret,ss)` mp_tac >>
     qpat_x_assum `lookup_callable_function _ _ _ = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_x_assum `(_ /\ _ /\ _ /\ _) \/ _` strip_assume_tac
  >- suspend "voidpost" >>
  suspend "bufferpost"
QED

Resume intcall_nested_return_enriched[voidpost]:
  `ann = NoneT` by
    (qpat_x_assum `type_widens_to _ _ ann` mp_tac >>
     qpat_x_assum `ret = NoneT` SUBST_ALL_TAC >>
     simp[NoAsms]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ out` mp_tac >>
  qpat_x_assum `wb_frame _ _ _ _ out` mp_tac >>
  qpat_x_assum `ce.ce_func_return_type _ = ret` mp_tac >>
  qpat_x_assum `vv = _` mp_tac >>
  qpat_x_assum `v = NoneV` mp_tac >>
  qpat_x_assum `ret = NoneT` mp_tac >>
  qpat_x_assum `ann = NoneT` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[post_value_type_def, exprLoweringTheory.lowered_value_type_def,
      vyperASTTheory.expr_type_def] >>
  irule exprSimHashTheory.vv_post_frame_intro >>
  simp[vv_holds_def, vv_at_def, post_value_type_def,
    exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def,
    expr_val_rel_def, expr_val_at_def, venomStateTheory.eval_operand_def,
    vyperValueTheory.evaluate_type_def, is_word_type_def,
    valueEncodingTheory.val_in_memory_def, valueEncodingTheory.val_wf_def,
    val_footprint_def, valueEncodingTheory.type_memory_size_def]
QED

Resume intcall_nested_return_enriched[bufferpost]:
  reverse conj_tac
  >- (strip_tac >> qexistsl [`buf`, `aid`, `off`] >> asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ out` mp_tac >>
  qpat_x_assum `wb_frame _ _ _ _ out` mp_tac >>
  qpat_x_assum `ce.ce_func_return_type _ = ret` mp_tac >>
  qpat_x_assum `type_widens_to _ ret ann` mp_tac >>
  qpat_x_assum `evaluate_type _ ret = _` mp_tac >>
  qpat_x_assum `value_has_type rtv v` mp_tac >>
  qpat_x_assum `vv = LocatedValue _ _` mp_tac >>
  qpat_x_assum `eval_operand _ out = _` mp_tac >>
  qpat_x_assum `val_in_memory _ _ _ out.vs_memory` mp_tac >>
  qpat_x_assum `FLOOKUP out.vs_allocas aid = _` mp_tac >>
  qpat_x_assum `sa.cs_next_id <= aid` mp_tac >>
  qpat_x_assum `aid < sb.cs_next_id` mp_tac >>
  qpat_x_assum `val_footprint _ _ <= _` mp_tac >>
  qpat_x_assum `off + buf.buf_size < _` mp_tac >>
  qpat_x_assum `!id lb lsz. local_region _ prev out _ _ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  qpat_x_assum `vv = _` SUBST1_TAC >>
  Cases_on `is_word_type ann`
  >- suspend "wordbuffer" >>
  suspend "widebuffer"
QED

Resume intcall_nested_return_enriched[wordbuffer]:
  `ret = ann` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  gvs[] >>
  irule (bodyIntCallRestoreResultsTheory.allocated_buffer_vv_post
    |> Q.INST [`e` |-> `Call (ce.ce_func_return_type (nsid_to_string (NONE,name))) (IntCall (NONE,name)) call_args dflt`]
    |> SIMP_RULE (srw_ss()) [vyperASTTheory.expr_type_def]) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  simp[] >>
  qexistsl [`aid`, `off`, `buf.buf_size`] >>
  simp[wordsTheory.w2n_n2w] >> metis_tac[]
QED

Resume intcall_nested_return_enriched[widebuffer]:
  `is_bytestring_type ann ==> is_bytestring_type ret` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >>
     metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]) >>
  irule bodyIntCallWidenedPostTheory.widened_allocated_buffer_post >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  simp[] >>
  qexistsl [`aid`, `off`, `buf.buf_size`] >> simp[] >> metis_tac[]
QED

Finalise intcall_nested_return_enriched

(* An allocated result supplies a complete write window above the frame. *)
Theorem intcall_return_allocated_window:
  allocas_above lo out /\
  eval_operand buf.buf_operand out = SOME (n2w off) /\
  FLOOKUP out.vs_allocas aid = SOME (off,buf.buf_size) /\
  type_memory_size tv <= buf.buf_size /\
  off + buf.buf_size < dimword (:256) ==>
  ?w a k. eval_operand (vv_operand (LocatedValue cty (base_ptr buf))) out = SOME w /\
    a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
    a + k < dimword (:256) /\ lo <= a
Proof
  strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  `lo <= off` by metis_tac[intCallFrameTheory.allocas_above_def] >>
  qexistsl [`n2w off`, `off`, `buf.buf_size`] >>
  gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def, wordsTheory.w2n_n2w]
QED

Theorem intcall_return_post_window:
  intcall_expr_res fp ce env ee sb out /\
  evaluate_type (get_tenv fp.jc_cx)
    (ce.ce_func_return_type (nsid_to_string (NONE,name))) = SOME rtv /\
  vv = LocatedValue cty (base_ptr buf) /\
  eval_operand buf.buf_operand out = SOME (n2w off) /\
  FLOOKUP out.vs_allocas aid = SOME (off,buf.buf_size) /\
  type_memory_size rtv <= buf.buf_size /\
  off + buf.buf_size < dimword (:256) ==>
  ~is_word_type (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) /\
   ~is_bytestring_type (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) ==>
   !tv'. evaluate_type (get_tenv fp.jc_cx)
      (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) = SOME tv' ==>
   ?w a k. eval_operand (vv_operand vv) out = SOME w /\
     a <= w2n w /\ type_memory_size tv' + w2n w <= a + k /\
     a + k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)
Proof
  strip_tac >>
  Cases_on `is_word_type ann \/ is_bytestring_type ann`
  >- (gvs[post_value_type_def] >> metis_tac[]) >>
  simp[post_value_type_def, exprLoweringTheory.lowered_value_type_def] >>
  rpt strip_tac >> gvs[] >>
  `allocas_above fp.jc_lo out` by fs[intcall_expr_res_def] >>
  drule_all intcall_return_allocated_window >>
  disch_then (qspec_then `cty` strip_assume_tac) >>
  qexistsl [`w`, `a`, `k`] >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_nested_return:
  !fp ce env ann name es dflt ty sa sb vv s0 es0 mut args ret ss rr
   prev penv rtv es1 t rc rbs pvs.
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    expr_body_pre ce fp.jc_cx env (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    supportedExprs$supported_expr fp.jc_tops (Call ann (IntCall (NONE,name)) es dflt) /\
    lookup_callable_function fp.jc_cx.in_deploy name fp.jc_tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) fp.jc_tops /\
    compile_expr ce ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    intcall_expr_res fp ce env es0 sa s0 /\
    intcall_entry fp.jc_tops fp.jc_ctx fp.jc_func ce fp.jc_cx env name es
      sa sb vv s0 es0 (mut,args,ret,ss,rr) prev penv rtv es1 t /\
    intcall_expr_res fp ce env (es1 with scopes := prev) sa t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ce.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    (!callee entered bb inst lbl arg_ops argv.
       gas_invoke_entry (fp.jc_ctx,fp.jc_func) t callee entered /\
       lookup_block t.vs_current_bb fp.jc_func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME inst /\
       decode_invoke inst = SOME (lbl,arg_ops) /\
       eval_operands arg_ops t = SOME argv ==>
       gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,callee)
         (intcall_callee_src fp.jc_cx name ss) (es1,entered) (\res ee r. F)
         (intcall_callee_exit fp.jc_func ce fp.jc_cx rtv rc
            (if rc = 0 /\
                ce.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT
             then SOME (HD argv) else NONE)
            sa.cs_next_id sb.cs_next_id t)) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (intcall_rest fp.jc_cx name mut ss prev rtv) (es1,t)
      (\res ee u. ?tv. res = INL tv /\
         vv_holds ce fp.jc_cx
           (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) tv vv ee u /\
         vv_at ce fp.jc_cx
           (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt))
           sa sb ee tv vv u /\
         (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt) <>
            expr_type (Call ann (IntCall (NONE,name)) es dflt) ==>
          vv_own ce fp.jc_cx
            (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt))
            sa sb ee tv vv u) /\
         (~expr_has_effect (Call ann (IntCall (NONE,name)) es dflt) ==>
          vv_storage_live fp.jc_cx vv ee u) /\
         (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
         (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt) <> NoneT /\
          ~is_word_type
             (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) /\
          ~is_bytestring_type
             (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) /\
          (case vv of StackValue _ _ => T
                    | LocatedValue _ p => p.ptr_location = LocMemory) ==>
          !tv'. evaluate_type (get_tenv fp.jc_cx)
                  (post_value_type ce (Call ann (IntCall (NONE,name)) es dflt)) =
                  SOME tv' ==>
            ?w a k. eval_operand (vv_operand vv) u = SOME w /\
              a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
              a + k < dimword (:256) /\
              (fp.jc_lo <= a \/
               ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
         intcall_expr_cont fp ce env es0 sa s0 ee sb u)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (`local_ptrs_reserved ce sa` by fs[intcall_expr_res_def] >>
     drule (CONJUNCT1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `ce.ce_func_return_type (nsid_to_string (NONE,name)) = ret` by
    (drule_all bodyIntCallAssemblyTheory.body_internal_decl_return_type >> simp[]) >>
  `evaluate_type (get_tenv fp.jc_cx) ret = SOME rtv` by
    (drule intcall_entry_source >> simp[]) >>
  drule_all intcall_nested_return_enriched >>
  strip_tac >>
  irule exprSimSubscriptMapTheory.gas_outcome_conseq >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `intcall_expr_res fp ce env ee sb out` >>
  qexists `tv` >> simp[] >>
  `intcall_expr_cont fp ce env es0 sa s0 ee sb out` by
    (irule intcall_expr_cont_vv_post >>
     metis_tac[]) >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [vv_post_def]) >>
  fs[post_value_type_def] >> rpt strip_tac >>
  qpat_x_assum `_ ==> ?buf aid off. _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule intcall_return_post_window >>
  goal_assum (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  simp[post_value_type_def] >> metis_tac[]
QED
