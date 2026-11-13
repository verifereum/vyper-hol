Theory bodyIntCallNrEndpoint
Ancestors
  bodyIntCallNrCompiler bodyIntCallNrVoid bodyIntCallNrMemory bodyIntCallNrStack
  bodyIntCallSeamDefs bodyIntCallMetadata bodyIntCallSource bodyIntCallWidenedPost
  bodySim supportedNames supportedProgram memoryLocalRhsProps compileVyper
  compileEnv exprLoweringProps loweringPosts bodyIntCallRestoreResults exprLowering
  fragExec externalReturnBufferlessCopyProbe vyperTyping vyperInterpreter
  venomExecSemantics venomState vyperState vyperImmutableAccessFrame
  vyperTypeEvalSoundness bodyIntCallReturnSource bodyIntCallCompletedFacts
Libs monadsyntax

Theorem nr_declared_return_type:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  ce.ce_func_return_type (nsid_to_string (NONE,name)) = ret
Proof
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (fs[body_inv_def] >> drule supported_program_names >>
     simp[supported_declaration_names_def]) >>
  `build_func_return_type tops name = ret` by
    (irule build_func_return_type_distinct >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  fs[body_inv_def, nsid_to_string_def]
QED

Theorem nr_allocated_call_post:
  ce.ce_func_return_type (nsid_to_string (NONE,name)) = cty /\
  type_widens_to (get_tenv cx) cty ann /\
  evaluate_type (get_tenv cx) cty = SOME tv /\ value_has_type tv v /\
  stmt_state_rel ctx func ce cx ee s /\ wb_frame ce es ee sa s0 s /\
  eval_operand buf.buf_operand s = SOME w /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!id lb lsz. local_region ce ee.scopes s id lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) ==>
  vv_post ctx func ce cx (Call ann (IntCall (NONE,name)) args dflt)
    es sa sb s0 ee (Value v) (LocatedValue cty (base_ptr buf)) s
Proof
  strip_tac >> Cases_on `is_word_type ann`
  >- (drule_all type_widens_to_word >> strip_tac >> gvs[] >>
      irule (SRULE [vyperASTTheory.expr_type_def]
        (Q.INST [`e` |-> `Call ann (IntCall (NONE,name)) args dflt`]
          (SPEC_ALL allocated_buffer_vv_post))) >>
      simp[post_value_type_def, lowered_value_type_def] >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule widened_allocated_buffer_post >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (fs[vyperTypeSystemTheory.type_widens_to_def] >>
      metis_tac[arg_type_fits_bytestring_source]) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem nr_callee_success_separation:
  intcall_callee_src cx name mut nr ss es = (INL v,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu) /\
  immutable_alloca_sep func ce cx (es with scopes := prev) t ==>
  immutable_alloca_sep func ce cx (eu with scopes := prev) t
Proof
  strip_tac >>
  `?u el. lock_if_nr cx nr (is_view_mut mut) es = (INL u,el)` by
    (qpat_x_assum `intcall_callee_src _ _ _ _ _ _ = _` mp_tac >>
     pure_rewrite_tac[intcall_callee_src_def, ignore_bind_def, bind_def] >>
     Cases_on `lock_if_nr cx nr (is_view_mut mut) es` >>
     rename1 `_ = (res,el)` >> Cases_on `res` >> simp[]) >>
  Cases_on `u` >>
  qpat_assum `lock_if_nr _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [lock_if_nr_def]) >>
  disch_then (strip_assume_tac o MATCH_MP intcall_lock_state_preserves_frame) >>
  `immutable_alloca_sep func ce cx (el with scopes := prev) t` by
    (irule immutable_alloca_sep_fields >>
     qexistsl_tac [`t`,`es with scopes := prev`] >> simp[] >> metis_tac[]) >>
  `immutable_alloca_sep func ce cx (ee with scopes := prev) t` by
    (irule function_body_immutable_alloca_sep >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`cx with stk updated_by CONS (NONE,name)`,`INL v`,`ss`] >>
     qpat_x_assum `intcall_callee_src _ _ _ _ _ _ = _` mp_tac >>
     simp[intcall_callee_src_def, ignore_bind_def, bind_def,
       Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  drule unlock_if_nr_immutables >> strip_tac >>
  irule immutable_alloca_sep_fields >>
  qexistsl_tac [`t`,`ee with scopes := prev`] >> simp[] >> metis_tac[]
QED

Theorem nr_marked_callee_success_separation:
  gas_marked_exec F (ctx,callee) (intcall_callee_src cx name mut nr ss)
    (es,entered) marks (INL v) ee r /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu) /\
  immutable_alloca_sep func ce cx (es with scopes := prev) t ==>
  immutable_alloca_sep func ce cx (eu with scopes := prev) t
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gasSummaryTheory.gas_marked_exec_def,
    Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >> strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `ee.gas_obs` assume_tac) >>
  irule nr_callee_success_separation >>
  goal_assum (drule_at Any) >>
  simp[Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem intcall_nr_return_endpoint:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  intcall_entry tops ctx func ce cx env name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv tv es1 t /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = ((nret:num),rbs,pvs) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_adopt_fmp = NONE /\ LENGTH ir.iret_values = nret /\
  value_has_type tv v /\ intret_vals_match tv v ir.iret_values /\
  state_rel func ce cx (ee with scopes := []) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!bb inst lbl arg_ops argv.
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
    nret = 0 /\ ret <> NoneT ==>
    val_in_memory tv v (w2n (HD argv)) cs.vs_memory) ==>
  ?k out. gas_path ctx func t (n+k) (OK out) /\
    vv_post ctx func ce cx (Call ann (IntCall (NONE,name)) es dflt)
      es0 sa sb s0 (ee with scopes := prev) (Value v) vv out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ce.ce_func_return_type (nsid_to_string (NONE,name)) = ret` by
    (drule_all nr_declared_return_type >> simp[]) >>
  `nret = returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ret` by
    (drule_all body_internal_decl_return_count >> simp[]) >>
  `type_widens_to (get_tenv cx) ret ann` by
    (drule_all body_intcall_source_selection >> strip_tac >>
     `env.type_defs = get_tenv cx` by
       fs[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >> gvs[]) >>
  qpat_x_assum `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [intcall_entry_def] >> strip_tac >>
  `wb_frame ce es0 (es1 with scopes := prev) sa s0 t` by
    (pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `expr_body_pre _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce prev t id b sz` by
    (rpt strip_tac >> irule (Q.INST [`esB` |-> `es1 with scopes := prev`]
       (SPEC_ALL bodyIntCallAssemblyTheory.expr_inv_local_regions_transport)
       |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  `rc' = nret /\ rbs' = rbs /\ pvs' = pvs` by
    (qpat_x_assum `ce.ce_func_info _ = (rc',_,_)` mp_tac >> simp[]) >>
  `ci_mono st2 st3` by
    (qpat_assum `compile_stage_intcall_args _ ce _ _ _ st2 = _`
       (mp_then Any mp_tac nr_staged_prefix) >>
     disch_then drule >> simp[ci_mono_refl]) >>
  Cases_on `nret = 0`
  >- (Cases_on `ret = NoneT` >- suspend "void" >> suspend "memory") >>
  suspend "stack"
QED

Resume intcall_nr_return_endpoint[void]:
  qpat_x_assum `ret = NoneT` SUBST_ALL_TAC >>
  qpat_x_assum `nret = 0` SUBST_ALL_TAC >>
  `tv = NoneTV` by
    (qpat_x_assum `evaluate_type _ NoneT = _` mp_tac >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  qpat_x_assum `tv = NoneTV` SUBST_ALL_TAC >>
  qpat_x_assum `rc' = 0` SUBST_ALL_TAC >>
  qpat_assum `ce.ce_func_return_type _ = NoneT` (fn rt =>
    qpat_x_assum `_ /\ _ ==> st2 = sa /\ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [rt])) >>
  qpat_x_assum `st2 = sa` SUBST_ALL_TAC >>
  `ir.iret_values = []` by
    (qpat_x_assum `LENGTH _ = 0` mp_tac >> simp[]) >>
  `fn_has_code st3 sb func` by
    (irule (cj 2 fn_has_code_split) >> conj_tac
     >- (qspecl_then [`INVOKE`,`Label lbl::invoke_args`,`st3`]
           mp_tac ci_mono_emit_void >>
         qpat_assum `emit_void _ _ _ = _`
           (fn th => pure_rewrite_tac [th, pairTheory.SND, ci_mono_def]) >>
         metis_tac[]) >>
     qexists_tac `sa` >> conj_tac
     >- (qpat_x_assum `ci_mono sa st3` mp_tac >> simp[ci_mono_def]) >>
     first_assum ACCEPT_TAC) >>
  suspend "void_physical"
QED

Resume intcall_nr_return_endpoint[void_physical]:
  `?out. gas_path ctx func t n (OK out) /\
     out.vs_current_bb = sb.cs_current_bb /\
     out.vs_inst_idx = LENGTH sb.cs_current_insts /\
     stmt_state_rel ctx func ce cx (ee with scopes := prev) out /\
     wb_frame ce es0 (ee with scopes := prev) sa s0 out` by
    (irule (Q.INST [`es` |-> `es1 with scopes := prev`,
       `hi` |-> `sb.cs_next_id`] (SPEC_ALL (cj 2 nr_void_physical_endpoint))
       |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[NoAsms] >>
     conj_tac >- (qexistsl_tac [`Label lbl::invoke_args`,`st3`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (goal_assum (drule_at (Pat `gas_path _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `state_rel _ _ _ _ _`)) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qexists_tac `es1` >> conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "void_post"
QED

Resume intcall_nr_return_endpoint[void_post]:
  drule return_bufferless_none_widens >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
  qexistsl_tac [`0`,`out`] >> simp[NoAsms] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (conj_tac >> first_assum ACCEPT_TAC) >>
  irule exprSimHashTheory.vv_post_frame_intro >>
  simp[NoAsms, post_value_type_def, lowered_value_type_def,
    vyperASTTheory.expr_type_def] >>
  conj_tac >- simp[is_word_type_def, is_bytestring_type_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `v = NoneV` by
    (qpat_x_assum `value_has_type NoneTV v` mp_tac >>
     simp[value_has_type_def]) >>
  qpat_x_assum `v = NoneV` SUBST_ALL_TAC >>
  simp[NoAsms, vv_holds_def, vv_at_def, read_result_def, return_def,
    expr_val_rel_def, expr_val_at_def, eval_operand_def,
    vyperValueTheory.evaluate_type_def, is_word_type_def,
    valueEncodingDefsTheory.val_in_memory_def,
    valueEncodingDefsTheory.val_wf_def, val_footprint_def,
    valueEncodingTheory.type_memory_size_def]
QED

Resume intcall_nr_return_endpoint[memory]:
  qpat_x_assum `nret = 0` SUBST_ALL_TAC >>
  qpat_x_assum `rc' = 0` SUBST_ALL_TAC >>
  qpat_assum `ce.ce_func_return_type _ = ret` (fn rt =>
    qpat_assum `ret <> NoneT` (fn ne =>
      qpat_x_assum `_ \/ _ ==> ?rbuf aid off. _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [rt,ne]))) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `ir.iret_values = []` by
    (qpat_x_assum `LENGTH _ = 0` mp_tac >> simp[]) >>
  `st2.cs_next_var <= st3.cs_next_var` by
    (qpat_assum `ci_mono st2 st3`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     first_assum ACCEPT_TAC) >>
  `w2n (n2w off : bytes32) = off` by
    (drule_all bodyIntCallCompletedModesTheory.compiled_return_buffer_geometry >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `val_in_memory tv v off cs.vs_memory` by
    (qpat_x_assum `!bb inst lbl arg_ops argv. _`
       (drule_all o SIMP_RULE (srw_ss()) []) >>
     qpat_assum `HD argv = n2w off` (fn th => rewrite_tac[th]) >>
     simp[]) >>
  `fn_has_code st3 sb func` by
    (irule (cj 2 fn_has_code_split) >> conj_tac
     >- (qspecl_then [`INVOKE`,`Label lbl::rbuf.buf_operand::invoke_args`,`st3`]
           mp_tac ci_mono_emit_void >>
         qpat_assum `emit_void _ _ _ = _`
           (fn th => pure_rewrite_tac [th, pairTheory.SND, ci_mono_def]) >>
         metis_tac[]) >>
     qexists_tac `sa` >> conj_tac
     >- (`ci_mono sa st2` by
           (qspec_then `rbs'` (qspec_then `sa` mp_tac) ci_mono_compile_alloc_buffer >>
            qpat_assum `compile_alloc_buffer _ _ = _`
              (fn th => pure_rewrite_tac[th,pairTheory.SND]) >> simp[]) >>
         qpat_assum `ci_mono sa st2`
           (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
         qpat_assum `ci_mono st2 st3`
           (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
         simp[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     first_assum ACCEPT_TAC) >>
  suspend "memory_physical"
QED

Resume intcall_nr_return_endpoint[memory_physical]:
  `?out. gas_path ctx func t n (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx (ee with scopes := prev) out /\
    wb_frame ce es0 (ee with scopes := prev) sa s0 out /\
    eval_operand rbuf.buf_operand out = SOME (n2w off) /\
    val_in_memory tv v off out.vs_memory /\
    FLOOKUP out.vs_allocas sa.cs_next_id = SOME (off,rbuf.buf_size) /\
    val_footprint tv v <= rbuf.buf_size /\
    (!id lb lsz. local_region ce prev out id lb lsz ==>
      off + rbuf.buf_size <= lb \/ lb + lsz <= off)` by
    (irule (Q.INST [`es` |-> `es1 with scopes := prev`]
       (SPEC_ALL nr_memory_physical_endpoint)
       |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[NoAsms] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qexistsl_tac [`rbs'`,`Label lbl::rbuf.buf_operand::invoke_args`,
           `st3`,`sa`,`st2`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qexistsl_tac [`callee`,`cs`,`entered`,`ir`,`func`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qexists_tac `es1` >> conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "memory_post"
QED

Resume intcall_nr_return_endpoint[memory_post]:
  qexistsl_tac [`0`,`out`] >> simp[NoAsms] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  irule nr_allocated_call_post >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexistsl_tac [`sa.cs_next_id`,`off`,`rbuf.buf_size`,`tv`,`n2w off`] >>
      simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume intcall_nr_return_endpoint[stack]:
  `0 < nret` by simp[] >>
  qpat_x_assum `rc' = nret` SUBST_ALL_TAC >>
  qpat_assum `0 < nret` (fn pos =>
    qpat_x_assum `_ \/ _ ==> ?rbuf aid off. _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [pos])) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `ci_mono sa st2` by
    (qspec_then `32 * nret` (qspec_then `sa` mp_tac) ci_mono_compile_alloc_buffer >>
     qpat_assum `compile_alloc_buffer _ _ = _`
       (fn th => pure_rewrite_tac[th,pairTheory.SND]) >> simp[]) >>
  `ci_mono st3 st4` by
    (qspecl_then [`INVOKE`,`Label lbl::invoke_args`,`nret`,`st3`]
       mp_tac ci_mono_emit_multi_op >>
     qpat_assum `emit_multi_op _ _ _ _ = _`
       (fn th => pure_rewrite_tac[th,pairTheory.SND]) >> simp[]) >>
  `ci_mono st4 sb` by
    (qspecl_then [`rbuf.buf_operand`,`results`,`0`,`st4`]
       mp_tac ci_mono_store_multi_results >>
     qpat_assum `store_multi_results _ _ _ _ = _`
       (fn th => pure_rewrite_tac[th,pairTheory.SND]) >> simp[]) >>
  `ci_mono sa st3` by metis_tac[ci_mono_trans] >>
  `ci_mono st3 sb` by metis_tac[ci_mono_trans] >>
  `fn_has_code st3 st4 func /\ fn_has_code st4 sb func` by
    (irule fn_has_code_split >> conj_tac >- metis_tac[ci_mono_def] >>
     conj_tac >- metis_tac[ci_mono_def] >>
     irule (cj 2 fn_has_code_split) >> conj_tac >- metis_tac[ci_mono_def] >>
     qexists_tac `sa` >> conj_tac >- metis_tac[ci_mono_def] >>
     first_assum ACCEPT_TAC) >>
  `st2.cs_next_var <= st3.cs_next_var /\ sa.cs_next_var <= st3.cs_next_var`
    by metis_tac[ci_mono_def] >>
  `local_ptrs_reserved ce st3` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >>
     first_assum ACCEPT_TAC) >>
  `w2n (n2w off : bytes32) = off` by
    (drule_all bodyIntCallCompletedModesTheory.compiled_return_buffer_geometry >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `expr_sim_inv ce cx env es0` mp_tac >>
     simp_tac (srw_ss()) [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  suspend "stack_physical"
QED

Resume intcall_nr_return_endpoint[stack_physical]:
  `?out. gas_path ctx func t
      (n + LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st4 sb))) (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx (ee with scopes := prev) out /\
    wb_frame ce es0 (ee with scopes := prev) sa s0 out /\
    eval_operand rbuf.buf_operand out = SOME (n2w off) /\
    val_in_memory tv v off out.vs_memory /\
    FLOOKUP out.vs_allocas sa.cs_next_id = SOME (off,rbuf.buf_size) /\
    val_footprint tv v <= rbuf.buf_size /\
    (!id lb lsz. local_region ce prev out id lb lsz ==>
      off + rbuf.buf_size <= lb \/ lb + lsz <= off)` by
    (irule (Q.INST [`es` |-> `es1 with scopes := prev`]
       (SPEC_ALL nr_stack_physical_endpoint)
       |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `ret` >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (goal_assum (drule_at (Pat `gas_path _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
         goal_assum (drule_at (Pat `emit_multi_op _ _ _ _ = _`)) >>
         simp[] >> rpt conj_tac >> metis_tac[]) >>
     qexists_tac `es1` >> conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "stack_post"
QED

Resume intcall_nr_return_endpoint[stack_post]:
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st4 sb))`,`out`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  irule nr_allocated_call_post >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qexistsl_tac [`sa.cs_next_id`,`off`,`rbuf.buf_size`,`tv`,`n2w off`] >>
      simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise intcall_nr_return_endpoint
