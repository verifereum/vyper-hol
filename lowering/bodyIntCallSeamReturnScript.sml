(* Seam 3 of the internal call: the INVOKE and the code after it, for the
   callee's own return type (intcall_return_restore) and a widened
   annotation (intcall_return_widened). *)

Theory bodyIntCallSeamReturn
Ancestors
  bodyIntCallSeamDefs
  bodyIntCallJointContract
  bodyIntCallSource bodyIntCallWidenedPost bodyIntCallWidenedEndpoint
  bodyIntCallSourceReturn bodyIntCallMetadata bodyIntCallReturnAdapters bodyIntCallCompilerBoundary bodyIntCallAssemblySource bodyIntCallAssemblyModes bodyIntCallAssembly bodyIntCallCompletedModes bodyIntCallCompletedFrame bodyIntCallCompletedFacts bodyIntCallCompletedSource bodyIntCallExemptReturn bodyIntCallStorePath bodyIntCallStoreRun bodyIntCallStorePost bodyIntCallEmitBoundary memoryLocalRhsProps supportedProgram supportedNames bodyIntCallReturnLayout bodyIntCallRestoreResults bodyIntCallRestoreFrame bodyIntCallCallerFrame bodyIntCallCountedPath bodyIntCallReturnBoundaryChecks bodyIntCallImmutableFrame bodyIntCallReturnSource bodySim exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts
  intCallCallee intCallFrame fragGasFocus gasOutcome gasContext
  bodyIntCallAllocatedForcing bodyIntCallAggregateStoreFrame bodyIntCallAggregateStoreLanding bodyIntCallSubslotGeometry bodyIntCallForcing bodyIntCallForcingCode bodyIntCallForcingCodeRun bodyIntCallForcingStorage bodyIntCallForcingReadOnly bodyIntCallStorageLanding bodyIntCallMaterializeLanding bodyIntCallSharpReturn bodyIntCallParameterGeometry bodyIntCallSourceSpans bodyIntCallStageOrigin bodyIntCallCopySharpRank bodyIntCallCopySharpDynamic bodyIntCallCopySharpFixed bodyIntCallCopySharpFast bodyIntCallCopySharpFields bodyIntCallCopySharpArray bodyIntCallCopySharpPrimitive bodyIntCallWidenCopy bodyIntCallDeclarationStore bodyIntCallDeclarationAlloc bodyIntCallDeclarationRegions bodyIntCallPrologueInit bodyIntCallLocalLanding bodyIntCallNameLanding bodyIntCallForceLanding bodyIntCallWordLanding bodyIntCallLiteralLanding bodyIntCallBodyTyping bodyIntCallSemanticEntry bodyIntCallHandler bodyIntCallResourceExit bodyIntCallPrologueResource bodyIntCallFrameProbe bodyIntCallReturnProbe bodyIntCallReturnCopy bodyIntCallProtectedLiteral bodyIntCallProtectedAlloc bodyIntCallProtectedBuffer bodyIntCallProtectedBytelike
  bodyIntCallWriteAuthorization bodyIntCallResourceEntry bodyIntCallResourceSpans bodyIntCallNormalResource bodyIntCallOutcomeFrame bodyIntCallFrameBoundary bodyIntCallReturnBoundary bodyIntCallReachableReturn bodyIntCallProducerOrder bodyIntCallProtectedReturn
  compileVyper exprLowering exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperAST venomState venomExecSemantics
Libs
  monadsyntax

(* Seam 3: return and revert handling.  The INVOKE with the callee's run
   as seam 2 gives it, then the copy of the returned value to the
   caller's buffer, the frame's cleanup and the cast: the call's
   expr_vv_sim post, or an abort passed on.  Only the case where the
   callee's return type is the call's annotation. *)
Theorem intcall_return_restore:
  !tops ctx func cenv cx tenv ty ann name es dflt es0 sa sb vv s0
   mut args ret ss rr prev penv rtv es1 t rc rbs pvs.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
      (vv,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
      (mut,args,ret,ss,rr) prev penv rtv es1 t /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    cenv.ce_func_return_type (nsid_to_string (NONE,name)) = ann /\
    (!callee entered bb inst lbl arg_ops argv.
       gas_invoke_entry (ctx,func) t callee entered /\
       lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME inst /\
       decode_invoke inst = SOME (lbl,arg_ops) /\
       eval_operands arg_ops t = SOME argv ==>
       gas_outcome F (cx_tops cx) (ctx,callee) (intcall_callee_src cx name ss)
         (es1,entered) (\res ee r. F)
         (intcall_callee_exit func cenv cx rtv rc
            (if rc = 0 /\
               cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT
            then SOME (HD argv) else NONE)
            sa.cs_next_id sb.cs_next_id t)) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (intcall_rest cx name mut ss prev rtv)
      (es1,t)
      (\res ee t'. ?tv. res = INL tv /\
         vv_post ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
           es0 sa sb s0 ee tv vv t' /\
         t'.vs_current_bb = sb.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  `post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt) =
   expr_type (Call ann (IntCall (NONE,name)) es dflt)` by
    (qpat_assum `cenv.ce_func_return_type _ = ann` mp_tac >>
     simp[post_value_type_def, lowered_value_type_def, expr_type_def]) >>
  `ret = ann` by (drule_all body_internal_decl_return_type >> simp[]) >>
  qpat_x_assum `ret = ann` SUBST_ALL_TAC >>
  `rc' = returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ann` by
    (drule_all body_internal_decl_return_count >> simp[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `evaluate_type (get_tenv cx) ann = SOME rtv` by
    fs[intcall_entry_def] >>
  `wb_frame cenv es0 sa s0 t` by
    (fs[intcall_entry_def, wb_frame_def] >> metis_tac[]) >>
  `!n b sz. local_region cenv es0.scopes s0 n b sz ==>
            local_region cenv prev t n b sz` by
    (rpt strip_tac >>
     irule (SRULE [] (Q.INST [`esB` |-> `es1 with scopes := prev`]
       (SPEC_ALL expr_inv_local_regions_transport))) >>
     qexistsl_tac [`cx`,`tenv`,`es1`,`es0`,`s0`,`sa`] >>
     fs[intcall_entry_def, expr_body_pre_def]) >>
  `immutable_alloca_sep func cenv cx (es1 with scopes := prev) t` by
    fs[intcall_entry_def, stmt_state_rel_def] >>
  qpat_assum `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[intcall_entry_def] >> strip_tac >>
  qpat_assum `cenv.ce_func_info _ = (rc'',rbs',pvs')` mp_tac >>
  qpat_assum `cenv.ce_func_info _ = (rc',rbs,pvs)` (fn th => rewrite_tac[th]) >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `rc' = rc''` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `rbs = rbs'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `pvs = pvs'` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `cenv.ce_func_return_type _ = ann` SUBST_ALL_TAC >>
  qpat_x_assum `ann = ann` kall_tac >>
  qpat_x_assum `!callee entered bb inst lbl arg_ops argv. _` drule_all >>
  strip_tac >>
  rewrite_tac[intcall_rest_def] >>
  pure_once_rewrite_tac[GSYM intcall_callee_src_def] >>
  irule invoke_cleanup_outcome >>
  conj_tac >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
    rewrite_tac[intcall_rest_def] >>
    pure_once_rewrite_tac[GSYM intcall_callee_src_def] >> simp[]) >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_invoke_entry _ _ _ _`)) >>
  qexists_tac `\v ee ir cs. intcall_callee_exit func cenv cx rtv rc'
    (if rc' = 0 /\ ann <> NoneT then SOME (HD argv) else NONE)
    sa.cs_next_id sb.cs_next_id t (INL v) ee (IntRet ir cs)` >>
  reverse conj_tac >-
    (simp[NoAsms, intcall_callee_exit_def] >>
     qpat_assum `cenv.ce_func_return_type _ = ann` (fn th => rewrite_tac[th])) >>
  rpt strip_tac >>
  `immutable_alloca_sep func cenv cx (ee with scopes := prev) t` by
    (irule marked_body_immutable_alloca_sep >>
     goal_assum (drule_at Any) >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[intcall_callee_src_def] >> strip_tac >>
     goal_assum (drule_at Any)) >>
  `gas_path ctx callee entered (LENGTH marks) (IntRet ir cs)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def,
       fragGasModeTheory.gas_marked_path_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(\v ee ir cs. _) _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [intcall_callee_exit_def, expr_exit_def]) >>
  simp[NoAsms] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule source_return_dispatch >> asm_rewrite_tac[] >>
  reverse conj_tac >- (qexists_tac `es1` >> first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `compile_multi_vvs _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_stage_intcall_args _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `gas_path _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `state_rel _ _ _ _ _`)) >>
  qexistsl_tac [`arg_ops`,`ann`,`lbl`,`rc'`,`rc'`,`rbs`,`rbs`,`rtv`,`HD argv`] >>
  asm_rewrite_tac[] >> simp[NoAsms, expr_type_def] >>
  qpat_assum `rc' = returns_stack_count _ _` (fn th => rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[]
QED

(* Held for the posts-interface change (post_value_type in loweringPosts):
   when the call's annotation differs from the callee's return type,
   compile_call's value has the return type, which vv_post can't describe
   until the posts describe values at their lowered type.  Seam 3's
   statement with the other side of the case split; not an alan seam. *)
Theorem widened_call_return_type[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Call ann (IntCall (NONE,name)) es dflt) st /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,F,args,[],ret,ss) /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops ==>
  cenv.ce_func_return_type (nsid_to_string (NONE,name)) = ret /\
  type_widens_to (get_tenv cx) ret ann
Proof
  strip_tac >>
  conj_tac >- (drule_all body_internal_decl_return_type >> simp[]) >>
  drule_all body_intcall_source_selection >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[]
QED

Theorem widened_return_classification[local]:
  type_widens_to tenv ret ann /\ ret <> ann ==>
  ~is_word_type ann /\
  (is_bytestring_type ann ==> is_bytestring_type ret)
Proof
  strip_tac >> conj_tac
  >- metis_tac[compileEnvTheory.type_widens_to_word] >>
  fs[vyperTypeSystemTheory.type_widens_to_def] >>
  metis_tac[arg_type_fits_bytestring_source]
QED

Theorem intcall_return_widened:
  !tops ctx func cenv cx tenv ty ann name es dflt es0 sa sb vv s0
   mut args ret ss rr prev penv rtv es1 t rc rbs pvs.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
      (vv,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
      (mut,args,ret,ss,rr) prev penv rtv es1 t /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> ann /\
    (!callee entered bb inst lbl arg_ops argv.
       gas_invoke_entry (ctx,func) t callee entered /\
       lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME inst /\
       decode_invoke inst = SOME (lbl,arg_ops) /\
       eval_operands arg_ops t = SOME argv ==>
       gas_outcome F (cx_tops cx) (ctx,callee) (intcall_callee_src cx name ss)
         (es1,entered) (\res ee r. F)
         (intcall_callee_exit func cenv cx rtv rc
            (if rc = 0 /\
               cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT
            then SOME (HD argv) else NONE)
            sa.cs_next_id sb.cs_next_id t)) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (intcall_rest cx name mut ss prev rtv)
      (es1,t)
      (\res ee t'. ?tv. res = INL tv /\
         vv_post ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
           es0 sa sb s0 ee tv vv t' /\
         t'.vs_current_bb = sb.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  drule_all widened_call_return_type >> strip_tac >>
  `ret <> ann` by metis_tac[] >>
  drule_all widened_return_classification >> strip_tac >>
  `ret <> NoneT` by (strip_tac >> gvs[]) >>
  `rc' = returns_stack_count
    (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ret` by
    (drule_all body_internal_decl_return_count >> simp[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `evaluate_type (get_tenv cx) ret = SOME rtv` by fs[intcall_entry_def] >>
  `wb_frame cenv es0 sa s0 t` by
    (fs[intcall_entry_def, wb_frame_def] >> metis_tac[]) >>
  `!n b sz. local_region cenv es0.scopes s0 n b sz ==>
            local_region cenv prev t n b sz` by
    (rpt strip_tac >>
     irule (SRULE [] (Q.INST [`esB` |-> `es1 with scopes := prev`]
       (SPEC_ALL expr_inv_local_regions_transport))) >>
     qexistsl_tac [`cx`,`tenv`,`es1`,`es0`,`s0`,`sa`] >>
     fs[intcall_entry_def, expr_body_pre_def]) >>
  `immutable_alloca_sep func cenv cx (es1 with scopes := prev) t` by
    fs[intcall_entry_def, stmt_state_rel_def] >>
  qpat_assum `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[intcall_entry_def] >> strip_tac >>
  qpat_assum `cenv.ce_func_info _ = (rc'',rbs',pvs')` mp_tac >>
  qpat_assum `cenv.ce_func_info _ = (rc',rbs,pvs)` (fn th => rewrite_tac[th]) >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `rc' = rc''` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `rbs = rbs'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `pvs = pvs'` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `cenv.ce_func_return_type _ = ret` SUBST_ALL_TAC >>
  qpat_x_assum `!callee entered bb inst lbl arg_ops argv. _` drule_all >>
  strip_tac >>
  rewrite_tac[intcall_rest_def] >>
  pure_once_rewrite_tac[GSYM intcall_callee_src_def] >>
  irule invoke_cleanup_outcome >>
  conj_tac >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
    rewrite_tac[intcall_rest_def] >>
    pure_once_rewrite_tac[GSYM intcall_callee_src_def] >> simp[]) >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_invoke_entry _ _ _ _`)) >>
  qexists_tac `\v ee ir cs. intcall_callee_exit func cenv cx rtv rc'
    (if rc' = 0 /\ ret <> NoneT then SOME (HD argv) else NONE)
    sa.cs_next_id sb.cs_next_id t (INL v) ee (IntRet ir cs)` >>
  reverse conj_tac >-
    (simp[NoAsms, intcall_callee_exit_def] >>
     qpat_assum `cenv.ce_func_return_type _ = ret` (fn th => rewrite_tac[th])) >>
  rpt strip_tac >>
  `immutable_alloca_sep func cenv cx (ee with scopes := prev) t` by
    (irule marked_body_immutable_alloca_sep >>
     goal_assum (drule_at Any) >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[intcall_callee_src_def] >> strip_tac >>
     goal_assum (drule_at Any)) >>
  `gas_path ctx callee entered (LENGTH marks) (IntRet ir cs)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def,
       fragGasModeTheory.gas_marked_path_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(\v ee ir cs. _) _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [intcall_callee_exit_def, expr_exit_def]) >>
  simp[NoAsms] >>
  `?k out. gas_path ctx func t (LENGTH marks + k) (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func cenv cx (ee with <|scopes := prev; gas_obs := []|>) out /\
    wb_frame cenv es0 sa s0 out /\
    (?buf aid off. vv = LocatedValue ret (base_ptr buf) /\
      eval_operand buf.buf_operand out = SOME (n2w off) /\
      val_in_memory rtv v off out.vs_memory /\
      FLOOKUP out.vs_allocas aid = SOME (off,buf.buf_size) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
      val_footprint rtv v <= buf.buf_size /\
      (!id lb lsz. local_region cenv prev out id lb lsz ==>
        off + buf.buf_size <= lb \/ lb + lsz <= off))` by
    (qpat_assum `ret <> NoneT` (fn th =>
       irule (Q.INST [`cty` |-> `ret`] (Q.SPEC `rc'` physical_source_return_dispatch)
         |> SIMP_RULE (srw_ss()) [th])) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qexists_tac `es1` >> first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `compile_multi_vvs _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_stage_intcall_args _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `gas_path _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `state_rel _ _ _ _ _`)) >>
     qexistsl_tac [`lbl`,`rbs`,`rc'`,`HD argv`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_x_assum `0 < rc' \/ ret <> NoneT ==> _` mp_tac >>
         qpat_assum `ret <> NoneT` (fn th => simp[NoAsms, th]) >>
         POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
         goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
         goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
         metis_tac[])
     >- (qpat_assum `rc' = returns_stack_count _ _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
     simp[]) >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`k`,`out`] >>
  conj_tac >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  simp[NoAsms] >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  `off < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ out` mp_tac >>
     simp[NoAsms, stmt_state_rel_def] >> strip_tac >>
     drule alloca_room_next_lt >>
     qpat_x_assum `alloca_inv out` mp_tac >>
     rewrite_tac[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> decide_tac) >>
  qpat_assum `vv = LocatedValue ret _` (fn th => pure_rewrite_tac[th]) >>
  irule widened_allocated_buffer_post >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (drule_all body_internal_decl_return_type >> simp[NoAsms]) >>
  goal_assum (drule_at (Pat `eval_operand _ out = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP out.vs_allocas _ = _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  simp[NoAsms] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `off < dimword (:256)` (fn th => simp[NoAsms, th]) >>
  first_assum ACCEPT_TAC
QED
