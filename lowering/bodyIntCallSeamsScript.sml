(* The internal call's body case (bodySimCallIntcall's intcall_body_expr_ok)
   cut at its two boundaries, the INVOKE and the callee's return:
   - intcall_args_frame_setup: the caller's code up to the INVOKE, against
     the source up to push_function (arguments evaluated, staged as the
     callee's parameters, return buffer allocated);
   - intcall_callee_body_sim: the callee's whole run from its entry,
     against its body under the body induction hypothesis;
   - intcall_return_restore: the INVOKE itself and the code after it, the
     return value copied back to the caller and an abort passed on.
   intcall_entry and intcall_callee_exit are the relations at the two
   boundaries; intcall_rest is the source after push_function. *)

Theory bodyIntCallSeams
Ancestors
  bodyIntCallSeamGrammarCheck bodyIntCallSeamReturnLayout
  bodyIntCallSeamInvokeBoundary bodyIntCallSeamPrefixSupport bodyIntCallSeamSourceJoin
  list bodyIntCallArgPrefixFrame bodyIntCallArgPrefixHistory bodyIntCallStageDistinctReturn bodyIntCallSource exprSimSend intCallStep vyperCall vyperTypeCallStackSoundness vyperTypeCallGraph
  bodyIntCallPackageEntryInterface bodyIntCallPackageResource bodyIntCallStageList bodyIntCallStageTransport bodyIntCallStageOwned bodyIntCallStageUnwrap bodyIntCallStageUnwrapCopy bodyIntCallStageUnwrapRead bodyIntCallStageCompile bodyIntCallStageHead bodyIntCallStageStore bodyIntCallTightStore bodyIntCallCompilerListTags bodyIntCallSmallStore bodyIntCallCompilerTags bodyIntCallStageAllocation bodyIntCallCompilerSeparation bodyIntCallCompilerClosure bodyIntCallCompilerExprBody bodyIntCallCompilerTypeBuiltin bodyIntCallCompilerBuiltin bodyIntCallCompilerCall bodyIntCallCompilerCreatePipeline bodyIntCallCompilerCreate bodyIntCallCompilerExternal bodyIntCallCompilerExtOperands bodyIntCallCompilerRawSystem bodyIntCallCompilerCallRoots bodyIntCallCompilerUniversalAggregate bodyIntCallCompilerLiteral bodyIntCallCompilerUniversal bodyIntCallCompilerCallbacks bodyIntCallCompilerAbiWrappers bodyIntCallCompilerConvert bodyIntCallCompilerSlice bodyIntCallCompilerRead bodyIntCallCompilerHash bodyIntCallCompilerMembership bodyIntCallCompilerScalar bodyIntCallCompilerDecoder bodyIntCallCompilerEncoder bodyIntCallCompilerAggregate bodyIntCallCompilerStaging bodyIntCallCompilerTypedMemory bodyIntCallCompilerUnwrap
  bodyIntCallHeldImmutableCopy bodyIntCallHeldImmutableWord bodyIntCallHeldByteFrame bodyIntCallHeldStorageWord bodyIntCallHeldCopyValue bodyIntCallHeldCopyFrame bodyIntCallCopyFrame bodyIntCallStorageTyped bodyIntCallStorageWord bodyIntCallStorageAllocate bodyIntCallStorageLoop bodyIntCallStorageRead bodyIntCallConsumerProbe bodyIntCallPackageLayout bodyIntCallHeldRead bodyIntCallReserveProbe bodyIntCallCapacityProbe bodyIntCallStagingBuffer bodyIntCallArgList bodyIntCallExecutionFrame bodyIntCallHeldArgs bodyIntCallHeadProducer bodyIntCallMemoryView bodyIntCallWordProducer bodyIntCallPureLayout bodyIntCallHeldFrame bodyIntCallTopLevelProducer bodyIntCallProvenanceIntro bodyIntCallPackageBoundary bodyIntCallArgSequence bodyIntCallArgType bodyIntCallResource bodyIntCallEncoderActualCopy bodyIntCallScratchCreditProbe
  bodyIntCallEncoderCountedExport bodyIntCallEncoderCountedArrays bodyIntCallEncoderCountedArrayPhases bodyIntCallEncoderCountedMembers bodyIntCallEncoderCountedComplex bodyIntCallEncoderCountedSpine bodyIntCallEncoderCountedPhases bodyIntCallEncoderCountedPrefix bodyIntCallEncoderCountedLeaves bodyIntCallDecoderCountedClosure bodyIntCallDecoderCountedLeaves bodyIntCallDecoderCountedArray bodyIntCallDecoderCountedLoopEntry bodyIntCallDecoderCountedLoopFinite bodyIntCallDecoderCountedLoopControl bodyIntCallDecoderCountedArrayBody bodyIntCallDecoderCountedArrayInit bodyIntCallDecoderCountedAggregates bodyIntCallDecoderCountedMembers bodyIntCallDecoderCountedDispatch bodyIntCallDecoderCountedMembersContract bodyIntCallDecoderCountedEmpty bodyIntCallDecoderCountedBody bodyIntCallDecoderCountedInput bodyIntCallDecoderCountedMember bodyIntCallDecoderCountedPrimitive bodyIntCallStoreFrame bodyIntCallMcopyFrame bodyIntCallWriteFrame bodyIntCallValueWindow bodyIntCallLocalArrayProducer bodyIntCallArraySuffix bodyIntCallArgLocalFrame bodyIntCallImmutableBoundary bodyIntCallArgCompose bodyIntCallArgEligibility
  bodyIntCallArgOwnedFrame bodyIntCallSourceFrame bodyIntCallStorageFrame bodyIntCallLocalFrame bodyIntCallPathLayout bodyIntCallProducerRoots
  bodyIntCallSourceReturn bodyIntCallMetadata bodyIntCallReturnAdapters bodyIntCallCompilerBoundary bodyIntCallAssemblySource bodyIntCallAssemblyModes bodyIntCallAssembly bodyIntCallCompletedModes bodyIntCallCompletedFrame bodyIntCallCompletedFacts bodyIntCallCompletedSource bodyIntCallExemptReturn bodyIntCallStorePath bodyIntCallStoreRun bodyIntCallStorePost bodyIntCallEmitBoundary memoryLocalRhsProps supportedProgram supportedNames bodyIntCallReturnLayout bodyIntCallRestoreResults bodyIntCallRestoreFrame bodyIntCallCallerFrame bodyIntCallCountedPath bodyIntCallReturnBoundaryChecks bodyIntCallImmutableFrame bodyIntCallReturnSource bodySim exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts
  intCallCallee intCallFrame fragGasFocus gasOutcome gasContext
  compileVyper exprLowering exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperAST venomState venomExecSemantics
Libs
  monadsyntax

(* The source of an internal call after push_function: the body, the
   frame's cleanup, and the cast of the returned value.  A supported
   callee is not nonreentrant and has no defaults
   (body_intcall_source_selection). *)
Definition intcall_rest_def:
  intcall_rest cx name mut ss prev rtv =
    do rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss;
                  return NoneV
               od) handle_function)
         (do pop_function prev;
             unlock_if_nr cx F (is_view_mut mut)
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
    od
End

(* The callee's body as the INVOKE runs it. *)
Definition intcall_callee_src_def:
  intcall_callee_src cx name ss =
    try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss;
            return NoneV
         od) handle_function
End

(* The INVOKE of internal function name (mut,args,ret,ss, raw-return flag
   rr), called with arguments es from the caller func, whose code for the
   call runs from sa to sb and gives vv, at the source state es0 and Venom
   state s0.  t is at the INVOKE, es1 is the source state push_function
   leaves, prev the caller's scopes it saved, penv the parameters' scope
   and rtv the evaluated return type.
   - Source: the arguments evaluated and read to the values penv binds;
     the callee's body is call-safe at the pushed context.
   - Code: the call's code as compile_call_intcall_shape gives it: the
     arguments (sa to st1), the return buffer rbuf if any (st1 to st2),
     the staging (st2 to st3), the INVOKE of the callee's label at st3
     with the buffer's pointer first when the callee returns through it,
     and after it the results' store into rbuf, up to sb; vv is rbuf's
     located value, or the void call's literal.
   - Position: t is at the INVOKE (instruction inst of block bb, operand
     words argv).
   - Return buffer: an ALLOCA of the call's own code (instruction id at
     least sa's next id) holding rbuf's address in t; when it is passed
     to the callee (HD argv), the return value's bytes fit in it, below
     t's frontier, and clear of the constructor's immutables.
   - Caller frame: t is related at es1 with the caller's scopes, and keeps
     s0's variables, allocas, and memory outside the caller's locals, as
     vv_post asks; the call's own ALLOCAs (ids in [sa, sb)) are clear of
     the caller's live locals.
   - Callee entry: the INVOKE enters a callee, and at the internal
     function's package (any nonreentrancy keys and transient flag, the
     caller's target) whose label is the INVOKE's and whose return-buffer
     flag matches the call's, the premises of
     compile_internal_prologue_entry hold for argv, and each memory
     parameter's region (the pointer argv passes, the parameter's size)
     lies in an ALLOCA of the call's own code: the staging buffer. *)
Definition intcall_entry_def:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
                (mut,args,ret,ss,rr) prev penv rtv es1 t <=>
    ~MEM (NONE,name) cx.stk /\
    (?s1 results t1 s2 vs t2.
       eval_expr_results cx es s1 = (INL results,t1) /\
       read_results cx results s2 = (INL vs,t2) /\
       bind_arguments (get_tenv cx) args vs = SOME penv) /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
      (int_calls_stmts ss) /\
    es1.scopes = [penv] /\
    gas_admissible (intcall_rest cx name mut ss prev rtv) expr_vv_res_ok es1 /\
    stmt_state_rel ctx func cenv cx (es1 with scopes := prev) t /\
    expr_sim_inv cenv cx tenv (es1 with scopes := prev) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es0 s0 t /\
    (!n lo sz aid off asz.
       local_region cenv prev t n lo sz /\
       FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
       regions_disjoint lo sz off asz) /\
    ?arg_vals st1 st2 invoke_args st3 rc rbs pvs lbl arg_ops bb inst argv.
      cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
      compile_multi_vvs compile_expr cenv es sa = (arg_vals,st1) /\
      compile_stage_intcall_args cenv arg_vals pvs (MAP expr_type es) st2 =
        (invoke_args,st3) /\
      lbl = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
              (nsid_to_string (NONE,name))
              (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
              cenv.ce_is_ctor /\
      (rc = 0 /\
       cenv.ce_func_return_type (nsid_to_string (NONE,name)) = NoneT ==>
       st2 = st1 /\ arg_ops = invoke_args /\
       (?u. emit_void INVOKE (Label lbl :: invoke_args) st3 = (u,sb)) /\
       vv = StackValue (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
              (Lit 0w)) /\
      (0 < rc \/
       cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT ==>
       ?rbuf aid off.
         compile_alloc_buffer (if 0 < rc then 32 * rc else rbs) st1 =
           (rbuf,st2) /\
         vv = LocatedValue
                (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
                (base_ptr rbuf) /\
         eval_operand rbuf.buf_operand t = SOME (n2w off) /\
         FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size) /\
         aid = st1.cs_next_id /\
         (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                inst.inst_id = aid) /\
         sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
         (0 < rc ==>
          arg_ops = invoke_args /\
          ?results st4 u.
            emit_multi_op INVOKE (Label lbl :: invoke_args) rc st3 =
              (results,st4) /\
            store_multi_results rbuf.buf_operand results 0 st4 = (u,sb)) /\
         (rc = 0 ==>
          arg_ops = rbuf.buf_operand :: invoke_args /\
          (?u. emit_void INVOKE (Label lbl :: rbuf.buf_operand :: invoke_args)
                 st3 = (u,sb)) /\
          HD argv = n2w off /\ type_memory_size rtv <= rbuf.buf_size /\
          w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next)) /\
      ~t.vs_halted /\ t.vs_current_bb = st3.cs_current_bb /\
      t.vs_inst_idx = LENGTH st3.cs_current_insts /\
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv /\
      (?callee entered. gas_invoke_entry (ctx,func) t callee entered) /\
      !callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key
       trans view ctor imm_len' ss' rt.
        lookup_function lbl ctx.ctx_functions = SOME callee /\
        setup_callee callee argv t = SOME setup /\
        set_internal_package_target cenv.ce_target
          (package_internal_fn tops use_trans (nkeys : string -> num)
             cenv.ce_is_ctor imm_len
             (mut,F,rr,name,args,([] : expr list),ret,ss)) =
          (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
        lbl' = lbl /\
        (has_rb <=>
           rc = 0 /\
           cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT) /\
        (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
        state_rel func ce cx (es1 with scopes := []) t /\
        internal_immutable_regions ce cx es1 t.vs_alloca_next /\
        internal_args_rel ce params penv (if has_rb then 1 else 0) argv
          t.vs_alloca_next t.vs_memory /\
        (!i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           ?aid off asz.
             FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
             (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                    inst.inst_id = aid) /\
             sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
             off <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
             w2n (EL ((if has_rb then 1 else 0) + i) argv) + psz <=
               off + asz) /\
        (has_rb ==> !i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
             (w2n (EL (1 + i) argv)) psz) /\
        (ce.ce_is_ctor ==> !i po psz nm tv iv io.
          i < LENGTH params /\ ~SND (EL i params) /\
          FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
          FLOOKUP ce.ce_module_vars (ce.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                     NONE => FEMPTY
                   | SOME imms => get_source_immutables ce.ce_module imms) nm =
            SOME (tv,iv) ==>
          regions_disjoint io (type_memory_size tv)
            (w2n (EL ((if has_rb then 1 else 0) + i) argv)) psz) /\
        (has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
          FLOOKUP ce.ce_module_vars (ce.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                     NONE => FEMPTY
                   | SOME imms => get_source_immutables ce.ce_module imms) nm =
            SOME (tv,iv) ==>
          regions_disjoint io (type_memory_size tv)
            (w2n (HD argv)) (type_memory_size rtv)) /\
        t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
        alloca_room ctx callee setup /\ fmp_room ctx callee setup
End

(* How the callee's run ends, seen from the caller's state t at the
   INVOKE, whose call's code has the ALLOCA ids in [n, m): an abort the
   call's source exception allows (expr_exit), or an IntRet with the
   returned value v: the callee's global state related at the caller's
   compile env, its stack values v's words (rc of them), the return
   buffer rb, if any, holding v, and the caller's memory below t's
   frontier untouched outside the call's own allocations (the return
   buffer and the staged memory arguments, which the callee may write).
   The memory frame is a fact of the callee's Venom code (it writes below
   its entry frontier only through the pointers it is passed), not of the
   body's simulation: stmt_frag's post carries no memory frame. *)
Definition intcall_callee_exit_def:
  intcall_callee_exit func cenv cx rtv rc (rb:bytes32 option) (n:num)
                      (m:num)
                      (t:venom_state) res (ee:evaluation_state) r <=>
    expr_exit res r \/
    ?v ir s'.
      res = INL v /\ r = IntRet ir s' /\
      state_rel func cenv cx (ee with scopes := []) s' /\
      intret_vals_match rtv v ir.iret_values /\
      LENGTH ir.iret_values = rc /\ ir.iret_adopt_fmp = NONE /\
      (!b sz. b + sz <= t.vs_alloca_next /\
              (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
                             n <= aid /\ aid < m ==>
                             regions_disjoint b sz off asz) ==>
              mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz t.vs_memory) /\
      (!p. rb = SOME p ==> val_in_memory rtv v (w2n p) s'.vs_memory)
End

(* The caller's compile env agrees with every function's
   build_compile_env for tops on the module-level fields the callee's
   package env takes from tops: the module, module-variable types and
   locations (immutables included), flag metadata and method ids.  body_inv pins the other module-level
   fields this way. *)
Definition cenv_module_pins_def:
  cenv_module_pins tops cenv <=>
    cenv.ce_module = NONE /\
    cenv.ce_module_var_type = build_var_type_map tops /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_flag_member_id = FST (build_flag_info tops (K (K 0)) (K 0)) /\
    cenv.ce_flag_n_members = SND (build_flag_info tops (K (K 0)) (K 0)) /\
    cenv.ce_method_id =
      (\s tys. w2n (calldata_method_id
                     (function_selector s (vyper_to_abi_types (type_env tops) tys))))
End

Theorem build_compile_env_module_pins:
  cenv_module_pins tops
    (build_compile_env tops vis mut fname args ret fbody use_trans)
Proof
  simp[cenv_module_pins_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* Held admission: the body_inv strengthening adds these pins to
   body_inv, which then proves this.  Only intcall_body_expr_ok uses it. *)
Theorem body_inv_module_pins:
  body_inv tops ctx cenv cx ==> cenv_module_pins tops cenv
Proof
  cheat
QED

(* Seam 1: argument evaluation and the callee's frame setup.  The
   caller's code up to the INVOKE runs against the source up to
   push_function, so any continuation from an intcall_entry state gives
   the whole call. *)
Theorem intcall_args_frame_setup:
  !tops ctx func cenv cx tenv ty ann name es dflt es0 sa sb vv s0
   mut args ret ss rr Q R.
    body_inv tops ctx cenv cx /\
    cenv_module_pins tops cenv /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    (~MEM (NONE,name) cx.stk ==> body_results_ok cx es) /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
      (vv,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt))
      expr_vv_res_ok es0 /\
    stmt_state_rel ctx func cenv cx es0 s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!res ee r. expr_exit res r ==> R res ee r) /\
    (!prev penv rtv es1 t.
       intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
         (mut,args,ret,ss,rr) prev penv rtv es1 t ==>
       gas_outcome F (cx_tops cx) (ctx,func) (intcall_rest cx name mut ss prev rtv)
         (es1,t) Q R) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) (es0,s0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_intcall_source_selection >> strip_tac >> gvs[] >>
  `call_evaluation_safe cx
     ((NONE,name)::int_calls_exprs es)` by
    fs[expr_body_pre_def, int_calls_expr_def] >>
  `~MEM (NONE,name) cx.stk` by
    metis_tac[call_evaluation_safe_target_not_mem] >>
  drule_all eval_expr_intcall_empty_defaults >>
  disch_then (qspecl_then [`ann`,`dflt`] assume_tac) >>
  `expr_sim_inv cenv cx tenv es0` by fs[expr_body_pre_def] >>
  `body_results_ok cx es` by simp[] >>
  `EVERY (\e. expr_body_pre cenv cx tenv e es0 /\ ~expr_has_effect e) es` by
    (simp[EVERY_MEM] >> rpt strip_tac
     >- metis_tac[bodyIntCallArgEligibilityTheory.expr_body_pre_intcall_arg]
     >> gvs[EVERY_MEM, expr_body_pre_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.call_operands_effect_root_def]) >>
  Cases_on `cenv.ce_func_info (nsid_to_string (NONE,name))` >>
  rename1 `cenv.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rest)` >>
  PairCases_on `rest` >>
  rename1 `cenv.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rbs,pvs)` >>
  `compile_call compile_expr cenv ann ty (IntCall (NONE,name)) es dflt sa = (vv,sb)` by
    fs[compile_expr_call] >>
  drule_all compile_call_intcall_shape >> strip_tac >>
  `ci_mono sa st1 /\ ci_mono st2 st3` by
    (conj_tac
     >- (qspecl_then [`compile_expr`,`cenv`,`es`,`sa`] mp_tac
           ci_mono_compile_multi_vvs >> simp[cj 1 stmtLoweringMonoTheory.ci_mono_compile_expr_sa]) >>
     qspecl_then [`cenv`,`arg_vals`,`pvs`,`MAP expr_type es`,`st2`] mp_tac
       ci_mono_compile_stage_intcall_args >> simp[]) >>
  `ci_mono st1 st2 /\ ci_mono st3 sb` by suspend "intervals" >>
  `fn_has_code sa st1 func /\ fn_has_code st1 st2 func /\
   fn_has_code st2 st3 func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split,
       compileEnvTheory.cs_extends_trans]) >>
  qpat_x_assum `eval_expr cx (Call _ _ _ _) = _` SUBST_ALL_TAC >>
  irule intcall_args_frame_then_outcome_history >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`,`tenv`,`sa`,`st1`,`tops`,`arg_vals`] >> simp[] >>
  rpt gen_tac >> strip_tac >> suspend "staging"
QED

Resume intcall_args_frame_setup[intervals]:
  Cases_on `0 < rcn` >> gvs[]
  >- (qspecl_then [`32 * rcn`,`st1`] mp_tac ci_mono_compile_alloc_buffer >>
      qspecl_then [`INVOKE`,
        `Label (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
          (nsid_to_string (NONE,name))
          (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor)
           ::invoke_args`,`rcn`,`st3`] mp_tac ci_mono_emit_multi_op >>
      qspecl_then [`rbuf.buf_operand`,`results`,`0`,`st4`] mp_tac
        ci_mono_store_multi_results >> simp[] >>
      simp[ci_mono_def] >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
  Cases_on `cenv.ce_func_return_type (nsid_to_string (NONE,name)) = NoneT`
  >- (gvs[] >>
      qmatch_asmsub_abbrev_tac `emit_void INVOKE ops st3` >>
      qspecl_then [`INVOKE`,`ops`,`st3`] mp_tac ci_mono_emit_void >>
      simp[ci_mono_def, compileEnvTheory.cs_extends_refl]) >>
  gvs[] >> qmatch_asmsub_abbrev_tac `emit_void INVOKE ops st3` >>
  qspecl_then [`INVOKE`,`ops`,`st3`] mp_tac ci_mono_emit_void >> simp[] >>
  qspecl_then [`rbs`,`st1`] mp_tac ci_mono_compile_alloc_buffer >> simp[]
QED

Resume intcall_args_frame_setup[staging]:
  `lookup_function func.fn_name ctx.ctx_functions = SOME func` by
    fs[stmt_state_rel_def, alloca_room_def] >>
  drule_all body_internal_decl_staging_flags >> strip_tac >>
  `LENGTH raws = LENGTH es /\ LENGTH arg_vals = LENGTH es` by metis_tac[] >>
  qmatch_asmsub_abbrev_tac `intcall_held_args cenv cx sa st1 ee t H` >>
  `EVERY (\(ty,raw,vv). vv_type vv = ty /\
    type_memory_bytes cenv ty < dimword(:256) /\
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      type_memory_bytes cenv ty = type_memory_size tv) H` by
    (metis_tac[Abbr `H`, intcall_arg_list_staging_layout]) >>
  `MAP (\(ty,raw,vv). ty) H = MAP expr_type es /\
   MAP (\(ty,raw,vv). raw) H = raws /\
   MAP (\(ty,raw,vv). vv) H = arg_vals` by
    simp[Abbr `H`, intcall_held_list_projections] >>
  `LIST_REL (\(ty,raw,vv) flag. flag ==> is_word_type ty) H pvs` by
    (`LIST_REL (\ty flag. flag ==> is_word_type ty)
       (MAP (\(ty,raw,vv). ty) H) pvs` by metis_tac[] >>
     pop_assum mp_tac >>
     simp[LIST_REL_MAP1, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  Cases_on `rcn = 0 /\ cenv.ce_func_return_type (nsid_to_string (NONE,name)) = NoneT`
  >- (gvs[] >> suspend "void_staging") >>
  `?rbuf. compile_alloc_buffer (if 0 < rcn then 32 * rcn else rbs) st1 = (rbuf,st2) /\
     vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
       (base_ptr rbuf)` by (Cases_on `0 < rcn` >> gvs[] >> metis_tac[]) >>
  qmatch_abbrev_tac `gas_outcome F (cx_tops cx) (ctx,func) pending (ee,t) Q R` >>
  `!D t' rb_inst b rtv.
    (?bb inst. lookup_block t'.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t'.vs_inst_idx = SOME inst /\
      inst.inst_opcode = INVOKE /\
      decode_invoke inst = SOME
        (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
          (nsid_to_string (NONE,name))
          (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor,
         if 0 < rcn then invoke_args else rbuf.buf_operand::invoke_args)) /\
    gas_marked_path F ctx func t 0 (OK t') /\
    EVERY (staged_arg cenv func ee st2 st3 t') D /\
    MAP (\(ty,tv,v,flag,op). op) D = invoke_args /\
    LIST_REL (\((ty,raw,vv),flag) (ty',tv,v,flag',op).
      ty' = ty /\ flag' = flag /\ evaluate_type (get_tenv cx) ty = SOME tv /\
      read_result cx raw ee = (INL v,ee)) (ZIP(H,pvs)) D /\
    stmt_state_rel ctx func cenv cx ee t' /\ wb_frame cenv ee st1 t t' /\
    ~t'.vs_halted /\ t'.vs_current_bb = st3.cs_current_bb /\
    t'.vs_inst_idx = LENGTH st3.cs_current_insts /\
    eval_operand rbuf.buf_operand t' = SOME (n2w b) /\
    FLOOKUP t'.vs_allocas st1.cs_next_id = SOME (b,rbuf.buf_size) /\
    MEM rb_inst (fn_insts func) /\ rb_inst.inst_opcode = ALLOCA /\
    rb_inst.inst_id = st1.cs_next_id /\ st1.cs_next_id < st2.cs_next_id /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    b + (if 0 < rcn then 0 else type_memory_size rtv) <= t'.vs_alloca_next /\
    (!ty tv v op w. MEM (ty,tv,v,F,op) D /\ eval_operand op t' = SOME w ==>
       regions_disjoint b (if 0 < rcn then 0 else type_memory_size rtv)
         (w2n w) (type_memory_size tv)) /\
    (!i j. i < LENGTH D /\ j < LENGTH D /\ i <> j ==>
      (\(ty,tv,v,flag,op) (ty',tv',v',flag',op'). ~flag /\ ~flag' ==>
        !w w'. eval_operand op t' = SOME w /\ eval_operand op' t' = SOME w' ==>
        regions_disjoint (w2n w) (type_memory_size tv)
          (w2n w') (type_memory_size tv')) (EL i D) (EL j D)) ==>
    gas_outcome F (cx_tops cx) (ctx,func) pending (ee,t) Q R` by
      suspend "nonvoid_join" >>
  Cases_on `0 < rcn` >- suspend "stack_staging" >>
  suspend "memory_staging"
QED

Resume intcall_args_frame_setup[void_staging]:
  gvs[] >>
  `fn_has_code st3 sb func` by
    (qspecl_then [`sa`,`st3`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
     (impl_tac >- (gvs[ci_mono_def] >> metis_tac[compileEnvTheory.cs_extends_trans])) >> simp[]) >>
  drule_all emitted_void_invoke_boundary >> strip_tac >>
  `fn_directly_calls ctx func.fn_name
    (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
      (nsid_to_string (NONE,name))
      (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor)` by
    metis_tac[] >>
  `MEM func ctx.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `local_ptrs_reserved cenv st1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> gvs[ci_mono_def]) >>
  drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)
    bodyIntCallStageDistinctEndpointTheory.intcall_stage_args_distinct_endpoint >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_directly_calls _ _ _`)) >>
  disch_then (qspecl_then [`pvs`,`st3`,`invoke_args`] mp_tac) >>
  simp[] >> strip_tac >>
  `LENGTH pvs = LENGTH H` by simp[] >>
  drule_all bodyIntCallStageDescriptorsTheory.staged_descriptors_projections >> strip_tac >>
  irule stmtSimDeclComposeTheory.gas_outcome_zero_prefix >>
  goal_assum (drule_at Any) >>
  suspend "void_source"
QED

Resume intcall_args_frame_setup[void_source]:
  `ret = NoneT` by metis_tac[body_internal_decl_return_type] >>
  `EVERY (\(ty,tv,v,flag,op). value_has_type tv v) D` by
    (drule_all intcall_staged_values_typed >> simp[]) >>
  `?penv. bind_arguments (get_tenv cx) args
     (MAP (\(ty,tv,v,flag,op). v) D) = SOME penv` by
    (irule intcall_staged_bind_arguments >> conj_tac >- simp[] >>
     qpat_x_assum `EVERY (\(ty,tv,v,flag,op). value_has_type tv v) D` mp_tac >>
     qpat_x_assum `EVERY (\(ty,tv,v,flag,op). evaluate_type _ ty = SOME tv) D` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >>
     first_x_assum (qspec_then `n` mp_tac) >>
     qabbrev_tac `dd = EL n D` >> PairCases_on `dd` >> simp[]) >>
  `evaluate_type (get_tenv cx) ret = SOME NoneTV` by
    simp[vyperValueTheory.evaluate_type_def] >>
  simp[ignore_bind_def, bind_return] >>
  ho_match_mp_tac (Q.INST
    [`vals` |-> `MAP (\(ty:type,tv:type_value,v:value,flag:bool,op:operand). v) D`,
     `penv` |-> `penv`, `rtv` |-> `NoneTV`]
    (SPEC_ALL (SRULE[lock_if_nr_def, ignore_bind_def, bind_return]
      intcall_read_bind_push_outcome))) >> simp[] >>
  qsuff_tac `gas_outcome F (cx_tops cx) (ctx,func)
    (intcall_rest cx name mut ss ee.scopes NoneTV)
    (ee with scopes := [penv],t') Q R`
  >- simp[intcall_rest_def, unlock_if_nr_def, ignore_bind_def] >>
  first_x_assum irule >>
  suspend "void_entry"
QED

Resume intcall_args_frame_setup[void_entry]:
  simp[intcall_entry_def] >>
  conj_tac >-
    (qexistsl_tac [`es0 with gas_obs := gs`, `MAP (\(ty,raw,vv). raw) H`,
       `ee with gas_obs := []`, `ee`, `MAP (\(ty,tv,v,flag,op). v) D`, `ee`] >>
     qpat_x_assum `!tail. eval_expr_results _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[]) >>
  conj_tac >-
    (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_push_body >>
     metis_tac[]) >>
  conj_tac >- suspend "void_admissible" >>
  suspend "void_frame_package"
QED

Resume intcall_args_frame_setup[void_admissible]:
  `!obs. read_results cx (MAP (\(ty,raw,vv). raw) H)
       (ee with gas_obs := obs) =
       (INL (MAP (\(ty,tv,v,flag,op). v) D),ee with gas_obs := obs)` by
    (gen_tac >>
     qspecl_then [`MAP (\(ty,raw,vv). raw) H`,`ee`,`ee.outcomes`,`obs`]
       mp_tac read_results_outcomes >>
     Cases_on `ee` >> simp[evaluation_state_fn_updates]) >>
  drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >> simp[] >>
  simp[gas_admissible_def, get_scopes_def, bind_def, return_def,
    lift_option_type_def, push_function_def, ignore_bind_def,
    intcall_rest_def, unlock_if_nr_def]
QED

Resume intcall_args_frame_setup[void_frame_package]:
  `ee.scopes = es0.scopes` by
    (qpat_assum `ee = es0 with <|outcomes := _; gas_obs := _|>` (fn th => simp[Once th])) >>
  `wb_frame cenv es0 sa s0 t'` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> conj_tac >-
       (qexistsl_tac [`ee`,`st1`,`t`] >> gvs[ci_mono_def]) >>
     metis_tac[]) >>
  fs[wb_frame_def] >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >-
    (`intcall_compiler_interval sa.cs_next_var sa sb` by
       (qpat_assum `compile_expr _ _ _ sa = _` mp_tac >>
        mp_tac (Q.SPECL [`cenv`,`ty`,`Call NoneT (IntCall (NONE,name)) es dflt`,
          `sa`,`sa.cs_next_var`] intcall_interval_compile_expr) >> simp[]) >>
     rpt strip_tac >> irule intcall_interval_local_separation >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexistsl_tac [`sa`,`aid`,`sb`,`func`] >> simp[] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  suspend "void_invoke_package"
QED

Resume intcall_args_frame_setup[void_invoke_package]:
  `fn_has_code st3 sb func` by
    (qspecl_then [`sa`,`st3`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  drule_all emitted_void_invoke_boundary >> strip_tac >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`bb`,`inst`] >> simp[] >>
  drule bodyIntCallStagePackageTheory.staged_args_operands_defined >> strip_tac >>
  qexists_tac `ws` >> simp[] >>
  reverse conj_tac >- suspend "void_package" >>
  gvs[]
QED

Resume intcall_args_frame_setup[void_package]:
  gvs[] >> conj_tac >- suspend "void_gas_entry" >>
  `cenv.ce_func_return_type (nsid_to_string (NONE,name)) = NoneT` by
    (drule_all bodyIntCallAssemblyTheory.body_internal_decl_return_type >> simp[]) >>
  qpat_assum `cenv.ce_func_return_type _ = NoneT` (fn th =>
    ho_match_mp_tac (GEN_ALL (SRULE[th, evaluation_state_fn_updates, arithmeticTheory.ADD_COMM]
      (Q.INST [`caller` |-> `cenv`, `ret` |-> `NoneT`, `rcn` |-> `0`,
        `es1` |-> `ee with scopes := [penv]`]
        (SPEC_ALL intcall_package_entry))))) >>
  qexistsl_tac [`MAP (\(ty,tv,v,flag,op). v) D`,`tenv`,`st3`,`st1`,
    `NoneTV`,`rbs`,`MAP (\(ty,tv,v,flag,op). flag) D`,`ee.scopes`,
    `internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
      (nsid_to_string (NONE,name))
      (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor`,
    `ws`,`D`] >>
  fs[cenv_module_pins_def, ci_mono_def] >>
  reverse conj_tac >- suspend "void_argv_bound" >>
  `EVERY (\(ty,tv,v,flag,op). evaluate_type (get_tenv cx) ty = SOME tv /\
     type_memory_bytes cenv ty = type_memory_size tv /\
     (flag ==> is_word_type ty)) D` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``]
       bodyIntCallStageDescriptorsTheory.staged_descriptors_type_sizes) >>
     qexistsl_tac [`H`,`ee`,`MAP (\(ty,tv,v,flag,op). flag) D`] >> simp[] >>
     qpat_x_assum `EVERY _ H` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_EL] >>
     rpt strip_tac >> first_x_assum drule >> qabbrev_tac `h = EL n H` >>
     PairCases_on `h` >> simp[]) >>
  pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
  simp[EVERY_EL] >> rpt strip_tac >> first_x_assum drule >>
  qabbrev_tac `d = EL n D` >> PairCases_on `d` >> simp[]
QED

Resume intcall_args_frame_setup[void_gas_entry]:
  irule bodyIntCallInvokeExistenceTheory.body_inv_internal_invoke_entry >>
  metis_tac[]
QED

Resume intcall_args_frame_setup[void_argv_bound]:
  `LENGTH ws = LENGTH args` by
    (drule tupleLoadPropsTheory.eval_operands_length >> simp[]) >>
  `1 + LENGTH args < dimword (:256)` by
    (irule bodyIntCallArgumentCountInterfaceTheory.body_intcall_staging_argument_count >>
     goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EVERY _ _`)) >> gvs[] >>
     goal_assum (drule_at (Pat `compile_stage_intcall_args _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >> decide_tac
QED

Resume intcall_args_frame_setup[stack_staging]:
  gvs[] >>
  `fn_has_code st3 st4 func` by
    (qspecl_then [`INVOKE`,
       `Label (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
         (nsid_to_string (NONE,name))
         (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor)
         ::invoke_args`,`rcn`,`st3`] mp_tac ci_mono_emit_multi_op >>
     qspecl_then [`rbuf.buf_operand`,`results`,`0`,`st4`] mp_tac
       ci_mono_store_multi_results >> simp[] >>
     qspecl_then [`st3`,`st4`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, fragExecTheory.fn_has_code_split]) >>
  drule_all emitted_multi_invoke_boundary >> strip_tac >>
  `fn_directly_calls ctx func.fn_name
    (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
      (nsid_to_string (NONE,name))
      (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor)` by
    metis_tac[] >>
  `MEM func ctx.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `local_ptrs_reserved cenv st1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> gvs[ci_mono_def]) >>
  `rcn <= 2` by
    (drule_all body_internal_decl_return_count >>
     metis_tac[returns_stack_count_bound]) >>
  `32 * rcn < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)
    intcall_stage_return_distinct_endpoint >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_directly_calls _ _ _`)) >>
  disch_then (qspecl_then [`st3`,`0`,`invoke_args`,`pvs`] mp_tac) >>
  simp[] >> strip_tac >>
  `?rtv. evaluate_type (get_tenv cx) ret = SOME rtv` by
    metis_tac[body_internal_return_physical] >>
  qpat_x_assum `!D t' rb_inst b rtv. _`
    (qspecl_then [`D`,`t'`,`inst`,`b`,`rtv`] match_mp_tac) >> gvs[] >>
  conj_tac >- metis_tac[] >> gvs[]
QED

Resume intcall_args_frame_setup[memory_staging]:
  `rcn = 0` by decide_tac >> gvs[] >>
  `fn_has_code st3 sb func` by
    (qspecl_then [`sa`,`st3`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
     (impl_tac >- (gvs[ci_mono_def] >> metis_tac[cs_extends_trans])) >> simp[]) >>
  drule_all emitted_void_invoke_boundary >> strip_tac >>
  `fn_directly_calls ctx func.fn_name
    (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
      (nsid_to_string (NONE,name))
      (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor)` by
    metis_tac[] >>
  `MEM func ctx.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `local_ptrs_reserved cenv st1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> gvs[ci_mono_def]) >>
  `ret <> NoneT` by metis_tac[body_internal_decl_return_type] >>
  drule_all body_internal_return_buffer_bound >> strip_tac >>
  drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)
    intcall_stage_return_distinct_endpoint >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_directly_calls _ _ _`)) >>
  disch_then (qspecl_then [`st3`,`type_memory_size tv`,`invoke_args`,`pvs`] mp_tac) >>
  simp[] >> strip_tac >>
  `?rtv. evaluate_type (get_tenv cx) ret = SOME rtv` by
    metis_tac[body_internal_return_physical] >>
  qpat_x_assum `!D t' rb_inst b rtv. _`
    (qspecl_then [`D`,`t'`,`inst`,`b`,`rtv`] match_mp_tac) >> gvs[] >>
  conj_tac >- metis_tac[] >> gvs[]
QED

Resume intcall_args_frame_setup[nonvoid_join]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  `LENGTH pvs = LENGTH H` by gvs[] >>
  drule_all bodyIntCallStageDescriptorsTheory.staged_descriptors_projections >> strip_tac >>
  irule stmtSimDeclComposeTheory.gas_outcome_zero_prefix >>
  goal_assum (drule_at Any) >> simp[Abbr `pending`] >>
  suspend "nonvoid_source"
QED

Resume intcall_args_frame_setup[nonvoid_source]:
  `EVERY (\(ty,tv,v,flag,op). value_has_type tv v) D` by
    (drule_all intcall_staged_values_typed >> simp[]) >>
  `?penv. bind_arguments (get_tenv cx) args
     (MAP (\(ty,tv,v,flag,op). v) D) = SOME penv` by
    (irule intcall_staged_bind_arguments >> conj_tac >- simp[] >>
     qpat_x_assum `EVERY (\(ty,tv,v,flag,op). value_has_type tv v) D` mp_tac >>
     qpat_x_assum `EVERY (\(ty,tv,v,flag,op). evaluate_type _ ty = SOME tv) D` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >>
     first_x_assum (qspec_then `n` mp_tac) >>
     qabbrev_tac `dd = EL n D` >> PairCases_on `dd` >> simp[]) >>
  simp[ignore_bind_def, bind_return] >>
  ho_match_mp_tac (Q.INST
    [`vals` |-> `MAP (\(ty:type,tv:type_value,v:value,flag:bool,op:operand). v) D`,
     `penv` |-> `penv`, `rtv` |-> `rtv`]
    (SPEC_ALL (SRULE[lock_if_nr_def, ignore_bind_def, bind_return]
      intcall_read_bind_push_outcome))) >> simp[] >>
  qsuff_tac `gas_outcome F (cx_tops cx) (ctx,func)
    (intcall_rest cx name mut ss ee.scopes rtv)
    (ee with scopes := [penv],t') Q R`
  >- gvs[intcall_rest_def, unlock_if_nr_def, ignore_bind_def] >>
  first_x_assum irule >> suspend "nonvoid_entry"
QED

Resume intcall_args_frame_setup[nonvoid_entry]:
  markerLib.RESUME_TAC >> (
  simp[intcall_entry_def] >>
  conj_tac >-
    (qexistsl_tac [`es0 with gas_obs := gs`, `MAP (\(ty,raw,vv). raw) H`,
       `ee with gas_obs := []`, `ee`, `MAP (\(ty,tv,v,flag,op). v) D`, `ee`] >>
     qpat_x_assum `!tail. eval_expr_results _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[]) >>
  conj_tac >-
    (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_push_body >>
     metis_tac[]) >>
  conj_tac >- suspend "nonvoid_admissible" >>
  suspend "nonvoid_frame_package")
QED

Resume intcall_args_frame_setup[nonvoid_admissible]:
  markerLib.RESUME_TAC >> (
  `!obs. read_results cx (MAP (\(ty,raw,vv). raw) H)
       (ee with gas_obs := obs) =
       (INL (MAP (\(ty,tv,v,flag,op). v) D),ee with gas_obs := obs)` by
    (gen_tac >>
     qspecl_then [`MAP (\(ty,raw,vv). raw) H`,`ee`,`ee.outcomes`,`obs`]
       mp_tac read_results_outcomes >>
     Cases_on `ee` >> simp[evaluation_state_fn_updates]) >>
  drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >> simp[] >>
  simp[gas_admissible_def, get_scopes_def, bind_def, return_def,
    lift_option_type_def, push_function_def, ignore_bind_def,
    intcall_rest_def, unlock_if_nr_def])
QED

Resume intcall_args_frame_setup[nonvoid_frame_package]:
  markerLib.RESUME_TAC >> (
  `ee.scopes = es0.scopes` by
    (qpat_assum `ee = es0 with <|outcomes := _; gas_obs := _|>` (fn th => simp[Once th])) >>
  `wb_frame cenv es0 sa s0 t'` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> conj_tac >-
       (qexistsl_tac [`ee`,`st1`,`t`] >> gvs[ci_mono_def]) >>
     metis_tac[]) >>
  fs[wb_frame_def] >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >-
    (`intcall_compiler_interval sa.cs_next_var sa sb` by
       (qpat_assum `compile_expr _ _ _ sa = _` mp_tac >>
        mp_tac (Q.SPECL [`cenv`,`ty`,`Call ann (IntCall (NONE,name)) es dflt`,
          `sa`,`sa.cs_next_var`] intcall_interval_compile_expr) >> simp[]) >>
     rpt strip_tac >> irule intcall_interval_local_separation >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexistsl_tac [`sa`,`aid`,`sb`,`func`] >> simp[] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  drule bodyIntCallStagePackageTheory.staged_args_operands_defined >> strip_tac >>
  qexistsl_tac [`st2`,`MAP (\(ty,tv,v,flag,op). op) D`,`st3`,
    `if 0 < rcn then ws else n2w b::ws`] >> simp[] >>
  conj_tac >- suspend "nonvoid_compile_shape" >>
  suspend "nonvoid_operands")
QED

Resume intcall_args_frame_setup[nonvoid_compile_shape]:
  strip_tac >> Cases_on `0 < rcn`
  >- (gvs[] >> gvs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  gvs[] >>
  `ret <> NoneT` by metis_tac[body_internal_decl_return_type] >>
  drule_all body_internal_return_buffer_bound >> strip_tac >> gvs[] >>
  suspend "nonvoid_compile_memory"
QED

Resume intcall_args_frame_setup[nonvoid_compile_memory]:
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `b MOD dimword (:256) <= b` by simp[arithmeticTheory.MOD_LESS_EQ] >>
  gvs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_LESS_EQ_MONO, arithmeticTheory.LESS_EQ_TRANS]
QED

Resume intcall_args_frame_setup[nonvoid_operands]:
  conj_asm1_tac >-
    (Cases_on `0 < rcn` >> simp[venomStateTheory.eval_operands_def]) >>
  conj_tac >-
    (irule bodyIntCallInvokeExistenceTheory.body_inv_internal_invoke_entry >>
     conj_tac >- simp[] >>
     qexistsl_tac [`args`,`if 0 < rcn then ws else n2w b::ws`,`bb`,`cenv`,
       `cx`,`inst`,`mut`,`name`,
       `if 0 < rcn then MAP (\(ty,tv,v,flag,op). op) D
        else rbuf.buf_operand::MAP (\(ty,tv,v,flag,op). op) D`,
       `ret`,`rr`,`ss`,`tops`] >> simp[]) >>
  suspend "nonvoid_package"
QED

Resume intcall_args_frame_setup[nonvoid_package]:
  gvs[] >>
  drule_all body_internal_decl_return_type >> strip_tac >>
  ho_match_mp_tac (GEN_ALL (CONV_RULE
    (RAND_CONV (SIMP_CONV (srw_ss())
      [evaluation_state_fn_updates, arithmeticTheory.ADD_COMM]))
    (Q.INST [`caller` |-> `cenv`,
      `es1` |-> `ee with scopes := [penv]`]
      (SPEC_ALL intcall_package_entry)))) >>
  qexistsl_tac [`ws`,`MAP (\(ty,tv,v,flag,op). v) D`,`tenv`,`st3`,`st2`,
    `n2w b`,`rbs`,`MAP (\(ty,tv,v,flag,op). flag) D`,`ee.scopes`,`D`] >>
  simp[evaluation_state_fn_updates] >>
  `ee with scopes := es0.scopes = ee` by
    (qpat_x_assum `ee.scopes = es0.scopes` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `ee` >> Cases_on `es0` >>
     simp[evaluation_state_fn_updates]) >>
  fs[cenv_module_pins_def, ci_mono_def] >>
  conj_tac >- suspend "nonvoid_direct_call" >>
  conj_tac >- suspend "nonvoid_descriptor_typing" >>
  conj_tac >- (Cases_on `0 < rcn` >> simp[]) >>
  conj_tac >- suspend "nonvoid_argv_bound" >>
  suspend "nonvoid_return_capacity"
QED

Resume intcall_args_frame_setup[nonvoid_direct_call]:
  `MEM inst (fn_insts func)` by
    (irule fragExecTheory.lookup_block_fn_insts >>
     goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
     qpat_x_assum `get_instruction _ _ = SOME inst` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
     metis_tac[listTheory.EL_MEM]) >>
  fs[stmt_state_rel_def, state_rel_def, fcgDefsTheory.fn_directly_calls_def] >>
  qexistsl_tac [`inst`,`if 0 < rcn then MAP (\(ty,tv,v,flag,op). op) D
      else rbuf.buf_operand::MAP (\(ty,tv,v,flag,op). op) D`] >>
  fs[venomExecSemanticsTheory.decode_invoke_def, AllCaseEqs()]
QED

Resume intcall_args_frame_setup[nonvoid_descriptor_typing]:
  `EVERY (\(ty,tv,v,flag,op). evaluate_type (get_tenv cx) ty = SOME tv /\
     type_memory_bytes cenv ty = type_memory_size tv /\
     (flag ==> is_word_type ty)) D` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``]
       bodyIntCallStageDescriptorsTheory.staged_descriptors_type_sizes) >>
     qexistsl_tac [`H`,`ee`,`MAP (\(ty,tv,v,flag,op). flag) D`] >> simp[] >>
     qpat_x_assum `EVERY _ H` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_EL] >>
     rpt strip_tac >> first_x_assum drule >> qabbrev_tac `h = EL n H` >>
     PairCases_on `h` >> simp[]) >>
  pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
  simp[EVERY_EL] >> rpt strip_tac >> first_x_assum drule >>
  qabbrev_tac `d = EL n D` >> PairCases_on `d` >> simp[]
QED

Resume intcall_args_frame_setup[nonvoid_argv_bound]:
  `LENGTH ws = LENGTH args` by
    (qpat_assum `eval_operands (MAP _ D) t' = SOME ws`
       (mp_then Any mp_tac tupleLoadPropsTheory.eval_operands_length) >> simp[]) >>
  `1 + LENGTH args < dimword (:256)` by
    (irule bodyIntCallArgumentCountInterfaceTheory.body_intcall_staging_argument_count >>
     goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EVERY _ _`)) >> gvs[] >>
     goal_assum (drule_at (Pat `compile_stage_intcall_args _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  Cases_on `0 < rcn` >> simp[] >> decide_tac
QED

Resume intcall_args_frame_setup[nonvoid_return_capacity]:
  strip_tac >> gvs[] >>
  drule_all body_internal_return_buffer_bound >> strip_tac >> gvs[] >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  qexistsl_tac [`b`,`rbuf.buf_size`,`rb_inst`] >> simp[] >>
  `t'.vs_alloca_next < dimword (:256)` by
    fs[stmt_state_rel_def, state_rel_def, alloca_room_def] >>
  decide_tac
QED

Finalise intcall_args_frame_setup

(* Seam 2: the call step's callee side.  From the callee's entry the
   INVOKE runs the packaged callee's code; under the body induction
   hypothesis for its body at cxf it ends as intcall_callee_exit says.
   rb is the return buffer the INVOKE passes, if the call has one.
   body_stmts_ok gives the source-related part of the exit; the memory
   frame below t's frontier is a fact of the callee's Venom code (it
   writes there only through rb and its memory parameters' pointers),
   which this seam proves on its own. *)
Theorem intcall_callee_body_sim:
  !tops ctx func cenv cx tenv name es sa sb vv s0 es0 mut args ret ss rr
   prev penv rtv es1 t callee entered rc rbs pvs.
    body_inv tops ctx cenv cx /\
    cenv_module_pins tops cenv /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    body_stmts_ok (cx with stk updated_by CONS (NONE,name)) ss /\
    intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
      (mut,args,ret,ss,rr) prev penv rtv es1 t /\
    gas_invoke_entry (ctx,func) t callee entered /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) ==>
    !bb inst lbl arg_ops argv.
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
           sa.cs_next_id sb.cs_next_id t)
Proof
  cheat
QED

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
  cheat
QED

(* The source facts an intcall_entry state carries. *)
Theorem intcall_entry_source:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t ==>
  ~MEM (NONE,name) cx.stk /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  ?s1 results t1 s2 vs t2.
    eval_expr_results cx es s1 = (INL results,t1) /\
    read_results cx results s2 = (INL vs,t2) /\
    bind_arguments (get_tenv cx) args vs = SOME penv
Proof
  rw[intcall_entry_def] >> metis_tac[]
QED
