(* The internal call's seam relations: intcall_rest and intcall_callee_src
   (the source after push_function and the callee's body as the INVOKE runs
   it), intcall_entry (the INVOKE boundary) and intcall_callee_exit (the
   callee's return), with the held body_inv_module_pins.  Seams 1 and 3
   (bodyIntCallSeamArgs, bodyIntCallSeamReturn) and the callee packaging
   (bodyIntCallJointPackage) sit on these; bodyIntCallSeams assembles them. *)

Theory bodyIntCallSeamDefs
Ancestors
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

(* Held admission: the body_inv strengthening adds these pins to
   body_inv, which then proves this.  Only intcall_body_expr_ok uses it. *)
Theorem body_inv_module_pins:
  body_inv tops ctx cenv cx ==> cenv_module_pins tops cenv
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
