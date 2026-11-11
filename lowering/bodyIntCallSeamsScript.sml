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
  bodyIntCallSource bodyIntCallWidenedPost bodyIntCallWidenedEndpoint
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
    locals_kept cenv es0 (es1 with scopes := prev) s0 t /\
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

(* body_inv carries the module-level pins (cenv_module_pins, bodySim). *)
Theorem body_inv_module_pins:
  body_inv tops ctx cenv cx ==> cenv_module_pins tops cenv
Proof
  simp[body_inv_def]
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
  cheat
QED

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
  `wb_frame cenv es0 (es1 with scopes := prev) sa s0 t` by
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
  conj_tac >- simp[] >>
  reverse conj_tac >- (qexists_tac `es1` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
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
  `wb_frame cenv es0 (es1 with scopes := prev) sa s0 t` by
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
    wb_frame cenv es0 (ee with <|scopes := prev; gas_obs := []|>) sa s0 out /\
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
     TRY (qexists_tac `es1` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
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
  goal_assum (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
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
