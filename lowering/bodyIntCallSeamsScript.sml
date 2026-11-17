(* The boundary relations of an internal call, cut at the INVOKE and the
   callee's return: intcall_entry is the relation at the INVOKE (arguments
   evaluated, staged as the callee's parameters, return buffer allocated),
   intcall_callee_exit the one at the callee's return; intcall_rest is the
   source after push_function and intcall_callee_src the callee's run. *)

Theory bodyIntCallSeams
Ancestors
  bodySim exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts
  intCallCallee intCallFrame fragGasFocus gasOutcome gasContext
  compileVyper exprLowering exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperAST venomState venomExecSemantics
Libs
  monadsyntax

(* The source of an internal call after push_function: the body, the
   frame's cleanup with the nonreentrant lock's release, and the cast of
   the returned value.  A supported callee has no defaults
   (body_intcall_source_selection). *)
Definition intcall_rest_def:
  intcall_rest cx name mut nr ss prev rtv =
    do rv <- finally_unless_halt
         (finally
            (try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss;
                     return NoneV
                  od) handle_function)
            (pop_function prev))
         (unlock_if_nr cx nr (is_view_mut mut));
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

(* The INVOKE of internal function name (mut, nonreentrancy flag nr,
   args,ret,ss, raw-return flag rr), called with arguments es from the caller func, whose code for the
   call runs from sa to sb and gives vv, at the source state es0 and Venom
   state s0.  t is at the INVOKE, es1 is the source state push_function
   leaves, prev the caller's scopes it saved, penv the parameters' scope
   and rtv the evaluated return type.
   - Source: the arguments evaluated to the values penv binds,
     and the lock taken when the callee is nonreentrant; the callee's
     body is call-safe at the pushed context.
   - Code: the call's code as compile_call_intcall_shape gives it: the
     return buffer rbuf if any (sa to st2), each argument lowered and
     staged at the callee's declared parameter type (st2 to st3), the
     INVOKE of the callee's label at st3
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
     vv_post asks.
   - Callee entry: the INVOKE enters a callee, and at the internal
     function's package (any nonreentrancy keys and transient flag, the
     caller's target) whose label is the INVOKE's and whose return-buffer
     flag matches the call's, the premises of
     compile_internal_prologue_entry hold for argv. *)
Definition intcall_entry_def:
  intcall_entry H tops ctx func cenv cx tenv name es sa sb vv s0 es0
                (mut,nr,args,ret,ss,rr) prev penv rtv es1 t <=>
    ~MEM (NONE,name) cx.stk /\
    (?s1 vs t1 s3 u t3.
       eval_exprs cx es s1 = (INL vs,t1) /\
       bind_arguments (get_tenv cx) args vs = SOME penv /\
       lock_if_nr cx nr (is_view_mut mut) s3 = (INL u,t3)) /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
      (int_calls_stmts ss) /\
    es1.scopes = [penv] /\
    gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es1 /\
    stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
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
    ?st2 invoke_args st3 rc rbs pvs lbl arg_ops bb inst argv.
      cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
      compile_stage_intcall_args compile_expr cenv es pvs
        (TAKE (LENGTH es) (cenv.ce_func_param_types (nsid_to_string (NONE,name))))
        st2 = (invoke_args,st3) /\
      lbl = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
              (nsid_to_string (NONE,name))
              (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
              cenv.ce_is_ctor /\
      (rc = 0 /\ rbs = 0 ==>
       st2 = sa /\ arg_ops = invoke_args /\
       (?u. emit_void INVOKE (Label lbl :: invoke_args) st3 = (u,sb)) /\
       vv = StackValue (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
              (Lit 0w)) /\
      (0 < rc \/ 0 < rbs ==>
       ?rbuf aid off.
         compile_alloc_buffer (if 0 < rc then 32 * rc else rbs) sa =
           (rbuf,st2) /\
         vv = LocatedValue
                (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
                (base_ptr rbuf) /\
         eval_operand rbuf.buf_operand t = SOME (n2w off) /\
         FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size) /\
         sa.cs_next_id <= aid /\
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
             (mut,nr,rr,name,args,([] : expr list),ret,ss)) =
          (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
        lbl' = lbl /\ (has_rb <=> rc = 0 /\ 0 < rbs) /\
        (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
        state_rel H func ce cx (es1 with scopes := []) t /\
        internal_immutable_regions ce cx es1 t.vs_alloca_next /\
        internal_args_rel ce params penv (if has_rb then 1 else 0) argv
          t.vs_alloca_next t.vs_memory /\
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
   INVOKE, whose call's code allocates from ALLOCA id n on: an abort the
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
  intcall_callee_exit H func cenv cx rtv rc (rb:bytes32 option) (n:num)
                      (t:venom_state) res (ee:evaluation_state) r <=>
    (expr_exit res r /\ halt_exit H cx ee res r) \/
    ?v ir s'.
      res = INL v /\ r = IntRet ir s' /\
      state_rel H func cenv cx (ee with scopes := []) s' /\
      intret_vals_match rtv v ir.iret_values /\
      LENGTH ir.iret_values = rc /\ ir.iret_adopt_fmp = NONE /\
      (!b sz. b + sz <= t.vs_alloca_next /\
              (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
                             n <= aid ==> regions_disjoint b sz off asz) ==>
              mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz t.vs_memory) /\
      (!p. rb = SOME p ==> val_in_memory rtv v (w2n p) s'.vs_memory)
End

(* The source facts an intcall_entry state carries. *)
Theorem intcall_entry_source:
  intcall_entry H tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t ==>
  ~MEM (NONE,name) cx.stk /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  ?s1 vs t1 s3 u t3.
    eval_exprs cx es s1 = (INL vs,t1) /\
    bind_arguments (get_tenv cx) args vs = SOME penv /\
    lock_if_nr cx nr (is_view_mut mut) s3 = (INL u,t3)
Proof
  rw[intcall_entry_def] >> metis_tac[]
QED
