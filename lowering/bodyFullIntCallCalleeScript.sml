(*
 * The internal call full case's callee stage over the finite-horizon joint
 * judgment.
 *
 * TOP-LEVEL:
 *   intcall_callee_full
 *)
Theory bodyFullIntCallCallee
Ancestors
  bodyFullIntCallDefs bodyIntCallSeams bodyFullPreds bodySimFull
  gasOutcomeFull fragGasFocus bodyPtrDefs gasShadow exprSimHypsDefs
  vyperInterpreter vyperAST list

val _ = Parse.hide "body";

(* (b) The callee, at (DF H, lo).  From the callee's entry the INVOKE runs
   the packaged callee's code, with the ghost a focus into the call starts
   from (the operands' provenance, no variables, the caller's taint
   otherwise); under the body judgment for its body at the pushed context
   it ends as intcall_callee_exit_full says.  This stage holds the callee
   frame's return producer too (the full twin of bodyMemIntCallFrameRet's
   internal_frame_ret_ok_mem, from stmtSimReturn's internal_frame_ret_*_full
   pieces), so the body judgment's frame_ret_ok_full premise is met inside
   it. *)
Theorem intcall_callee_full:
  !DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn callee entered rc
   rbs pvs.
    body_inv tops ctx cenv cx /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args [] ret ss) tops /\
    body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es
         sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
         G tn) /\
    gas_invoke_entry (ctx,func) t callee entered /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) ==>
    !bb inst lbl arg_ops argv.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
         MAP (op_prov G) arg_ops)
        (cx_tops cx) cx st0 (intcall_callee_src cx name ss)
        (es1, entered, FEMPTY, tn with t_var := FEMPTY)
        (\H res ee G' tn' t'. F)
        (\H res ee gt r.
           intcall_callee_exit_full (DF, lo) H func cenv cx rtv rc
             (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
             sa.cs_next_id t tn res ee gt r)
Proof
  cheat
QED
