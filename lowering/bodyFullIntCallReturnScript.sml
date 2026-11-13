(*
 * The internal call full case's return stage over the finite-horizon joint
 * judgment.
 *
 * TOP-LEVEL:
 *   intcall_return_full
 *)
Theory bodyFullIntCallReturn
Ancestors
  bodyFullIntCallDefs bodyIntCallSeams bodyFullPreds bodySimFull
  gasOutcomeFull fragGasFocus bodyPtrDefs gasShadow gasContext
  exprSimHypsDefs exprLowering vyperInterpreter vyperAST list

val _ = Parse.hide "body";

(* (c) Return and unlock restore, at (DF H, lo).  From an
   intcall_entry_full state t at the INVOKE, with every callee run the
   INVOKE can enter ending as stage (b) gives it: the INVOKE, the results'
   store into the return buffer, the frame's cleanup with the lock's
   release, and the cast reach the call's joint vv post at the end of its
   code; with the value unwrapped after it, they reach its joint value
   post. *)
Theorem intcall_return_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 st0 sa sm shadow_sa shadow_sm vv s0 G0 tn0 mut nr args ret ss
   rr prev penv rtv es1 t G tn rc rbs pvs.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args [] ret ss) tops /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
      (vv, sm) /\
    compile_expr cenv ty
      (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)) shadow_sa =
      (vv, shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es
         sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
         G tn) /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    (!callee entered bb inst lbl arg_ops argv.
       gas_invoke_entry (ctx,func) t callee entered /\
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
              sa.cs_next_id t tn res ee gt r)) ==>
    (fn_has_code sa sm func /\
     fn_has_code shadow_sa shadow_sm shadow_func ==>
     gas_outcome_full
       (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
       (cx_tops cx) cx st0 (intcall_rest cx name mut nr ss prev rtv)
       (es1, t, G, tn)
       (\H res ee G tn t'. ?tv. res = INL tv /\
         vv_post H ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
           es0 sa sm s0 ee tv vv t' /\
         vv_store_bound cx (expr_type (Call ann (IntCall (NONE,name)) es dflt))
           (lowered_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
           ee tv vv t' /\
         t'.vs_current_bb = sm.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sm.cs_current_insts /\
         alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
         ptr_vv_ok cx
           (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
           tv vv ee G tn t' /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv ee = (INL val, ee) /\
                !rt w. evaluate_type (get_tenv cx)
                         (post_value_type cenv
                            (Call ann (IntCall (NONE,name)) es dflt)) =
                         SOME rt /\
                       eval_operand (vv_operand vv) t' = SOME w ==>
                       w2n w + type_memory_size rt <= lo /\
                       (!mem. mem_agree_outside tn.t_mem t'.vs_memory mem ==>
                              val_in_memory rt val (w2n w) mem)) /\
         (!ty' op. vv = StackValue ty' op /\
                   ~is_word_type
                      (post_value_type cenv
                         (Call ann (IntCall (NONE,name)) es dflt)) ==>
                   ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt)
                     op G t') /\
         (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt)
                    p.ptr_operand G t') /\
         ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
       (\H res ee gt r. expr_exit res r)) /\
    (!op sb shadow_sb.
       unwrap_value cenv vv sm = (op, sb) /\
       unwrap_value cenv vv shadow_sm = (op, shadow_sb) /\
       gas_shadow_state sb shadow_sb /\
       fn_has_code sa sb func /\
       fn_has_code shadow_sa shadow_sb shadow_func /\
       gas_admissible
         (bind (intcall_rest cx name mut nr ss prev rtv) (read_result cx))
         expr_res_ok es1 ==>
       gas_outcome_full
         (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         (cx_tops cx) cx st0
         (bind (intcall_rest cx name mut nr ss prev rtv) (read_result cx))
         (es1, t, G, tn)
         (\H res ee G tn t'. ?v. res = INL v /\
           expr_post H ctx func cenv cx (Call ann (IntCall (NONE,name)) es dflt)
             es0 sa sb s0 ee v op t' /\
           expr_store_bound cx
             (expr_type (Call ann (IntCall (NONE,name)) es dflt)) v op t' /\
           t'.vs_current_bb = sb.cs_current_bb /\
           t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
           alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
           ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
           ptr_val_ok cx
             (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt))
             v op G tn t' /\
           (~is_word_type
               (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) ==>
            ptr_buf_ok cenv (Call ann (IntCall (NONE,name)) es dflt) op G t') /\
           ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
         (\H res ee gt r. expr_exit res r))
Proof
  cheat
QED
