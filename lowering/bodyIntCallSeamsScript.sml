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
  bodyIntCallSeamDefs bodyIntCallSeamArgs bodyIntCallSeamReturn
  bodyIntCallJointPackage bodyIntCallJointInd vyperTypeCallStackSoundness
Libs
  monadsyntax

(* The definitions and seams 1 and 3 live below the joint induction's
   steps (bodyIntCallSeamDefs, bodyIntCallSeamArgs, bodyIntCallSeamReturn),
   so the call step can use them for nested internal calls; their names
   are re-exported here for bodySimCallIntcall. *)
Theorem body_inv_module_pins = bodyIntCallSeamDefsTheory.body_inv_module_pins
Theorem intcall_entry_source = bodyIntCallSeamDefsTheory.intcall_entry_source
Theorem intcall_args_frame_setup = bodyIntCallSeamArgsTheory.intcall_args_frame_setup
Theorem intcall_return_restore = bodyIntCallSeamReturnTheory.intcall_return_restore
Theorem intcall_return_widened = bodyIntCallSeamReturnTheory.intcall_return_widened

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
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `?E. call_stack_follows (call_edge_rel E) ((NONE,name)::cx.stk) /\
       irreflexive (TC (call_edge_rel E)) /\
       functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name))`
    by (qpat_x_assum `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [intcall_entry_def]) >>
        qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
        simp_tac (srw_ss()) [call_evaluation_safe_def] >> strip_tac >>
        qexists_tac `edges` >> asm_simp_tac (srw_ss()) []) >>
  `!fp. fp.jc_edges = E /\ fp.jc_owner = (NONE,name) /\ fp.jc_tops = tops ==>
        intcall_stmts_producer fp ss` by simp[intcall_joint_producers] >>
  drule_all intcall_callee_packaging >>
  simp[]
QED
