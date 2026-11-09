(* The internal callee's packaging, stated once over the joint statement
   producer: from the INVOKE (intcall_entry), the packaged callee's run
   ends as intcall_callee_exit says, given intcall_stmts_producer for the
   callee's body at every joint frame owned by the callee under an edge
   relation E that witnesses the pushed call stack.  Seam 2
   (bodyIntCallSeams) takes the producer from intcall_joint_producers;
   the joint call step's nested internal call takes it from its
   call-graph descent premise.
 *
 * TOP-LEVEL:
 *   intcall_callee_packaging
 *)

Theory bodyIntCallJointPackage
Ancestors
  bodyIntCallSeamDefs bodyIntCallJointContract bodyIntCallActualEntryFields
Libs
  monadsyntax

Theorem intcall_callee_packaging:
  !E tops ctx func cenv cx tenv name es sa sb vv s0 es0 mut args ret ss rr
   prev penv rtv es1 t callee entered rc rbs pvs.
    body_inv tops ctx cenv cx /\
    cenv_module_pins tops cenv /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    call_stack_follows (call_edge_rel E) ((NONE,name)::cx.stk) /\
    irreflexive (TC (call_edge_rel E)) /\
    functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name)) /\
    (!fp. fp.jc_edges = E /\ fp.jc_owner = (NONE,name) /\ fp.jc_tops = tops ==>
          intcall_stmts_producer fp ss) /\
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
