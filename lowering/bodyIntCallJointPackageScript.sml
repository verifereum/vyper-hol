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
  list venomExecProps venomWf bodyIntCallPackageRootReady bodyIntCallPackageProducerOutcome bodyIntCallPackageExitFields bodyIntCallPackageBodyOutcome bodyIntCallPackagePrefix bodyIntCallPackageBodyControl bodyIntCallPackageEpilogue bodyIntCallPackageHandler bodyIntCallPackageProducerEntry bodyIntCallPackageProducerExit bodyIntCallPackageStateTransport bodyIntCallPackageRoot bodyIntCallPackageRootSemantic bodyIntCallPackageGeometry bodyIntCallPackageRun bodyIntCallPackageBounds bodyIntCallPackageSemantic bodyIntCallProducerBounds bodyIntCallProducerSemantic bodyIntCallInvokedCode bodyIntCallPackageInputs bodyIntCallEntryInputs bodyIntCallSelectedCode bodyIntCallDeployCode bodyIntCallExtractCode bodyIntCallInvokeEntry bodyIntCallSeamDefs bodyIntCallJointContract bodyIntCallActualJointInit bodyIntCallActualEntryProtection bodyIntCallActualEntryLanding bodyIntCallActualEntryWitness bodyIntCallActualRootFrame
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
  rpt strip_tac >>
  `?label ce params has_rb is_nr key trans view ctor ilen ss' rt.
    set_internal_package_target cenv.ce_target
      (package_internal_fn tops F (assign_nkeys tops 0) cenv.ce_is_ctor
        (if cx.in_deploy then
           compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
         else 0)
        (mut,F,rr,name,args,([]:expr list),ret,ss)) =
      (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen,ss',rt)` by
    simp[GSYM pairTheory.EXISTS_PROD] >>
  drule_all invoked_internal_body_run >> strip_tac >>
  drule_all gas_invoke_entry_decode >> strip_tac >>
  drule_all body_inv_invoked_internal_code >> strip_tac >>
  drule_all intcall_entry_root_ready >>
  disch_then (qx_choose_then `P` (qx_choose_then `staged` (qx_choose_then `fp`
    (qx_choose_then `env` (qx_choose_then `env_after` (qx_choose_then `bindings`
      (fn th => map_every assume_tac (CONJUNCTS th)))))))) >>
  `~block_is_terminated body_start` by
    (drule internal_entry_body_open >> simp[]) >>
  drule internal_package_return_option >> strip_tac >>
  `intcall_stmts_producer fp ss` by (first_x_assum irule >> simp[]) >>
  `stmts_env fp.jc_root_ce NoLoop
      (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
      ss body_start = (body_env,body_end)` by
    (Cases_on `ret = NoneT` >> gvs[]) >>
  drule_all intcall_root_caller_exit_fields >> strip_tac >>
  drule_all intcall_entry_package_inputs >> strip_tac >>
  irule gas_outcome_path_prefix >> goal_assum (drule_at Any) >>
  `cx_tops fp.jc_cx = cx_tops cx` by
    fs[gasContextTheory.cx_tops_def, vyperContextTheory.get_module_code_def] >>
  pure_rewrite_tac[intcall_callee_src_def] >>
  qpat_assum `cx_tops fp.jc_cx = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  qpat_assum `fp.jc_ctx = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `fp.jc_func = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `fp.jc_cx = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule intcall_producer_callee_outcome >>
  goal_assum (drule_at Any) >>
  conj_tac >-
    (qpat_assum `fp.jc_prot = _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `fp.jc_root_ce = _` kall_tac >>
  simp[] >> conj_tac >- (qexists `(NONE,name)` >> simp[]) >>
  conj_tac >-
    (qpat_assum `has_rb <=> _` (fn th => pure_rewrite_tac[GSYM th]) >>
     Cases_on `has_rb` >> simp[]) >>
  conj_tac >- (goal_assum (drule_at Any)) >>
  goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
  qexistsl [`body_env`,`env_after`,`body_end`,`final`] >>
  Cases_on `ret = NoneT` >> gvs[]
QED
