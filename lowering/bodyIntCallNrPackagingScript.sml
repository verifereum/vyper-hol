(* Guarded internal callee packaging over the joint statement producer. *)
Theory bodyIntCallNrPackaging
Ancestors
  bodyIntCallNrBodyCode bodyIntCallNrInvokedCode bodyIntCallNrNormalLanding
  bodyIntCallNrEntryReady bodyIntCallNrBodyOutcome bodyIntCallEntryPhi
  bodyIntCallPackageControl bodyIntCallPackageExitFields
  bodyIntCallPackageBodyControl bodyIntCallJointPackage
  compileVyper compileEnv venomExecProps venomWf list vyperInterpreter
  concretizeAnalysisOwnership
Libs
  monadsyntax

Theorem selected_internal_guarded_boundary:
  body_inv tops ctx caller_ce cx /\
  lookup_function label ctx.ctx_functions = SOME callee /\
  new_block label before = (old,entry) /\
  compile_internal_function ce params has_rb nr key trans view ctor ilen
    ss rt entry = ((),final) /\ fn_has_code entry final callee /\
  setup_callee callee argv caller = SOME setup /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state ==>
  ?ce2 rpc imm prelock body_start body_env body_end.
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,rpc,imm),prelock) /\
    (if nr then compile_nonreentrant_lock key trans view prelock
     else ((),prelock)) = ((),body_start) /\
    stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    fn_has_code entry prelock callee /\ fn_has_code prelock body_start callee /\
    fn_has_code body_start body_end callee /\ fn_has_code body_end final callee /\
    entry.cs_current_insts = [] /\
    entry.cs_current_bb = (HD callee.fn_blocks).bb_label /\
    (phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions) = setup /\
    (~block_is_terminated body_end ==>
      ?su. (if nr then compile_nonreentrant_unlock key trans view body_end
            else ((),body_end)) = ((),su) /\
        (case rt of NONE => emit_inst RET [rpc] [] su
                  | SOME ty => emit_inst INVALID [] [] su) = ((),final))
Proof
  strip_tac >> drule_all internal_function_guarded_body_code >> strip_tac >>
  drule_all body_inv_function_entry_label >> strip_tac >>
  `entry.cs_current_insts = [] /\
   entry.cs_current_bb = (HD callee.fn_blocks).bb_label` by gvs[new_block_def] >>
  `(phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions) = setup`
    by (irule internal_entry_phi_landing >> metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >> simp[]
QED

Theorem internal_package_guard_metadata:
  set_internal_package_target target
    (package_internal_fn tops T (K global_nonreentrant_slot) ctor ilen
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor',ilen',ss',rt) ==>
  is_nr = nr /\ key = global_nonreentrant_slot /\ trans = T /\
  view = (mut = View) /\ ss' = ss /\
  ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,mut = View)
Proof
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def, is_view_mut_def] >> strip_tac >> gvs[]
QED

Theorem body_inv_nonreentrant_view:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret ss) tops ==>
  is_view_mut mut = (mut = View)
Proof
  strip_tac >>
  `function_mutability_ok [(NONE,tops)] vis mut T dflts ss` by
    (fs[bodySimTheory.body_inv_def] >> metis_tac[]) >>
  fs[vyperTypeContractTheory.function_mutability_ok_def, is_view_mut_def] >>
  metis_tac[]
QED

Theorem internal_guarded_body_open:
  compile_nonreentrant_lock key T view pre = ((),post) ==>
  ~block_is_terminated post
Proof
  Cases_on `view` >>
  simp[contextTheory.compile_nonreentrant_lock_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  disch_then (SUBST1_TAC o SYM) >>
  Cases_on `pre.cs_current_insts` >>
  simp[block_is_terminated_def, LAST_CONS_cond, LAST_APPEND_CONS,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem intcall_callee_packaging_nr:
  !E tops ctx func cenv cx tenv name es sa sb vv s0 es0 mut args ret ss rr
   prev penv rtv es1 t callee entered retc rbs pvs.
    body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
    lookup_callable_function cx.in_deploy name tops = SOME (mut,T,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut T rr name args dflts ret ss) tops /\
    call_stack_follows (call_edge_rel E) ((NONE,name)::cx.stk) /\
    irreflexive (TC (call_edge_rel E)) /\
    functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name)) /\
    (!fp. fp.jc_edges = E /\ fp.jc_owner = (NONE,name) /\ fp.jc_tops = tops ==>
      intcall_stmts_producer fp ss) /\
    intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
      (mut,T,args,ret,ss,rr) prev penv rtv es1 t /\
    gas_invoke_entry (ctx,func) t callee entered /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (retc,rbs,pvs) ==>
    !bb inst lbl arg_ops argv.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv ==>
      gas_outcome F (cx_tops cx) (ctx,callee) (intcall_callee_src cx name mut T ss)
        (es1,entered) (\res ee r. F)
        (intcall_callee_exit func cenv cx mut T rtv retc
          (if retc = 0 /\ cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT
           then SOME (HD argv) else NONE) sa.cs_next_id sb.cs_next_id t)
Proof
  rpt strip_tac >>
  `?label ce params has_rb is_nr key trans view ctor ilen ss' rt.
    set_internal_package_target cenv.ce_target
      (package_internal_fn tops T (K global_nonreentrant_slot) cenv.ce_is_ctor
        (if cx.in_deploy then
          compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
         else 0) (mut,T,rr,name,args,([]:expr list),ret,ss)) =
      (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen,ss',rt)` by
    simp[GSYM pairTheory.EXISTS_PROD] >>
  drule_all body_inv_invoked_internal_code_flag >> strip_tac >>
  drule_all bodyIntCallInvokeEntryTheory.gas_invoke_entry_decode >> strip_tac >>
  gvs[] >> drule_all selected_internal_guarded_boundary >> strip_tac >>
  drule internal_package_guard_metadata >> strip_tac >>
  drule_all body_inv_nonreentrant_view >> strip_tac >> gvs[] >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    (irule bodySimTheory.body_inv_nonreentrant_slot >> metis_tac[]) >>
  `nonreentrant_slot_separated cx` by
    fs[bodyIntCallSeamDefsTheory.intcall_entry_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperStorageLayoutSafetyTheory.storage_layout_safe_def] >>
  `fn_inst_ids_distinct callee` by
    (drule venomExecPropsTheory.lookup_function_MEM >> strip_tac >>
     irule concretizeAnalysisOwnershipTheory.source_member_ids_distinct >>
     metis_tac[]) >>
  qabbrev_tac `P = (\a k. a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint a k off asz)` >>
  qabbrev_tac `staged = (\b z. ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv))` >>
  irule intcall_entry_guard_outcome_nr >>
  conj_tac >- simp[bodyIntCallSeamDefsTheory.intcall_callee_exit_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `set_internal_package_target _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `call_stack_follows _ _`)) >>
  goal_assum (drule_at (Pat `eval_operands _ _ = _`)) >>
  goal_assum (drule_at (Pat `decode_invoke _ = _`)) >>
  goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `cenv.ce_func_info _ = _`)) >>
  goal_assum (drule_at (Pat `lookup_callable_function _ _ _ = _`)) >>
  qexistsl [`P`, `body_start`, `staged`] >>
  simp[is_view_mut_def, GSYM markerTheory.Abbrev_def] >>
  FAIL_TAC "guard continuation"
QED
