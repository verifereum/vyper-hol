(* Return-side framing at the internal-call boundary. *)
Theory bodyPtrIntCallRestoreSeam
Ancestors
  bodyIntCallSeams bodyPtrDefs bodyPtrIntCallConfinement
  bodyPtrBytestringBuiltinsWindowGhost exprSimDefs exprSimProps
  loweringPosts compileEnv venomState venomExecSemantics
  vyperState vyperInterpreter gasSummaryComposePtr fragGasSeqPtr fragGasPathPtr
  finite_map pred_set list vyperTypeEvalSoundness vyperTypeBindArguments
  vyperTypeInvariants vyperTypeSystem exprSimHypsDefs vyperContext

(* Concrete and ghost confinement have different jobs: the exit seam
   preserves the bytes; the protected-set frame prevents new taint there. *)
Theorem intcall_callee_exit_local_windows:
  !func cenv cx rtv rc rb first t v ee ir s P tn tm es.
  intcall_callee_exit func cenv cx rtv (rc:num) rb (first:num) t
    (INL v) ee (IntRet ir s) /\
  intcall_mem_frame P tn tm /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      first <= aid ==> regions_disjoint b sz off asz) /\
    (!i. b <= i /\ i < b + sz ==> i IN P)) ==>
  !name b sz. local_region cenv es.scopes t name b sz ==>
    mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory /\
    (!i. b <= i /\ i < b + sz /\ i IN tm.t_mem ==> i IN tn.t_mem)
Proof
  simp[intcall_callee_exit_def, expr_exit_def] >>
  rpt strip_tac
  >- metis_tac[] >>
  fs[intcall_mem_frame_def, SUBSET_DEF, IN_INTER] >> metis_tac[]
QED

Theorem intcall_callee_exit_restore_ghost:
  !func cenv cx rtv rc rb first t v ee ir s d es G tn sa u H tm P.
  intcall_callee_exit func cenv cx rtv (rc:num) rb (first:num) t
    (INL v) ee (IntRet ir s) /\
  ghost_inv d cenv cx es G tn t /\
  local_ptrs_rel func cenv es.scopes t /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x w. not_fresh_at sa x /\ lookup_var x t = SOME w ==>
    lookup_var x u = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  u.vs_memory = s.vs_memory /\ stor_taint_ok cx tm u /\
  intcall_mem_frame P tn tm /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      first <= aid ==> regions_disjoint b sz off asz) /\
    (!i. b <= i /\ i < b + sz ==> i IN P)) ==>
  ghost_inv d cenv cx es H tm u
Proof
  rpt gen_tac >> strip_tac >> irule ghost_inv_local_window_transport >>
  simp[] >> qexistsl_tac [`G`, `func`, `t`, `sa`, `tn`] >> simp[] >>
  drule intcall_callee_exit_local_windows >>
  disch_then (qspecl_then [`P`, `tn`, `tm`, `es`] assume_tac) >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> goal_assum (drule_at Any)
QED

(* Only scope cleanup remains on the supported nonreentrant-free path. *)
Theorem intcall_rest_without_lock[local]:
  !cx name mut ss prev rtv.
    intcall_rest cx name mut F ss prev rtv =
    bind (finally (intcall_callee_src cx name ss) (pop_function prev))
      (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
        (\crv. return (Value crv)))
Proof
  simp[intcall_rest_def, intcall_callee_src_def,
       vyperInterpreterTheory.unlock_if_nr_def, finally_unless_halt_return]
QED

Theorem intcall_rest_marked_success:
  !D ctx func PG cx name mut ss prev rtv es s0 G0 tn0 marks v mid G tn r crv.
    gas_marked_exec_ptr D (ctx,func) PG (intcall_callee_src cx name ss)
      (es,s0,G0,tn0) marks (INL v) mid G tn r /\
    safe_cast rtv v = SOME crv ==>
    gas_marked_exec_ptr D (ctx,func) PG
      (intcall_rest cx name mut F ss prev rtv)
      (es,s0,G0,tn0) marks (INL (Value crv))
      (mid with scopes := prev) G tn r
Proof
  rewrite_tac[gas_marked_exec_ptr_def, intcall_rest_without_lock] >>
  rpt gen_tac >> strip_tac >> simp[] >> gen_tac >>
  simp[bind_def, finally_def, pop_function_def, set_scopes_def,
       ignore_bind_def, return_def, lift_option_type_def, lift_option_def]
QED

Theorem intcall_rest_marked_exception:
  !D ctx func PG cx name mut ss prev rtv es s0 G0 tn0 marks ex mid G tn r.
    gas_marked_exec_ptr D (ctx,func) PG (intcall_callee_src cx name ss)
      (es,s0,G0,tn0) marks (INR ex) mid G tn r ==>
    gas_marked_exec_ptr D (ctx,func) PG
      (intcall_rest cx name mut F ss prev rtv)
      (es,s0,G0,tn0) marks (INR ex)
      (mid with scopes := prev) G tn r
Proof
  rewrite_tac[gas_marked_exec_ptr_def, intcall_rest_without_lock] >>
  rpt gen_tac >> strip_tac >> simp[] >> gen_tac >>
  simp[bind_def, finally_def, pop_function_def, set_scopes_def,
       ignore_bind_def, return_def, raise_def]
QED

(* The caller's typed call selects a live signature.  Successful binding,
   rather than a raw-argument typing assumption, types the pushed scope. *)
Theorem intcall_entry_typed_callee:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  well_typed_expr tenv (Call ty (IntCall (NONE,name)) es drv) /\
  get_module_code cx NONE = SOME ts /\
  lookup_callable_function cx.in_deploy name ts =
    SOME (mut,nr,args,[],ret,ss) ==>
  ?env_body env_after.
    type_stmts env_body ret ss = SOME env_after /\
    env_consistent env_body (cx with stk updated_by CONS (NONE,name)) es1 /\
    state_well_typed es1 /\ accounts_well_typed es1.accounts /\
    context_well_typed cx /\ functions_well_typed cx /\
    evaluate_type env_body.type_defs ret = SOME rtv /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\
    call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
      (int_calls_stmts ss)
Proof
  strip_tac >>
  qpat_x_assum `intcall_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [intcall_entry_def]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`well_typed_expr _ _`, `get_module_code _ _ = _`,
     `lookup_callable_function _ _ _ = _`, `bind_arguments _ _ _ = _`,
     `evaluate_type _ _ = _`, `call_evaluation_safe _ _`,
     `es1.scopes = _`, `expr_sim_inv _ _ _ _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `env_consistent tenv cx (es1 with scopes := prev) /\
   state_well_typed (es1 with scopes := prev) /\
   accounts_well_typed es1.accounts /\ context_well_typed cx /\
   functions_well_typed cx` by
    (qpat_assum `expr_sim_inv _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[expr_sim_inv_def]) >>
  `IS_SOME (FLOOKUP tenv.fn_sigs (NONE,name))` by
    fs[Once well_typed_expr_def, AllCaseEqs()] >>
  drule_all callable_body_typing_from_env_consistent >> strip_tac >>
  `accounts_well_typed (es1 with scopes := prev).accounts` by simp[] >>
  drule_all intcall_default_env_side_conditions >> strip_tac >>
  `scope_well_typed penv` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `env_scopes_consistent env_body
     (cx with stk updated_by CONS (NONE,name)) es1` by
    (`env_scopes_consistent env_body
       (cx with stk updated_by CONS (NONE,name)) (es1 with scopes := [penv])`
       suffices_by (qpat_assum `es1.scopes = _`
         (fn th => simp[NoAsms, GSYM th])) >>
     irule bind_arguments_env_scopes_consistent >>
     qexistsl [`args`, `get_tenv cx`, `vs`] >> simp[get_tenv_def] >>
     metis_tac[]) >>
  qpat_x_assum `!fn. env_context_consistent _ _ /\ _`
    (qspec_then `name` strip_assume_tac) >>
  qexistsl [`env_body`, `env_after`] >>
  simp[env_consistent_def] >>
  gvs[env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED
