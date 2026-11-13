(* Return-side framing at the internal-call boundary. *)
Theory bodyPtrIntCallRestoreSeam
Ancestors
  bodyIntCallSeams bodyPtrDefs bodyPtrIntCallConfinement
  bodyPtrBytestringBuiltinsWindowGhost exprSimDefs exprSimProps
  loweringPosts compileEnv venomState venomExecSemantics
  vyperState vyperInterpreter gasSummaryComposePtr fragGasSeqPtr fragGasPathPtr
  finite_map pred_set list vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeSystem vyperTyping vyperValue vyperTypeEnv vyperContext

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

Theorem intcall_callee_src_typed_cast:
  !cx name body env env_after ret rtv es1 v mid.
    type_stmts env ret body = SOME env_after /\
    env_consistent env (cx with stk updated_by CONS (NONE,name)) es1 /\
    state_well_typed es1 /\ accounts_well_typed es1.accounts /\
    context_well_typed cx /\ functions_well_typed cx /\
    call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
      (int_calls_stmts body) /\
    evaluate_type env.type_defs ret = SOME rtv /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    intcall_callee_src cx name body es1 = (INL v,mid) ==>
    safe_cast rtv v = SOME v
Proof
  rpt gen_tac >> strip_tac >> rename1 `type_stmts env ret ss = SOME env_after` >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (NONE,name)) ss es1` >>
  rename1 `eval_stmts _ _ _ = (res,st)` >>
  `context_well_typed (cx with stk updated_by CONS (NONE,name)) /\
   functions_well_typed (cx with stk updated_by CONS (NONE,name))` by
    (conj_tac >- fs[context_well_typed_def] >>
     qpat_x_assum `functions_well_typed cx` mp_tac >>
     simp[functions_well_typed_def, get_module_code_def,
         get_tenv_def, fn_sigs_consistent_def, fn_sigs_declared_complete_def,
         toplevel_vtypes_complete_def, bare_globals_complete_def,
         bare_global_assignable_complete_def, flag_members_complete_def,
         well_formed_type_def, fn_sigs_live_def, context_function_live_context,
         lookup_var_slot_from_layout_def]) >>
  drule_all (cj 2 eval_scc_type_sound_results_mutual) >> strip_tac >>
  Cases_on `res` >>
  gvs[intcall_callee_src_def, try_def, ignore_bind_def, bind_def,
      return_def, raise_def]
  >~ [`safe_cast NoneTV NoneV`] >-
    simp[vyperValueOperationTheory.safe_cast_def]
  >~ [`eval_stmts _ _ _ = (INL (),_)`] >-
    metis_tac[cj 2 no_fallthrough_eval_no_success] >>
  rename1 `handle_function ex st = (INL v,mid)` >>
  Cases_on `ex` >> gvs[handle_function_def, return_def, raise_def] >>
  drule_all env_extends_return_exception_typed >>
  simp[vyperTypeStmtResultTheory.return_exception_typed_def,
       vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  strip_tac >> gvs[] >> irule safe_cast_well_typed >> simp[]
QED
