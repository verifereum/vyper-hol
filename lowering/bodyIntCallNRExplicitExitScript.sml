(* Explicit returns have already run the compiled unlock.  Transport their
   epilogue-aware certificate, without executing another Venom instruction. *)
Theory bodyIntCallNRExplicitExit
Ancestors
  bodyIntCallSeamDefs bodyIntCallJointContract bodyIntCallNRSource
  bodyIntCallPackageStateTransport bodyIntCallPackageRootResource
  stmtSimReturn compileEnv loweringStateRelDefs exprSimDefs
  vyperInterpreter vyperState

Theorem intcall_explicit_callee_exit:
  !fp v ee r cx owner rtv cenv retc t n m rb func mut nr key.
  intcall_stmt_exit fp (INR (ReturnException v)) ee r /\
  fp.jc_root_ce.ce_nonreentrant = (nr,key,T,is_view_mut mut) /\
  (nr /\ ~is_view_mut mut ==> cx.nonreentrant_slot = SOME key) /\
  fp.jc_cx = (cx with stk updated_by CONS owner) /\
  fp.jc_ret_tv = rtv /\
  fp.jc_root_ce.ce_module_vars = cenv.ce_module_vars /\
  fp.jc_root_ce.ce_module = cenv.ce_module /\
  fp.jc_root_ce.ce_is_ctor = cenv.ce_is_ctor /\
  fp.jc_root_ce.ce_returns_count = retc /\ fp.jc_morig = t /\
  (!a k. fp.jc_prot a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m ==> regions_disjoint a k off asz) /\
  OPTION_MAP FST fp.jc_rb = rb ==>
  intcall_callee_exit func cenv cx mut nr rtv retc rb n m t (INL v) ee r
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `intcall_stmt_exit _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_stmt_exit_def])
  >- (Cases_on `r` >> gvs[expr_exit_def]) >>
  drule_all intret_q_source_epilogue >> strip_tac >>
  rename1 `_ (ee with scopes := []) = (INL (),ue)` >>
  `?ue'. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),ue') /\
          ue = (ue' with scopes := [])` by
    (`unlock_if_nr cx nr (is_view_mut mut) =
        (if nr /\ ~is_view_mut mut then
           release_nonreentrant_lock fp.jc_cx.txn.target key
         else return ())` by
       (Cases_on `nr /\ ~is_view_mut mut` >> gvs[unlock_if_nr_def]) >>
     `unlock_if_nr cx nr (is_view_mut mut) (ee with scopes := []) =
        (INL (),ue)` by gvs[Excl "unlock_if_nr_def"] >>
     qpat_x_assum `unlock_if_nr _ _ _ = _` kall_tac >>
     Cases_on `unlock_if_nr cx nr (is_view_mut mut) ee` >>
     gvs[intcall_unlock_scopes, Excl "unlock_if_nr_def"]) >>
  gvs[result_rel_def] >>
  `state_rel func cenv cx (ue' with scopes := []) u` by
    (irule state_rel_empty_scopes_env >>
     qexistsl [`fp.jc_root_ce`, `fp.jc_func`] >>
     fs[state_rel_call_stack]) >>
  simp[intcall_callee_exit_def, Excl "unlock_if_nr_def"] >>
  qexists_tac `ue'` >>
  conj_tac >-
    (Cases_on `nr /\ ~is_view_mut mut` >> gvs[unlock_if_nr_def]) >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> rename1 `fp.jc_rb = SOME pair` >>
  PairCases_on `pair` >> gvs[]
QED
