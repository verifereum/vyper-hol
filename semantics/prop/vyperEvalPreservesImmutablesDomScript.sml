Theory vyperEvalPreservesImmutablesDom
Ancestors
  pair vyperMisc vyperAST vyperValue vyperContext vyperState vyperStorageBackend vyperCreate vyperCreateFrame vyperInterpreter
  vyperLookup vyperScopePreservation vyperStatePreservation
  vyperPlaceFrames vyperEvalExprPreservesScopesDom
  vyperImmutablesPreservation vyperCallFrame vyperCallOutcomeFrame vyperPlaceFrames

(* ========================================================================
   Preservation of immutables domain through eval_expr / eval_stmts.

   TOP-LEVEL:
     eval_expr_preserves_immutables_addr_dom
     eval_expr_preserves_immutables_dom
     eval_base_place_preserves_immutables_addr_dom
     eval_base_place_preserves_immutables_dom
     eval_exprs_preserves_immutables_addr_dom
     eval_stmts_preserves_immutables_addr_dom
     eval_stmts_preserves_immutables_dom
   ======================================================================== *)

(* ===== Predicate bundling both domain properties ===== *)

Definition preserves_immutables_dom_def:
  preserves_immutables_dom cx (st:evaluation_state) (st':evaluation_state) ⇔
    (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔
           IS_SOME (ALOOKUP st'.immutables tgt)) ∧
    (∀src n imms imms'.
       ALOOKUP st.immutables cx.txn.target = SOME imms ∧
       ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
       (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
        IS_SOME (FLOOKUP (get_source_immutables src imms') n)))
End

Theorem preserves_immutables_dom_refl[local]:
  ∀cx st. preserves_immutables_dom cx st st
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

Theorem preserves_immutables_dom_trans[local]:
  ∀cx st1 st2 st3.
    preserves_immutables_dom cx st1 st2 ∧
    preserves_immutables_dom cx st2 st3 ⇒
    preserves_immutables_dom cx st1 st3
Proof
  rw[preserves_immutables_dom_def] >>
  gvs[optionTheory.IS_SOME_EXISTS]
QED

Theorem preserves_immutables_dom_eq[local]:
  ∀cx st st'.
    st'.immutables = st.immutables ⇒ preserves_immutables_dom cx st st'
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

Theorem preserves_immutables_dom_scopes[local]:
  (!cx s t sc. preserves_immutables_dom cx (s with scopes := sc) t <=>
                 preserves_immutables_dom cx s t) /\
  (!cx s t sc. preserves_immutables_dom cx s (t with scopes := sc) <=>
                 preserves_immutables_dom cx s t) /\
  (!cx s t f. preserves_immutables_dom cx (s with scopes updated_by f) t <=>
                 preserves_immutables_dom cx s t) /\
  (!cx s t f. preserves_immutables_dom cx s (t with scopes updated_by f) <=>
                 preserves_immutables_dom cx s t)
Proof
  simp[preserves_immutables_dom_def]
QED

Theorem bool_dispatch_imm_dom[local]:
  !cx ss1 ss2 v s r t.
    (!s r t. eval_stmts cx ss1 s = (r,t) ==> preserves_immutables_dom cx s t) /\
    (!s r t. eval_stmts cx ss2 s = (r,t) ==> preserves_immutables_dom cx s t) /\
    (if v = BoolV T then eval_stmts cx ss1
     else if v = BoolV F then eval_stmts cx ss2
     else raise (Error (TypeError "not BoolV"))) s = (r,t) ==>
    preserves_immutables_dom cx s t
Proof
  rpt gen_tac >> Cases_on `v = BoolV T` >> simp[] >>
  Cases_on `v = BoolV F` >> simp[raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl]
QED

(* ===== Trivial monad helpers ===== *)

Theorem read_value_result_immutables[local]:
  ∀tv st res st'. read_result cx tv st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  metis_tac[read_result_state]
QED

Theorem transfer_value_immutables[local]:
  ∀f t a st res st'.
    transfer_value f t a st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  rpt strip_tac >>
  drule vyperStatePreservationTheory.transfer_value_immutables >>
  simp[]
QED

Theorem lookup_flag_mem_immutables[local]:
  ∀cx nsid mid st res st'.
    lookup_flag_mem cx nsid mid st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  rpt CASE_TAC >> simp[return_def, raise_def]
QED

Theorem lift_option_same_state[local]:
  lift_option v msg s = (r,s') ==> s' = s
Proof
  Cases_on `v` >> simp[lift_option_def, return_def, raise_def]
QED

Theorem lift_option_type_same_state[local]:
  lift_option_type v msg s = (r,s') ==> s' = s
Proof
  Cases_on `v` >> simp[lift_option_type_def, return_def, raise_def]
QED

Theorem write_place_imm_dom[local]:
  !cx p v st res st'.
    write_place cx p v st = (res,st') ==> preserves_immutables_dom cx st st'
Proof
  rw[preserves_immutables_dom_def] >>
  metis_tac[write_place_immutables_addr_dom, write_place_immutables_dom]
QED

Theorem append_place_imm_dom[local]:
  !cx p v st res st'.
    append_place cx p v st = (res,st') ==> preserves_immutables_dom cx st st'
Proof
  rpt gen_tac >> Cases_on `p`
  >- (strip_tac >> irule preserves_immutables_dom_eq >>
      metis_tac[append_storage_place_scopes_immutables]) >>
  simp[append_place_def, bind_def, lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, lift_sum_def, return_def, raise_def]) >>
  rpt strip_tac >>
  imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
  gvs[] >> metis_tac[write_place_imm_dom, preserves_immutables_dom_refl]
QED

Theorem pop_place_imm_dom[local]:
  !cx p st res st'. pop_place cx p st = (res,st') ==>
    preserves_immutables_dom cx st st'
Proof
  rpt gen_tac >> Cases_on `p`
  >- (strip_tac >> irule preserves_immutables_dom_eq >>
      metis_tac[pop_storage_place_scopes_immutables])
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def, preserves_immutables_dom_refl] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
      imp_res_tac lift_sum_state >> imp_res_tac lift_option_type_state >>
      gvs[preserves_immutables_dom_refl] >>
      pairarg_tac >> gvs[bind_def, ignore_bind_def, set_scopes_def, return_def] >>
      irule preserves_immutables_dom_eq >> simp[]) >>
  simp[pop_place_def, bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       get_immutables_def, get_address_immutables_def, set_immutable_def,
       set_address_immutables_def, return_def, raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), return_def, raise_def, preserves_immutables_dom_def,
      get_source_immutables_def, set_source_immutables_def] >>
  rw[] >> gvs[alistTheory.ALOOKUP_ADELKEY] >>
  CASE_TAC >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[alistTheory.ALOOKUP_ADELKEY]
QED

Theorem handle_function_immutables[local]:
  ∀exc st res st'.
    handle_function exc st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  Cases_on `exc` >> simp[handle_function_def, return_def, raise_def]
QED

Theorem acquire_nonreentrant_lock_immutables[local]:
  ∀addr slot is_view st res st'.
    acquire_nonreentrant_lock addr slot is_view st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem release_nonreentrant_lock_immutables[local]:
  ∀addr slot st res st'.
    release_nonreentrant_lock addr slot st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem lock_acquire_cond_immutables[local]:
  ∀nr slot_opt addr is_view s res s'.
    (if nr then
       case slot_opt of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock addr slot is_view
     else return ()) s = (res, s') ⇒
    s'.immutables = s.immutables
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[raise_def]
  \\ imp_res_tac acquire_nonreentrant_lock_immutables
QED

Theorem finally_lock_release_immutables[local]:
  ∀nr mut slot_opt addr s res s'.
    (if nr ∧ mut ≠ View ∧ mut ≠ Pure then
       case slot_opt of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock addr slot
     else return ()) s = (res, s') ⇒
    s'.immutables = s.immutables
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr ∧ mut ≠ View ∧ mut ≠ Pure` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[return_def]
  \\ imp_res_tac release_nonreentrant_lock_immutables
QED

Theorem preserves_immutables_dom_txn_eq[local]:
  ∀cx cx' st st'.
    cx'.txn = cx.txn ⇒
    (preserves_immutables_dom cx' st st' ⇔ preserves_immutables_dom cx st st')
Proof
  simp[preserves_immutables_dom_def]
QED

Theorem intcall_default_frame_imm_dom[local]:
  (∀st res st'.
     eval_exprs cxd needed_dflts st = (res,st') ⇒
     preserves_immutables_dom cxd st st') ⇒
  finally
    (do
       set_scopes [FEMPTY];
       eval_exprs cxd needed_dflts
     od)
    (set_scopes prev) sget = (res,st1) ⇒
  preserves_immutables_dom cxd sget st1
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, bind_def, ignore_bind_def, set_scopes_def, return_def] >>
  Cases_on `eval_exprs cxd needed_dflts (sget with scopes := [FEMPTY])` >>
  Cases_on `q` >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `∀st res st'. eval_exprs cxd needed_dflts st = (res,st') ⇒ _`
    (drule_then assume_tac) >>
  gvs[preserves_immutables_dom_def]
QED

Theorem case_IntCall_imm_dom_inner[local]:
  ∀cx src_id_opt fname body env st0 vs sevl dflt_vs sdfl
   fres sfnl es needed_dflts prev.
    (∀st res st'.
       eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ∧
    (∀st res st'.
       eval_exprs (cx with stk updated_by CONS (src_id_opt,fname))
         needed_dflts st = (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    (∀st res st'.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fname)) body st =
       (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    eval_exprs cx es st0 = (INL vs, sevl) ∧
    eval_exprs (cx with stk updated_by CONS (src_id_opt,fname))
      needed_dflts sevl = (INL dflt_vs, sdfl) ∧
    finally
      (try (bind (eval_stmts (cx with stk updated_by CONS (src_id_opt,fname))
         body) (λx. return NoneV)) handle_function)
      (pop_function prev)
      (sdfl with scopes := [env]) = (fres, sfnl) ⇒
    preserves_immutables_dom cx st0 sfnl
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >> conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl` >> conj_tac
  >- (irule (iffLR preserves_immutables_dom_txn_eq) >>
      qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >>
      simp[] >> gvs[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl with scopes := [env]` >>
  gvs[preserves_immutables_dom_eq] >>
  irule (iffLR preserves_immutables_dom_txn_eq) >>
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >> simp[] >>
  qpat_x_assum `try _ _ _ = _` mp_tac >>
  simp[try_def, bind_def, AllCaseEqs(), return_def, raise_def,
       handle_function_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, preserves_immutables_dom_eq] >>
  first_x_assum drule >> gvs[preserves_immutables_dom_eq] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[handle_function_def, return_def, raise_def, preserves_immutables_dom_eq] >>
  first_x_assum drule >> gvs[preserves_immutables_dom_eq] >>
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >>
  gvs[handle_function_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac handle_function_immutables
QED

Definition post_default_intcall_tail_def:
  post_default_intcall_tail cx src_id_opt fn mut nr args ret ss vs dflt_vs prev sdfl =
    (do
       all_tenv <<- get_tenv cx;
       env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
                "IntCall bind_arguments";
       rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
       is_view <<- (mut = View ∨ mut = Pure);
       (if nr then
          case cx.nonreentrant_slot of
          | NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
        else return ());
       cxf <- push_function (src_id_opt,fn) env cx;
       rv <- finally
         (try (do eval_stmts cxf ss; return NoneV od) handle_function)
         (do
            pop_function prev;
            if nr ∧ ¬is_view then
              case cx.nonreentrant_slot of
              | NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) sdfl
End

Theorem post_default_intcall_tail_unfold[local]:
  post_default_intcall_tail cx src_id_opt fn mut nr args ret ss vs dflt_vs prev sdfl =
    (do
       all_tenv <<- get_tenv cx;
       env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
                "IntCall bind_arguments";
       rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
       is_view <<- (mut = View ∨ mut = Pure);
       (if nr then
          case cx.nonreentrant_slot of
          | NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
        else return ());
       cxf <- push_function (src_id_opt,fn) env cx;
       rv <- finally
         (try (do eval_stmts cxf ss; return NoneV od) handle_function)
         (do
            pop_function prev;
            if nr ∧ ¬is_view then
              case cx.nonreentrant_slot of
              | NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) sdfl
Proof
  rw[post_default_intcall_tail_def]
QED

Definition intcall_tail_body_provider_def:
  intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl =
    ∀env s_bind rtv s_eval lk s_lock cx' s_push.
      lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments" sdfl = (INL env,s_bind) ∧
      lift_option_type (evaluate_type (get_tenv cx) ret)
        "IntCall eval ret" s_bind = (INL rtv,s_eval) ∧
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View ∨ mut = Pure)
       else return ()) s_eval = (INL lk,s_lock) ∧
      push_function (src_id_opt,fn) env cx s_lock = (INL cx',s_push) ⇒
      ∀st res st'. eval_stmts cx' ss st = (res,st') ⇒
        preserves_immutables_dom cx' st st'
End

Theorem intcall_tail_body_provider_unfold[local]:
  intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl =
    ∀env s_bind rtv s_eval lk s_lock cx' s_push.
      lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments" sdfl = (INL env,s_bind) ∧
      lift_option_type (evaluate_type (get_tenv cx) ret)
        "IntCall eval ret" s_bind = (INL rtv,s_eval) ∧
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View ∨ mut = Pure)
       else return ()) s_eval = (INL lk,s_lock) ∧
      push_function (src_id_opt,fn) env cx s_lock = (INL cx',s_push) ⇒
      ∀st res st'. eval_stmts cx' ss st = (res,st') ⇒
        preserves_immutables_dom cx' st st'
Proof
  rw[intcall_tail_body_provider_def]
QED

Theorem intcall_post_default_eq_imm_dom[local]:
  ∀cx cxd st0 sevl sdfl st'.
    cxd.txn = cx.txn ⇒
    preserves_immutables_dom cx st0 sevl ⇒
    preserves_immutables_dom cxd sevl sdfl ⇒
    st'.immutables = sdfl.immutables ⇒
    preserves_immutables_dom cx st0 st'
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >>
  conj_tac >- simp[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl` >>
  conj_tac
  >- (irule (iffLR preserves_immutables_dom_txn_eq) >>
      qexists_tac `cxd` >> simp[]) >>
  irule preserves_immutables_dom_eq >> simp[]
QED

Theorem case_IntCall_imm_dom_inner_pres[local]:
  ∀cx src_id_opt fname body st0 sevl sdfl fres sfnl env prev.
    preserves_immutables_dom cx st0 sevl ∧
    preserves_immutables_dom
      (cx with stk updated_by CONS (src_id_opt,fname)) sevl sdfl ∧
    (∀st res st'.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fname)) body st =
       (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    finally
      (try (bind (eval_stmts (cx with stk updated_by CONS (src_id_opt,fname))
         body) (λx. return NoneV)) handle_function)
      (pop_function prev)
      (sdfl with scopes := [env]) = (fres,sfnl) ⇒
    preserves_immutables_dom cx st0 sfnl
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >> conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl` >> conj_tac
  >- (irule (iffLR preserves_immutables_dom_txn_eq) >>
      qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >>
      simp[] >> gvs[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl with scopes := [env]` >>
  gvs[preserves_immutables_dom_eq] >>
  irule (iffLR preserves_immutables_dom_txn_eq) >>
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >> simp[] >>
  qpat_x_assum `try _ _ _ = _` mp_tac >>
  simp[try_def, bind_def, AllCaseEqs(), return_def, raise_def,
       handle_function_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, preserves_immutables_dom_eq] >>
  qpat_assum `∀st res st'. eval_stmts _ _ st = (res,st') ⇒ _`
    drule >> gvs[preserves_immutables_dom_eq] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[handle_function_def, return_def, raise_def, preserves_immutables_dom_eq] >>
  qpat_assum `∀st res st'. eval_stmts _ _ st = (res,st') ⇒ _`
    drule >> gvs[preserves_immutables_dom_eq] >>
  rpt strip_tac >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- simp[] >>
       irule preserves_immutables_dom_eq >> simp[] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       conj_tac >- simp[] >>
       irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- (irule preserves_immutables_dom_eq >>
                     imp_res_tac handle_function_immutables >> simp[]) >>
       irule preserves_immutables_dom_eq >> simp[] >> NO_TAC) >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >>
  gvs[handle_function_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac handle_function_immutables
QED


Theorem intcall_body_finally_release_imm_dom[local]:
  ∀cx src_id_opt fn mut nr ss prev env st res st'.
    (∀st0 res0 st1.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss st0 = (res0,st1) ⇒
       preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) st0 st1) ∧
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss;
               return NoneV od) handle_function)
      (do pop_function prev;
          if nr ∧ mut ≠ View ∧ mut ≠ Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return () od)
      (st with scopes := [env]) = (res,st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `st with scopes := [env]` >>
  conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
  irule (iffLR preserves_immutables_dom_txn_eq) >>
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fn)` >> simp[] >>
  qpat_x_assum `try _ _ _ = _` mp_tac >>
  simp[try_def, bind_def, AllCaseEqs(), return_def, raise_def,
       handle_function_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, preserves_immutables_dom_eq] >>
  qpat_assum `∀st0 res0 st1. eval_stmts _ _ st0 = (res0,st1) ⇒ _`
    drule >> gvs[preserves_immutables_dom_eq] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[handle_function_def, return_def, raise_def, preserves_immutables_dom_eq] >>
  qpat_assum `∀st0 res0 st1. eval_stmts _ _ st0 = (res0,st1) ⇒ _`
    drule >> gvs[preserves_immutables_dom_eq] >>
  rpt strip_tac >>
  qpat_assum `∀st0 res0 st1. eval_stmts _ _ st0 = (res0,st1) ⇒ _`
    drule >> strip_tac >>
  imp_res_tac handle_function_immutables >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  imp_res_tac finally_lock_release_immutables >>
  irule preserves_immutables_dom_trans >>
  first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >> gvs[]
QED

Theorem intcall_body_finally_release_imm_dom_use[local]:
  ∀cx src_id_opt fn mut nr ss prev env st q st'.
    (∀st0 res0 st1.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss st0 = (res0,st1) ⇒
       preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) st0 st1) ⇒
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss;
               return NoneV od) handle_function)
      (do pop_function prev;
          if nr ∧ mut ≠ View ∧ mut ≠ Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return () od)
      (st with scopes := [env]) = (q,st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  irule intcall_body_finally_release_imm_dom >>
  qexistsl [`env`, `fn`, `mut`, `nr`, `prev`, `q`, `src_id_opt`, `ss`] >>
  simp[]
QED

(* ----- Case 5: Return (SOME e) ----- *)
Theorem case_Return_SOME_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Return (SOME e)) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac read_value_result_immutables >> imp_res_tac read_result_state >> gvs[]
QED

(* ----- Case 6: Raise reason ----- *)
(* ----- Case 8: Log id es ----- *)
Theorem case_Log_imm_dom[local]:
  ∀cx id es.
    (∀st res st'. eval_exprs cx es st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Log id es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def, push_log_def] >>
  rpt strip_tac >> imp_res_tac lift_option_state >>
  gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq]
QED

(* ----- Case 9: AnnAssign id typ e ----- *)
Theorem case_AnnAssign_imm_dom[local]:
  ∀cx id typ e.
    (∀tenv s'' tyv t.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv, t) ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (AnnAssign id typ e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       new_variable_def, LET_THM, get_scopes_def, check_def, type_check_def, assert_def,
       set_scopes_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac lift_option_type_same_state >> gvs[preserves_immutables_dom_refl] >>
  (* Discharge IH guard using lift_option_type assumption *)
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac read_value_result_immutables >> imp_res_tac read_result_state >> gvs[] >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `s'³'` >>
  conj_tac >- gvs[] >>
  irule preserves_immutables_dom_eq >>
  qpat_x_assum `_ s'³' = (res, st')` mp_tac >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, assert_def, return_def, raise_def, set_scopes_def,
       AllCaseEqs()] >>
  Cases_on `s'³'.scopes` >>
  simp[raise_def, set_scopes_def, return_def] >>
  rpt strip_tac >> gvs[]
QED

(* ----- Case 10: Append bt e ----- *)
Theorem case_Append_imm_dom[local]:
  !cx bt e.
    (!st res st'. eval_target_place cx bt st = (res,st') ==>
       preserves_immutables_dom cx st st') /\
    (!s p t. eval_target_place cx bt s = (INL p,t) ==>
       !st res st'. eval_expr cx e st = (res,st') ==>
         preserves_immutables_dom cx st st') ==>
    !st res st'. eval_stmt cx (Append bt e) st = (res,st') ==>
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  imp_res_tac append_place_imm_dom >>
  metis_tac[preserves_immutables_dom_trans]
QED


(* ----- Case 13: If e ss1 ss2 ----- *)
Theorem case_If_imm_dom[local]:
  ∀cx e ss1 ss2.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' x t'.
       eval_expr cx e s'' = (INL tv,t) ∧ push_scope s'³' = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss1 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' x t'.
       eval_expr cx e s'' = (INL tv,t) ∧ push_scope s'³' = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (If e ss1 ss2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, push_scope_def,
       switch_BoolV_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Simplify push_scope conditions and derive unconditional IHs *)
  RULE_ASSUM_TAC (REWRITE_RULE [push_scope_def, return_def]) >> gvs[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  last_x_assum (drule_then strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `s''` >> conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `s'' with scopes updated_by CONS FEMPTY` >>
  conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
       bind_def, ignore_bind_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[preserves_immutables_dom_refl] >>
  simp[preserves_immutables_dom_scopes, preserves_immutables_dom_refl] >>
  drule_all bool_dispatch_imm_dom >>
  simp[preserves_immutables_dom_scopes]
QED

(* ----- Case 14: For id typ it n body ----- *)
Theorem case_For_imm_dom[local]:
  ∀cx id typ it n body.
    (∀tenv s'' tyv t.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ)
         "For evaluate_type" s'' = (INL tyv, t) ⇒
       ∀st res st'. eval_iterator cx it st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀tenv s'' tyv t s'³' vs t' s'⁴' x t''.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ)
         "For evaluate_type" s'' = (INL tyv, t) ∧
       eval_iterator cx it s'³' = (INL vs, t') ∧
       check (compatible_bound (Dynamic n) (LENGTH vs))
             "For too long" s'⁴' = (INL x, t'') ⇒
       ∀st res st'. eval_for cx tyv id body vs st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac lift_option_type_same_state >> gvs[preserves_immutables_dom_refl] >>
  (* Discharge iterator IH guard: tenv = get_tenv cx ∧ lift_option_type *)
  `∀st res st'. eval_iterator cx it st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by
    (first_x_assum match_mp_tac >> metis_tac[]) >>
  imp_res_tac check_state >> gvs[preserves_immutables_dom_refl] >>
  (* iterator error: IH directly *)
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  (* Success: chain through iterator then eval_for *)
  irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
  conj_tac >- (first_x_assum drule >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* ----- Case 15: Expr e ----- *)
Theorem case_Expr_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Expr e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac read_value_result_immutables >> imp_res_tac read_result_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  imp_res_tac check_state >> imp_res_tac type_check_state >>
  gvs[preserves_immutables_dom_eq]
QED

(* ----- Case 17: eval_stmts (s::ss) ----- *)
Theorem case_eval_stmts_cons_imm_dom[local]:
  ∀cx s ss.
    (∀st res st'. eval_stmt cx s st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' x t. eval_stmt cx s s'' = (INL x,t) ⇒
       ∀st res st'. eval_stmts cx ss st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmts cx (s::ss) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- (last_x_assum irule >> metis_tac[]) >>
  first_x_assum irule >> first_assum (irule_at Any) >> metis_tac[]
QED

(* ----- Case 18: eval_iterator (Array e) ----- *)
Theorem case_Array_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_iterator cx (Array e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def] >>
  simp[option_CASE_rator] >>
  simp[AllCaseEqs()] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, return_def, raise_def] >>
  imp_res_tac read_value_result_immutables >>
  imp_res_tac read_result_state >> gvs[]
QED

(* ----- Case 19: eval_iterator (Range e1 e2) ----- *)
Theorem case_Range_imm_dom[local]:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv1 t s'³' s t'.
       eval_expr cx e1 s'' = (INL tv1,t) ∧ read_result cx tv1 s'³' = (INL s,t') ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_iterator cx (Range e1 e2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       LET_THM] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  gvs[preserves_immutables_dom_refl] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >> simp[]
QED


(* ----- Case 29: eval_for (v::vs) ----- *)
Theorem case_eval_for_cons_imm_dom[local]:
  ∀cx nm body v vs.
    (∀s'' x t. push_scope_with_var nm tyv v s'' = (INL x,t) ⇒
       ∀st res st'. eval_stmts cx body st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' x t s'³' broke t'.
       push_scope_with_var nm tyv v s'' = (INL x,t) ∧
       finally
         (try do eval_stmts cx body; return F od handle_loop_exception)
         pop_scope s'³' = (INL broke,t') ∧ ¬broke ⇒
       ∀st res st'. eval_for cx tyv nm body vs st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_for cx tyv nm body (v::vs) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  (* Simplify IHs: push_scope_with_var always succeeds *)
  RULE_ASSUM_TAC (REWRITE_RULE [push_scope_with_var_def, return_def]) >>
  gvs[] >>
  (* Unfold eval_for (v::vs) *)
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, push_scope_with_var_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >|
  [ (* Success case: finally returned INL broke *)
    irule preserves_immutables_dom_trans >>
    qexists_tac `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v; popped := [] |>))` >>
    conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
    qpat_x_assum `finally _ _ _ = _` mp_tac >>
    simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
         bind_def, ignore_bind_def] >>
    rpt strip_tac >> gvs[] >>
    rename1 `try _ _ _ = (_, s_try)` >>
    irule preserves_immutables_dom_trans >>
    qexists_tac `s_try with scopes := tl` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s_try` >> conj_tac
        >- (qpat_x_assum `try _ _ _ = _` mp_tac >>
            PURE_REWRITE_TAC [ignore_bind_def] >>
            simp[try_def, bind_def, return_def, AllCaseEqs(),
                 handle_loop_exception_def, raise_def] >>
            rpt strip_tac >> gvs[return_def, raise_def] >>
            TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
            first_x_assum drule >> simp[] >> strip_tac >>
            BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def])
        >- (irule preserves_immutables_dom_eq >> simp[]))
    >- (Cases_on `broke` >> gvs[return_def, preserves_immutables_dom_refl] >>
        first_x_assum (qspecl_then [
            `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v; popped := [] |>))`,
            `s_try with scopes := tl`] mp_tac) >>
        simp[finally_def, ignore_bind_def, bind_def,
             pop_scope_def, return_def] >>
        disch_then drule >> simp[]),
    (* Error case: finally returned INR e *)
    irule preserves_immutables_dom_trans >>
    qexists_tac `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v; popped := [] |>))` >>
    conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
    qpat_x_assum `finally _ _ _ = _` mp_tac >>
    simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
         bind_def, ignore_bind_def] >>
    rpt strip_tac >> gvs[] >>
    TRY (rename1 `try _ _ _ = (_, s_try)` >>
         irule preserves_immutables_dom_trans >> qexists_tac `s_try` >>
         conj_tac
         >- (qpat_x_assum `try _ _ _ = _` mp_tac >>
             PURE_REWRITE_TAC [ignore_bind_def] >>
             simp[try_def, bind_def, return_def, AllCaseEqs(),
                  handle_loop_exception_def, raise_def] >>
             rpt strip_tac >> gvs[return_def, raise_def] >>
             TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
             first_x_assum drule >> simp[] >> strip_tac >>
             BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def])
         >- (irule preserves_immutables_dom_eq >> simp[]) >> NO_TAC) >>
    qpat_x_assum `try _ _ _ = _` mp_tac >>
    PURE_REWRITE_TAC [ignore_bind_def] >>
    simp[try_def, bind_def, return_def, AllCaseEqs(),
         handle_loop_exception_def, raise_def] >>
    rpt strip_tac >> gvs[return_def, raise_def] >>
    TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
    first_x_assum drule >> simp[] >> strip_tac >>
    BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def]
  ]
QED

(* ----- Case 33: eval_expr (IfExp e e' e'') ----- *)
Theorem case_IfExp_imm_dom[local]:
  ∀cx e e' e''.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'. eval_expr cx e'' st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'. eval_expr cx e' st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (IfExp _ e e' e'') st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       switch_BoolV_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >>
  gvs[preserves_immutables_dom_refl] >>
  (* Derive unconditional IHs for e' and e'' *)
  `∀st res st'. eval_expr cx e' st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by metis_tac[] >>
  `∀st res st'. eval_expr cx e'' st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by metis_tac[] >>
  rename1 `read_result cx tv _ = (INL loaded,_)` >>
  Cases_on `loaded = BoolV T` >>
  gvs[raise_def, preserves_immutables_dom_refl] >>
  Cases_on `loaded = BoolV F` >>
  gvs[raise_def, preserves_immutables_dom_refl]
QED

(* ----- Subscript helper lemmas ----- *)

(* Subgoal 1: success path - res' branches into value or storage read.
   Need to show preserves_immutables_dom cx s_e2 st'
   where s_e2 is the state after eval_expr e2. *)
Theorem subscript_helper_success_path[local]:
  ∀cx s_cab s_es st' tv1 v2 res' res.
    s_cab.immutables = s_es.immutables ⇒
    lift_sum (evaluate_subscript (get_tenv cx) arr_tv tv1 v2) s_cab = (INL res', s_es) ⇒
    (case res' of
       INL v => return v
     | INR (is_transient,slot,tv) =>
       do
         v <- read_storage_slot cx is_transient slot tv;
         return (Value v)
       od) s_es = (res, st') ⇒
    preserves_immutables_dom cx s_cab st'
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_eq >>
  gvs[lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `res'` >> gvs[return_def] >>
  rename1 `INR trip` >> PairCases_on `trip` >>
  gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_storage_slot_immutables
QED

(* Subgoal 2: evaluate_subscript returns INR (error) -
   need preserves_immutables_dom cx st s_e2
   (chaining st → s_e1 → s_e2 via e1 and e2 IHs) *)
Theorem subscript_helper_eval_sub_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 tv2 v2 s_gv s_es e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    s_gv.immutables = s_e2.immutables ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INL tv2, s_e2) ⇒
    read_result cx tv2 s_e2 = (INL v2, s_gv) ⇒
    (case evaluate_subscript (get_tenv cx) arr_tv tv1 v2 of
       INL v => return v
     | INR e => raise (Error e)) s_gv = (INR e', s_es) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Subgoal 3: evaluate_subscript returns INR (error) -
   need preserves_immutables_dom cx s_e2 s_es *)
Theorem subscript_helper_eval_sub_err_bwd[local]:
  ∀cx s_e2 s_gv s_es tv1 tv2 v2 e'.
    s_gv.immutables = s_e2.immutables ⇒
    read_result cx tv2 s_e2 = (INL v2, s_gv) ⇒
    (case evaluate_subscript (get_tenv cx) arr_tv tv1 v2 of
       INL v => return v
     | INR e => raise (Error e)) s_gv = (INR e', s_es) ⇒
    preserves_immutables_dom cx s_e2 s_es
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_eq >>
  Cases_on `evaluate_subscript (get_tenv cx) arr_tv tv1 v2` >> gvs[raise_def, return_def]
QED

(* Subgoal 6: read_result cx returns INR (error) -
   need preserves_immutables_dom cx st s_e2 *)
Theorem subscript_helper_get_value_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 tv2 s_gv e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    s_gv.immutables = s_e2.immutables ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INL tv2, s_e2) ⇒
    read_result cx tv2 s_e2 = (INR e', s_gv) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Subgoal 7: read_result cx returns INR (error) -
   need preserves_immutables_dom cx s_e2 s_gv *)
Theorem subscript_helper_get_value_err_bwd[local]:
  ∀cx s_e2 s_gv tv2 e'.
    s_gv.immutables = s_e2.immutables ⇒
    read_result cx tv2 s_e2 = (INR e', s_gv) ⇒
    preserves_immutables_dom cx s_e2 s_gv
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >> gvs[]
QED

(* Subgoal 8: eval_expr e2 returns INR (error) -
   need preserves_immutables_dom cx st s_e2 *)
Theorem subscript_helper_e2_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INR e', s_e2) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* ----- Case 36: eval_expr (Subscript e1 e2) ----- *)
Theorem case_Subscript_imm_dom[local]:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv1 t. eval_expr cx e1 s'' = (INL tv1,t) ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Subscript _ e1 e2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >> gvs[] >>
  `preserves_immutables_dom cx st s''` by metis_tac[] >>
  gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- simp[] >>
  metis_tac[]
QED

(* ----- Case 37: eval_expr (Attribute e id) ----- *)
Theorem case_Attribute_imm_dom[local]:
  ∀cx e id.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Attribute _ e id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac select_result_state >> gvs[]
QED

(* ----- Case 39: eval_expr (Pop bt) ----- *)
Theorem case_Pop_imm_dom[local]:
  ∀cx bt.
    (∀st res st'. eval_target_place cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Pop _ bt) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  drule pop_place_imm_dom >> strip_tac >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  metis_tac[]
QED

(* ----- Case 41: eval_expr (Call (Send has_gas) es drv) ----- *)
Theorem case_Send_imm_dom[local]:
  ∀cx has_gas es drv.
    (∀s'' x t. type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Call _ (Send has_gas) es drv) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `LENGTH es = if has_gas then 3 else 2` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, preserves_immutables_dom_refl] >>
  first_x_assum (qspecl_then [`st`, `()`, `st`] mp_tac) >>
  simp[type_check_def, assert_def, return_def] >> strip_tac >>
  rpt CASE_TAC >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule eval_send_preserves_non_accounts >> strip_tac >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >> gvs[]
QED

(* ----- Case 45: eval_exprs (e::es) ----- *)
Theorem case_eval_exprs_cons_imm_dom[local]:
  ∀cx e es.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' v t'.
       eval_expr cx e s'' = (INL tv,t) ∧ read_result cx tv s'³' = (INL v,t') ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_exprs cx (e::es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac read_result_state >> gvs[] >>
  (* read_result succeeded: chain st -> s'' -> s'⁴' *)
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- gvs[] >> NO_TAC) >>
  qpat_x_assum `∀s''. _` (qspecl_then [`st`, `tv`, `s''`, `s''`, `v''`, `s''`] mp_tac) >>
  simp[] >> disch_then drule >> strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[]
QED


(* ----- Case: eval_expr (Name id) ----- *)
Theorem case_Name_imm_dom[local]:
  ∀cx id.
    ∀st res st'.
      eval_expr cx (Name _ id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* ----- Case: eval_expr (Builtin bt es) ----- *)
Theorem case_Builtin_imm_dom[local]:
  ∀cx ty bt es.
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) ∧ bt ≠ Len ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) ∧ bt = Len ⇒
       ∀st res st'.
         eval_expr cx (HD es) st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Builtin ty bt es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `bt = Len` >> gvs[] >>
  (* bt = Len branch: eval_expr (HD es) then result_array_length *)
  TRY (gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
       imp_res_tac result_array_length_state >> gvs[] >>
       irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       gvs[preserves_immutables_dom_eq] >>
       first_x_assum (qspec_then `st` mp_tac) >>
       simp[check_def, type_check_def, assert_def, return_def] >> NO_TAC) >>
  (* bt ≠ Len branch *)
  `∀st res st'. eval_exprs cx es st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by
    (first_x_assum (qspec_then `st` mp_tac) >>
     simp[check_def, type_check_def, assert_def, return_def]) >>
  gvs[bind_def, AllCaseEqs(), return_def, raise_def, get_accounts_def] >>
  Cases_on `evaluate_builtin cx s'³'.accounts ty bt (MAP expr_type es) vs` >>
  gvs[return_def, raise_def]
QED

(* ----- Case: eval_expr (TypeBuiltin tb typ es) ----- *)
Theorem case_TypeBuiltin_imm_dom[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (TypeBuiltin _ tb typ es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >>
       gvs[return_def, raise_def]) >>
  first_x_assum (qspec_then `st` mp_tac) >>
  simp[check_def, type_check_def, assert_def, return_def]
QED

Theorem check_same_state[local]:
  check b msg s = (r, s') ⇒ s' = s
Proof
  rw[check_def, type_check_def, assert_def]
QED

Theorem type_check_same_state[local]:
  type_check b msg s = (r, s') ⇒ s' = s
Proof
  rw[type_check_def, assert_def]
QED

Theorem intcall_args_length_sub[local]:
  ∀given expected defaults.
    given ≤ expected ⇒
    (expected − given ≤ defaults ⇔ expected ≤ given + defaults)
Proof
  decide_tac
QED

Theorem intcall_default_frame_imm_dom_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd prev res sdfl.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut stup nr stup2
        args sstup dflts sstup2 ret body s3 x1 t3 s4 vs0 t4 es0 cx0.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut = FST tup0 ∧ stup = SND tup0 ∧ (nr ⇔ FST stup) ∧
      stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
      dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
      body = SND sstup2 ∧
      type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      es0 = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
      cx0 = cx with stk updated_by CONS (src_id_opt,fn) ⇒
      ∀st res st'. eval_exprs cx0 es0 st = (res,st') ⇒
        preserves_immutables_dom cx0 st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    type_check
      (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
       LENGTH (FST (SND (SND tup))) ≤
         LENGTH es + LENGTH (FST (SND (SND (SND tup)))))
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts =
      DROP (LENGTH (FST (SND (SND (SND tup)))) −
            (LENGTH (FST (SND (SND tup))) − LENGTH es))
           (FST (SND (SND (SND tup)))) ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (res,sdfl) ⇒
    preserves_immutables_dom cxd sevl sdfl
Proof
  rpt strip_tac \\
  irule intcall_default_frame_imm_dom \\
  qexists_tac `needed_dflts` \\
  qexists_tac `prev` \\
  qexists_tac `res` \\
  simp[] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
      LENGTH (FST (SND (SND tup))) − LENGTH es ≤
        LENGTH (FST (SND (SND (SND tup)))))
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (`(LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
       LENGTH (FST (SND (SND tup))) − LENGTH es ≤
         LENGTH (FST (SND (SND (SND tup))))) =
      (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
       LENGTH (FST (SND (SND tup))) ≤
         LENGTH es + LENGTH (FST (SND (SND (SND tup)))))` by
       simp[intcall_args_length_sub] \\
     pop_assum SUBST1_TAC \\
     qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` ACCEPT_TAC) \\
  first_assum (qspecl_then
    [`ih_check_s`, `xrec`, `srec`,
     `ih_mod_s`, `ts`, `smod`,
     `ih_fun_s`, `tup`, `sfun`,
     `FST tup`, `SND tup`, `FST (SND tup)`,
     `SND (SND tup)`, `FST (SND (SND tup))`,
     `SND (SND (SND tup))`, `FST (SND (SND (SND tup)))`,
     `SND (SND (SND (SND tup)))`,
     `FST (SND (SND (SND (SND tup))))`,
     `SND (SND (SND (SND (SND tup))))`,
     `ih_len_s`, `xlen`, `slen`,
     `ih_args_s`, `vs`, `sevl`,
     `needed_dflts`, `cxd`] mp_tac) \\
  simp[] \\
  disch_then drule \\
  simp[]
QED

Theorem intcall_tail_body_provider_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     default_s dflt_vs sdfl get_scope_s prev get_scope_t mut stup nr stup2
     args sstup dflts sstup2 ret ss.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env t6 s7 prev0 t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      eval_exprs cxd0 needed_dflts0 s5 = (INL dflt_vs0,t5) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s6 = (INL env,t6) ∧
      get_scopes s7 = (INL prev0,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 =
        (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st res st'. eval_stmts cx0 ss0 st = (res,st') ⇒
        preserves_immutables_dom cx0 st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
    ss = SND sstup2 ∧
    type_check
      (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    eval_exprs cxd needed_dflts default_s = (INL dflt_vs,sdfl) ∧
    get_scopes get_scope_s = (INL prev,get_scope_t) ⇒
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt strip_tac \\
  PURE_REWRITE_TAC[intcall_tail_body_provider_def] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac \\
     simp_tac (srw_ss()) [intcall_args_length_sub]) \\
  qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
                  args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
                  needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env0 t6
                  s7 prev0 t7 s8 rtv0 t8 is_view s9 lk0 t9 s10 cx0 t10.
                  type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
                  _ ⇒ ∀st0 res0 st1.
                    eval_stmts cx0 ss0 st0 = (res0,st1) ⇒
                    preserves_immutables_dom cx0 st0 st1`
    (qspecl_then
      [`ih_check_s`, `xrec`, `srec`,
       `ih_mod_s`, `ts`, `smod`,
       `ih_fun_s`, `tup`, `sfun`,
       `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
       `ret`, `ss`, `ih_len_s`, `xlen`, `slen`,
       `ih_args_s`, `vs`, `sevl`, `needed_dflts`, `cxd`,
       `default_s`, `dflt_vs`, `sdfl`, `get_tenv cx`, `sdfl`, `env`, `s_bind`,
       `get_scope_s`, `prev`, `get_scope_t`, `s_bind`, `rtv`, `s_eval`,
       `mut = View ∨ mut = Pure`, `s_eval`, `lk`, `s_lock`, `s_lock`, `cx'`,
       `s_push`] (fn ih =>
         SUBGOAL_THEN (lhand (concl ih))
           (fn guard => first_assum (fn ev =>
             ACCEPT_TAC (MP (Q.SPECL [`st`, `res`, `st'`] (MP ih guard)) ev))))) \\
  rpt conj_tac \\
  FIRST [first_assum ACCEPT_TAC, REFL_TAC]
QED

Theorem intcall_post_default_setup_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     default_s dflt_vs sdfl get_scope_s prev get_scope_t mut stup nr stup2
     args sstup dflts sstup2 ret ss.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ⇒
      ∀st res st'. eval_exprs cxd0 needed_dflts0 st = (res,st') ⇒
        preserves_immutables_dom cxd0 st st') ∧
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env t6 s7 prev0 t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      eval_exprs cxd0 needed_dflts0 s5 = (INL dflt_vs0,t5) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s6 = (INL env,t6) ∧
      get_scopes s7 = (INL prev0,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 =
        (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st res st'. eval_stmts cx0 ss0 st = (res,st') ⇒
        preserves_immutables_dom cx0 st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
    ss = SND sstup2 ∧
    type_check
      (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (INL dflt_vs,sdfl) ∧
    eval_exprs cxd needed_dflts default_s = (INL dflt_vs,sdfl) ∧
    get_scopes get_scope_s = (INL prev,get_scope_t) ⇒
    preserves_immutables_dom cxd sevl sdfl ∧
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac
  >- (qspecl_then
        [`cx`, `src_id_opt`, `fn`, `es`,
         `ih_check_s`, `ih_mod_s`, `ih_fun_s`, `ih_len_s`, `ih_args_s`,
         `xrec`, `srec`, `ts`, `smod`, `tup`, `sfun`, `xlen`, `slen`,
         `vs`, `sevl`, `needed_dflts`, `cxd`, `prev`, `INL dflt_vs`, `sdfl`]
        (fn th => SUBGOAL_THEN (lhand (concl th)) (ACCEPT_TAC o MP th))
        intcall_default_frame_imm_dom_from_generated_ih \\
      rpt conj_tac \\
      FIRST [first_assum ACCEPT_TAC,
        qpat_x_assum `stup = SND tup` (fn h_stup =>
        qpat_x_assum `stup2 = SND stup` (fn h_stup2 =>
        qpat_x_assum `args = FST stup2` (fn h_args =>
        qpat_x_assum `sstup = SND stup2` (fn h_sstup =>
        qpat_x_assum `dflts = FST sstup` (fn h_dflts =>
          PURE_REWRITE_TAC [GSYM h_stup, GSYM h_stup2, GSYM h_args,
                            GSYM h_sstup, GSYM h_dflts] \\
          first_assum ACCEPT_TAC)))))]) \\
  qspecl_then
    [`cx`, `src_id_opt`, `fn`, `es`,
     `ih_check_s`, `ih_mod_s`, `ih_fun_s`, `ih_len_s`, `ih_args_s`,
     `xrec`, `srec`, `ts`, `smod`, `tup`, `sfun`, `xlen`, `slen`,
     `vs`, `sevl`, `needed_dflts`, `cxd`,
     `default_s`, `dflt_vs`, `sdfl`, `get_scope_s`, `prev`, `get_scope_t`,
     `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
     `ret`, `ss`]
    (fn th => SUBGOAL_THEN (lhand (concl th)) (ACCEPT_TAC o MP th))
    intcall_tail_body_provider_from_generated_ih \\
  rpt conj_tac \\
  first_assum ACCEPT_TAC
QED

Theorem finally_set_scopes_eval_exprs_success[local]:
  ∀cxd es prev sevl vs sdfl.
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd es
       od)
      (set_scopes prev) sevl = (INL vs,sdfl) ⇒
    ∃pre.
      eval_exprs cxd es (sevl with scopes := [FEMPTY]) = (INL vs,pre) ∧
      sdfl = pre with scopes := prev ∧
      get_scopes sdfl = (INL prev,sdfl)
Proof
  rpt strip_tac \\
  qpat_x_assum `finally _ _ _ = _` mp_tac \\
  simp[finally_def, bind_def, ignore_bind_def, set_scopes_def,
       return_def, raise_def, get_scopes_def] \\
  Cases_on `eval_exprs cxd es (sevl with scopes := [FEMPTY])` \\
  Cases_on `q` \\
  simp[return_def, raise_def, get_scopes_def] \\
  rpt strip_tac \\
  gvs[] \\
  qexists_tac `r` \\
  simp[get_scopes_def, return_def]
QED

Theorem type_check_intcall_args_length_sub[local]:
  type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
    msg s = (INL x,t) ==>
  type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
    msg s = (INL x,t)
Proof
  simp[type_check_def, assert_def] \\
  IF_CASES_TAC \\ simp[] \\
  decide_tac
QED

Theorem intcall_live_post_default_setup_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     dflt_vs sdfl prev mut stup nr stup2 args sstup dflts sstup2 ret ss.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ⇒
      ∀st res st'. eval_exprs cxd0 needed_dflts0 st = (res,st') ⇒
        preserves_immutables_dom cxd0 st st') ∧
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env t6 s7 prev0 t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      eval_exprs cxd0 needed_dflts0 s5 = (INL dflt_vs0,t5) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s6 = (INL env,t6) ∧
      get_scopes s7 = (INL prev0,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 =
        (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st res st'. eval_stmts cx0 ss0 st = (res,st') ⇒
        preserves_immutables_dom cx0 st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
    ss = SND sstup2 ∧
    type_check
      (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (INL dflt_vs,sdfl) ⇒
    preserves_immutables_dom cxd sevl sdfl ∧
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt gen_tac \\ strip_tac \\
  drule finally_set_scopes_eval_exprs_success \\
  disch_then (qx_choose_then `pre_sdfl` strip_assume_tac) \\
  conj_tac
  >- (qspecl_then
        [`cx`, `src_id_opt`, `fn`, `es`,
         `ih_check_s`, `ih_mod_s`, `ih_fun_s`, `ih_len_s`, `ih_args_s`,
         `xrec`, `srec`, `ts`, `smod`, `tup`, `sfun`, `xlen`, `slen`,
         `vs`, `sevl`, `needed_dflts`, `cxd`, `prev`, `INL dflt_vs`, `sdfl`]
        irule intcall_default_frame_imm_dom_from_generated_ih \\
      MAP_EVERY qexists_tac
        [`cx`, `dflt_vs`, `es`, `fn`, `ih_args_s`, `ih_check_s`, `ih_fun_s`,
         `ih_len_s`, `ih_mod_s`, `needed_dflts`, `prev`, `sfun`, `slen`,
         `smod`, `src_id_opt`, `srec`, `ts`, `tup`, `vs`, `xlen`, `xrec`] \\
      rpt conj_tac \\
      FIRST [first_assum ACCEPT_TAC,
        qpat_x_assum `stup = SND tup` (fn h_stup =>
        qpat_x_assum `stup2 = SND stup` (fn h_stup2 =>
        qpat_x_assum `args = FST stup2` (fn h_args =>
        qpat_x_assum `sstup = SND stup2` (fn h_sstup =>
        qpat_x_assum `dflts = FST sstup` (fn h_dflts =>
        qpat_x_assum `needed_dflts = DROP _ _` (fn h_needed =>
          PURE_REWRITE_TAC [GSYM h_stup, GSYM h_stup2, GSYM h_args,
                            GSYM h_sstup, GSYM h_dflts] \\
          FIRST [ACCEPT_TAC h_needed, first_assum ACCEPT_TAC]))))))]) \\
  PURE_REWRITE_TAC[intcall_tail_body_provider_def] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac \\
     simp_tac (srw_ss()) [intcall_args_length_sub]) \\
  qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
                  args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
                  needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env0 t6
                  s7 prev0 t7 s8 rtv0 t8 is_view s9 lk0 t9 s10 cx0 t10.
                  type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
                  _ ⇒ ∀st0 res0 st1.
                    eval_stmts cx0 ss0 st0 = (res0,st1) ⇒
                    preserves_immutables_dom cx0 st0 st1`
    (qspecl_then
      [`ih_check_s`, `xrec`, `srec`,
       `ih_mod_s`, `ts`, `smod`,
       `ih_fun_s`, `tup`, `sfun`,
       `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
       `ret`, `ss`, `ih_len_s`, `xlen`, `slen`,
       `ih_args_s`, `vs`, `sevl`, `needed_dflts`, `cxd`,
       `sevl with scopes := [FEMPTY]`, `dflt_vs`, `pre_sdfl`, `get_tenv cx`,
       `sdfl`, `env`, `s_bind`, `sdfl`, `prev`, `sdfl`, `s_bind`, `rtv`,
       `s_eval`, `mut = View ∨ mut = Pure`, `s_eval`, `lk`, `s_lock`,
       `s_lock`, `cx'`, `s_push`] (fn ih =>
         SUBGOAL_THEN (lhand (concl ih))
           (fn guard => first_assum (fn ev =>
             ACCEPT_TAC (MP (Q.SPECL [`st`, `res`, `st'`] (MP ih guard)) ev))))) \\
  rpt conj_tac \\
  FIRST [first_assum ACCEPT_TAC, REFL_TAC]
QED

Theorem intcall_case_live_post_default_setup_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     dflt_vs sdfl prev mut stup nr stup2 args sstup dflts sstup2 ret ss.
    (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
        body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
      (INL ts,t') ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts)
        "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
      stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
      args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
      sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
      type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
        "IntCall args length" s'⁵' = (INL x',t'³') ∧
      eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
      es' = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
      cx' = cx with stk updated_by CONS (src_id_opt,fn) ⇒
      ∀st res st'.
        eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
    (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
        ss s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵'
        all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹'
        s'¹²' cx' t'¹⁰'.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
      (INL ts,t') ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts)
        "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
      stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
      args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
      sstup2 = SND sstup ∧ ret = FST sstup2 ∧ ss = SND sstup2 ∧
      type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
        "IntCall args length" s'⁵' = (INL x',t'³') ∧
      eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
      needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
      cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
      eval_exprs cxd needed_dflts s'⁷' = (INL dflt_vs,t'⁵') ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args (vs ⧺ dflt_vs))
        "IntCall bind_arguments" s'⁸' = (INL env,t'⁶') ∧
      get_scopes s'⁹' = (INL prev,t'⁷') ∧
      lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'¹⁰' =
      (INL rtv,t'⁸') ∧ (is_view ⇔ mut = View ∨ mut = Pure) ∧
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot =>
           acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s'¹¹' = (INL lk,t'⁹') ∧
      push_function (src_id_opt,fn) env cx s'¹²' = (INL cx',t'¹⁰') ⇒
      ∀st res st'.
        eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
    (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧ ss = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (INL dflt_vs,sdfl) ⇒
    preserves_immutables_dom cxd sevl sdfl ∧
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt gen_tac \\
  strip_tac \\
  pop_assum $ mk_asm "default_case_ih" \\
  strip_tac \\
  pop_assum $ mk_asm "body_case_ih" \\
  strip_tac \\
  qspecl_then
    [`cx`, `src_id_opt`, `fn`, `es`,
     `ih_check_s`, `ih_mod_s`, `ih_fun_s`, `ih_len_s`, `ih_args_s`,
     `xrec`, `srec`, `ts`, `smod`, `tup`, `sfun`, `xlen`, `slen`,
     `vs`, `sevl`, `needed_dflts`, `cxd`, `dflt_vs`, `sdfl`, `prev`,
     `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
     `ret`, `ss`]
    mp_tac intcall_live_post_default_setup_from_generated_ih \\
  (impl_tac >-
     (conj_tac >- (asm "default_case_ih" mp_tac \\ simp[]) \\
      conj_tac >- (asm "body_case_ih" mp_tac \\ simp[]) \\
      simp[])) \\
  simp[]
QED

Theorem intcall_default_frame_to_caller_imm_dom[local]:
  ∀cx src_id_opt fn st0 sevl sdfl.
    preserves_immutables_dom cx st0 sevl ∧
    preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) sevl sdfl ⇒
    preserves_immutables_dom cx st0 sdfl
Proof
  rpt strip_tac \\
  irule preserves_immutables_dom_trans \\
  qexists_tac `sevl` \\
  conj_tac >- simp[] \\
  irule (iffLR preserves_immutables_dom_txn_eq) \\
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fn)` \\
  simp[]
QED

Theorem intcall_tail_after_finally_cast_imm_dom[local]:
  !cx src_id_opt fn mut nr ss prev env st0 sevl r r2 q r' retv res st'.
    preserves_immutables_dom cx st0 sevl /\
    preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) sevl r /\
    r2.immutables = r.immutables /\
    (!st res st'.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss st = (res,st') ==>
       preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) st st') /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss;
               return NoneV od) handle_function)
      (do pop_function prev;
          if nr /\ mut <> View /\ mut <> Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return () od)
      (r2 with scopes := [env]) = (q,r') /\
    (case q of
     | INL v =>
         do crv <- lift_option_type (safe_cast retv v) "IntCall cast ret";
            return (Value crv) od r'
     | INR e => (INR e,r')) = (res,st') ==>
    preserves_immutables_dom cx st0 st'
Proof
  rpt strip_tac >>
  `preserves_immutables_dom cx r2 r'` by
    (qspecl_then [`cx`, `src_id_opt`, `fn`, `mut`, `nr`, `ss`, `prev`, `env`, `r2`, `q`, `r'`]
       mp_tac intcall_body_finally_release_imm_dom_use >>
     simp[] >>
     disch_then irule >>
     simp[]) >>
  `preserves_immutables_dom cx st0 r2` by
    (irule preserves_immutables_dom_trans >>
     qexists_tac `r` >>
     conj_tac >- metis_tac[intcall_default_frame_to_caller_imm_dom] >>
     irule preserves_immutables_dom_eq >> simp[]) >>
  Cases_on `q` >> gvs[bind_def, return_def] >-
    (Cases_on `lift_option_type (safe_cast retv x) "IntCall cast ret" r'` >>
     gvs[] >>
     imp_res_tac lift_option_type_same_state >>
     gvs[return_def, raise_def] >>
     Cases_on `q` >> gvs[] >>
     irule preserves_immutables_dom_trans >>
     qexists_tac `r2` >> simp[]) >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `r2` >> simp[]
QED

Theorem post_default_intcall_tail_imm_dom[local]:
  ∀cx src_id_opt fn mut nr args ret ss vs dflt_vs st0 sevl sdfl prev res st'.
    preserves_immutables_dom cx st0 sevl ∧
    preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) sevl sdfl ∧
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl ∧
    post_default_intcall_tail cx src_id_opt fn mut nr args ret ss vs dflt_vs prev sdfl = (res,st') ⇒
    preserves_immutables_dom cx st0 st'
Proof
  rpt strip_tac \\
  qpat_x_assum `post_default_intcall_tail _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac \\
  simp[post_default_intcall_tail_unfold, bind_def] \\
  BasicProvers.TOP_CASE_TAC \\
  FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac \\
  reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ gvs[] \\
      metis_tac[intcall_default_frame_to_caller_imm_dom]) \\
  BasicProvers.TOP_CASE_TAC \\
  FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac \\
  reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ gvs[] \\
      metis_tac[intcall_default_frame_to_caller_imm_dom]) \\
  rewrite_tac[bind_def, ignore_bind_def, COND_RATOR] \\
  BasicProvers.TOP_CASE_TAC \\
  `r''.immutables = sdfl.immutables` by
    (Cases_on `nr` \\ gvs[return_def, raise_def] \\
     Cases_on `cx.nonreentrant_slot` \\ gvs[return_def, raise_def] \\
     imp_res_tac acquire_nonreentrant_lock_immutables \\ gvs[]) \\
  reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ gvs[] \\
      irule preserves_immutables_dom_trans \\
      qexists_tac `r` \\
      conj_tac
      >- (irule preserves_immutables_dom_trans \\
          qexists_tac `sevl` \\
          conj_tac >- simp[] \\
          irule (iffLR preserves_immutables_dom_txn_eq) \\
          qexists_tac `cx with stk updated_by CONS (src_id_opt,fn)` \\
          simp[]) \\
      irule preserves_immutables_dom_eq \\ simp[]) \\
  rewrite_tac[bind_def] \\
  BasicProvers.TOP_CASE_TAC \\
  gvs[push_function_def, return_def] \\
  qpat_x_assum `intcall_tail_body_provider _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o SRULE[intcall_tail_body_provider_def]) \\
  disch_then (qspecl_then
    [`x`, `r`, `x'`, `r`, `r''`,
     `cx with stk updated_by CONS (src_id_opt,fn)`, `r'' with scopes := [x]`]
    mp_tac) \\
  simp[push_function_def, return_def] \\
  strip_tac \\
  BasicProvers.TOP_CASE_TAC \\
  gvs[] \\
  strip_tac \\
  qpat_x_assum `_ ⇒ ∀st res st'. eval_stmts _ _ st = (res,st') ⇒ _` mp_tac \\
  (impl_tac >- (Cases_on `nr` \\ gvs[return_def, raise_def] \\ Cases_on `cx.nonreentrant_slot` \\ gvs[return_def, raise_def])) \\
  strip_tac \\
  qspecl_then [`cx`, `src_id_opt`, `fn`, `mut`, `nr`, `ss`, `prev`, `x`,
                `st0`, `sevl`, `r`, `r''`, `q`, `r'`, `x'`, `res`, `st'`]
    mp_tac intcall_tail_after_finally_cast_imm_dom \\
  simp[] \\
  disch_then irule \\
  simp[ignore_bind_def]
QED
(* ===== Helper lemmas for ExtCall/IntCall cases ===== *)

Theorem case_IntCall_imm_dom[local]:
  ∀cx src_id_opt fn es vs st res st'.
  eval_expr cx (Call _ (IntCall (src_id_opt,fn)) es vs) st = (res,st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
      body' s'⁵' x' t'³'.
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
    stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
    args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ⇒
    ∀st res st'.
      eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
      body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
    stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
    args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ∧
    eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
    es' = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cx' = cx with stk updated_by CONS (src_id_opt,fn) ⇒
    ∀st res st'.
      eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
      ss s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵'
      all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹'
      s'¹²' cx' t'¹⁰'.
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
    stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
    args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ ss = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ∧
    eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    eval_exprs cxd needed_dflts s'⁷' = (INL dflt_vs,t'⁵') ∧
    all_tenv = get_tenv cx ∧
    lift_option_type (bind_arguments all_tenv args (vs ⧺ dflt_vs))
      "IntCall bind_arguments" s'⁸' = (INL env,t'⁶') ∧
    get_scopes s'⁹' = (INL prev,t'⁷') ∧
    lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'¹⁰' =
    (INL rtv,t'⁸') ∧ (is_view ⇔ mut = View ∨ mut = Pure) ∧
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot =>
         acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) s'¹¹' = (INL lk,t'⁹') ∧
    push_function (src_id_opt,fn) env cx s'¹²' = (INL cx',t'¹⁰') ⇒
    ∀st res st'.
      eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
  preserves_immutables_dom cx st st'
Proof
  rpt strip_tac
  \\ qpat_x_assum `eval_expr _ _ _ = _` mp_tac
  \\ simp[Once evaluate_def, bind_def, LET_THM]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  (* Peel: check recursion *)
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ rw[preserves_immutables_dom_refl])
  (* Peel: lift_option get_module_code *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  (* Peel: lift_option lookup_callable_function *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ gvs[preserves_immutables_dom_refl])
  (* Peel: check args length *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  (* eval_exprs cx es: specialize first IH using drule_all *)
  \\ BasicProvers.TOP_CASE_TAC
  \\ last_x_assum $ funpow 2 drule_then drule
  \\ simp_tac std_ss []
  \\ disch_then $ drule_then drule
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ strip_tac \\ gvs[])
  (* eval_exprs cx es succeeded *)
  \\ simp[get_scopes_def, return_def]
  \\ strip_tac
  \\ qpat_x_assum `bind _ _ _ = _` mp_tac
  \\ simp[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt strip_tac \\
      qpat_x_assum `r'⁵' = st'` (SUBST1_TAC o SYM) \\
      irule preserves_immutables_dom_trans \\
      qexists_tac `r'⁴'` \\
      conj_tac >- first_assum ACCEPT_TAC \\
      irule (iffLR preserves_immutables_dom_txn_eq) \\
      qexists_tac `cx with stk updated_by CONS (src_id_opt,fn)` \\ simp[] \\
      irule intcall_default_frame_imm_dom \\
      qexists_tac `DROP (LENGTH (FST (SND (SND (SND x'')))) -
                       (LENGTH (FST (SND (SND x''))) - LENGTH es))
                      (FST (SND (SND (SND x''))))` \\
      qexists_tac `r'⁴'.scopes` \\
      qexists_tac `INR y` \\
      simp[] \\
      conj_tac
      >- (rpt strip_tac \\
          drule type_check_intcall_args_length_sub \\
          strip_tac \\
          qpat_x_assum `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
                           _ ⇒ ∀st res st'.
                             eval_exprs cx' es' st = (res,st') ⇒ _`
            (qspecl_then
              [`st`, `x`, `r`, `st`, `x'`, `r'`, `st`, `x''`, `r''`,
               `FST x''`, `SND x''`, `FST (SND x'')`, `SND (SND x'')`,
               `FST (SND (SND x''))`, `SND (SND (SND x''))`,
               `FST (SND (SND (SND x'')))`,
               `SND (SND (SND (SND x'')))`,
               `FST (SND (SND (SND (SND x''))))`,
               `SND (SND (SND (SND (SND x''))))`,
               `st`, `x'³'`, `r'³'`, `st`, `x'⁴'`, `r'⁴'`,
               `DROP (LENGTH (FST (SND (SND (SND x'')))) −
                      (LENGTH (FST (SND (SND x''))) − LENGTH es))
                     (FST (SND (SND (SND x''))))`,
               `cx with stk updated_by CONS (src_id_opt,fn)`] mp_tac) \\
          impl_tac >-
            (rpt conj_tac \\
             FIRST [REFL_TAC, first_assum ACCEPT_TAC]) \\
          disch_then drule \\
          strip_tac \\
          first_assum ACCEPT_TAC) \\
      qpat_x_assum `finally _ _ _ = _` mp_tac \\
      simp[ignore_bind_def])
  (* INL branch: fold remaining pipeline through post_default_intcall_tail *)
  \\ qpat_assum
       `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
          _ ⇒ ∀st res st'. eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st'`
       (mk_asm "default_imm_ih")
  \\ qpat_assum
       `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret ss s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵' all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹' s'¹²' cx' t'¹⁰'.
          _ ⇒ ∀st res st'. eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st'`
       (mk_asm "body_imm_ih")
  \\ qspecl_then
       [`cx`, `src_id_opt`, `fn`, `es`,
        `st`, `st`, `st`, `st`, `st`,
        `x`, `r`, `x'`, `r'`, `x''`, `r''`, `x'³'`, `r'³'`,
        `x'⁴'`, `r'⁴'`,
        `DROP (LENGTH (FST (SND (SND (SND x'')))) -
               (LENGTH (FST (SND (SND x''))) - LENGTH es))
              (FST (SND (SND (SND x''))))`,
        `cx with stk updated_by CONS (src_id_opt,fn)`,
        `x'⁵'`, `r'⁵'`, `r'⁴'.scopes`,
        `FST x''`, `SND x''`, `FST (SND x'')`, `SND (SND x'')`,
        `FST (SND (SND x''))`, `SND (SND (SND x''))`,
        `FST (SND (SND (SND x'')))`, `SND (SND (SND (SND x'')))`,
        `FST (SND (SND (SND (SND x''))))`,
        `SND (SND (SND (SND (SND x''))))`]
       mp_tac intcall_case_live_post_default_setup_from_generated_ih
  \\ (impl_tac >- (asm "default_imm_ih" mp_tac \\ simp[]))
  \\ (impl_tac >- (asm "body_imm_ih" mp_tac \\ simp[]))
  \\ strip_tac
  \\ qpat_x_assum `default_imm_ih :- _` kall_tac
  \\ qpat_x_assum `body_imm_ih :- _` kall_tac
  \\ TRY (qpat_x_assum
       `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
          _ ⇒ ∀st res st'. eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st'`
       kall_tac)
  \\ TRY (qpat_x_assum
       `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret ss s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵' all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹' s'¹²' cx' t'¹⁰'.
          _ ⇒ ∀st res st'. eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st'`
       kall_tac)
  \\ `preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) r'⁴' r'⁵' ∧
       intcall_tail_body_provider cx src_id_opt fn (FST x'') (FST (SND x''))
         (FST (SND (SND x''))) (FST (SND (SND (SND (SND x'')))))
         (SND (SND (SND (SND (SND x''))))) x'⁴' x'⁵' r'⁵'` by
       (first_x_assum irule \\ rpt conj_tac \\ simp[ignore_bind_def])
  \\ simp[GSYM post_default_intcall_tail_unfold]
  \\ rpt strip_tac
  \\ qspecl_then
       [`cx`, `src_id_opt`, `fn`, `FST x''`, `FST (SND x'')`,
        `FST (SND (SND x''))`, `FST (SND (SND (SND (SND x''))))`,
        `SND (SND (SND (SND (SND x''))))`, `x'⁴'`, `x'⁵'`,
        `st`, `r'⁴'`, `r'⁵'`, `r'⁴'.scopes`, `res`, `st'`]
       mp_tac post_default_intcall_tail_imm_dom
  \\ simp[]
  \\ disch_then irule
  \\ simp[post_default_intcall_tail_unfold, bind_def, ignore_bind_def]
QED

(* ===== Main Mutual Induction ===== *)

Theorem intcall_mutual_default_frame_imm_dom_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd prev res sdfl.
    (∀s'' x t s'³' ts0 t' s'⁴' tup0 t'' mut stup nr stup2 args sstup dflts sstup2 ret
        body' s'⁵' x' t'³' s'⁶' vs0 t'⁴' es' cx' s'⁷' prev0 t'⁵' s'⁸' x'' t'⁶'.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
        (INL ts0,t') ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s'⁴' = (INL tup0,t'') ∧
      mut = FST tup0 ∧ stup = SND tup0 ∧ (nr ⇔ FST stup) ∧
      stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
      dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
      body' = SND sstup2 ∧
      type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
        "IntCall args length" s'⁵' = (INL x',t'³') ∧
      eval_exprs cx es s'⁶' = (INL vs0,t'⁴') ∧
      es' = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
      cx' = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s'⁷' = (INL prev0,t'⁵') ∧
      set_scopes [FEMPTY] s'⁸' = (INL x'',t'⁶') ⇒
      ∀st res st'. eval_exprs cx' es' st = (res,st') ⇒
        preserves_immutables_dom cx' st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    type_check
      (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
       LENGTH (FST (SND (SND tup))) ≤
         LENGTH es + LENGTH (FST (SND (SND (SND tup)))))
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts =
      DROP (LENGTH (FST (SND (SND (SND tup)))) −
            (LENGTH (FST (SND (SND tup))) − LENGTH es))
           (FST (SND (SND (SND tup)))) ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    get_scopes sevl = (INL prev,sevl) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (res,sdfl) ⇒
    preserves_immutables_dom cxd sevl sdfl
Proof
  rpt strip_tac \\
  irule intcall_default_frame_imm_dom \\
  qexists_tac `needed_dflts` \\
  qexists_tac `prev` \\
  qexists_tac `res` \\
  simp[] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
      LENGTH (FST (SND (SND tup))) − LENGTH es ≤
        LENGTH (FST (SND (SND (SND tup)))))
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac \\
     simp[type_check_def, assert_def] \\
     IF_CASES_TAC \\ simp[] \\
     decide_tac) \\
  first_assum (qspecl_then
    [`ih_check_s`, `xrec`, `srec`,
     `ih_mod_s`, `ts`, `smod`,
     `ih_fun_s`, `tup`, `sfun`,
     `FST tup`, `SND tup`, `FST (SND tup)`,
     `SND (SND tup)`, `FST (SND (SND tup))`,
     `SND (SND (SND tup))`, `FST (SND (SND (SND tup)))`,
     `SND (SND (SND (SND tup)))`,
     `FST (SND (SND (SND (SND tup))))`,
     `SND (SND (SND (SND (SND tup))))`,
     `ih_len_s`, `xlen`, `slen`,
     `ih_args_s`, `vs`, `sevl`,
     `needed_dflts`, `cxd`,
     `sevl`, `prev`, `sevl`, `sevl`, `()`,
     `sevl with scopes := [FEMPTY]`] mp_tac) \\
  simp[get_scopes_def, set_scopes_def, return_def] \\
  disch_then drule \\
  simp[]
QED

Theorem intcall_mutual_tail_body_provider_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     dflt_vs sdfl prev mut stup nr stup2 args sstup dflts sstup2 ret ss.
    (∀s'' x t s'³' ts0 t' s'⁴' tup0 t'' mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 ss0 s'⁵' x' t'³' s'⁶' vs0 t'⁴'
        needed_dflts0 cxd0 s'⁷' prev0 t'⁵' s'⁸' dflt_vs0 t'⁶'
        all_tenv s'⁹' env t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹'
        s'¹²' cx' t'¹⁰'.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
        (INL ts0,t') ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s'⁴' = (INL tup0,t'') ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s'⁵' = (INL x',t'³') ∧
      eval_exprs cx es s'⁶' = (INL vs0,t'⁴') ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s'⁷' = (INL prev0,t'⁵') ∧
      finally
        (do
           set_scopes [FEMPTY];
           eval_exprs cxd0 needed_dflts0
         od)
        (set_scopes prev0) s'⁸' = (INL dflt_vs0,t'⁶') ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s'⁹' = (INL env,t'⁷') ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s'¹⁰' =
        (INL rtv,t'⁸') ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s'¹¹' = (INL lk,t'⁹') ∧
      push_function (src_id_opt,fn) env cx s'¹²' = (INL cx',t'¹⁰') ⇒
      ∀st res st'. eval_stmts cx' ss0 st = (res,st') ⇒
        preserves_immutables_dom cx' st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
    ss = SND sstup2 ∧
    type_check
      (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    get_scopes sevl = (INL prev,sevl) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (INL dflt_vs,sdfl) ⇒
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt strip_tac \\
  PURE_REWRITE_TAC[intcall_tail_body_provider_def] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac \\
     simp_tac (srw_ss()) [intcall_args_length_sub]) \\
  qpat_assum `∀s'' x t s'³' ts0 t' s'⁴' tup0 t'' mut0 stup0 nr0 stup20
                  args0 sstup0 dflts0 sstup20 ret0 ss0 s'⁵' x' t'³'
                  s'⁶' vs0 t'⁴' needed_dflts0 cxd0 s'⁷' prev0 t'⁵'
                  s'⁸' dflt_vs0 t'⁶' all_tenv s'⁹' env0 t'⁷' s'¹⁰'
                  rtv0 t'⁸' is_view s'¹¹' lk0 t'⁹' s'¹²' cx0 t'¹⁰'.
                  type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
                  _ ⇒ ∀st0 res0 st1.
                    eval_stmts cx0 ss0 st0 = (res0,st1) ⇒
                    preserves_immutables_dom cx0 st0 st1`
    (qspecl_then
      [`ih_check_s`, `xrec`, `srec`,
       `ih_mod_s`, `ts`, `smod`,
       `ih_fun_s`, `tup`, `sfun`,
       `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
       `ret`, `ss`, `ih_len_s`, `xlen`, `slen`,
       `ih_args_s`, `vs`, `sevl`, `needed_dflts`, `cxd`,
       `sevl`, `prev`, `sevl`, `sevl`, `dflt_vs`, `sdfl`, `get_tenv cx`,
       `sdfl`, `env`, `s_bind`, `s_bind`, `rtv`, `s_eval`,
       `mut = View ∨ mut = Pure`, `s_eval`, `lk`, `s_lock`, `s_lock`, `cx'`,
       `s_push`] (fn ih =>
         SUBGOAL_THEN (lhand (concl ih))
           (fn guard => first_assum (fn ev =>
             ACCEPT_TAC (MP (Q.SPECL [`st`, `res`, `st'`] (MP ih guard)) ev))))) \\
  rpt conj_tac \\
  FIRST [first_assum ACCEPT_TAC, REFL_TAC]
QED


Theorem intcall_mutual_live_default_frame_imm_dom[local]:
  ∀cx src_id_opt fn es check_res mod_code fn_tup len_res arg_vs default_vs
     st0 s_args sdfl.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0
        s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      es0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s5 = (INL prev0,t5) ∧
      set_scopes [FEMPTY] s6 = (INL x2,t6) ⇒
      ∀st0 res0 st1. eval_exprs cxd0 es0 st0 = (res0,st1) ⇒ preserves_immutables_dom cxd0 st0 st1) ⇒
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" st0 = (INL check_res,st0) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" st0 = (INL mod_code,st0) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn mod_code) "IntCall lookup_function" st0 =
      (INL fn_tup,st0) ∧
    type_check
      (LENGTH es ≤ LENGTH (FST (SND (SND fn_tup))) ∧
       LENGTH (FST (SND (SND fn_tup))) ≤ LENGTH es + LENGTH (FST (SND (SND (SND fn_tup)))))
      "IntCall args length" st0 = (INL len_res,st0) ∧
    eval_exprs cx es st0 = (INL arg_vs,s_args) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
           (DROP (LENGTH (FST (SND (SND (SND fn_tup)))) −
                  (LENGTH (FST (SND (SND fn_tup))) − LENGTH es))
                 (FST (SND (SND (SND fn_tup)))))
       od)
      (set_scopes s_args.scopes) s_args = (INL default_vs,sdfl) ⇒
    preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) s_args sdfl
Proof
  rpt strip_tac \\
  qspecl_then
    [`cx`, `src_id_opt`, `fn`, `es`,
     `st0`, `st0`, `st0`, `st0`, `st0`,
     `check_res`, `st0`, `mod_code`, `st0`, `fn_tup`, `st0`, `len_res`, `st0`,
     `arg_vs`, `s_args`,
     `DROP (LENGTH (FST (SND (SND (SND fn_tup)))) −
            (LENGTH (FST (SND (SND fn_tup))) − LENGTH es))
           (FST (SND (SND (SND fn_tup))))`,
     `cx with stk updated_by CONS (src_id_opt,fn)`,
     `s_args.scopes`, `INL default_vs`, `sdfl`]
    irule intcall_mutual_default_frame_imm_dom_from_generated_ih \\
  conj_tac
  >- REFL_TAC \\
  conj_tac
  >- simp[get_scopes_def, return_def] \\
  MAP_EVERY qexists_tac
    [`arg_vs`, `check_res`, `default_vs`, `es`, `fn_tup`, `len_res`,
     `mod_code`, `st0`] \\
  rpt conj_tac \\
  FIRST [REFL_TAC, first_assum ACCEPT_TAC]
QED

Theorem intcall_mutual_live_tail_body_provider[local]:
  ∀cx src_id_opt fn es check_res mod_code fn_tup len_res arg_vs default_vs
     st0 s_args sdfl.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0
        s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s5 = (INL prev0,t5) ∧
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed_dflts0 od) (set_scopes prev0) s6 = (INL dflt_vs0,t6) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0)) "IntCall bind_arguments" s7 = (INL env,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 = (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then case cx.nonreentrant_slot of NONE => raise (Error (TypeError "nonreentrant slot missing"))
                 | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st0 res0 st1. eval_stmts cx0 ss0 st0 = (res0,st1) ⇒ preserves_immutables_dom cx0 st0 st1) ⇒
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" st0 = (INL check_res,st0) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" st0 = (INL mod_code,st0) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn mod_code) "IntCall lookup_function" st0 =
      (INL fn_tup,st0) ∧
    type_check
      (LENGTH es ≤ LENGTH (FST (SND (SND fn_tup))) ∧
       LENGTH (FST (SND (SND fn_tup))) ≤ LENGTH es + LENGTH (FST (SND (SND (SND fn_tup)))))
      "IntCall args length" st0 = (INL len_res,st0) ∧
    eval_exprs cx es st0 = (INL arg_vs,s_args) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
           (DROP (LENGTH (FST (SND (SND (SND fn_tup)))) −
                  (LENGTH (FST (SND (SND fn_tup))) − LENGTH es))
                 (FST (SND (SND (SND fn_tup)))))
       od)
      (set_scopes s_args.scopes) s_args = (INL default_vs,sdfl) ⇒
    intcall_tail_body_provider cx src_id_opt fn (FST fn_tup) (FST (SND fn_tup))
      (FST (SND (SND fn_tup))) (FST (SND (SND (SND (SND fn_tup)))))
      (SND (SND (SND (SND (SND fn_tup))))) arg_vs default_vs sdfl
Proof
  rpt strip_tac \\
  qspecl_then
    [`cx`, `src_id_opt`, `fn`, `es`,
     `st0`, `st0`, `st0`, `st0`, `st0`,
     `check_res`, `st0`, `mod_code`, `st0`, `fn_tup`, `st0`, `len_res`, `st0`,
     `arg_vs`, `s_args`,
     `DROP (LENGTH (FST (SND (SND (SND fn_tup)))) −
            (LENGTH (FST (SND (SND fn_tup))) − LENGTH es))
           (FST (SND (SND (SND fn_tup))))`,
     `cx with stk updated_by CONS (src_id_opt,fn)`,
     `default_vs`, `sdfl`, `s_args.scopes`,
     `FST fn_tup`, `SND fn_tup`, `FST (SND fn_tup)`, `SND (SND fn_tup)`,
     `FST (SND (SND fn_tup))`, `SND (SND (SND fn_tup))`,
     `FST (SND (SND (SND fn_tup)))`, `SND (SND (SND (SND fn_tup)))`,
     `FST (SND (SND (SND (SND fn_tup))))`,
     `SND (SND (SND (SND (SND fn_tup))))`]
    (fn th => SUBGOAL_THEN (lhand (concl th)) (ACCEPT_TAC o MP th))
    intcall_mutual_tail_body_provider_from_generated_ih \\
  rpt conj_tac \\
  FIRST [REFL_TAC, first_assum ACCEPT_TAC,
         PURE_REWRITE_TAC[get_scopes_def, return_def] \\ REFL_TAC]
QED

Theorem case_IntCall_imm_dom_from_mutual_ih[local]:
  ∀cx src_id_opt fn es vs st res st'.
    eval_expr cx (Call _ (IntCall (src_id_opt,fn)) es vs) st = (res,st') ⇒
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ⇒
      ∀st0 res0 st1. eval_exprs cx es st0 = (res0,st1) ⇒ preserves_immutables_dom cx st0 st1) ⇒
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0
        s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      es0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s5 = (INL prev0,t5) ∧
      set_scopes [FEMPTY] s6 = (INL x2,t6) ⇒
      ∀st0 res0 st1. eval_exprs cxd0 es0 st0 = (res0,st1) ⇒ preserves_immutables_dom cxd0 st0 st1) ⇒
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0
        s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s5 = (INL prev0,t5) ∧
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed_dflts0 od) (set_scopes prev0) s6 = (INL dflt_vs0,t6) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0)) "IntCall bind_arguments" s7 = (INL env,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 = (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then case cx.nonreentrant_slot of NONE => raise (Error (TypeError "nonreentrant slot missing"))
                 | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st0 res0 st1. eval_stmts cx0 ss0 st0 = (res0,st1) ⇒ preserves_immutables_dom cx0 st0 st1) ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac
  \\ qpat_x_assum `eval_expr _ _ _ = _` mp_tac
  \\ simp[Once evaluate_def, bind_def, LET_THM]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ rw[preserves_immutables_dom_refl])
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ gvs[preserves_immutables_dom_refl])
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  \\ BasicProvers.TOP_CASE_TAC
  \\ qpat_x_assum
       `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3.
          _ ⇒ ∀st0 res0 st1. eval_exprs cx es st0 = (res0,st1) ⇒ preserves_immutables_dom cx st0 st1`
       (funpow 2 drule_then drule)
  \\ simp_tac std_ss []
  \\ disch_then $ drule_then drule
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ strip_tac \\ gvs[])
  \\ simp[get_scopes_def, return_def]
  \\ strip_tac
  \\ qpat_x_assum `bind _ _ _ = _` mp_tac
  \\ simp[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt strip_tac \\
      rpt (qpat_x_assum `_ = st` SUBST_ALL_TAC) \\
      irule intcall_default_frame_to_caller_imm_dom \\
      qexists_tac `fn` \\
      qexists_tac `r'⁴'` \\
      qexists_tac `src_id_opt` \\
      simp[] \\
      qspecl_then
        [`cx`, `src_id_opt`, `fn`, `es`,
         `st`, `st`, `st`, `st`, `st`,
         `()`, `st`, `x'`, `st`, `x''`, `st`, `()`, `st`, `x'⁴'`, `r'⁴'`,
         `DROP (LENGTH (FST (SND (SND (SND x'')))) -
                (LENGTH (FST (SND (SND x''))) - LENGTH es))
               (FST (SND (SND (SND x''))))`,
         `cx with stk updated_by CONS (src_id_opt,fn)`, `r'⁴'.scopes`,
         `INR y`, `r'⁵'`]
        mp_tac intcall_mutual_default_frame_imm_dom_from_generated_ih \\
      (impl_tac >-
         (conj_tac >- (qpat_x_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6. _ ⇒ ∀st0 res0 st1. eval_exprs cxd0 es0 st0 = (res0,st1) ⇒ preserves_immutables_dom cxd0 st0 st1` mp_tac \\ simp[]) \\
          TRY (qpat_x_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6. _` kall_tac) \\
          TRY (qpat_x_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7 s8 rtv t8 is_view s9 lk t9 s10 cx0 t10. _` kall_tac) \\
          rpt conj_tac \\ simp[get_scopes_def, set_scopes_def, return_def,
                                type_check_def, assert_def, ignore_bind_def] \\
          TRY decide_tac)) \\
      simp[])
  \\ `preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) r'⁴' r'⁵'` by
       (qspecl_then
          [`cx`, `src_id_opt`, `fn`, `es`, `()`, `x'`, `x''`, `()`, `x'⁴'`,
           `x'⁵'`, `st`, `r'⁴'`, `r'⁵'`]
          mp_tac intcall_mutual_live_default_frame_imm_dom \\
        (impl_tac >-
           (qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6. _ ⇒ ∀st0 res0 st1. eval_exprs cxd0 es0 st0 = (res0,st1) ⇒ preserves_immutables_dom cxd0 st0 st1`
              mp_tac \\
            simp[])) \\
        (impl_tac >-
           (simp[get_scopes_def, return_def, type_check_def, assert_def,
                 ignore_bind_def] \\
            TRY decide_tac)) \\
        simp[])
  \\ `intcall_tail_body_provider cx src_id_opt fn (FST x'') (FST (SND x''))
        (FST (SND (SND x''))) (FST (SND (SND (SND (SND x'')))))
        (SND (SND (SND (SND (SND x''))))) x'⁴' x'⁵' r'⁵'` by
       (qspecl_then
          [`cx`, `src_id_opt`, `fn`, `es`, `()`, `x'`, `x''`, `()`, `x'⁴'`,
           `x'⁵'`, `st`, `r'⁴'`, `r'⁵'`]
          mp_tac intcall_mutual_live_tail_body_provider \\
        (impl_tac >-
           (qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7 s8 rtv t8 is_view s9 lk t9 s10 cx0 t10. _ ⇒ ∀st0 res0 st1. eval_stmts cx0 ss0 st0 = (res0,st1) ⇒ preserves_immutables_dom cx0 st0 st1`
              mp_tac \\
            simp[])) \\
        (impl_tac >-
           (simp[get_scopes_def, return_def, type_check_def, assert_def,
                 ignore_bind_def] \\
            TRY decide_tac)) \\
        simp[])
  \\ simp[GSYM post_default_intcall_tail_unfold]
  \\ rpt strip_tac
  \\ qspecl_then
       [`cx`, `src_id_opt`, `fn`, `FST x''`, `FST (SND x'')`,
        `FST (SND (SND x''))`, `FST (SND (SND (SND (SND x''))))`,
        `SND (SND (SND (SND (SND x''))))`, `x'⁴'`, `x'⁵'`,
        `st`, `r'⁴'`, `r'⁵'`, `r'⁴'.scopes`, `res`, `st'`]
       mp_tac post_default_intcall_tail_imm_dom
  \\ simp[]
  \\ disch_then irule
  \\ simp[post_default_intcall_tail_unfold, bind_def, ignore_bind_def]
QED

Theorem raw_call_callback_preserves_immutables_dom[local]:
  ∀cx flags result st res st'.
    ((λ(success,returnData,accounts',tStorage',emitted_logs).
        do
          x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- append_logs emitted_logs;
          if flags.rcf_revert_on_failure then
            do
              x <- if success then return () else raise (Error (RevertData returnData));
              if flags.rcf_max_outsize = 0 then return (Value NoneV)
              else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData)))
            od
          else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
          else
            return
              (Value
                 (ArrayV (TupleV [BoolV success; BytesV (TAKE flags.rcf_max_outsize returnData)])))
        od) result st = (res,st')) ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  PairCases_on `result` >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp[update_accounts_def, update_transient_def, append_logs_def,
      bind_def, ignore_bind_def, return_def, raise_def, assert_def, check_def, type_check_def,
      AllCaseEqs()] >>
  rpt IF_CASES_TAC >>
  simp[update_accounts_def, update_transient_def, append_logs_def,
      bind_def, ignore_bind_def, return_def, raise_def, assert_def, check_def, type_check_def,
      AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  irule preserves_immutables_dom_eq >> gvs[]
QED


Theorem immutables_dom_extended[local]:
  (∀cx s st res st'. eval_stmt cx s st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx ss st res st'. eval_stmts cx ss st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx it st res st'. eval_iterator cx it st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒ preserves_immutables_dom cx st st') /\
  (!cx t st res st'. eval_base_place cx t st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (!cx t st res st'. eval_target_place cx t st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> preserves_immutables_dom cx st st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt strip_tac
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- (drule_all case_Return_SOME_imm_dom >> simp[])
  (* Raise RaiseBare *)
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  (* Raise RaiseUnreachable *)
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  (* Raise (RaiseReason e): only eval_expr changes state *)
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), raise_def, return_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >> gvs[])
  (* Assert e AssertBare / AssertUnreachable: only eval_expr changes state *)
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
      simp[switch_BoolV_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> imp_res_tac read_result_state >> gvs[] >>
      Cases_on `v' = BoolV T` >> gvs[return_def, raise_def] >>
      Cases_on `v' = BoolV F` >> gvs[return_def, raise_def])
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
      simp[switch_BoolV_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> imp_res_tac read_result_state >> gvs[] >>
      Cases_on `v' = BoolV T` >> gvs[return_def, raise_def] >>
      Cases_on `v' = BoolV F` >> gvs[return_def, raise_def])
  (* Assert e (AssertReason se): chain eval_expr e → eval_expr se *)
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      imp_res_tac read_result_state >> gvs[] >>
      qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
      simp[switch_BoolV_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> imp_res_tac read_result_state >> gvs[] >>
      Cases_on `v' = BoolV T` >> gvs[return_def, raise_def] >>
      Cases_on `v' = BoolV F` >> gvs[return_def, raise_def] >>
      gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >> gvs[] >>
      irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
      conj_tac >- metis_tac[] >> metis_tac[])
  >- (drule_all case_Log_imm_dom >> simp[])
  >- (drule_all case_AnnAssign_imm_dom >> simp[])
  >- (drule_all case_Append_imm_dom >> simp[])
  >- suspend "AssignPlace"
  >- suspend "AssignTuple"
  >- suspend "AugAssign"
  >- (drule_all case_If_imm_dom >> simp[])
  >- (drule_all case_For_imm_dom >> simp[])
  >- (drule_all case_Expr_imm_dom >> simp[])
  >- (gvs[evaluate_def, return_def, preserves_immutables_dom_refl])
  >- (drule_all case_eval_stmts_cons_imm_dom >> simp[])
  >- (drule_all case_Array_imm_dom >> simp[])
  >- (drule_all case_Range_imm_dom >> simp[])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (drule_all case_eval_for_cons_imm_dom >> simp[])
  >- (drule_all case_Name_imm_dom >> simp[])
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def] >> strip_tac >>
       imp_res_tac lookup_global_immutables >>
       irule preserves_immutables_dom_eq >> gvs[])
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def] >> strip_tac >>
       imp_res_tac lookup_flag_mem_immutables >>
       irule preserves_immutables_dom_eq >> gvs[])
  >- (drule_all case_IfExp_imm_dom >> simp[])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
            get_scopes_def, get_immutables_def, get_address_immutables_def,
            lift_option_def, lift_option_type_def, lift_sum_def, LET_THM, check_def, type_check_def, assert_def,
            ignore_bind_def, get_accounts_def, lift_sum_def,
            get_transient_storage_def, update_accounts_def, update_transient_def] >>
       rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
       first_x_assum irule >> first_assum (irule_at Any) >>
            simp[check_def, type_check_def, assert_def])
  >- (drule_all case_Subscript_imm_dom >> simp[])
  >- (drule_all case_Attribute_imm_dom >> simp[])
  >- (drule_all case_Builtin_imm_dom >> simp[])
  >- (drule_all case_Pop_imm_dom >> simp[])
  >- (drule_all case_TypeBuiltin_imm_dom >> simp[])
  >- (drule_all case_Send_imm_dom >> simp[])
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
      TRY (gvs[] >> NO_TAC) >>
      drule eval_ext_call_preserves_non_accounts >> strip_tac >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule preserves_immutables_dom_eq >> gvs[])
  >- (drule_all case_IntCall_imm_dom_from_mutual_ih >> simp[])
  (* ===== Chain interaction builtins (unguarded eval_exprs IH) ===== *)
  (* All 5 cases: eval_exprs first, then pure/state ops that preserve immutables.
     Pattern: unfold, case-split, apply IH via drule, close failure paths,
     use transitivity + _eq for success path. *)
  (* RawCallTarget *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, type_check_def, assert_def, lift_option_type_def,
           option_CASE_rator] >>
      rpt strip_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
      TRY (gvs[] >> NO_TAC) >>
      drule eval_raw_call_preserves_non_accounts >> strip_tac >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule preserves_immutables_dom_eq >> gvs[])
  (* RawCallCalldataTarget *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, type_check_def, assert_def, lift_option_type_def,
           option_CASE_rator] >>
      rpt strip_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
      TRY (gvs[] >> NO_TAC) >>
      drule eval_raw_call_preserves_non_accounts >> strip_tac >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule preserves_immutables_dom_eq >> gvs[])
  (* RawLog *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def,
           push_log_def, option_CASE_rator] >>
      rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      first_x_assum drule >> strip_tac >>
      TRY (gvs[] >> NO_TAC) >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule preserves_immutables_dom_eq >> gvs[])
  (* RawRevert *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, type_check_def, assert_def] >>
      rpt strip_tac >> gvs[] >>
      first_x_assum drule >> gvs[])
  (* SelfDestructTarget *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def,
           get_accounts_def, option_CASE_rator] >>
      rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      first_x_assum drule >> strip_tac >>
      TRY (gvs[] >> NO_TAC) >>
      imp_res_tac transfer_value_immutables >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule preserves_immutables_dom_eq >> gvs[])
  (* CreateTarget *)
  >- (Cases_on `kind` >> gvs[] >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
      imp_res_tac check_create_blueprint_result_state >> gvs[] >>
      res_tac >>
      imp_res_tac eval_create_preserves_scopes_immutables >>
      metis_tac[preserves_immutables_dom_trans, preserves_immutables_dom_eq])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (drule_all case_eval_exprs_cons_imm_dom >> simp[])
  >> qpat_x_assum `_ = (res,st')` mp_tac
  >> simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def, get_scopes_def, check_def, type_check_def,
       assert_def]
  >> rpt strip_tac >> gvs[preserves_immutables_dom_refl]
  >> imp_res_tac lift_option_type_state
  >> imp_res_tac read_place_state >> imp_res_tac read_result_state
  >> imp_res_tac place_type_value_state >> imp_res_tac get_place_state
  >> imp_res_tac lookup_global_immutables
  >> imp_res_tac extend_place_state
  >> imp_res_tac read_result_state
  >> imp_res_tac read_result_state >> imp_res_tac lift_sum_state
  >> gvs[preserves_immutables_dom_refl, preserves_immutables_dom_eq]
  >> imp_res_tac write_place_imm_dom
  >> gvs[value_CASE_rator, array_value_CASE_rator, AllCaseEqs(), raise_def,
      preserves_immutables_dom_refl]
  >> TRY (first_x_assum (drule_all_then assume_tac))
  >> TRY (first_x_assum (drule_all_then assume_tac))
  >> metis_tac[preserves_immutables_dom_trans]
QED

val PLACE_IMM_DOM_TAC =
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def, get_scopes_def, check_def, type_check_def,
       assert_def, lift_option_type_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac read_place_state >> imp_res_tac read_result_state >>
  imp_res_tac place_type_value_state >> imp_res_tac get_place_state >>
  imp_res_tac extend_place_state >>
  imp_res_tac read_result_state >>
  imp_res_tac read_result_state >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac write_place_imm_dom >>
  metis_tac[preserves_immutables_dom_trans];

Resume immutables_dom_extended[AssignPlace]:
  PLACE_IMM_DOM_TAC
QED
Resume immutables_dom_extended[AssignTuple]:
  PLACE_IMM_DOM_TAC
QED
Resume immutables_dom_extended[AugAssign]:
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def, lift_option_type_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac lift_sum_state >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac read_result_state >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac write_place_imm_dom >>
  first_x_assum (drule_all_then assume_tac) >>
  TRY (first_x_assum (drule_all_then assume_tac)) >>
  TRY (first_x_assum (drule_all_then assume_tac)) >>
  metis_tac[preserves_immutables_dom_trans]
QED
Finalise immutables_dom_extended


(* ===== Main theorems ===== *)

Theorem eval_expr_preserves_immutables_addr_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_extended, preserves_immutables_dom_def]
QED

Theorem eval_expr_preserves_immutables_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 5 immutables_dom_extended) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_base_place_preserves_immutables_addr_dom:
  ∀cx bt st res st'.
    eval_base_place cx bt st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_extended, preserves_immutables_dom_def]
QED

Theorem eval_base_place_preserves_immutables_dom:
  ∀cx bt st res st'.
    eval_base_place cx bt st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 7 immutables_dom_extended) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_exprs_preserves_immutables_dom:
  ∀cx es st res st'.
    eval_exprs cx es st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 6 immutables_dom_extended) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_exprs_preserves_immutables_addr_dom:
  ∀cx es st res st'.
    eval_exprs cx es st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_extended, preserves_immutables_dom_def]
QED

Theorem eval_stmts_preserves_immutables_addr_dom:
  ∀cx ss st res st'.
    eval_stmts cx ss st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_extended, preserves_immutables_dom_def]
QED

Theorem eval_stmts_preserves_immutables_dom:
  ∀cx ss st res st'.
    eval_stmts cx ss st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 2 immutables_dom_extended) >>
  rw[preserves_immutables_dom_def]
QED

(* Integration audit: immutable-domain exports must remain kernel closed. *)
val () = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Immutable-domain oracle debt: " ^ name)
  end) (DB.thms "vyperEvalPreservesImmutablesDom");
