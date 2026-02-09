Theory vyperScopePreservingExpr
Ancestors
  option vyperInterpreter vyperLookup vyperScopePreservation

(* Scope-preserving expressions: expressions that do not modify scopes.
   Pop is the only expression constructor that modifies scoped variables.
*)

Definition scope_preserving_expr_def:
  scope_preserving_expr (Name _) = T ∧
  scope_preserving_expr (TopLevelName _) = T ∧
  scope_preserving_expr (FlagMember _ _) = T ∧
  scope_preserving_expr (Literal _) = T ∧
  scope_preserving_expr (IfExp e1 e2 e3) = (scope_preserving_expr e1 ∧ scope_preserving_expr e2 ∧ scope_preserving_expr e3) ∧
  scope_preserving_expr (StructLit _ kes) = EVERY scope_preserving_expr (MAP SND kes) ∧
  scope_preserving_expr (Subscript e1 e2) = (scope_preserving_expr e1 ∧ scope_preserving_expr e2) ∧
  scope_preserving_expr (Attribute e _) = scope_preserving_expr e ∧
  scope_preserving_expr (Builtin _ es) = EVERY scope_preserving_expr es ∧
  scope_preserving_expr (TypeBuiltin _ _ es) = EVERY scope_preserving_expr es ∧
  scope_preserving_expr (Pop _) = F ∧
  scope_preserving_expr (Call _ es drv) =
    (EVERY scope_preserving_expr es ∧
     OPTION_ALL scope_preserving_expr drv)
Termination
  WF_REL_TAC `measure expr_size` >>
  rw[] >>
  Induct_on `kes` >> rw[] >>
  PairCases_on `h` >> rw[] >>
  res_tac >> simp[]
End

(* ------------------------------------------------------------------------
   Individual Case Lemmas
   ------------------------------------------------------------------------ *)

Theorem case_Name[local]:
  ∀cx id.
    (∀st res st'.
       eval_expr cx (Name id) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  rpt strip_tac >> fs[evaluate_def, bind_def, AllCaseEqs()] >> gvs[] >>
  TRY (drule get_scopes_scopes >> simp[] >> drule get_immutables_scopes >> simp[] >>
       drule lift_sum_scopes >> simp[] >> drule return_scopes >> simp[]) >>
  TRY (drule get_scopes_scopes >> simp[] >> drule get_immutables_scopes >> simp[] >>
       drule lift_sum_scopes >> simp[]) >>
  TRY (drule get_scopes_scopes >> simp[] >> drule get_immutables_scopes >> simp[]) >>
  drule get_scopes_scopes >> simp[]
QED

Theorem case_TopLevelName[local]:
  ∀cx src_id_opt id.
    (∀st res st'.
       eval_expr cx (TopLevelName (src_id_opt, id)) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_global_scopes >> simp[]
QED

Theorem case_FlagMember[local]:
  ∀cx nsid mid.
    (∀st res st'.
       eval_expr cx (FlagMember nsid mid) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_flag_mem_scopes >> simp[]
QED

Theorem case_IfExp[local]:
  ∀cx e1 e2 e3.
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ scope_preserving_expr e2 ⇒ st.scopes = st'.scopes) ∧
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e3 st = (res, st') ⇒ scope_preserving_expr e3 ⇒ st.scopes = st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ scope_preserving_expr e1 ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (IfExp e1 e2 e3) st = (res, st') ⇒
       scope_preserving_expr (IfExp e1 e2 e3) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  fs[evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def, scope_preserving_expr_def, raise_def] >>
  gvs[] >>
  `st.scopes = s''.scopes` by (first_x_assum drule >> simp[]) >>
  Cases_on `tv = Value (BoolV T)` >> gvs[] >-
    (first_x_assum drule >> simp[] >> metis_tac[]) >>
  Cases_on `tv = Value (BoolV F)` >> gvs[raise_def] >>
  qpat_x_assum `∀s'' tv1 t. eval_expr cx e1 s'' = (INL tv1, t) ⇒ _` drule >>
  simp[] >> metis_tac[]
QED

Theorem case_Literal[local]:
  ∀cx l.
    (∀st res st'.
       eval_expr cx (Literal l) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  rpt strip_tac >> fs[evaluate_def, return_def]
QED

(* Case: StructLit - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates MAP SND kes as expressions, then constructs struct.
   If eval_exprs preserves scopes (IH), result preserves scopes.

   Plan reference: Case 6 *)
Theorem case_StructLit[local]:
  ∀cx src kes.
    (∀st res st'.
       eval_exprs cx (MAP SND kes) st = (res, st') ⇒
       EVERY scope_preserving_expr (MAP SND kes) ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (StructLit src kes) st = (res, st') ⇒
       scope_preserving_expr (StructLit src kes) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >> PairCases_on `src` >>
  fs[evaluate_def, bind_def, AllCaseEqs(), scope_preserving_expr_def, return_def] >> gvs[] >>
  first_x_assum drule >> gvs[listTheory.EVERY_MAP]
QED

Theorem case_Subscript[local]:
  ∀cx e1 e2.
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ scope_preserving_expr e2 ⇒ st.scopes = st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ scope_preserving_expr e1 ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Subscript e1 e2) st = (res, st') ⇒
       scope_preserving_expr (Subscript e1 e2) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), scope_preserving_expr_def] >>
  imp_res_tac return_scopes >> imp_res_tac lift_sum_scopes >>
  imp_res_tac lift_option_scopes >> imp_res_tac get_Value_scopes
  (* First subgoal is the main success path with case on res' *)
  >- (Cases_on `res'` >> gvs[return_def, bind_def, AllCaseEqs()]
      (* INL case - direct return *)
      >- metis_tac[]
      (* INR case - storage slot access *)
      >> PairCases_on `y` >> gvs[bind_def, AllCaseEqs(), lift_option_def, return_def, raise_def]
      >> imp_res_tac read_storage_slot_scopes >> gvs[]
      >> Cases_on `evaluate_type (type_env ts) y2` >> gvs[return_def, raise_def]
      >> metis_tac[])
  (* Remaining error cases *)
  >> metis_tac[]
QED

Theorem case_Attribute[local]:
  ∀cx e id.
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ scope_preserving_expr e ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Attribute e id) st = (res, st') ⇒
       scope_preserving_expr (Attribute e id) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), scope_preserving_expr_def] >>
  imp_res_tac return_scopes >> imp_res_tac lift_sum_scopes >>
  imp_res_tac get_Value_scopes >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem case_Builtin[local]:
  ∀cx bt es.
    (∀s'' x t.
       check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY scope_preserving_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Builtin bt es) st = (res, st') ⇒
       scope_preserving_expr (Builtin bt es) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), scope_preserving_expr_def, ignore_bind_def,
      check_def, assert_def, return_def, raise_def, get_accounts_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_builtin cx s''.accounts bt vs` >> gvs[return_def, raise_def]) >>
  first_x_assum drule >> gvs[ETA_THM]
QED

Theorem case_Pop[local]:
  ∀cx bt.
    (∀st res st'.
       eval_expr cx (Pop bt) st = (res, st') ⇒
       scope_preserving_expr (Pop bt) ⇒ st.scopes = st'.scopes)
Proof
  rw[scope_preserving_expr_def]
QED

Theorem case_TypeBuiltin[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY scope_preserving_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (TypeBuiltin tb typ es) st = (res, st') ⇒
       scope_preserving_expr (TypeBuiltin tb typ es) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), scope_preserving_expr_def, ignore_bind_def,
      check_def, assert_def, return_def, raise_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >> gvs[return_def, raise_def]) >>
  first_x_assum drule >> gvs[ETA_THM]
QED

Theorem case_Send[local]:
  ∀cx es drv.
    (∀s'' x t.
       check (LENGTH es = 2) "Send args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY scope_preserving_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Call Send es drv) st = (res, st') ⇒
       scope_preserving_expr (Call Send es drv) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), scope_preserving_expr_def, ignore_bind_def,
      check_def, assert_def, return_def, raise_def, lift_option_def] >>
  TRY (drule transfer_value_scopes >> strip_tac) >>
  TRY (Cases_on `dest_NumV (EL 1 vs)` >> gvs[return_def, raise_def]) >>
  TRY (Cases_on `dest_AddressV (HD vs)` >> gvs[return_def, raise_def]) >>
  first_x_assum drule >> gvs[ETA_THM]
QED

Theorem case_ExtCall[local]:
  ∀cx is_static func_name arg_types ret_type es drv.
    (∀s'' vs t s'3' t' s'4' target_addr t'' s'5' value_opt arg_vals t'3'
         s'6' ts t'4' s'7' calldata t'5' s'8' accounts t'6' s'9' tStorage
         t'7' s'10' t'8' success accounts' tStorage' s'11' t'9' s'12' t'10'
         s'13' t'11'.
       eval_exprs cx es s'' = (INL vs,t) ∧
       check (vs ≠ []) "ExtCall no target" s'3' = (INL (),t') ∧
       lift_option (dest_AddressV (HD vs))
         "ExtCall target not address" s'4' = (INL target_addr,t'') ∧
       (if is_static then return (NONE,TL vs)
        else do
          check (TL vs ≠ []) "ExtCall no value";
          v <- lift_option (dest_NumV (HD (TL vs))) "ExtCall value not int";
          return (SOME v,TL (TL vs))
        od) s'5' = (INL (value_opt,arg_vals),t'3') ∧
       lift_option (get_self_code cx)
         "ExtCall get_self_code" s'6' = (INL ts,t'4') ∧
       lift_option (build_ext_calldata (type_env ts) func_name arg_types arg_vals)
         "ExtCall build_calldata" s'7' = (INL calldata,t'5') ∧
       get_accounts s'8' = (INL accounts,t'6') ∧
       get_transient_storage s'9' = (INL tStorage,t'7') ∧
       lift_option (run_ext_call cx.txn.target target_addr calldata value_opt
                      accounts tStorage (vyper_to_tx_params cx.txn))
         "ExtCall run failed" s'10' = (INL (success,[],accounts',tStorage'),t'8') ∧
       check success "ExtCall reverted" s'11' = (INL (),t'9') ∧
       update_accounts (K accounts') s'12' = (INL (),t'10') ∧
       update_transient (K tStorage') s'13' = (INL (),t'11') ∧
       IS_SOME drv ⇒
       ∀st res st'.
         eval_expr cx (THE drv) st = (res,st') ⇒
         scope_preserving_expr (THE drv) ⇒ st.scopes = st'.scopes) ∧
    (∀st res st'.
       eval_exprs cx es st = (res, st') ⇒ EVERY scope_preserving_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Call (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res, st') ⇒
       scope_preserving_expr (Call (ExtCall is_static (func_name,arg_types,ret_type)) es drv) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  qhdtm_x_assum`scope_preserving_expr`mp_tac >>
  qhdtm_x_assum`eval_expr`mp_tac >>
  rw[scope_preserving_expr_def, evaluate_def, ETA_AX] >>
  qpat_x_assum`_ = (_,_)`mp_tac >>
  simp_tac(srw_ss()++DNF_ss)[
    bind_def, ignore_bind_def, CaseEq"prod", CaseEq"sum", COND_RATOR,
    CaseEq"bool", return_def] >>
  reverse strip_tac >-  rw[] >>
  reverse strip_tac >- rw[check_def, assert_def] >>
  reverse strip_tac >-
    rw[check_def, assert_def, lift_option_def, CaseEq"option",
       raise_def, return_def, option_CASE_rator] >>
  reverse strip_tac >- (
    reverse strip_tac >-
      rw[check_def, assert_def, lift_option_def, CaseEq"option",
         raise_def, return_def, option_CASE_rator] >>
    reverse strip_tac >-
      rw[check_def, assert_def, lift_option_def, CaseEq"option",
         raise_def, return_def, option_CASE_rator] >>
    reverse strip_tac >-
      rw[check_def, assert_def, lift_option_def, CaseEq"option",
         raise_def, return_def, option_CASE_rator] >>
    reverse strip_tac >-
      rw[check_def, assert_def, lift_option_def, CaseEq"option",
         raise_def, return_def, option_CASE_rator] >>
    reverse strip_tac >-
      rw[check_def, assert_def, lift_option_def, CaseEq"option",
         raise_def, return_def, option_CASE_rator, get_accounts_def] >>
    reverse strip_tac >-
      rw[check_def, assert_def, lift_option_def, CaseEq"option",
         raise_def, return_def, option_CASE_rator, get_accounts_def,
         get_transient_storage_def] >>
    reverse strip_tac >-
      rw[check_def, assert_def, lift_option_def, CaseEq"option",
         raise_def, return_def, option_CASE_rator, get_accounts_def,
         get_transient_storage_def] >>
    rpt gen_tac >>
    simp[check_def, assert_def, lift_option_def, get_accounts_def,
         get_transient_storage_def, return_def] >>
    pairarg_tac >>
    simp[bind_def, assert_def, update_accounts_def, update_transient_def, return_def,
         lift_sum_def] >>
    simp[CaseEq"option", raise_def, return_def, option_CASE_rator] >>
    rw[]
    >- (
      last_x_assum drule >>
      simp[check_def, assert_def, lift_option_def, return_def, bind_def,
           ignore_bind_def, get_accounts_def, get_transient_storage_def,
           option_CASE_rator, update_accounts_def, update_transient_def] >>
      disch_then $ drule_at Any >> simp[] >>
      gvs[IS_SOME_EXISTS] >>
      first_x_assum drule \\ rw[] >>
      gvs[CaseEq"option",CaseEq"prod",raise_def] >>
      first_x_assum irule >>
      goal_assum drule )
    \\ pop_assum mp_tac
    \\ simp[bind_def, CaseEq"prod", CaseEq"sum", sum_CASE_rator]
    \\ srw_tac[DNF_ss][return_def,raise_def] \\ rw[] )
 \\ reverse strip_tac
 >- rw[check_def, assert_def, lift_option_def, CaseEq"option",
       raise_def, return_def, option_CASE_rator, get_accounts_def,
       get_transient_storage_def]
 \\ reverse strip_tac
 >- rw[check_def, assert_def, lift_option_def, CaseEq"option",
       raise_def, return_def, option_CASE_rator, get_accounts_def,
       get_transient_storage_def]
 \\ reverse strip_tac
 >- rw[check_def, assert_def, lift_option_def, CaseEq"option",
       raise_def, return_def, option_CASE_rator, get_accounts_def,
       get_transient_storage_def]
 \\ reverse strip_tac
 >- rw[check_def, assert_def, lift_option_def, CaseEq"option",
       raise_def, return_def, option_CASE_rator, get_accounts_def,
       get_transient_storage_def]
 \\ reverse strip_tac
 >- rw[check_def, assert_def, lift_option_def, CaseEq"option",
       raise_def, return_def, option_CASE_rator, get_accounts_def,
       get_transient_storage_def] >>
  rpt gen_tac >>
  simp[check_def, assert_def, lift_option_def, get_accounts_def,
       get_transient_storage_def, return_def] >>
  pairarg_tac >>
  simp[bind_def, assert_def, update_accounts_def, update_transient_def, return_def,
       lift_sum_def] >>
  simp[CaseEq"option", raise_def, return_def, option_CASE_rator] >>
  rw[]
  >- (
    last_x_assum drule >>
    simp[check_def, assert_def, lift_option_def, return_def, bind_def,
         ignore_bind_def, get_accounts_def, get_transient_storage_def,
         option_CASE_rator, update_accounts_def, update_transient_def] >>
    disch_then $ drule_at Any >> simp[] >>
    gvs[IS_SOME_EXISTS] >>
    first_x_assum drule \\ rw[] >>
    gvs[CaseEq"option",CaseEq"prod",raise_def] >>
    first_x_assum irule >>
    goal_assum drule )
  \\ pop_assum mp_tac
  \\ simp[bind_def, CaseEq"prod", CaseEq"sum", sum_CASE_rator]
  \\ srw_tac[DNF_ss][return_def,raise_def] \\ rw[]
QED

(* Case: IntCall - the complex case with finally/pop_function.

   The key is that get_scopes saves prev = st.scopes before entering function,
   and finally ... (pop_function prev) restores scopes to prev at the end,
   regardless of whether the function body succeeded or failed. *)
Theorem case_IntCall[local]:
  ∀cx src_id_opt fn es drv.
    (* IH from evaluate_ind for eval_stmts in function body - not needed for scopes *)
    (* IH for eval_exprs on arguments *)
    (∀s'' x t s'3' ts t' s'4' tup t'' stup args sstup dflts sstup2 ret ss s'5' x' t'3'.
       check (¬MEM (src_id_opt, fn) cx.stk) "recursion" s'' = (INL x, t) ∧
       lift_option (get_module_code cx src_id_opt) "IntCall get_module_code" s'3' = (INL ts, t') ∧
       lift_option (lookup_callable_function cx.in_deploy fn ts) "IntCall lookup_function" s'4' = (INL tup, t'') ∧
       stup = SND tup ∧ args = FST stup ∧ sstup = SND stup ∧
       dflts = FST sstup ∧ sstup2 = SND sstup ∧
       ret = FST sstup2 ∧ ss = SND sstup2 ∧
       check (LENGTH args = LENGTH es) "IntCall args length" s'5' = (INL x', t'3') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY scope_preserving_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Call (IntCall (src_id_opt, fn)) es drv) st = (res, st') ⇒
       scope_preserving_expr (Call (IntCall (src_id_opt, fn)) es drv) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, assert_def, lift_option_def, get_scopes_def, push_function_def,
       pop_function_def, set_scopes_def, scope_preserving_expr_def] >>
  strip_tac >> gvs[return_def, raise_def] >>
  TRY (drule_all finally_set_scopes >> strip_tac >> gvs[]) >>
  TRY (Cases_on `safe_cast rtv rv` >> gvs[return_def, raise_def]) >>
  TRY (gvs[CaseEq"option", option_CASE_rator, raise_def, return_def]) >>
  TRY (Cases_on `bind_arguments (type_env ts) (FST (SND tup)) vs` >> gvs[return_def, raise_def]) >>
  TRY (Cases_on `lookup_callable_function cx.in_deploy fn ts` >> gvs[return_def, raise_def]) >>
  TRY (Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]) >>
  TRY (last_x_assum mp_tac >> simp[check_def, assert_def, return_def, lift_option_def] >>
       strip_tac >> first_x_assum drule >> gvs[scope_preserving_expr_def] >> metis_tac[])
QED

Theorem case_eval_exprs_nil[local]:
  ∀cx.
    (∀st res st'.
       eval_exprs cx [] st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_exprs_cons[local]:
  ∀cx e es.
    (∀s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv, t) ∧ get_Value tv s'3' = (INL v, t') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY scope_preserving_expr es ⇒ st.scopes = st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ scope_preserving_expr e ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_exprs cx (e::es) st = (res, st') ⇒
       EVERY scope_preserving_expr (e::es) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  `st.scopes = s''.scopes` by (first_x_assum drule >> simp[]) >>
  `s'³'.scopes = s'⁴'.scopes` by (
    last_x_assum (qspecl_then [`st`, `tv`, `s''`, `s''`, `v''`, `s'³'`] mp_tac) >>
    simp[]) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   Main Mutual Induction Theorem

   Assembles individual case lemmas into the full mutual induction.
   The key insight is that we prove the same scopes-preserving property
   for ALL evaluate functions (including statements), but for statements
   we get it for free since we set their predicates to T (trivially true).

   We use a specialized version of evaluate_ind with:
   - P0-P6 (statement predicates) = λcx args. T
   - P7 (eval_expr predicate) = scopes preservation with scope_preserving_expr
   - P8 (eval_exprs predicate) = scopes preservation with EVERY scope_preserving_expr
   ------------------------------------------------------------------------ *)

(* Derive specialized induction principle for expr_scopes_mutual.
   This encapsulates the SML needed to specialize evaluate_ind. *)
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (g:assignment_target). T``
  val p4 = ``\(cx:evaluation_context) (gs:assignment_target list). T``
  val p5 = ``\(cx:evaluation_context) (t:base_assignment_target). T``
  val p6 = ``\(cx:evaluation_context) (nm:num) (body:stmt list) (vs:value list). T``
  val p7 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> scope_preserving_expr e ==> st.scopes = st'.scopes``
  val p8 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> EVERY scope_preserving_expr es ==> st.scopes = st'.scopes``
  val spec_ind = SPECL [p0, p1, p2, p3, p4, p5, p6, p7, p8] evaluate_ind
  val spec_ind_beta = CONV_RULE (DEPTH_CONV BETA_CONV) spec_ind
in
  val expr_scopes_ind_principle = save_thm("expr_scopes_ind_principle", spec_ind_beta)
end

(* Main mutual induction. *)
Theorem expr_scopes_mutual[local]:
  (∀cx e st res st'.
     eval_expr cx e st = (res, st') ⇒ scope_preserving_expr e ⇒ st.scopes = st'.scopes) ∧
  (∀cx es st res st'.
     eval_exprs cx es st = (res, st') ⇒ EVERY scope_preserving_expr es ⇒ st.scopes = st'.scopes)
Proof
  (* Proof assembles all case lemmas via the specialized induction principle.

     The case lemmas have `x` in their IH hypotheses, but the induction
     principle specializes to `()` (the unit value from check). We simplify
     the lemmas to match by using SIMP_RULE. *)
  let
    (* Simplify case lemmas to specialize unit-typed variables *)
    val case_Builtin' = SIMP_RULE (srw_ss()) [] case_Builtin
    val case_TypeBuiltin' = SIMP_RULE (srw_ss()) [] case_TypeBuiltin
    val case_Send' = SIMP_RULE (srw_ss()) [] case_Send
    val case_ExtCall' = SIMP_RULE (srw_ss()) [] case_ExtCall
    val case_IntCall' = SIMP_RULE (srw_ss()) [] case_IntCall
    val case_eval_exprs_cons' = SIMP_RULE (srw_ss()) [] case_eval_exprs_cons
  in
    MP_TAC expr_scopes_ind_principle >> impl_tac >- (
      rpt conj_tac >> TRY (simp[]) >-
      (* Name *)
      metis_tac[case_Name] >-
      (* TopLevelName *)
      metis_tac[case_TopLevelName] >-
      (* FlagMember *)
      metis_tac[case_FlagMember] >-
      (* IfExp *)
      ACCEPT_TAC case_IfExp >-
      (* Literal *)
      metis_tac[case_Literal] >-
      (* StructLit *)
      metis_tac[case_StructLit] >-
      (* Subscript *)
      ACCEPT_TAC case_Subscript >-
      (* Attribute *)
      ACCEPT_TAC case_Attribute >-
      (* Builtin *)
      ACCEPT_TAC case_Builtin' >-
      (* Pop *)
      ACCEPT_TAC case_Pop >-
      (* TypeBuiltin *)
      ACCEPT_TAC case_TypeBuiltin' >-
      (* Send *)
      ACCEPT_TAC case_Send' >-
      (* ExtCall - covers both static and non-static *)
      ACCEPT_TAC case_ExtCall' >-
      (* IntCall *)
      ACCEPT_TAC case_IntCall' >-
      (* eval_exprs [] *)
      ACCEPT_TAC case_eval_exprs_nil >-
      (* eval_exprs cons *)
      ACCEPT_TAC case_eval_exprs_cons'
    ) >>
    simp[]
  end
QED

(* ------------------------------------------------------------------------
   Main Theorems

   Extracts the eval_expr/eval_exprs cases from the mutual induction.
   ------------------------------------------------------------------------ *)

Theorem eval_expr_preserves_scopes:
  ∀cx e st res st'.
    scope_preserving_expr e ∧ eval_expr cx e st = (res, st') ⇒
    st.scopes = st'.scopes
Proof
  metis_tac[expr_scopes_mutual]
QED

Theorem eval_exprs_preserves_scopes:
  ∀cx es st res st'.
    EVERY scope_preserving_expr es ∧ eval_exprs cx es st = (res, st') ⇒
    st.scopes = st'.scopes
Proof
  metis_tac[expr_scopes_mutual]
QED
