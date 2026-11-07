Theory vyperEvalPureExpr

Ancestors
  vyperPureExpr vyperLookup vyperState vyperStatePreservation vyperPlaceFrames
  vyperStorageTrace

(* ===== eval_pure_expr / eval_pure_exprs ===== *)
(*
  eval_pure_expr  : cx -> st -> expr -> eval_result option
  eval_pure_exprs : cx -> st -> expr list -> value list option

  eval_pure_expr evaluates a pure expression to the same result as eval_expr.
  Locations stay unresolved until an operation needs their contents.

  eval_pure_exprs evaluates a list of pure expressions, materialising
  each result to a value (reading from storage if needed).
*)

Definition eval_pure_expr_def:
  (* Base cases *)
  eval_pure_expr cx st (Name _ id) =
    (if IS_SOME (lookup_scopes id st.scopes)
     then SOME (PlaceR (MemoryPlace id [])) else NONE) ∧

  eval_pure_expr cx st (TopLevelName ty nsid) =
    (case eval_expr cx (TopLevelName ty nsid) st of
     | (INL tv, _) => SOME tv
     | _ => NONE) ∧

  eval_pure_expr cx st (FlagMember _ nsid mid) =
    lookup_flag_member cx nsid mid ∧

  eval_pure_expr cx st (Literal _ l) =
    SOME (Value (evaluate_literal l)) ∧

  (* Conditional *)
  eval_pure_expr cx st (IfExp _ cond et ef) =
    (case eval_pure_expr cx st cond of
     | SOME res =>
       (case read_result cx res st of
        | (INL (BoolV b), _) =>
          (case (if b then eval_pure_expr cx st et else eval_pure_expr cx st ef) of
           | SOME selected =>
             (case conditional_result cx selected st of
              | (INL result, _) => SOME result
              | _ => NONE)
           | NONE => NONE)
        | _ => NONE)
     | NONE => NONE) ∧

  (* Struct literal *)
  eval_pure_expr cx st (StructLit _ src kes) =
    (case eval_pure_exprs cx st (MAP SND kes) of
     | SOME vs => SOME (Value (StructV (ZIP (MAP FST kes, vs))))
     | NONE => NONE) ∧

  (* Subscript *)
  eval_pure_expr cx st (Subscript ty e1 e2) =
    (case eval_pure_expr cx st e1 of
     | SOME tv1 =>
       (case eval_pure_expr cx st e2 of
        | SOME idx =>
          (case read_result cx idx st of
           | (INL v2, _) =>
             (case select_result cx (expr_type e1) tv1 (ValueSubscript v2) st of
              | (INL result, _) => SOME result
              | _ => NONE)
           | _ => NONE)
        | _ => NONE)
     | NONE => NONE) ∧

  (* Attribute access *)
  eval_pure_expr cx st (Attribute _ e id) =
    (case eval_pure_expr cx st e of
     | SOME res =>
       (case select_result cx (expr_type e) res (AttrSubscript id) st of
        | (INL result, _) => SOME result
        | _ => NONE)
     | _ => NONE) ∧

  (* General builtins *)
  eval_pure_expr cx st (Builtin ty bt es) =
    (if bt = Len then
       (case es of
        | [e] =>
          (case eval_pure_expr cx st e of
           | SOME tv =>
             (case result_array_length cx tv st of
              | (INL len, _) => SOME (Value (IntV (&len)))
              | _ => NONE)
           | NONE => NONE)
        | _ => NONE)
     else if builtin_args_length_ok bt (LENGTH es) ∧ ¬precompile_builtin bt then
       (case eval_pure_exprs cx st es of
        | SOME vs =>
          (case evaluate_builtin cx st.accounts ty bt (MAP expr_type es) vs of
           | INL v => SOME (Value v)
           | INR _ => NONE)
        | NONE => NONE)
     else NONE) ∧

  (* General type builtins *)
  eval_pure_expr cx st (TypeBuiltin _ tb typ es) =
    (if type_builtin_args_length_ok tb (LENGTH es) then
       (case eval_pure_exprs cx st es of
        | SOME vs =>
          (case evaluate_type_builtin cx tb typ (MAP expr_type es) vs of
           | INL v => SOME (Value v)
           | INR _ => NONE)
        | NONE => NONE)
     else NONE) ∧

  (* Non-pure expressions *)
  eval_pure_expr cx st _ = NONE ∧

  (* eval_pure_exprs: evaluate list, materialising each result *)
  eval_pure_exprs cx st [] = SOME [] ∧

  eval_pure_exprs cx st (e::es) =
    (case eval_pure_expr cx st e of
     | SOME tv =>
       (case read_result cx tv st of
        | (INL v, _) =>
          (case eval_pure_exprs cx st es of
           | SOME vs => SOME (v::vs)
           | NONE => NONE)
        | _ => NONE)
     | NONE => NONE)
Termination
  WF_REL_TAC `measure (sum_size
    (\(cx:evaluation_context, st:evaluation_state, e). expr_size e)
    (\(cx:evaluation_context, st:evaluation_state, es).
       list_size expr_size es))` >>
  rpt gen_tac >>
  Induct_on `kes` >>
  simp[pairTheory.FORALL_PROD, basicSizeTheory.pair_size_def]
End

(* Convenience wrapper: evaluate pure expression to value *)
Definition eval_pure_value_def:
  eval_pure_value cx st e =
    (case eval_pure_expr cx st e of
     | SOME tv =>
       (case read_result cx tv st of
        | (INL v, _) => SOME v
        | _ => NONE)
     | NONE => NONE)
End

val monadic_defs =
  [vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
   vyperStateTheory.return_def,
   vyperStateTheory.lift_sum_def, vyperStateTheory.get_scopes_def,
   vyperStateTheory.get_accounts_def, vyperStateTheory.type_check_def,
   vyperStateTheory.assert_def, vyperStateTheory.raise_def];

Theorem trace_result_transport[local]:
  storage_trace_frame f ==>
  FST (f (st with storage_trace := observations)) = FST (f st)
Proof
  pure_rewrite_tac[storage_trace_frame_def] >> strip_tac >>
  first_assum (qspecl_then [`st`, `observations`] mp_tac) >>
  first_x_assum (qspecl_then [`st`, `st.storage_trace`] mp_tac) >>
  Cases_on `f (st with storage_trace := [])` >> simp[]
QED

Theorem trace_execution_transport[local]:
  storage_trace_frame f /\ f st = (r, st with storage_trace := q) ==>
  ?q'. f (st with storage_trace := p) = (r, st with storage_trace := q')
Proof
  pure_rewrite_tac[storage_trace_frame_def] >> strip_tac >>
  first_assum (qspecl_then [`st`, `p`] mp_tac) >>
  first_x_assum (qspecl_then [`st`, `st.storage_trace`] mp_tac) >>
  Cases_on `f (st with storage_trace := [])` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  qexists_tac `p ++ r'.storage_trace` >>
  qpat_x_assum `st with storage_trace := q = _` mp_tac >>
  simp[evaluation_state_component_equality]
QED

Theorem observation_trace_results[local]:
  FST (read_result cx r (st with storage_trace := p)) = FST (read_result cx r st) /\
  FST (select_result cx ty r sb (st with storage_trace := p)) = FST (select_result cx ty r sb st) /\
  FST (conditional_result cx r (st with storage_trace := p)) = FST (conditional_result cx r st) /\
  FST (result_array_length cx r (st with storage_trace := p)) = FST (result_array_length cx r st)
Proof
  rpt conj_tac >> irule trace_result_transport >>
  simp[storage_trace_frame_read_result, storage_trace_frame_select,
       storage_trace_frame_conditional_result, storage_trace_frame_array_length]
QED

Theorem evaluator_trace_results[local]:
  FST (eval_expr cx e (st with storage_trace := p)) = FST (eval_expr cx e st) /\
  FST (eval_exprs cx es (st with storage_trace := p)) = FST (eval_exprs cx es st)
Proof
  conj_tac >> irule trace_result_transport >>
  metis_tac[evaluate_storage_trace_frame]
QED

Theorem read_result_trace[local]:
  read_result cx r (st with storage_trace := p) =
  (FST (read_result cx r st), st with storage_trace := p)
Proof
  Cases_on `read_result cx r (st with storage_trace := p)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  mp_tac (cj 1 observation_trace_results) >> simp[]
QED

Theorem read_result_storage_trace:
  read_result cx r (st with storage_trace := p) =
  (FST (read_result cx r st), st with storage_trace := p)
Proof
  simp[read_result_trace]
QED

Theorem conditional_result_trace[local]:
  conditional_result cx r (st with storage_trace := p) =
  (FST (conditional_result cx r st), st with storage_trace := p)
Proof
  Cases_on `conditional_result cx r (st with storage_trace := p)` >>
  drule conditional_result_state >> strip_tac >> gvs[] >>
  mp_tac (cj 3 observation_trace_results) >> simp[]
QED

Theorem result_array_length_trace[local]:
  result_array_length cx r (st with storage_trace := p) =
  (FST (result_array_length cx r st), st with storage_trace := p)
Proof
  Cases_on `result_array_length cx r (st with storage_trace := p)` >>
  drule result_array_length_state >> strip_tac >> gvs[] >>
  mp_tac (cj 4 observation_trace_results) >> simp[]
QED

Theorem select_result_trace[local]:
  select_result cx ty r sb st = (v,s) ==>
  !p. ?q. select_result cx ty r sb (st with storage_trace := p) =
    (v,st with storage_trace := q)
Proof
  strip_tac >> drule select_result_state >> strip_tac >> gen_tac >>
  irule trace_execution_transport >>
  simp[storage_trace_frame_select] >> metis_tac[]
QED

Theorem eval_expr_trace[local]:
  eval_expr cx e st = (r,st with storage_trace := q) ==>
  !p. ?q'. eval_expr cx e (st with storage_trace := p) =
    (r,st with storage_trace := q')
Proof
  rpt strip_tac >> irule trace_execution_transport >>
  metis_tac[evaluate_storage_trace_frame]
QED

Theorem eval_exprs_trace[local]:
  eval_exprs cx es st = (r,st with storage_trace := q) ==>
  !p. ?q'. eval_exprs cx es (st with storage_trace := p) =
    (r,st with storage_trace := q')
Proof
  rpt strip_tac >> irule trace_execution_transport >>
  metis_tac[evaluate_storage_trace_frame]
QED

Theorem projection_pair[local]:
  FST z = r ==> ?u. z = (r,u)
Proof
  Cases_on `z` >> simp[]
QED

Theorem trace_execution_back[local]:
  storage_trace_frame f /\ f (st with storage_trace := p) = (r,t) ==>
  ?u. f st = (r,u)
Proof
  strip_tac >> irule projection_pair >>
  drule trace_result_transport >>
  disch_then (qspecl_then [`st`, `p`] mp_tac) >> simp[]
QED

Theorem eval_expr_trace_back[local]:
  eval_expr cx e (st with storage_trace := p) = (r,t) ==>
  ?u. eval_expr cx e st = (r,u)
Proof
  strip_tac >> irule trace_execution_back >>
  metis_tac[evaluate_storage_trace_frame]
QED

Theorem eval_exprs_trace_back[local]:
  eval_exprs cx es (st with storage_trace := p) = (r,t) ==>
  ?u. eval_exprs cx es st = (r,u)
Proof
  strip_tac >> irule trace_execution_back >>
  metis_tac[evaluate_storage_trace_frame]
QED

Theorem select_result_trace_back[local]:
  select_result cx ty r sb (st with storage_trace := p) = (v,t) ==>
  ?u. select_result cx ty r sb st = (v,u)
Proof
  strip_tac >> irule trace_execution_back >>
  metis_tac[storage_trace_frame_select]
QED

(* ===== Forward direction: eval_pure_expr/exprs SOME ⇒ eval_expr/exprs INL ===== *)

Theorem eval_pure_to_eval_mutual:
  (∀cx st e v.
    eval_pure_expr cx st e = SOME v ⇒
    ?observations. eval_expr cx e st =
      (INL v, st with storage_trace := observations)) ∧
  (∀cx st es vs.
    eval_pure_exprs cx st es = SOME vs ⇒
    ?observations. eval_exprs cx es st =
      (INL vs, st with storage_trace := observations))
Proof
  ho_match_mp_tac eval_pure_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  (* Name *)
  >- (gvs[Once eval_pure_expr_def] >>
      simp[Once vyperInterpreterTheory.evaluate_def,
           vyperStateTheory.get_scopes_def, vyperStateTheory.type_check_def,
           vyperStateTheory.assert_def] >> simp monadic_defs >>
      qexists_tac `st.storage_trace` >> simp[])
  (* TopLevelName *)
  >- (fs[Once eval_pure_expr_def] >>
      Cases_on `eval_expr cx (TopLevelName ty nsid) st` >>
      gvs[AllCaseEqs()] >>
      drule_at Any eval_expr_preserves_state >> simp[pure_expr_def] >>
      metis_tac[])
  (* FlagMember *)
  >- (fs[Once eval_pure_expr_def,
         Once vyperInterpreterTheory.evaluate_def] >>
      qexists_tac `st.storage_trace` >> simp[] >>
      metis_tac[lookup_flag_member_to_lookup_flag_mem])
  (* Literal *)
  >- (fs[Once eval_pure_expr_def,
         Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >> qexists_tac `st.storage_trace` >> simp[])
  (* IfExp *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >> gvs[AllCaseEqs()] >>
      imp_res_tac read_result_state >>
      imp_res_tac conditional_result_state >> gvs[] >>
      simp[vyperInterpreterTheory.switch_BoolV_def] >>
      simp monadic_defs >>
      simp[read_result_trace] >>
      qpat_x_assum `eval_expr _ _ st = (INL selected,_)`
        (mp_then Any (qspec_then `observations'` strip_assume_tac) eval_expr_trace) >>
      simp[conditional_result_trace] >>
      metis_tac[])
  (* StructLit *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      Cases_on `src` >> simp[LET_DEF] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp (LET_DEF :: monadic_defs) >> metis_tac[])
  (* Subscript *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      imp_res_tac read_result_state >>
      imp_res_tac select_result_state >> gvs[] >>
      qpat_assum `eval_expr _ _ st = (INL idx,_)`
        (mp_then Any (qspec_then `observations'` strip_assume_tac) eval_expr_trace) >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >> simp[read_result_trace] >>
      metis_tac[select_result_trace])
  (* Attribute *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      imp_res_tac select_result_state >> gvs[] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >> metis_tac[select_result_trace])
  (* Builtin *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      `bt <> Env MsgGas` by
        (strip_tac >>
         gvs[AllCaseEqs(), vyperStatePreservationTheory.evaluate_builtin_MsgGas]) >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
      gvs[AllCaseEqs()] >>
      simp monadic_defs >>
      imp_res_tac result_array_length_state >>
      simp[vyperContextTheory.builtin_args_length_ok_def] >>
      simp[vyperStateTheory.get_accounts_def,
           vyperInterpreterTheory.precompile_call_success_def,
           vyperInterpreterTheory.precompile_builtin_def] >>
      gvs[] >> simp monadic_defs >>
      simp[result_array_length_trace] >> metis_tac[])
  (* TypeBuiltin *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
      simp monadic_defs >> metis_tac[])
  (* Pop - impossible *)
  >- fs[eval_pure_expr_def]
  (* Call - impossible *)
  >- fs[eval_pure_expr_def]
  (* [] case *)
  >- (fs[Once eval_pure_expr_def, Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >> qexists_tac `st.storage_trace` >> simp[])
  (* e::es case *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      drule read_result_state >> strip_tac >> gvs[] >>
      drule eval_exprs_trace >>
      disch_then (qspec_then `observations'` strip_assume_tac) >>
      simp[read_result_trace] >> metis_tac[])
QED

Theorem eval_pure_expr_to_eval_expr_some:
  ∀cx st e v.
    eval_pure_expr cx st e = SOME v ⇒
    ?observations. eval_expr cx e st =
      (INL v, st with storage_trace := observations)
Proof
  metis_tac[eval_pure_to_eval_mutual]
QED

Theorem eval_expr_to_eval_pure_expr_none:
  ∀cx st st' e err.
    eval_expr cx e st = (INR err, st') ⇒
    eval_pure_expr cx st e = NONE
Proof
  rpt strip_tac >>
  CCONTR_TAC >> gvs[] >>
  Cases_on `eval_pure_expr cx st e` >> gvs[] >>
  drule (eval_pure_to_eval_mutual |> CONJUNCT1) >> gvs[]
QED

(* ===== Reverse direction: eval_expr/exprs INL ⇒ eval_pure_expr/exprs SOME ===== *)

Theorem eval_to_eval_pure_mutual:
  (∀cx st e. ∀st' v.
    pure_expr e ∧ eval_expr cx e st = (INL v, st') ⇒
    eval_pure_expr cx st e = SOME v) ∧
  (∀cx st es. ∀st' vs.
    EVERY pure_expr es ∧ eval_exprs cx es st = (INL vs, st') ⇒
    eval_pure_exprs cx st es = SOME vs)
Proof
  ho_match_mp_tac eval_pure_expr_ind >>
  rpt conj_tac
  (* Name *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once vyperInterpreterTheory.evaluate_def] >>
      gvs monadic_defs >>
      gvs[AllCaseEqs()] >> simp[Once eval_pure_expr_def])
  (* TopLevelName *)
  >- (rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      Cases_on `eval_expr cx (TopLevelName ty nsid) st` >>
      gvs[AllCaseEqs()])
  (* FlagMember *)
  >- (rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[Once vyperInterpreterTheory.evaluate_def] >>
      irule lookup_flag_mem_to_lookup_flag_member_some >>
      metis_tac[])
  (* Literal *)
  >- (rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[Once vyperInterpreterTheory.evaluate_def] >>
      gvs monadic_defs)
  (* IfExp *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      imp_res_tac eval_expr_preserves_state >> gvs[] >>
      gvs monadic_defs >> gvs[AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >>
      gvs[vyperInterpreterTheory.switch_BoolV_def] >>
      gvs monadic_defs >> gvs[AllCaseEqs()] >>
      imp_res_tac eval_expr_preserves_state >> gvs[] >>
      imp_res_tac conditional_result_state >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `v'' = BoolV T` >> gvs monadic_defs >>
      Cases_on `v'' = BoolV F` >> gvs monadic_defs >>
      gvs[AllCaseEqs()] >>
      qpat_x_assum `s'' = st with storage_trace := _` SUBST_ALL_TAC >>
      gvs[read_result_trace] >>
      drule projection_pair >> strip_tac >>
      imp_res_tac eval_expr_trace_back >>
      `s'³' = (st with storage_trace := s''.storage_trace)
                 with storage_trace := s'³'.storage_trace` by metis_tac[] >>
      qpat_x_assum `s'³' = _` SUBST_ALL_TAC >>
      gvs[conditional_result_trace] >>
      imp_res_tac projection_pair >> metis_tac[])
  (* StructLit *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      Cases_on `src` >>
      simp[Once vyperInterpreterTheory.evaluate_def, LET_DEF] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      `EVERY pure_expr (MAP SND kes)` by gvs[listTheory.EVERY_EL] >>
      gvs[])
  (* Subscript *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      `s'' = st with storage_trace := s''.storage_trace` by
        metis_tac[eval_expr_preserves_state] >>
      pop_assum SUBST_ALL_TAC >>
      drule eval_expr_trace_back >> strip_tac >>
      `s'³' = (st with storage_trace := s''.storage_trace)
                 with storage_trace := s'³'.storage_trace` by
        metis_tac[eval_expr_preserves_state] >>
      pop_assum SUBST_ALL_TAC >>
      gvs[read_result_trace] >>
      imp_res_tac projection_pair >>
      imp_res_tac select_result_trace_back >> metis_tac[])
  (* Attribute *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      `s'' = st with storage_trace := s''.storage_trace` by
        metis_tac[eval_expr_preserves_state] >>
      pop_assum SUBST_ALL_TAC >>
      drule select_result_trace_back >> strip_tac >> gvs[])
  (* Builtin *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      Cases_on `bt = Len` >> gvs[]
      >- (* Len case *)
         (`LENGTH es = 1` by
            gvs[vyperContextTheory.builtin_args_length_ok_def] >>
          Cases_on `es` >> gvs[] >>
          fs[vyperStateTheory.bind_def] >>
          gvs[AllCaseEqs()] >>
          rename1 `eval_expr cx h st = (INL tv, s1)` >>
          rename1 `result_array_length cx tv s1 = (INL len, s2)` >>
          `s1 = st with storage_trace := s1.storage_trace` by
            metis_tac[eval_expr_preserves_state] >>
          pop_assum SUBST_ALL_TAC >>
          gvs[result_array_length_trace, vyperStateTheory.return_def] >>
          imp_res_tac projection_pair >> metis_tac[])
      >- (* non-Len case *)
         (`EVERY pure_expr es` by gvs[listTheory.EVERY_EL] >>
          fs[vyperStateTheory.bind_def] >>
          gvs[AllCaseEqs()] >>
          rename1 `eval_exprs cx es st = (INL vs, s1)` >>
          `eval_pure_exprs cx st es = SOME vs` by metis_tac[] >>
          simp[] >>
          `s1 = st with storage_trace := s1.storage_trace` by
            metis_tac[eval_exprs_preserves_state] >>
          pop_assum SUBST_ALL_TAC >>
          fs[vyperStateTheory.get_accounts_def, vyperStateTheory.return_def,
             vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
             vyperInterpreterTheory.precompile_call_success_def] >>
          Cases_on `evaluate_builtin cx st.accounts ty bt (MAP expr_type es) vs` >>
          gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]))
  (* TypeBuiltin *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
      simp[vyperStateTheory.bind_def] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      `EVERY pure_expr es` by gvs[listTheory.EVERY_EL] >>
      rename1 `eval_exprs cx es st = (INL vs, s1)` >>
      `eval_pure_exprs cx st es = SOME vs` by metis_tac[] >>
      simp[] >>
      Cases_on `evaluate_type_builtin cx tb typ (MAP expr_type es) vs` >>
      gvs[vyperStateTheory.lift_sum_def, vyperStateTheory.return_def,
          vyperStateTheory.raise_def])
  (* Pop - impossible *)
  >- simp[pure_expr_def]
  (* Call - impossible *)
  >- simp[pure_expr_def]
  (* [] case *)
  >- (simp[Once eval_pure_expr_def, Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs)
  (* e::es case *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[listTheory.EVERY_DEF] >>
      qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      rename1 `eval_expr cx e st = (INL tv, s1)` >>
      rename1 `read_result cx tv s1 = (INL v, s2)` >>
      `s1 = st with storage_trace := s1.storage_trace` by
        metis_tac[eval_expr_preserves_state] >>
      pop_assum SUBST_ALL_TAC >>
      gvs[read_result_trace] >>
      imp_res_tac projection_pair >>
      imp_res_tac eval_exprs_trace_back >> metis_tac[])
QED

Theorem eval_expr_to_eval_pure_expr_some:
  ∀cx st st' e v.
    pure_expr e ∧ eval_expr cx e st = (INL v, st') ⇒
    eval_pure_expr cx st e = SOME v
Proof
  metis_tac[eval_to_eval_pure_mutual]
QED

Theorem eval_pure_expr_to_eval_expr_none:
  ∀cx st e.
    pure_expr e ∧ eval_pure_expr cx st e = NONE ⇒
    ∃err observations. eval_expr cx e st =
      (INR err, st with storage_trace := observations)
Proof
  rpt strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `(res, st')` >>
  Cases_on `res`
  >- (drule_all (eval_to_eval_pure_mutual |> CONJUNCT1) >> gvs[])
  >- (`st' = st with storage_trace := st'.storage_trace` by
        metis_tac[eval_expr_preserves_state] >> metis_tac[])
QED

(* Pure correspondence exports must not depend on admissions. *)
val () = List.app
  (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail ("pure correspondence proof is not closed: " ^ name)
    end)
  (DB.thms "vyperEvalPureExpr");
