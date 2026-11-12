(* Exact immutables framing for runtime syntax with safe mutation roots. *)
Theory vyperRuntimeWriteSafetyFrame
Ancestors
  list pair option vyperAST vyperContext vyperMisc vyperState
  vyperInterpreter vyperTypeSystem vyperRuntimeWriteSafety
  vyperMachineFrame vyperCallOutcomeFrame vyperStatePreservation
  vyperImmutablesPreservation vyperScopePreservation vyperCreateFrame
  vyperStoragePlaceProvenance vyperEvalFrame vyperPlaceFrames
Libs monadsyntax evalWalkLib

val () = monadsyntax.enable_monad "vyper_evaluation";

(* Instantiate the existing machine-frame leaf catalogue, not its unconditional
   evaluator theorem: mutation leaves need the safe-target induction arm. *)
val imms_relation = ``\(s:evaluation_state) (t:evaluation_state).
  t.immutables = s.immutables``;
val imms_frame_net =
  let
    val rules = [state_rel_frame_bind_guarded, state_rel_frame_try,
      state_rel_frame_finally, state_rel_frame_finally_unless_halt]
    val leaves = [machine_frame_primitives, machine_frame_read_result,
      machine_frame_read_results, machine_frame_reads, machine_frame_select_result,
      machine_frame_extend_place, machine_frame_get_place, machine_frame_read_place,
      machine_frame_place_type_value, machine_frame_new_variable,
      machine_frame_next_gas_reading, machine_frame_precompile_call_success,
      machine_frame_handlers, machine_frame_push_function,
      machine_frame_pop_function, machine_frame_unchanged_reads,
      machine_frame_array_iterator_results]
    fun leaf th = (subst [``machine_frame`` |-> imms_relation] (concl th),
      irule state_rel_frame_machine >> conj_tac
      >- simp[machine_frame_def] >> MATCH_ACCEPT_TAC th)
    val log_leaf =
      (``state_rel_frame ^imms_relation (push_log lg)``,
       simp[state_rel_frame_def] >> metis_tac[push_log_immutables])
  in evalWalkLib.walk_net (map SPEC_ALL rules)
       (log_leaf :: map leaf (List.concat (map (CONJUNCTS o SPEC_ALL) leaves))) end;

val imms_frame_result = BETA_RULE
  (ISPEC imms_relation (Q.GEN `R` state_rel_frame_result));
val IMMS_IH_TAC =
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM imms_frame_result]) >>
  evalWalkLib.IH_TAC {stop = K false, normalise = SIMP_RULE bool_ss
    [oneTheory.one, ignore_bind_def, FST, SND, pair_case_thm, UNCURRY,
     lock_if_nr_def, unlock_if_nr_def]};
val IMMS_STEP = evalWalkLib.STEP {net = imms_frame_net, at = RAND_CONV,
  unfolds = [switch_BoolV_def, ignore_bind_def],
  intros = [CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac, strip_tac, conj_tac,
    CONV_TAC (RAND_CONV ETA_CONV),
    CHANGED_TAC (fn (asl,w) => simp_tac bool_ss
      (List.filter (is_eq o concl) (map (BETA_RULE o ASSUME) asl)) (asl,w))],
  fallbacks = [IMMS_IH_TAC, evalWalkLib.NORMALISE_IH_TAC IMMS_IH_TAC]};
val IMMS_CASE = evalWalkLib.EVAL_CASE all_tac IMMS_STEP;
val IMMS_WRITE =
  qmatch_goalsub_rename_tac `write_place cx pl value` >>
  `!sid id path. pl <> ImmutablePlace sid id path` by metis_tac[] >>
  Cases_on `pl` >> fs[] >> simp[imms_frame_result] >> rpt strip_tac
  >- metis_tac[write_storage_place_immutables] >>
  drule write_memory_place_frame >> strip_tac >> gvs[];

Theorem runtime_writes_frame_mutual:
  (!cx s. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     stmt_writes_ok (runtime_write_root R) s ==>
     !st res st'. eval_stmt cx s st = (res,st') ==> st'.immutables = st.immutables) /\
  (!cx ss. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     stmts_writes_ok (runtime_write_root R) ss ==>
     !st res st'. eval_stmts cx ss st = (res,st') ==> st'.immutables = st.immutables) /\
  (!cx it. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     (case it of Array e => expr_writes_ok (runtime_write_root R) e
       | Range x y => expr_writes_ok (runtime_write_root R) x /\ expr_writes_ok (runtime_write_root R) y) ==>
     !st res st'. eval_iterator cx it st = (res,st') ==> st'.immutables = st.immutables) /\
  (!cx tyv nm body vs. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     stmts_writes_ok (runtime_write_root R) body ==>
     !st res st'. eval_for cx tyv nm body vs st = (res,st') ==> st'.immutables = st.immutables) /\
  (!cx e. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     expr_writes_ok (runtime_write_root R) e ==>
     !st res st'. eval_expr cx e st = (res,st') ==> st'.immutables = st.immutables) /\
  (!cx es. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     EVERY (expr_writes_ok (runtime_write_root R)) es ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> st'.immutables = st.immutables) /\
  (!cx t. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     runtime_write_root R t /\ target_writes_ok (runtime_write_root R) t ==>
     !st res st'. eval_base_place cx t st = (res,st') ==>
       st'.immutables = st.immutables /\
       (!sid id path. res <> INL (PlaceR (ImmutablePlace sid id path)))) /\
  (!cx t. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     runtime_write_root R t /\ target_writes_ok (runtime_write_root R) t ==>
     !st res st'. eval_target_place cx t st = (res,st') ==>
       st'.immutables = st.immutables /\
       (!sid id path. res <> INL (ImmutablePlace sid id path))) /\
  (!cx g v. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     atarget_writes_ok (runtime_write_root R) g ==>
     !st res st'. assign_tuple_targets cx g v st = (res,st') ==> st'.immutables = st.immutables) /\
  (!cx gs vs. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     EVERY (atarget_writes_ok (runtime_write_root R)) gs ==>
     !st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> st'.immutables = st.immutables) /\
  (!cx es. ~cx.in_deploy /\ runtime_write_roots_resolve cx R /\
     runtime_callable_writes_ok (get_module_code cx) R /\
     EVERY (expr_writes_ok (runtime_write_root R)) es ==>
     !st res st'. eval_expr_results cx es st = (res,st') ==> st'.immutables = st.immutables)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget _)`]
  >- (simp[runtime_write_root_def, expr_writes_ok_def] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once evaluate_def] >> strip_tac >> conj_tac
      >- metis_tac[lookup_global_immutables] >>
      fs[runtime_write_roots_resolve_def] >>
      first_x_assum drule >> strip_tac >>
      qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
      simp[lookup_global_def, bind_def, lift_option_type_def, return_def,
           raise_def] >>
      Cases_on `decl` >> rename1 `(di,nm)` >> Cases_on `di` >>
      simp[bind_def, ignore_bind_def, return_def, raise_def,
           record_storage_event_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >~ [`eval_base_place cx (NameTarget _)`]
  >- (simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def, type_check_def,
           assert_def, check_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >~ [`eval_base_place cx (AttributeTarget _ _)`]
  >- (strip_tac >> simp[runtime_write_root_def, expr_writes_ok_def] >>
      strip_tac >> fs[] >> rpt gen_tac >>
      simp[Once evaluate_def] >>
      Cases_on `eval_base_place cx t st` >>
      rename1 `eval_base_place cx t st = (answer,mid)` >>
      first_x_assum drule >> strip_tac >>
      Cases_on `answer` >>
      simp[bind_def, raise_def] >> strip_tac >> gvs[] >>
      conj_tac
      >- (fs[machine_frame_def, state_rel_frame_result] >>
          metis_tac[machine_frame_extend_place, state_rel_frame_result,
                    machine_frame_def]) >>
      rename1 `eval_base_place _ _ _ = (INL operand,_)` >>
      Cases_on `operand` >> fs[] >>
      fs[extend_place_def, bind_def, ignore_bind_def, return_def,
         raise_def, AllCaseEqs()] >>
      rename1 `extend_place _ (PlaceR pl) _ _ = _` >>
      Cases_on `pl` >> fs[] >>
      fs[extend_place_def, extend_memory_place_def, bind_def,
         ignore_bind_def, return_def, raise_def, lift_sum_def, AllCaseEqs()] >>
      gvs[] >> drule extend_storage_place_subregion >>
      strip_tac >> gvs[])
  >~ [`eval_stmt cx (Return (SOME _))`]
  >- (strip_tac >> simp[stmt_writes_ok_def] >> strip_tac >>
      PURE_REWRITE_TAC[GSYM imms_frame_result] >> IMMS_CASE)
  >~ [`eval_base_place cx (SubscriptTarget _ _)`]
  >- suspend "subscript_target"
  >~ [`eval_target_place cx t`]
  >- suspend "target_place"
  >> PURE_REWRITE_TAC[GSYM imms_frame_result,
       stmt_writes_ok_def, expr_writes_ok_def, atarget_writes_ok_def,
       runtime_write_root_def, EVERY_DEF] >>
     rpt strip_tac
  >~ [`eval_stmt cx Pass`]
  >- IMMS_CASE
  >~ [`eval_stmt cx Continue`] >- IMMS_CASE
  >~ [`eval_stmt cx Break`] >- IMMS_CASE
  >~ [`eval_stmt cx (Expr _)`] >- IMMS_CASE
  >~ [`eval_stmt cx (Return NONE)`] >- IMMS_CASE
  >~ [`eval_stmt cx (AnnAssign _ _ _)`] >- IMMS_CASE
  >~ [`eval_stmt cx (If _ _ _)`] >- IMMS_CASE
  >~ [`eval_stmt cx (Log _ _)`]
  >- (IMMS_CASE >> simp[imms_frame_result] >> metis_tac[push_log_immutables])
  >~ [`eval_stmt cx (Raise RaiseBare)`] >- IMMS_CASE
  >~ [`eval_stmt cx (Raise RaiseUnreachable)`] >- IMMS_CASE
  >~ [`eval_stmt cx (Raise (RaiseReason _))`] >- (fs[] >> IMMS_CASE)
  >~ [`eval_stmt cx (Raise (RaiseCustomError _))`]
  >- (fs[] >> IMMS_CASE >> first_x_assum irule >>
      simp[] >> drule order_custom_error_args_perm >>
      metis_tac[sortingTheory.PERM_EVERY])
  >~ [`eval_stmt cx (Assert _ AssertBare)`] >- IMMS_CASE
  >~ [`eval_stmt cx (Assert _ AssertUnreachable)`] >- IMMS_CASE
  >~ [`eval_stmt cx (Assert _ (AssertReason _))`] >- (fs[] >> IMMS_CASE)
  >~ [`eval_stmt cx (Assert _ (AssertCustomError _))`]
  >- (fs[] >> IMMS_CASE >> first_x_assum irule >>
      simp[] >> drule order_custom_error_args_perm >>
      metis_tac[sortingTheory.PERM_EVERY])
  >~ [`eval_stmts cx []`] >- IMMS_CASE
  >~ [`eval_stmts cx (_::_)`] >- IMMS_CASE
  >~ [`eval_iterator cx (Array _)`] >- (fs[] >> IMMS_CASE)
  >~ [`eval_iterator cx (Range _ _)`] >- (fs[] >> IMMS_CASE)
  >~ [`eval_expr cx (Literal _ _)`] >- IMMS_CASE
  >~ [`eval_expr cx (Name _ _)`] >- IMMS_CASE
  >~ [`eval_expr cx (TopLevelName _ _)`] >- IMMS_CASE
  >~ [`eval_expr cx (FlagMember _ _ _)`] >- IMMS_CASE
  >~ [`eval_expr cx (IfExp _ _ _ _)`] >- IMMS_CASE
  >~ [`eval_expr cx (Subscript _ _ _)`] >- IMMS_CASE
  >~ [`eval_expr cx (Attribute _ _ _)`] >- IMMS_CASE
  >~ [`eval_expr cx (StructLit _ _ _)`] >- (IMMS_CASE >> metis_tac[])
  >~ [`eval_exprs cx []`] >- IMMS_CASE
  >~ [`eval_exprs cx (_::_)`] >- IMMS_CASE
  >~ [`eval_expr_results cx []`] >- IMMS_CASE
  >~ [`eval_expr_results cx (_::_)`] >- IMMS_CASE
  >~ [`eval_for cx _ _ _ []`] >- IMMS_CASE
  >~ [`eval_for cx _ _ _ (_::_)`] >- IMMS_CASE
  >~ [`eval_stmt cx (For _ _ _ _ _)`] >- IMMS_CASE
  >~ [`eval_stmt cx (Assign (TupleTarget _) _)`] >- IMMS_CASE
  >~ [`assign_tuple_targets cx (TupleTarget _) _`] >- (IMMS_CASE >> metis_tac[])
  >~ [`assign_tuple_target_list cx [] []`] >- IMMS_CASE
  >~ [`assign_tuple_target_list cx (_::_) (_::_)`] >- IMMS_CASE
  >~ [`assign_tuple_target_list cx _ _`] >- IMMS_CASE
  >~ [`eval_expr cx (Builtin _ _ _)`]
  >- (IMMS_CASE
      >- (gvs[type_check_def, assert_def, check_def, return_def, raise_def] >>
          Cases_on `es` >> fs[builtin_args_length_ok_def] >>
          metis_tac[]) >> metis_tac[])
  >~ [`eval_expr cx (TypeBuiltin _ _ _ _)`] >- (IMMS_CASE >> metis_tac[])
  >~ [`eval_stmt cx (Assign (BaseTarget _) _)`]
  >- (IMMS_CASE
      >- (simp[imms_frame_result] >> metis_tac[]) >>
      IMMS_WRITE)
  >~ [`eval_stmt cx (AugAssign _ _ _ _)`]
  >- (IMMS_CASE
      >- (simp[imms_frame_result] >> metis_tac[]) >> IMMS_WRITE)
  >~ [`assign_tuple_targets cx (BaseTarget _) _`]
  >- (IMMS_CASE
      >- (simp[imms_frame_result] >> metis_tac[]) >> IMMS_WRITE)
  >~ [`eval_expr cx (Pop _ _)`]
  >- (IMMS_CASE
      >- (simp[imms_frame_result] >> metis_tac[]) >>
      qmatch_goalsub_rename_tac `pop_place cx pl` >>
      `!sid id path. pl <> ImmutablePlace sid id path` by metis_tac[] >>
      Cases_on `pl` >> fs[]
      >- (simp[imms_frame_result] >> metis_tac[pop_storage_place_scopes_immutables]) >>
      simp[pop_place_def] >> rpt IMMS_STEP)
  >~ [`eval_expr cx (Call _ (Send _) _ _)`]
  >- (IMMS_CASE
      >- metis_tac[] >> simp[imms_frame_result] >>
      metis_tac[eval_send_preserves_non_accounts])
  >~ [`eval_expr cx (Call _ (ExtCall _ _ _ _) _ _)`]
  >- (IMMS_CASE
      >- metis_tac[rich_listTheory.EVERY_TAKE]
      >- metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
      >- metis_tac[rich_listTheory.EVERY_DROP] >>
      simp[imms_frame_result] >> metis_tac[eval_ext_call_preserves_non_accounts])
  >~ [`eval_expr cx (Call _ (RawCallTarget _) _ _)`]
  >- (IMMS_CASE
      >- metis_tac[] >> simp[imms_frame_result] >>
      metis_tac[eval_raw_call_preserves_non_accounts])
  >~ [`eval_expr cx (Call _ (RawCallCalldataTarget _) _ _)`]
  >- (IMMS_CASE
      >- metis_tac[] >> simp[imms_frame_result] >>
      metis_tac[eval_raw_call_preserves_non_accounts])
  >~ [`eval_expr cx (Call _ RawRevert _ _)`] >- (IMMS_CASE >> metis_tac[])
  >~ [`eval_expr cx (Call _ RawLog _ _)`]
  >- (simp_tac bool_ss [Once evaluate_def] >>
      irule state_rel_frame_bind_guarded >> conj_tac
      >- simp[] >> conj_tac
      >- metis_tac[] >> rpt gen_tac >> strip_tac >>
      simp[imms_frame_result, bind_def, ignore_bind_def, type_check_def,
        assert_def, check_def, return_def, raise_def, lift_option_type_def,
        lift_option_def, check_not_static_def, push_log_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >> FAIL_TAC "ordinary frames"
QED
