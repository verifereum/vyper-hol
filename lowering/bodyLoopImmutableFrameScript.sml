Theory bodyLoopImmutableFrame
Ancestors
  alist list relation vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperTypeContract vyperTypeSystem vyperStorageAccessFrame
  vyperTypeCallGraphSoundness vyperAST vyperState vyperInterpreter
  vyperBareGlobalName vyperImmutablesPreservation vyperStoragePlaceProvenance
  vyperContext vyperCallOutcomeFrame vyperEvalFrame vyperMachineFrame
  vyperScopePreservation vyperCreateFrame vyperLookupStorage vyperMisc
  whitelistForIterImmFrame bodyStorageCases rich_list
Libs evalWalkLib

(* A loop's initial calls generate a set closed under callable bodies and
   defaults. The checker guards each member of this set against writes. *)
Theorem loop_calls_reachable_writes:
  EVERY (callee_writes_ok mods p) calls ==>
  ?reached.
    EVERY reached calls /\
    !sid fn ts deploy mut nr args dflts ret body.
      reached (sid,fn) /\
      ALOOKUP mods sid = SOME ts /\
      lookup_callable_function deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (callee_write_ok p)) dflts /\
      stmts_writes_ok (callee_write_ok p) body /\
      EVERY reached (function_int_calls dflts body)
Proof
  strip_tac >>
  qexists_tac
    `\callee. ?origin. MEM origin calls /\
      (origin = callee \/
       TC (call_edge_rel (contract_call_edges mods)) origin callee)` >>
  conj_tac >- (simp[EVERY_MEM] >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `origin` (CONJUNCTS_THEN assume_tac)) STRIP_ASSUME_TAC) >>
  rename1 `lookup_callable_function deploy fn ts =
             SOME (mut,nr,args,dflts,ret,bod)` >>
  Cases_on `dflts = [] /\ bod = []`
  >- gvs[stmt_writes_ok_def, function_int_calls_def, int_calls_expr_def,
         int_calls_stmt_def] >>
  `?vis mut' nr' raw args' ret'.
     MEM (FunctionDecl vis mut' nr' raw fn args' dflts ret' bod) ts` by
    metis_tac[lookup_callable_function_SOME_decompose] >>
  strip_tac >>
  drule ALOOKUP_MEM >> strip_tac >>
  `EVERY (expr_writes_ok (callee_write_ok p)) dflts /\
   stmts_writes_ok (callee_write_ok p) bod` by
    (qpat_x_assum `EVERY _ calls` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >>
     simp[callee_writes_ok_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
     disch_then (drule_at Any) >> disch_then (drule_at Any) >>
     simp[contract_reachable_TC] >> metis_tac[]) >>
  simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM ((sid,fn),callee) (contract_call_edges mods)` by
    (irule contract_call_edges_function >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  metis_tac[TC_SUBSET, TC_TRANSITIVE, transitive_def, call_edge_rel_def]
QED

Theorem extend_immutable_array_field_error[local]:
  lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) ==>
  ?err. extend_place cx (PlaceR (ImmutablePlace src name []))
          (AttrSubscript fld) st = (INR err,st)
Proof
  simp[lookup_immutable_def, extend_place_def, read_place_def,
       place_type_value_def, get_immutables_def, get_address_immutables_def,
       bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, subscripts_type_def, evaluate_subscripts_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[] >>
  strip_tac >> simp[return_def, raise_def, subscripts_type_def,
                    evaluate_subscripts_def]
QED

Theorem eval_base_place_immutable_array_access[local]:
  !target cx st st' src name path elem bound av.
    lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) /\
    eval_base_place cx target st =
      (INL (PlaceR (ImmutablePlace src name path)),st') ==>
    !pending. place_access target pending = (TopLevelNameTarget (src,name),[]) \/
      (target = TopLevelNameTarget (src,name) /\ path = [])
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget nsid) st = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_immutable_root]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx inner st = _` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >> strip_tac >>
  simp[place_access_def] >>
  first_x_assum (qspecl_then [`cx`,`st`] mp_tac) >>
  disch_then drule_all >> strip_tac
  >~ [`place_access inner [] = _`]
  >- (first_x_assum (qspec_then `[]` strip_assume_tac) >>
      gvs[place_access_def]) >>
  gvs[place_access_def] >>
  qmatch_asmsub_rename_tac
    `extend_place cx (PlaceR (ImmutablePlace src name child)) (AttrSubscript fld) mid` >>
  first_x_assum (qspec_then `fld::pending` strip_assume_tac) >> gvs[] >>
  gvs[Once evaluate_def] >>
  drule lookup_global_immutables >> strip_tac >>
  `?err. extend_place cx (PlaceR (ImmutablePlace src name []))
           (AttrSubscript fld) mid = (INR err,mid)` by
    (irule extend_immutable_array_field_error >>
     qexistsl [`av`,`bound`,`elem`] >> gvs[lookup_immutable_def]) >>
  gvs[]
QED

Theorem immutable_array_guarded_target:
  lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av) /\
  callee_write_ok (TopLevelNameTarget (src,name)) target /\
  eval_target_place cx target st = (INL pl,st') ==>
  !path. pl <> ImmutablePlace src name path
Proof
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, get_place_def,
                      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all eval_base_place_immutable_array_access >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[callee_write_ok_def, place_contains_def, place_access_def]
QED

(* Only the captured array cell must survive, including on error exits. *)
val array_cell =
  ``\cx st. lookup_immutable cx st src name = SOME (ArrayTV elem bound,ArrayV av)``;
val array_relation = rhs (concl (DEPTH_CONV BETA_CONV
  ``\s t. ^array_cell cx s ==> ^array_cell cx t``));
val array_frame_result = BETA_RULE
  (ISPEC array_relation (Q.GEN `R` state_rel_frame_result));

Theorem guarded_array_target_bind[local]:
  state_rel_frame ^array_relation (eval_target_place cx target) /\
  callee_write_ok (TopLevelNameTarget (src,name)) target /\
  (!s p t. eval_target_place cx target s = (INL p,t) ==>
        (!path. p <> ImmutablePlace src name path) ==>
        state_rel_frame ^array_relation (next p)) ==>
  state_rel_frame ^array_relation (bind (eval_target_place cx target) next)
Proof
  simp[array_frame_result, bind_def] >> rpt strip_tac >>
  Cases_on `eval_target_place cx target st` >>
  rename1 `eval_target_place cx target st = (answer,mid)` >>
  Cases_on `answer` >> gvs[] >>
  qpat_assum `!st res st'. eval_target_place cx target st = _ ==> _`
    (drule_then drule) >> strip_tac
  >- (rename1 `eval_target_place cx target st = (INL pl,mid)` >>
      `!path. pl <> ImmutablePlace src name path` by
        metis_tac[immutable_array_guarded_target] >>
      qpat_x_assum `!s p t. eval_target_place _ _ _ = _ ==> _`
        (drule_then (drule_then drule)) >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem array_mutation_frames[local]:
  (!path. pl <> ImmutablePlace src name path) ==>
  state_rel_frame ^array_relation (write_place cx pl value) /\
  state_rel_frame ^array_relation (append_place cx pl value) /\
  state_rel_frame ^array_relation (pop_place cx pl)
Proof
  strip_tac >> simp[array_frame_result] >>
  `!src' name' path. pl = ImmutablePlace src' name' path ==>
     (src',name') <> (src,name)` by metis_tac[pairTheory.PAIR_EQ] >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[
    lookup_immutable_write_other, append_guarded_immutable_frame,
    pop_place_immutable_other]
QED

val array_net =
  let
    val leaves = [machine_frame_primitives, machine_frame_read_result,
      machine_frame_read_results, machine_frame_reads, machine_frame_select_result,
      machine_frame_extend_place, machine_frame_get_place, machine_frame_read_place,
      machine_frame_place_type_value, machine_frame_new_variable,
      machine_frame_next_gas_reading, machine_frame_precompile_call_success,
      machine_frame_handlers, machine_frame_push_function,
      machine_frame_pop_function, machine_frame_unchanged_reads,
      machine_frame_array_iterator_results]
    fun leaf th = (subst [``machine_frame`` |-> array_relation] (concl th),
      irule state_rel_frame_machine >> conj_tac
      >- simp[machine_frame_def, lookup_immutable_def] >> MATCH_ACCEPT_TAC th)
  in evalWalkLib.walk_net
    (map SPEC_ALL [state_rel_frame_bind_guarded, state_rel_frame_try,
      state_rel_frame_finally, state_rel_frame_finally_unless_halt])
    (map leaf (List.concat (map (CONJUNCTS o SPEC_ALL) leaves))) end;

Theorem array_code_stk[local]:
  get_module_code (cx with stk updated_by f) = get_module_code cx
Proof
  simp[FUN_EQ_THM, get_module_code_def]
QED

val array_context_simps = [array_code_stk, oneTheory.one,
  ignore_bind_def, FST, SND, pair_case_thm, UNCURRY];
val array_induction_hypothesis =
  evalWalkLib.IH_TAC {stop = K false,
    normalise = SIMP_RULE bool_ss array_context_simps};
val array_syntax = [int_calls_expr_def, int_calls_stmt_def, int_calls_iterator_def,
  int_calls_assert_reason_def, int_calls_raise_reason_def, int_calls_atarget_def,
  stmt_writes_ok_def, expr_writes_ok_def, atarget_writes_ok_def,
  GSYM vyperTypeEvalProofsTheory.int_calls_exprs_MAP_SND,
  EVERY_APPEND, EVERY_DEF, SF ETA_ss];
val ARRAY_TRANSITIVITY =
  qmatch_goalsub_abbrev_tac `!s t u. P s t /\ P t u ==> P s u` >>
  simp[Abbr `P`];
val ARRAY_ATOMIC =
  FIRST (map (fn n => irule (cj n array_mutation_frames) >>
    first_assum MATCH_ACCEPT_TAC) [1,2,3]);
val ARRAY_STEP =
  FIRST [
    MATCH_MP_TAC guarded_array_target_bind >>
      conj_tac >- (first_assum MATCH_ACCEPT_TAC ORELSE array_induction_hypothesis) >>
      conj_tac >- first_assum MATCH_ACCEPT_TAC >> rpt strip_tac,
    evalWalkLib.STEP
      {net = array_net, at = RAND_CONV,
       unfolds = [switch_BoolV_def, ignore_bind_def, check_not_static_def,
         vyperCreateTheory.eval_create_operands_def],
       intros = [ARRAY_TRANSITIVITY, CONV_TAC (HO_REWR_CONV FORALL_PROD),
         gen_tac, strip_tac, conj_tac, CONV_TAC (RAND_CONV ETA_CONV)],
       fallbacks = [array_induction_hypothesis,
         evalWalkLib.NORMALISE_IH_TAC array_induction_hypothesis,
         ARRAY_ATOMIC]}];
val ARRAY_CASE = evalWalkLib.EVAL_CASE all_tac ARRAY_STEP;
val array_guard = ``callee_write_ok (TopLevelNameTarget (src,name))``;
val ARRAY_ATOMIC_FRAME = simp_tac (srw_ss()) [array_frame_result,
  lookup_immutable_def, return_def, raise_def, push_log_def, update_accounts_def,
  update_pending_deletions_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[eval_ext_call_preserves_non_accounts, eval_raw_call_preserves_non_accounts,
    eval_send_preserves_non_accounts, eval_create_preserves_scopes_immutables,
    vyperStatePreservationTheory.transfer_value_immutables];
val ARRAY_CUSTOM = ARRAY_CASE >>
  qmatch_goalsub_rename_tac `eval_exprs cx ordered` >>
  drule order_custom_error_args_perm >> strip_tac >>
  `EVERY reached (int_calls_exprs ordered)` by
    (simp[body_exprs_main_calls_every] >>
     qpat_x_assum `EVERY reached (int_calls_exprs (custom_error_exprs _))` mp_tac >>
     simp[body_exprs_main_calls_every] >> metis_tac[sortingTheory.PERM_EVERY]) >>
  `EVERY (expr_writes_ok ^array_guard) ordered` by metis_tac[sortingTheory.PERM_EVERY] >>
  array_induction_hypothesis;
val ARRAY_CASE_SIMPLE = ARRAY_CASE >>
  (first_assum ACCEPT_TAC ORELSE simp[array_frame_result, return_def, raise_def]);
fun ARRAY_EXPR_CHUNK (g as (_,w)) =
  case strip_comb (rand w) of
    (head,[_,chunk]) =>
      if aconv head ``eval_exprs`` then
        (`EVERY reached (int_calls_exprs ^chunk) /\
          EVERY (expr_writes_ok ^array_guard) ^chunk` by
           (fs[body_exprs_main_calls_every] >> conj_tac >>
            rpt (FIRST [irule EVERY_TAKE, irule EVERY_DROP]) >> first_assum ACCEPT_TAC) >>
         array_induction_hypothesis) g
      else NO_TAC g
  | _ => NO_TAC g;

val array_code = ``\cx. get_module_code cx = ALOOKUP mods /\ cx.in_deploy = deploy``;
val array_iterator_writes = ``\it. case it of
    Array e => expr_writes_ok ^array_guard e
  | Range lo hi => expr_writes_ok ^array_guard lo /\ expr_writes_ok ^array_guard hi``;

(* The induction covers calls reached from the iterator body. Each reached
   callee supplies the guard and the call closure for its defaults and body. *)
Theorem reachable_immutable_array_frame[local]:
  (!sid func ts mut nr args dflts ret bod.
    reached (sid,func) /\ ALOOKUP mods sid = SOME ts /\
    lookup_callable_function deploy func ts = SOME (mut,nr,args,dflts,ret,bod) ==>
    EVERY (expr_writes_ok ^array_guard) dflts /\
    stmts_writes_ok ^array_guard bod /\ EVERY reached (function_int_calls dflts bod)) ==>
  (!cx s. ^array_code cx /\ EVERY reached (int_calls_stmt s) /\
          stmt_writes_ok ^array_guard s ==>
     state_rel_frame ^array_relation (eval_stmt cx s)) /\
  (!cx ss. ^array_code cx /\ EVERY reached (int_calls_stmts ss) /\
           stmts_writes_ok ^array_guard ss ==>
     state_rel_frame ^array_relation (eval_stmts cx ss)) /\
  (!cx it. ^array_code cx /\ EVERY reached (int_calls_iterator it) /\
           ^array_iterator_writes it ==>
     state_rel_frame ^array_relation (eval_iterator cx it)) /\
  (!cx tyv nm bod vs. ^array_code cx /\ EVERY reached (int_calls_stmts bod) /\
                     stmts_writes_ok ^array_guard bod ==>
     state_rel_frame ^array_relation (eval_for cx tyv nm bod vs)) /\
  (!cx e. ^array_code cx /\ EVERY reached (int_calls_expr e) /\
          expr_writes_ok ^array_guard e ==>
     state_rel_frame ^array_relation (eval_expr cx e)) /\
  (!cx es. ^array_code cx /\ EVERY reached (int_calls_exprs es) /\
           EVERY (expr_writes_ok ^array_guard) es ==>
     state_rel_frame ^array_relation (eval_exprs cx es)) /\
  (!cx t. ^array_code cx /\ EVERY reached (int_calls_target t) /\
          target_writes_ok ^array_guard t ==>
     state_rel_frame ^array_relation (eval_base_place cx t)) /\
  (!cx t. ^array_code cx /\ EVERY reached (int_calls_target t) /\
          target_writes_ok ^array_guard t ==>
     state_rel_frame ^array_relation (eval_target_place cx t)) /\
  (!cx g v. ^array_code cx /\ EVERY reached (int_calls_atarget g) /\
            atarget_writes_ok ^array_guard g ==>
     state_rel_frame ^array_relation (assign_tuple_targets cx g v)) /\
  (!cx gs vs. ^array_code cx /\ EVERY reached (int_calls_atargets gs) /\
              EVERY (atarget_writes_ok ^array_guard) gs ==>
     state_rel_frame ^array_relation (assign_tuple_target_list cx gs vs))
Proof
  BETA_TAC >> strip_tac >> ho_match_mp_tac evaluate_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) array_syntax >> rpt strip_tac >>
  all_tac
  >~ [`eval_expr _ (Call _ (IntCall _) _ _)`] >- suspend "intcall"
  >~ [`eval_expr _ (Builtin _ _ _)`] >- suspend "builtin"
  >~ [`eval_expr _ (Call _ (CreateTarget _ _ _ _) _ _)`] >- suspend "create"
  >~ [`eval_expr _ (Call _ RawLog _ _)`] >- suspend "rawlog"
  >~ [`eval_stmt _ Pass`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ Continue`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ Break`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Return NONE)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Return (SOME _))`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Raise RaiseBare)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Raise RaiseUnreachable)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Raise (RaiseReason _))`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Assert _ AssertBare)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Assert _ AssertUnreachable)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Assert _ (AssertReason _))`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Raise (RaiseCustomError _))`]
  >- ARRAY_CUSTOM
  >~ [`eval_stmt _ (Assert _ (AssertCustomError _))`]
  >- ARRAY_CUSTOM
  >~ [`eval_stmts _ []`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmts _ (_::_)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_exprs _ []`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_exprs _ (_::_)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (Literal _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (Name _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (TopLevelName _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (FlagMember _ _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (IfExp _ _ _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (Subscript _ _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (Attribute _ _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Expr _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (AnnAssign _ _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (If _ _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_iterator _ (Array _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_iterator _ (Range _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_for _ _ _ _ []`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_for _ _ _ _ (_::_)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (For _ _ _ _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (StructLit _ _ _)`] >- (fs[SF ETA_ss] >> ARRAY_CASE_SIMPLE)
  >~ [`eval_stmt _ (Assign (TupleTarget _) _)`] >- ARRAY_CASE_SIMPLE
  >~ [`assign_tuple_targets _ (TupleTarget _) _`] >- ARRAY_CASE_SIMPLE
  >~ [`assign_tuple_target_list _ [] []`] >- ARRAY_CASE_SIMPLE
  >~ [`assign_tuple_target_list _ (_::_) (_::_)`] >- ARRAY_CASE_SIMPLE
  >~ [`assign_tuple_target_list _ _ _`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Log _ _)`] >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _)`] >- (fs[SF ETA_ss] >> ARRAY_CASE_SIMPLE)
  >~ [`eval_expr _ (Call _ (Send _) _ _)`] >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _)`]
  >- (ARRAY_CASE >> FIRST [ARRAY_EXPR_CHUNK, ARRAY_ATOMIC_FRAME])
  >~ [`eval_expr _ (Call _ (RawCallTarget _) _ _)`]
  >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (Call _ (RawCallCalldataTarget _) _ _)`]
  >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (Call _ SelfDestructTarget _ _)`]
  >- (ARRAY_CASE >> ARRAY_ATOMIC_FRAME)
  >~ [`eval_expr _ (Call _ RawRevert _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Assign (BaseTarget _) _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (AugAssign _ _ _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`assign_tuple_targets _ (BaseTarget _) _`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_expr _ (Pop _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_stmt _ (Append _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_base_place _ (NameTarget _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_base_place _ (TopLevelNameTarget _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_base_place _ (AttributeTarget _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_base_place _ (SubscriptTarget _ _)`] >- ARRAY_CASE_SIMPLE
  >~ [`eval_target_place _ _`] >- ARRAY_CASE_SIMPLE
  >~ [`assign_tuple_target_list _ (_::_) []`] >- ARRAY_CASE_SIMPLE
QED

Resume reachable_immutable_array_frame[builtin]:
  ARRAY_CASE
  >- (gvs[type_check_def, assert_def, check_def, return_def, raise_def] >>
      Cases_on `es` >> gvs[builtin_args_length_ok_def, int_calls_expr_def,
                            EVERY_APPEND]) >>
  gvs[type_check_def, assert_def, check_def, return_def, raise_def,
      code_slice_source_SOME, expr_writes_ok_def, int_calls_expr_def, EVERY_APPEND,
      DISJ_IMP_THM, FORALL_AND_THM, AllCaseEqs()] >>
  array_induction_hypothesis
QED

Resume reachable_immutable_array_frame[create]:
  ARRAY_CASE >>
  all_tac >>~- ([`state_rel_frame _ (eval_create _ _ _ _ _ _ _)`],
    ARRAY_ATOMIC_FRAME) >>
  rename1 `state_rel_frame _ (eval_exprs cx (create_operand_order kind has_salt es))` >>
  `EVERY reached (int_calls_exprs (create_operand_order kind has_salt es)) /\
   EVERY (expr_writes_ok ^array_guard) (create_operand_order kind has_salt es)` by
    (simp[body_exprs_main_calls_every] >>
     fs[body_exprs_main_calls_every] >>
     Cases_on `kind` >> Cases_on `es` >>
     gvs[vyperCreateTheory.create_operand_order_def, EVERY_TAKE, EVERY_DROP] >>
     rename1 `EVERY _ rest` >> Cases_on `rest` >>
     gvs[vyperCreateTheory.create_operand_order_def, EVERY_TAKE, EVERY_DROP]) >>
  array_induction_hypothesis
QED

Resume reachable_immutable_array_frame[rawlog]:
  simp_tac bool_ss [Once evaluate_def] >>
  MATCH_MP_TAC state_rel_frame_bind_guarded >> conj_tac >- ARRAY_TRANSITIVITY >>
  conj_tac >- array_induction_hypothesis >>
  rpt gen_tac >> strip_tac >>
  simp[array_frame_result, bind_def, ignore_bind_def, type_check_def,
       assert_def, check_def, return_def, raise_def, lift_option_type_def,
       check_not_static_def, push_log_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `dest_ArrayV (HD v)` >> gvs[return_def, raise_def] >>
  Cases_on `dest_BytesV (EL 1 v)` >> gvs[return_def, raise_def] >>
  fs[lookup_immutable_def]
QED

Resume reachable_immutable_array_frame[intcall]:
  simp_tac bool_ss [Once evaluate_def] >>
  ntac 5 ARRAY_STEP >> ntac 5 ARRAY_STEP >>
  ntac 5 ARRAY_STEP >> ntac 5 ARRAY_STEP >>
  ntac 5 ARRAY_STEP >>
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [LET_THM, FST, SND] >>
  rename1 `INL (imut,inr,iargs,idflts,iretty,ibody)` >>
  qmatch_asmsub_rename_tac `get_module_code cx sid` >>
  qmatch_asmsub_rename_tac `lookup_callable_function cx.in_deploy func ts` >>
  `get_module_code cx sid = SOME ts` by
    (qpat_x_assum `lift_option_type (get_module_code _ _) _ _ = _` mp_tac >>
     simp[vyperTypeEvalProofsTheory.lift_option_type_INL_eq]) >>
  `lookup_callable_function cx.in_deploy func ts =
     SOME (imut,inr,iargs,idflts,iretty,ibody)` by
    (qpat_x_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _` mp_tac >>
     simp[vyperTypeEvalProofsTheory.lift_option_type_INL_eq]) >>
  `ALOOKUP mods sid = SOME ts /\
   lookup_callable_function deploy func ts = SOME (imut,inr,iargs,idflts,iretty,ibody)` by
    (conj_tac
     >- (qpat_assum `get_module_code cx = ALOOKUP mods`
           (fn eq => qpat_assum `get_module_code cx sid = SOME ts`
             (ACCEPT_TAC o REWRITE_RULE [eq])))
     >> qpat_assum `cx.in_deploy <=> deploy`
          (fn eq => qpat_assum `lookup_callable_function cx.in_deploy func ts = _`
            (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `EVERY (expr_writes_ok ^array_guard) idflts /\ stmts_writes_ok ^array_guard ibody /\
   EVERY reached (int_calls_exprs idflts) /\ EVERY reached (int_calls_stmts ibody)` by
    (qpat_assum `!sid func ts mut nr args dflts ret bod. _`
      (qspecl_then [`sid`,`func`,`ts`,`imut`,`inr`,`iargs`,`idflts`,`iretty`,`ibody`] mp_tac) >>
     fs[function_int_calls_def, EVERY_APPEND]) >>
  `!n. EVERY (expr_writes_ok ^array_guard) (DROP n idflts) /\
       EVERY reached (int_calls_exprs (DROP n idflts))` by
    simp[EVERY_DROP, int_calls_exprs_DROP_EVERY] >>
  ntac 5 ARRAY_STEP >>
  strip_tac >> ARRAY_STEP >>
  ARRAY_STEP >- ARRAY_TRANSITIVITY
  >- (fs[type_check_def, assert_def, return_def, raise_def] >>
      array_induction_hypothesis) >>
  ntac 5 ARRAY_STEP >> ntac 5 ARRAY_STEP >>
  ntac 5 ARRAY_STEP >> ntac 3 ARRAY_STEP
  >- (rpt strip_tac >> fs[array_code_stk] >>
      simp_tac (srw_ss()) [lookup_immutable_def] >>
      evalWalkLib.FORWARD_IH_TAC
        {normalise = SIMP_RULE (srw_ss()) (lookup_immutable_def::array_context_simps)}) >>
  rpt (CHANGED_TAC ARRAY_STEP) >>
  simp_tac bool_ss [lock_if_nr_def, unlock_if_nr_def]
  >- (POP_ASSUM_LIST (K all_tac) >>
      rewrite_tac[array_frame_result] >> rpt gen_tac >> strip_tac >>
      Cases_on `inr` >> Cases_on `cx.nonreentrant_slot` >>
      gvs[return_def, raise_def] >>
      rename1 `acquire_nonreentrant_lock _ slot _` >>
      Cases_on `acquire_nonreentrant_lock cx.txn.target slot
        (is_view_mut imut \/ cx.txn.is_static) st` >>
      drule vyperStatePreservationTheory.acquire_nonreentrant_lock_immutables >>
      Cases_on `imut = View \/ imut = Pure` >>
      gvs[is_view_mut_def, ignore_bind_def, bind_def, check_not_static_def,
          type_check_def, assert_def, check_def, return_def, raise_def,
          AllCaseEqs()] >>
      strip_tac >> simp[lookup_immutable_def])
  >~ [`state_rel_frame _ (eval_stmts _ _)`]
  >- (qmatch_asmsub_rename_tac `push_function (sid,func) env cx ps = (INL cxf,pt)` >>
      `cxf = cx with stk updated_by CONS (sid,func)` by
        (qpat_x_assum `push_function _ _ _ _ = _` mp_tac >> simp[push_function_def, return_def]) >>
      gvs[array_code_stk] >>
      simp_tac (srw_ss()) [lookup_immutable_def] >>
      evalWalkLib.FORWARD_IH_TAC
        {normalise = SIMP_RULE (srw_ss()) (lookup_immutable_def::array_context_simps)}) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[array_frame_result] >> rpt gen_tac >> strip_tac >>
  Cases_on `inr /\ imut <> View /\ imut <> Pure` >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  drule vyperStatePreservationTheory.release_nonreentrant_lock_immutables >>
  simp[lookup_immutable_def]
QED

Finalise reachable_immutable_array_frame

Theorem for_bare_immutable_array_body_observation:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  iterator_unmodified (Array (TopLevelName (ArrayT et bd) (src,name))) ss /\
  stmt_loop_calls_ok [(NONE,tops)]
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) bound ss) /\
  lookup_immutable cx st src name = SOME (ArrayTV elem arrbound,ArrayV av) /\
  eval_stmts cx ss st = (res,st') ==>
  lookup_immutable cx st' src name = lookup_immutable cx st src name
Proof
  simp[iterator_unmodified_def, expr_places_def, stmt_loop_calls_ok_def,
       loop_iterator_place_def] >> rpt strip_tac >>
  drule loop_calls_reachable_writes >> strip_tac >>
  `callee_write_ok (TopLevelNameTarget (src,name)) =
   (\w. ~place_contains w (TopLevelNameTarget (src,name)))` by
    (simp[FUN_EQ_THM, callee_write_ok_def] >> gen_tac >>
     Cases_on `FST (place_access w [])` >> simp[place_contains_def, place_access_def]) >>
  `!sid fn ts mut nr args dflts ret body.
     reached (sid,fn) /\ ALOOKUP [(NONE,tops)] sid = SOME ts /\
     lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
     EVERY (expr_writes_ok ^array_guard) dflts /\
     stmts_writes_ok ^array_guard body /\ EVERY reached (function_int_calls dflts body)` by
    (rpt gen_tac >>
     qpat_assum `!sid fn ts deploy mut nr args dflts ret body. _`
       (MATCH_ACCEPT_TAC o SPEC_ALL)) >>
  `state_rel_frame
    (\s t. lookup_immutable cx s src name = SOME (ArrayTV elem arrbound,ArrayV av) ==>
            lookup_immutable cx t src name = SOME (ArrayTV elem arrbound,ArrayV av))
    (eval_stmts cx ss)` by
    (drule_then (irule o cj 2) reachable_immutable_array_frame >>
     simp[FUN_EQ_THM, get_module_code_def]) >>
  drule_all state_rel_frame_at >> simp[]
QED
