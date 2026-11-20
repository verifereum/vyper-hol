(*
 * Main mutual evaluator type-soundness proof for the executable Vyper type
 * system.
 *
 * This file proves eval_scc_type_sound_mutual,
 * covering statements, statement lists, iterators, assignment targets, base
 * targets, for-loop bodies, and expressions.  Statement/list consequences are
 * stated separately in vyperTypeStmtSoundness.
 *)

Theory vyperTypeEvalSoundness
Ancestors
  list rich_list sorting pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperCreate vyperCreateFrame vyperCallFrame vyperInterpreter vyperCallOutcomeFrame vyperState vyperContext vyperStorage vyperTyping vyperLookup
  vyperImmutableMetadataFrame[ignore_grammar]
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeCallOutcome[ignore_grammar] vyperCallOutcome[ignore_grammar]
  vyperTypeArgFits vyperTypeExtCallSoundness vyperTypeGlobalLookupSoundness vyperTypeAssignContext vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperEvalExprPreservesScopesDom vyperPlaceResultTyping vyperPlaceTyping
  vyperPlaceWriteSoundness vyperTargetPlaceWrite vyperPlaceMutationSoundness
  vyperAugAssignWriteSoundness vyperSystemControl
  vyperTypeEvalProofs vyperTypeEvalCaseProofs
Libs
  wordsLib markerLib intLib

Theorem LIST_REL_create_operand_layout[local]:
  LIST_REL R xs ys ==>
  LIST_REL R (create_operand_layout kind has_salt xs)
    (create_operand_layout kind has_salt ys)
Proof
  Cases_on `kind` >> Cases_on `xs` >> Cases_on `ys` >>
  simp[create_operand_layout_def] >> strip_tac >>
  imp_res_tac LIST_REL_LENGTH >> fs[]
  >~ [`LIST_REL R (_ ++ _) (_ ++ _)`]
  >- (irule LIST_REL_APPEND_suff >> metis_tac[LIST_REL_TAKE, LIST_REL_DROP]) >>
  qmatch_assum_rename_tac `LIST_REL R left right` >>
  qmatch_goalsub_abbrev_tac `DROP n left` >>
  `LIST_REL R (DROP n left) (DROP n right)` by metis_tac[LIST_REL_DROP] >>
  `LIST_REL R (TAKE n left) (TAKE n right)` by metis_tac[LIST_REL_TAKE] >>
  Cases_on `DROP n left` >> Cases_on `DROP n right` >> gvs[] >>
  irule LIST_REL_APPEND_suff >> simp[]
QED

Theorem exprs_runtime_typed_create_operand_layout[local]:
  exprs_runtime_typed env es vs ==>
  exprs_runtime_typed env (create_operand_layout kind has_salt es)
    (create_operand_layout kind has_salt vs)
Proof
  rw[exprs_runtime_typed_def] >>
  qexists_tac `create_operand_layout kind has_salt tvs` >>
  conj_tac >> irule LIST_REL_create_operand_layout >> simp[]
QED

Theorem create_operands_result_sound[local]:
  runtime_consistent env cx st /\
  exprs_runtime_typed env es (create_operand_layout kind has_salt vs) /\
  create_arg_types_ok kind has_salt (MAP expr_type es) /\
  eval_create_operands cx kind has_salt rof (MAP expr_type es)
    literal_offset vs st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\
  (!msg. res <> INR (Error (TypeError msg))) /\
  (case res of
   | INL tv => expr_result_typed env
       (Call (BaseT AddressT) (CreateTarget kind has_salt rof kw_order) es NONE) tv
   | INR _ => T)
Proof
  Cases_on `kind` >>
  simp[eval_create_operands_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac check_create_blueprint_result_state >> gvs[]
  >~ [`check_create_blueprint _ _ _ _ = (INR _,_)`]
  >- (gvs[runtime_consistent_def] >>
      metis_tac[check_create_blueprint_no_type_error]) >>
  drule_all create_tail_result_sound_simp >> simp[]
QED

(* Split only the new outer contracts, not the old ordinary/place result pair. *)
fun has_soundness_aux_conj tm =
  if is_forall tm then has_soundness_aux_conj (snd (dest_forall tm))
  else if is_imp tm then has_soundness_aux_conj (snd (dest_imp tm))
  else is_conj tm andalso
    (free_in ``typed_scope_transition`` (snd (dest_conj tm)) orelse
     free_in ``live_memory_result`` (snd (dest_conj tm)) orelse
     free_in ``writable_place_result`` (snd (dest_conj tm)));

fun expose_soundness_aux_tac g =
  if has_soundness_aux_conj (snd g) then
    ((if is_conj (snd g) then conj_tac
      else if is_forall (snd g) then gen_tac
      else disch_then strip_assume_tac) >> expose_soundness_aux_tac) g
  else all_tac g;

(* Trace roots are keyed by the outer evaluator equation, never by an IH. *)
val soundness_root_inventory = ref ([] : string list);
val trace_root_inventory = ref ([] : (string * term) list);
fun trace_root_key tm =
  let val body = #2 (strip_forall tm)
      val (premises,conclusion) = dest_imp body
      val _ = if same_const (fst (strip_comb conclusion)) ``typed_scope_transition``
              then () else raise Fail "Not a scope-transition conclusion"
      val equation = List.last (strip_conj premises)
      val (evaluator,args) = strip_comb (lhs equation)
      fun name t = #1 (dest_const (fst (strip_comb t)))
      val operation = name evaluator
      val arg = el 2 args
      val constructor = if operation = "eval_target_place" then "" else name arg
      val suffix =
        case operation of
          "eval_target_place" => "Target"
        | "eval_base_place" => "Base_" ^ constructor
        | "eval_exprs" => if listSyntax.is_nil arg then "Exprs_nil" else "Exprs_cons"
        | "eval_expr" => "Expr_" ^ constructor ^
            (if constructor = "Call" then "_" ^ name (el 2 (#2 (strip_comb arg))) else "")
        | _ => raise Fail ("Unknown transition evaluator: " ^ operation)
  in "Trace_" ^ suffix end;
fun suspend_trace_root g =
  let val tm = #2 g
      val label = trace_root_key tm
      val _ = if List.exists (fn (key,_) => key = label) (!trace_root_inventory)
              then raise Fail ("Duplicate transition root: " ^ label) else ()
      val _ = trace_root_inventory := !trace_root_inventory @ [(label,tm)]
  in suspend label g end;

val live_root_inventory = ref ([] : (string * term) list);
fun live_root_key tm =
  let val body = #2 (strip_forall tm)
      val (premises,conclusion) = dest_imp body
      val _ = if free_in ``live_memory_result`` conclusion then ()
              else raise Fail "Not a live-result conclusion"
      val (evaluator,args) = strip_comb (lhs (List.last (strip_conj premises)))
      fun name t = #1 (dest_const (fst (strip_comb t)))
      val operation = name evaluator
      val arg = el 2 args
      val suffix =
        case operation of
          "eval_target_place" => "Target"
        | "eval_base_place" => "Base_" ^ name arg
        | "eval_expr" => "Expr_" ^ name arg ^
            (if name arg = "Call" then "_" ^ name (el 2 (#2 (strip_comb arg))) else "")
        | _ => raise Fail ("Unknown live-result evaluator: " ^ operation)
  in "LiveRoot" ^ suffix end;
fun suspend_live_root g =
  let val tm = #2 g
      val label = live_root_key tm
      val _ = if List.exists (fn (key,_) => key = label) (!live_root_inventory)
              then raise Fail ("Duplicate live-result root: " ^ label) else ()
      val _ = live_root_inventory := !live_root_inventory @ [(label,tm)]
  in suspend label g end;

Theorem eval_scc_type_sound_results_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn) /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => ?env_exn. env_extends env env_exn /\ env_consistent env_exn cx st' /\
                           return_exception_typed env_exn ret_ty exn) /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => ?tyv. evaluate_type env.type_defs ty = SOME tyv /\
                      EVERY (iterator_result_typed tyv) vs
    | INR _ => T) /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (iterator_result_typed tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_for cx tyv id body vs st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ env_consistent env cx st' /\
    no_type_error_result res /\
    case res of
    | INR exn => return_exception_typed env ret_ty exn
    | INL _ => T) /\
  (!cx e. (!env st res st'.
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e st = (res,st') ==>
    ((well_typed_expr env e ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of INL pv => eval_result_typed (env,cx,st') pv (Type (expr_type e)) | INR _ => T) /\
     (!vt. type_place_expr env e = SOME vt ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of INL pv => eval_result_typed (env,cx,st') pv vt | INR _ => T))) /\
   (!env st res st'.
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e st = (res,st') ==>
    typed_scope_transition st st') /\
   (!env st res st'.
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e st = (res,st') ==>
    case res of INL pv => live_memory_result st' pv | INR _ => T)) /\
  (!cx es. (!env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => exprs_runtime_typed env es vs
    | INR _ => T) /\
   (!env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\ eval_exprs cx es st = (res,st') ==>
    typed_scope_transition st st')) /\
  (!cx bt. (!env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of INL pv => eval_result_typed (env,cx,st') pv vt | INR _ => T) /\
   (!env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,st') ==>
    typed_scope_transition st st') /\
   (!env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,st') ==>
    case res of INL pv => live_memory_result st' pv | INR _ => T) /\
   (!env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_base_place cx bt st = (res,st') ==>
    case res of INL pv => writable_place_result cx st' pv | INR _ => T)) /\
  (!cx bt. (!env ty st res st'.
    well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of INL p => eval_result_typed (env,cx,st') (PlaceR p) (Type ty) | INR _ => T) /\
   (!env ty st res st'.
    well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,st') ==>
    typed_scope_transition st st') /\
   (!env ty st res st'.
    well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,st') ==>
    case res of INL p => live_memory_result st' (PlaceR p) | INR _ => T) /\
   (!env ty st res st'.
    well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ eval_target_place cx bt st = (res,st') ==>
    case res of INL p => writable_place_result cx st' (PlaceR p) | INR _ => T)) /\
  (!cx g v. !env ty st res st'.
    well_typed_atarget env g ty /\ value_runtime_typed env ty v /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget g) /\ assign_tuple_targets cx g v st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res) /\
  (!cx gs vs. !env tys st res st'.
    LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets gs) /\ assign_tuple_target_list cx gs vs st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> expose_soundness_aux_tac >>
  (fn (g as (asms,w)) =>
    let
      fun head tm = #Name (dest_thy_const (#1 (strip_comb tm)))
      fun app tm =
        let val (h,args) = strip_comb tm
            val n = #Name (dest_thy_const h)
        in (List.exists (fn s => s = n) ["eval_stmt", "eval_stmts", "eval_iterator", "eval_for",
              "eval_expr", "eval_exprs", "eval_base_place", "eval_target_place"]
            andalso length args = (if n = "eval_for" then 6 else 3)) orelse
           (List.exists (fn s => s = n) ["assign_tuple_targets", "assign_tuple_target_list"] andalso
            length args = 4)
        end handle HOL_ERR _ => false
      val body = #2 (strip_forall w)
      val equations = if is_imp body then strip_conj (fst (dest_imp body)) else asms
      val outer = List.filter (fn a => is_eq a andalso app (lhs a)) equations
      val tm = case outer of [equation] => lhs equation
             | _ => raise Fail "Expected one outer evaluator equation"
      val (h,args) = strip_comb tm
      val n = head h
      val arg = el 2 args
      fun shape t = if listSyntax.is_nil t then "nil" else "cons"
      fun expr_label e =
        let val (_,xs) = strip_comb e
        in if head e = "Call" then "Expr_Call_" ^ head (el 2 xs)
           else "Expr_" ^ head e end
      fun stmt_label s =
        let val (_,xs) = strip_comb s
            val c = head s
        in if c = "Return" then "Return_" ^ head (hd xs)
           else if c = "Raise" then head (hd xs)
           else if c = "Assert" then head (el 2 xs)
           else if c = "Assign" then
             (if head (hd xs) = "BaseTarget" then "Assign_Base" else "Assign_Tuple")
           else c end
      val is_trace = free_in ``typed_scope_transition`` w
      val is_live = free_in ``live_memory_result`` w
      val is_writable = free_in ``writable_place_result`` w
      val label =
        if is_writable then
          (if n = "eval_target_place" then "WritableRootTarget"
           else "WritableRootBase_" ^ head arg)
        else if is_live then
          (if n = "eval_target_place" then "LiveRootTarget"
           else if n = "eval_base_place" then "LiveRootBase_" ^ head arg
           else "LiveRootExpr_" ^ head arg)
        else if n = "eval_stmt" then stmt_label arg
        else if n = "eval_stmts" then "Stmts_" ^ shape arg
        else if n = "eval_iterator" then "Iterator_" ^ head arg
        else if n = "eval_for" then "For_" ^ shape (el 5 args)
        else if n = "eval_expr" then expr_label arg
        else if n = "eval_exprs" then "Exprs_" ^ shape arg
        else if n = "eval_base_place" then "BasePlaceRoot_" ^ head arg
        else if n = "eval_target_place" then "TargetPlace"
        else if n = "assign_tuple_targets" then "TupleStore_" ^ head arg
        else if n = "assign_tuple_target_list" then
          "TupleStores_" ^ shape arg ^ "_" ^ shape (el 3 args)
        else raise Fail ("Unknown soundness evaluator: " ^ n)
      val key = if is_trace then trace_root_key w
                else if is_live then live_root_key w else label
      val _ = if List.exists (fn seen => seen = key) (!soundness_root_inventory)
              then raise Fail ("Duplicate soundness root: " ^ key) else ()
      val _ = soundness_root_inventory := key :: !soundness_root_inventory
    in
      if is_trace then suspend_trace_root g
      else if is_live then suspend_live_root g
      else if label = "Expr_Call_ExtCall" then
        (rpt gen_tac >> strip_tac >>
         reverse conj_tac >- (
           rpt gen_tac >> strip_tac >>
           qpat_x_assum `type_place_expr _ (Call _ (ExtCall _ _ _ _) _ _) = SOME _` mp_tac >>
           simp[type_place_expr_Call_ExtCall_NONE]) >>
         suspend "Expr_Call_ExtCall_result") g
      else suspend label g
    end)
QED

Resume eval_scc_type_sound_results_mutual[Pass]:
  gvs[evaluate_def, return_def, no_type_error_result_def, type_stmt_def]
QED

Resume eval_scc_type_sound_results_mutual[Continue]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[Break]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[Return_NONE]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def, value_runtime_typed_def, value_has_type_def,
      evaluate_type_def]
QED

Resume eval_scc_type_sound_results_mutual[Return_SOME]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Return (SOME e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_expr_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `er` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tv,s1)` >>
    `live_memory_result s1 tv` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL tv`, `s1`] mp_tac) >> simp[]) >>
    Cases_on `read_result cx tv s1` >>
    rename1 `read_result cx tv s1 = (mr,s2)` >>
    Cases_on `mr` >> gvs[raise_def, no_type_error_result_def]
    >- (
      drule read_result_state >> strip_tac >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all live_result_read_typed >> strip_tac >>
      gvs[return_exception_typed_def, value_runtime_typed_def] >>
      metis_tac[type_widens_to_value_has_type]) >>
    drule read_result_state >> strip_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    conj_tac >- (drule_all live_result_read_typed >>
      simp[no_type_error_result_def]) >>
    drule read_result_no_control >> strip_tac >>
    Cases_on `y` >> gvs[no_control_exc_def, return_exception_typed_def]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[RaiseBare]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[RaiseUnreachable]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[RaiseReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >> reverse strip_tac >- (
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule_all >> simp[] >>
    drule_all eval_expr_exception_return_typed >>
    rw[] >> gvs[no_type_error_result_def]) >>
  BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  gvs[] >> rename1 `eval_expr cx e st = (INL pv,mid)` >>
  `live_memory_result mid pv` by (
    qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
      (qspecl_then [`env`, `st`, `INL pv`, `mid`] mp_tac) >> simp[]) >>
  drule_all live_result_read_typed >> strip_tac >>
  gvs[value_runtime_typed_def, evaluate_type_def, no_type_error_result_def,
      return_exception_typed_def, value_has_type_StringTV, AllCaseEqs(),
      dest_StringV_def, lift_option_type_def, return_def, raise_def] >>
  imp_res_tac value_has_type_StringTV >>
  gvs[dest_StringV_def, return_def, raise_def, no_type_error_result_def,
      return_exception_typed_def] >>
  drule read_result_no_control >> strip_tac >>
  Cases_on `e'` >> gvs[no_control_exc_def]
QED

Resume eval_scc_type_sound_results_mutual[AssertBare]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertBare))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    `live_memory_result st1 x` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL x`, `st1`] mp_tac) >> simp[]) >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (loaded,st2)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    reverse (Cases_on `loaded`)
    >- (drule read_result_no_control >> strip_tac >>
        Cases_on `y` >>
        gvs[switch_BoolV_def, bind_def, raise_def, no_control_exc_def,
            no_type_error_result_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b` >>
    gvs[switch_BoolV_def, bind_def, return_def, raise_def,
        no_type_error_result_def, return_exception_typed_def] >>
    rpt strip_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AssertUnreachable]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertUnreachable))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    `live_memory_result st1 x` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL x`, `st1`] mp_tac) >> simp[]) >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (loaded,st2)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    reverse (Cases_on `loaded`)
    >- (drule read_result_no_control >> strip_tac >>
        Cases_on `y` >>
        gvs[switch_BoolV_def, bind_def, raise_def, no_control_exc_def,
            no_type_error_result_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b` >>
    gvs[switch_BoolV_def, bind_def, return_def, raise_def,
        no_type_error_result_def, return_exception_typed_def] >>
    rpt strip_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AssertReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason e')))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  Cases_on `expr_res` >> rewrite_tac[no_type_error_result_def]
  >- (
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
    qpat_x_assum `!vt. _` kall_tac >>
    qpat_x_assum `case INL x of INL pv => eval_result_typed _ pv _ | INR _ => T` mp_tac >>
    simp_tac (srw_ss()) [] >> strip_tac >>
    `live_memory_result st1 x` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL x`, `st1`] mp_tac) >> simp[]) >>
    qpat_x_assum `!s tv t. eval_expr cx e s = (INL tv,t) ==> _`
      (drule_then (mk_asm "reason_ih")) >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (loaded,st2)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    reverse (Cases_on `loaded`)
    >- (drule read_result_no_control >> strip_tac >>
        Cases_on `y` >>
        gvs[switch_BoolV_def, bind_def, raise_def, no_control_exc_def,
            no_type_error_result_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b` >> simp[switch_BoolV_def, bind_def, return_def]
    >- (rpt strip_tac >> gvs[no_type_error_result_def]) >>
    asm_x "reason_ih" strip_assume_tac >>
    Cases_on `eval_expr cx e' st1` >>
    rename1 `eval_expr cx e' st1 = (reason_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `reason_res` >> gvs[no_type_error_result_def]
    >- (
      `live_memory_result st2 x'` by (
        qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
          (qspecl_then [`env`, `st1`, `INL x'`, `st2`] mp_tac) >> simp[]) >>
      Cases_on `read_result cx x' st2` >>
      rename1 `read_result cx x' st2 = (reason_loaded,st3)` >>
      drule_all live_result_read_typed >> strip_tac >> gvs[] >>
      reverse (Cases_on `reason_loaded`)
      >- (drule read_result_no_control >> strip_tac >>
          Cases_on `y` >>
          gvs[no_control_exc_def, return_exception_typed_def,
              no_type_error_result_def] >> rpt strip_tac >> gvs[]) >>
      gvs[value_runtime_typed_def, evaluate_type_def] >>
      drule value_has_type_StringTV >> strip_tac >>
      gvs[dest_StringV_def, lift_option_type_def, return_def, raise_def,
          no_type_error_result_def, return_exception_typed_def] >>
      rpt strip_tac >> gvs[]) >>
    gvs[bind_def, no_type_error_result_def] >>
    rw[] >>
    drule eval_expr_exception_return_typed >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!s tv t. eval_expr cx e s = (INL tv,t) ==> _` kall_tac >>
  qpat_x_assum `!vt. _` kall_tac >>
  gvs[no_type_error_result_def] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Log]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Log id es))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def, AllCaseEqs()] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, push_log_def,
       no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res, st1)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ env_consistent _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  Cases_on `exprs_res` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> gvs[state_well_typed_def, accounts_well_typed_def] >>
    Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id x` >>
    gvs[lift_option_def, return_def, raise_def, ignore_bind_def, bind_def,
        check_def, assert_def, push_log_def, AllCaseEqs()] >>
    drule_all env_consistent_logs_append >>
    simp[return_exception_typed_def]) >>
  strip_tac >> gvs[] >>
  drule eval_exprs_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `get_tenv cx = env.type_defs` by fs[env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type env.type_defs typ = SOME tyv` by
    (qspecl_then [`env.type_defs`,`typ`] mp_tac assignable_type_well_formed >>
     simp[] >> rewrite_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  pop_assum strip_assume_tac >>
  irule annassign_statement_sound_from_expr_ih >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `tyv` >> simp[]) >>
  conj_tac >- simp[] >>
  qexists_tac `e` >> qexists_tac `st` >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!tenv s'' tyv t. _`
        (qspecl_then [`env.type_defs`, `st`, `tyv`, `st`] mp_tac) >>
      simp[lift_option_type_def, return_def] >>
      strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
        (drule_all_then strip_assume_tac) >>
      qpat_x_assum `well_typed_expr env' e ==> _` (drule_then strip_assume_tac) >>
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env'`, `st''`, `res'`, `st'''`] mp_tac) >>
      simp[] >> Cases_on `res'` >> gvs[]) >>
  rpt conj_tac >> asm_rewrite_tac[]
QED

Resume eval_scc_type_sound_results_mutual[Append]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Append bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >>
  Cases_on `type_place_target env bt` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME vt` >>
  Cases_on `vt` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type ty)` >>
  Cases_on `ty` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty bd))` >>
  Cases_on `bd` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
  strip_tac >>
  qpat_x_assum `env = env'` (SUBST_ALL_TAC o SYM) >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res, st1)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  reverse (Cases_on `target_res`)
  >- (qpat_x_assum `!s p t. eval_target_place cx bt s = (INL p,t) ==> _` kall_tac >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[] >>
      drule eval_target_place_no_control >>
      simp[no_control_exc_return_exception_typed]) >>
  simp_tac(srw_ss()) [] >>
  qpat_x_assum `!s p t. eval_target_place cx bt s = (INL p,t) ==> _`
    (drule_then strip_assume_tac) >>
  Cases_on `eval_expr cx e st1` >>
  rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (qspecl_then [`env`, `st1`, `expr_res`, `st2`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
    (qspecl_then [`env`, `st1`, `expr_res`, `st2`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!env ty st res st'. _` kall_tac >>
  qpat_x_assum `!vt. _` kall_tac >>
  reverse (Cases_on `expr_res`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule eval_expr_exception_return_typed >> simp[]) >>
  gvs[] >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `eval_result_typed (env,cx,st2) (PlaceR x) (Type (ArrayT elem_ty (Dynamic n)))` by
    (irule eval_result_typed_transport >> qexists_tac `st1` >> simp[]) >>
  `writable_place_result cx st2 (PlaceR x)` by
    (irule writable_place_result_transport >> qexists_tac `st1` >> simp[]) >>
  `live_memory_result st2 (PlaceR x)` by
    (Cases_on `x` >> simp[live_memory_result_def] >>
     drule_all live_memory_result_transport >> simp[live_memory_result_def]) >>
  `?elem_tv. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
     runtime_place_typed cx st2 x (ArrayTV elem_tv (Dynamic n))` by
    gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `read_result cx x' st2` >>
  rename1 `read_result cx x' st2 = (loaded,st3)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  reverse (Cases_on `loaded`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule read_result_no_control >> simp[no_control_exc_return_exception_typed]) >>
  qmatch_assum_rename_tac `read_result cx x' st2 = (INL right,st2)` >>
  `value_runtime_typed env elem_ty right` by
    (drule_all read_live_result_widens_type >> simp[]) >>
  `value_has_type elem_tv right` by gvs[value_runtime_typed_def] >>
  strip_tac >> gvs[] >>
  `runtime_consistent env cx st2` by simp[runtime_consistent_def] >>
  `runtime_place_writable cx st2 x` by gvs[writable_place_result_def] >>
  drule_at (Pat `append_place`) append_place_sound >>
  disch_then (qspecl_then [`n`, `elem_tv`, `env`] mp_tac) >> simp[] >>
  impl_tac >- (Cases_on `x` >> gvs[live_memory_result_def] >> metis_tac[]) >>
  strip_tac >> gvs[runtime_consistent_def] >>
  Cases_on `res` >> gvs[no_type_error_result_def] >>
  drule append_place_no_control >> simp[no_control_exc_return_exception_typed]
QED

Resume eval_scc_type_sound_results_mutual[Assign_Tuple]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once type_stmt_def, atarget_accepts_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac [int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[call_evaluation_safe_append_right] >>
  `call_evaluation_safe cx (int_calls_atarget (TupleTarget gs))` by
    metis_tac[call_evaluation_safe_append_left] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
    (qspecl_then [`env`, `st`, `er`, `s1`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  qpat_x_assum `!vt. _` kall_tac >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s tv t s' v t'. _` kall_tac >>
      simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule eval_expr_exception_return_typed >> simp[]) >>
  qpat_x_assum `!s tv t s' v t'. _` (mk_asm "tuple_ih") >>
  gvs[] >> rename1 `eval_expr cx e st = (INL tv,s1)` >>
  Cases_on `read_result cx tv s1` >>
  rename1 `read_result cx tv s1 = (mr,s2)` >>
  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
  reverse (Cases_on `mr`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule read_result_no_control >> simp[no_control_exc_return_exception_typed]) >>
  simp_tac(srw_ss()) [] >>
  strip_tac >> gvs[] >>
  asm_x "tuple_ih" strip_assume_tac >>
  qpat_x_assum `!s tv t s' v t'. _` (drule_all_then strip_assume_tac) >>
  gvs[] >> Cases_on `res` >> gvs[no_type_error_result_def] >>
  drule assign_tuple_targets_no_control >> simp[no_control_exc_return_exception_typed]
QED

Resume eval_scc_type_sound_results_mutual[Assign_Base]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  suspend "Assign_Base_sequence"
QED

Resume eval_scc_type_sound_results_mutual[AugAssign]:
  suspend "AugAssign_place"
QED

Resume eval_scc_type_sound_results_mutual[If]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (If e ss ss'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  rename1 `eval_expr cx e st = (cond_res, st1)` >>
  reverse(Cases_on `cond_res`)
  >- (
    simp_tac(srw_ss())[] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac(srw_ss())[] >>
    first_x_assum drule >>
    simp_tac(srw_ss())[no_type_error_result_def] >>
    strip_tac >>
    drule_all eval_expr_exception_return_typed >> simp[]
  ) >>
  simp_tac(srw_ss())[ignore_bind_def, bind_def] >>
  CASE_TAC >>
  reverse CASE_TAC >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qpat_x_assum `push_scope st1 = (INR _,_)` mp_tac >>
    simp_tac(srw_ss())[push_scope_def,return_def]
  ) >>
  rename1 `eval_expr cx e st = (INL tv, st1)` >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result st' pv | INR _ => T`
    (qspecl_then [`env`,`st`,`INL tv`,`st1`] mp_tac) >>
  (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition st st'` kall_tac >>
  qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` kall_tac >>
  strip_tac >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss')`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule scope_bracket_post >>
  conj_asm1_tac >- (
    irule env_consistent_env_maps_wf >> simp[] >>
    goal_assum drule >> simp[]
  ) >>
  qmatch_asmsub_abbrev_tac`finally body_fun pop_scope sf` >>
  qexistsl_tac[`body_fun`,`st1`] >>
  PURE_REWRITE_TAC[bind_def, ignore_bind_def] >>
  ASM_REWRITE_TAC[] >>
  first_x_assum (drule_then drule) >> strip_tac >>
  last_x_assum (drule_then drule) >> strip_tac >>
  qpat_x_assum `push_scope st1 = (INL x',sf)`
    (strip_assume_tac o
     SIMP_RULE (srw_ss()) [push_scope_def, return_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  pure_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
  BETA_TAC >> ASM_REWRITE_TAC[] >>
  qmatch_goalsub_abbrev_tac`body_fun st2` >>
  Cases_on`body_fun st2` >>
  simp_tac std_ss [pairTheory.PAIR_EQ, sumTheory.sum_case_def] >>
  qmatch_assum_rename_tac`body_fun st2 = (rf,sf)` >>
  qho_match_abbrev_tac`P rf sf` >>
  `st1 with scopes := FEMPTY::st1.scopes = st2` by
    simp[Abbr`st2`, evaluation_state_component_equality] >>
  irule switch_BoolV_live_empty_scope_post >>
  qexistsl_tac [`cx`,`env`,`eval_stmts cx ss'`,`eval_stmts cx ss`,`tv`,`st1`] >>
  qunabbrev_tac`body_fun` >>
  simp[] >>
  qpat_x_assum `st1 with scopes := FEMPTY::st1.scopes = st2` kall_tac >>
  conj_tac >- (
    rpt strip_tac >> qunabbrev_tac`P` >> BETA_TAC >>
    simp_tac (srw_ss()) [Abbr`st2`] >> ASM_REWRITE_TAC[] >>
    conj_tac >- (
      irule push_scope_preserves_state_well_typed >>
      qexistsl_tac [`st1`,`()`] >>
      simp[push_scope_def, return_def, evaluation_state_component_equality]) >>
    conj_tac >- gvs[no_type_error_result_def] >>
    irule no_control_exc_return_exception_typed >> simp[]) >>
  `accounts_well_typed st2.accounts` by simp[Abbr`st2`] >>
  `env_consistent env cx st2` by (simp[Abbr`st2`] >> irule push_scope_env_consistent >> simp[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    rename1 `eval_stmts cx ss' st2 = (res1,st1')` >>
    qunabbrev_tac`P` >> BETA_TAC >>
    `state_well_typed st2` by (
      irule push_scope_preserves_state_well_typed >>
      qexists_tac `st1` >> qexists_tac `()` >>
      simp[push_scope_def, return_def, Abbr`st2`]) >>
    first_x_assum drule_all >> strip_tac >>
    qpat_x_assum `!env ret_ty env' st' res st''. _` kall_tac >>
    simp[] >>
    `st2 = st1 with scopes := FEMPTY::st1.scopes`
      by simp[evaluation_state_component_equality, Abbr`st2`] >>
    conj_tac >- (
      strip_tac >> gvs[] >>
      drule eval_stmts_preserves_scopes_len >> simp[]) >>
    Cases_on `res1` >> gvs[]
    >- (
      Cases_on `st1'.scopes` >> gvs[]
      >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
      irule type_stmts_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
        simp[] >> disch_then irule >>
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      conj_tac >- (
        qexists_tac `x''` >>
        qexists_tac `ret_ty` >>
        qexists_tac `ss'` >> simp[] >>
        rpt strip_tac >> fs[] >>
        drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
        strip_tac >> gvs[FDOM_FEMPTY] >>
        drule lookup_scopes_is_some_same_fdoms >> simp[] >>
        disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
        qpat_x_assum `env_consistent env cx st1` mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
        strip_tac >> strip_tac >>
        Cases_on `lookup_scopes id t` >> gvs[] >>
        qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
          (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INL ()`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >>
      disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INL ()` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    conj_tac >- (
      irule env_extends_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>


      conj_tac >- (
        conj_tac >- (
          rpt strip_tac >> fs[] >>
          `?entry. lookup_scopes id st1.scopes = SOME entry` by (
            qpat_x_assum`env_consistent _ _ st1`mp_tac >>
            simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
          `FLOOKUP h id = NONE` suffices_by simp[] >>
          drule lookup_scopes_not_in_new_head >>
          disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
          simp[] >>
          disch_then irule >> simp[]) >>
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >>
        disch_then irule >> simp[]) >>
      conj_tac >- (
        qexists_tac `env_exn` >> simp[] >>
        rpt strip_tac >> fs[] >>
        `lookup_scopes id st1.scopes = NONE` by (
          qpat_x_assum`env_consistent env cx st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
          Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
          metis_tac[optionTheory.IS_SOME_DEF]) >>
        qspecl_then [`cx`, `ss'`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
          mp_tac eval_stmts_preserves_tail_lookup_none >>
        simp[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INR y`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >> disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INR y` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    irule env_extends_return_exception_typed >>
    qexists_tac `env_exn` >> simp[]) >>
  conj_tac >- (
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx ss st2 = (res1,st1')` >>
  qunabbrev_tac`P` >> BETA_TAC >>
  `state_well_typed st2` by (
    irule push_scope_preserves_state_well_typed >>
    qexists_tac `st1` >> qexists_tac `()` >>
    simp[push_scope_def, return_def, Abbr`st2`]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[] >>
  `st2 = st1 with scopes := FEMPTY::st1.scopes`
    by simp[evaluation_state_component_equality, Abbr`st2`] >>
  conj_tac >- (
    strip_tac >> gvs[] >>
    drule eval_stmts_preserves_scopes_len >> simp[]) >>
  Cases_on `res1` >> gvs[]
  >- (
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    irule type_stmts_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      rpt strip_tac >> fs[] >>
      drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
      simp[] >> disch_then irule >>
      qpat_x_assum`env_consistent _ _ st1`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
    conj_tac >- (
      qexists_tac `x` >>
      qexists_tac `ret_ty` >>
      qexists_tac `ss` >> simp[] >>
      rpt strip_tac >> fs[] >>
      drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
      strip_tac >> gvs[FDOM_FEMPTY] >>
      drule lookup_scopes_is_some_same_fdoms >> simp[] >>
      disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
      qpat_x_assum `env_consistent env cx st1` mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
      strip_tac >> strip_tac >>
      Cases_on `lookup_scopes id t` >> gvs[] >>
      qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
        (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INL ()`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >>
    disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INL ()` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  Cases_on `st1'.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
  conj_tac >- (
    irule env_extends_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >> disch_then irule >> simp[]) >>
      rpt strip_tac >> fs[] >>
      `?entry. lookup_scopes id st1.scopes = SOME entry` by (
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      `FLOOKUP h id = NONE` suffices_by simp[] >>
      drule lookup_scopes_not_in_new_head >>
      disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
      simp[] >> disch_then irule >> simp[]) >>
    conj_tac >- (
      qexists_tac `env_exn` >> simp[] >>
      rpt strip_tac >> fs[] >>
      `lookup_scopes id st1.scopes = NONE` by (
        qpat_x_assum`env_consistent env cx st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
        Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
        metis_tac[optionTheory.IS_SOME_DEF]) >>
      qspecl_then [`cx`, `ss`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
        mp_tac eval_stmts_preserves_tail_lookup_none >>
      simp[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INR y`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >> disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INR y` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  irule env_extends_return_exception_typed >>
  qexists_tac `env_exn` >> simp[]) >>
  metis_tac[]
QED

Resume eval_scc_type_sound_results_mutual[Expr]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Expr e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, type_check_def,
    assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> Cases_on `x` >>
    gvs[eval_result_typed_def]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Stmts_nil]:
  rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, Once evaluate_def,
      return_def, no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Stmts_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmts (s::ss))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmt s)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_stmts ss` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_stmt s` >> simp[]) >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `r1` >> gvs[]
  >- (
    Cases_on `eval_stmts cx ss st1` >>
    rename1 `eval_stmts cx ss st1 = (r2,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    strip_tac >> fs[bind_def] >> gvs[] >>
    Cases_on `r2` >> gvs[no_type_error_result_def]
    >- (
      qexists_tac `env_exn` >> simp[] >>
      irule env_extends_trans >>
      qexists_tac `env''` >> simp[] >>
      irule type_stmt_env_extends >> simp[] >>
      conj_tac >- (irule env_consistent_env_maps_wf >> goal_assum drule >> simp[]) >>
      qexists_tac `ret_ty` >> qexists_tac `s` >> simp[]) >>
    simp[]) >>
  strip_tac >> gvs[] >>
  qexists_tac `env` >> simp[env_extends_refl]
QED

Resume eval_scc_type_sound_results_mutual[For]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (For id typ it n body'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_iterator it)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_stmts body'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts body')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_iterator it` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `env.type_defs = get_tenv cx` by (
    qpat_x_assum `env_consistent env cx st` mp_tac >>
    rewrite_tac[env_consistent_def, env_context_consistent_def] >>
    strip_tac >> simp[]) >>
  `?env_after. type_stmts (extend_local env id typ F) ret_ty body' = SOME env_after` by (
    qpat_x_assum `IS_SOME (type_stmts (extend_local env id typ F) ret_ty body')` mp_tac >>
    rewrite_tac[optionTheory.IS_SOME_EXISTS]) >>
  `well_formed_type env.type_defs typ` by metis_tac[assignable_type_well_formed] >>
  qpat_x_assum `well_formed_type env.type_defs typ` mp_tac >>
  qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >>
  rewrite_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME iter_tyv` >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
       check_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (iter_res, st1)` >>
  qpat_x_assum `!tenv s'' tyv t. _`
    (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`] mp_tac) >>
  impl_tac >- simp[lift_option_type_def, return_def] >>
  disch_then (qspecl_then [`env`, `typ`, `st`, `iter_res`, `st1`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  Cases_on `iter_res`
  >- (
    rename1 `eval_iterator cx it st = (INL vs, st1)` >>
    qpat_x_assum `case INL vs of INL vs => _ | INR v1 => _`
      (mp_tac o SIMP_RULE (srw_ss()) []) >>
    strip_tac >>
    `tyv = iter_tyv` by (
      qpat_x_assum `evaluate_type env.type_defs typ = SOME tyv` mp_tac >>
      qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >>
      qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
      simp[]) >>
    qpat_x_assum `EVERY (iterator_result_typed tyv) vs` mp_tac >>
    qpat_x_assum `tyv = iter_tyv` (fn th => rewrite_tac[th]) >>
    strip_tac >>
    Cases_on `compatible_bound (Dynamic n) (LENGTH vs)`
    >- (
      qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
      qpat_assum `eval_iterator cx it st = (INL vs, st1)` (fn th => rewrite_tac[th]) >>
      rewrite_tac[bind_def, return_def, raise_def, assert_def, check_def, lift_option_type_def] >>
      Cases_on `eval_for cx iter_tyv id body' vs st1` >>
      rename1 `eval_for cx iter_tyv id body' vs st1 = (for_res, st2)` >>
      qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _`
        (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`, `st`, `vs`, `st1`, `st1`, `()`, `st1`] mp_tac) >>
      impl_tac >- simp[lift_option_type_def, return_def, check_def, assert_def] >>
      disch_then (qspecl_then [`env`, `ret_ty`, `typ`, `env_after`, `st1`, `for_res`, `st2`] mp_tac) >>
      simp[bind_def, ignore_bind_def, return_def, assert_def] >> strip_tac >>
      strip_tac >> gvs[no_type_error_result_def]) >>
    strip_tac >>
    qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _` kall_tac >>
    qpat_x_assum `(let tenv = get_tenv cx in _) st = (res,st')` mp_tac >>
    qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
    qpat_assum `eval_iterator cx it st = (INL vs, st1)` (fn th => rewrite_tac[th]) >>
    simp[LET_THM, bind_def, ignore_bind_def, return_def, assert_def, raise_def,
        check_def, lift_option_type_def, no_type_error_result_def,
        return_exception_typed_def] >> strip_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _` kall_tac >>
  qpat_x_assum `(let tenv = get_tenv cx in _) st = (res,st')` mp_tac >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
  qpat_assum `eval_iterator cx it st = (INR y, st1)` (fn th => rewrite_tac[th]) >>
  simp[LET_THM, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_type_def] >>
  strip_tac >> gvs[] >>
  conj_tac >- (
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def]) >>
  irule no_control_exc_return_exception_typed >>
  drule eval_iterator_no_control >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[For_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ [] _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >> gvs[no_type_error_result_def]
QED


Resume eval_scc_type_sound_results_mutual[For_cons]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_for _ _ _ _ (r::vs) _ = _` >>
  `iterator_result_typed tyv r /\ EVERY (iterator_result_typed tyv) vs` by fs[] >>
  Cases_on `read_result cx r st` >>
  rename1 `read_result cx r st = (rd_res, st_rd)` >>
  drule_all iterator_result_read_typed >> strip_tac >>
  qpat_x_assum `st_rd = st` SUBST_ALL_TAC >>
  Cases_on `rd_res`
  >~ [`read_result cx r st = (INR exn, st)`]
  >- (
    qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
    qpat_assum `read_result cx r st = _` (fn th => rewrite_tac[th]) >>
    simp_tac(srw_ss())[] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    drule read_result_no_control >>
    simp_tac(srw_ss())[no_control_exc_def] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (qpat_x_assum `no_type_error_result _` mp_tac) >>
    simp_tac(srw_ss())[return_exception_typed_def, no_type_error_result_def]) >>
  rename1 `read_result cx r st = (INL v, st)` >>
  `value_has_type tyv v` by fs[] >>
  qpat_x_assum `EVERY _ (_::_)` kall_tac >>
  qpat_x_assum `no_type_error_result (INL _)` kall_tac >>
  qpat_x_assum `case INL v of INL _ => _ | INR _ => _` kall_tac >>
  qpat_x_assum `read_result cx r st = (INL v,st)` (fn rd =>
    rpt (last_x_assum (fn ih => assume_tac (REWRITE_RULE [rd]
      (SPECL [``st:evaluation_state``, ``v:value``, ``st:evaluation_state``] ih)))) >>
    assume_tac rd) >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       push_scope_with_var_def, return_def] >>
  qpat_assum `read_result cx r st = _` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (loop_res, st_after)` >>
  strip_tac >>
  `stp =
    st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>))` by
    simp[Abbr`stp`] >>
  qunabbrev_tac `loop_body` >>
  drule for_body_decompose_for_cons_pushed >>
  rewrite_tac[ignore_bind_def] >>
  disch_then drule >>
  strip_tac >>
  `env.type_defs = get_tenv cx` by (
    qpat_x_assum `env_consistent env cx st` mp_tac >>
    simp_tac (srw_ss()) [env_consistent_def, env_context_consistent_def] >>
    rpt strip_tac) >>
  `state_well_typed stp` by (
    `well_formed_type_value tyv` by (
      qpat_assum `evaluate_type env.type_defs ty = SOME tyv`
        (ACCEPT_TAC o MATCH_MP evaluate_type_well_formed_type_value)) >>
    qpat_x_assum `stp = _` SUBST1_TAC >>
    irule for_cons_pushed_state_well_typed >>
    simp[]) >>
  `accounts_well_typed stp.accounts` by (
    qpat_x_assum `stp = _` SUBST1_TAC >>
    simp[NoAsms, evaluation_state_component_equality] >>
    qpat_assum `accounts_well_typed st.accounts` ACCEPT_TAC) >>
  `env_consistent (extend_local env id ty F) cx stp` by (
    qunabbrev_tac `stp` >>
    metis_tac[push_scope_with_var_env_consistent]) >>
  qpat_x_assum `!s'' x t. push_scope_with_var id tyv v s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `stp`] mp_tac) >>
  impl_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
  disch_then (qspecl_then [`extend_local env id ty F`, `ret_ty`, `env_after`,
                           `stp`, `res_body`, `st_body`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  Cases_on `res_body` >> simp[NoAsms]
  >- (
    `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
      irule scope_bracket_preserves_swt >> simp[] >>
      qexists_tac `cx` >> qexists_tac `INL x` >>
      qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
      qexists_tac `body'` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
    `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
      (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
    `env_consistent env cx (st_body with scopes := TL st_body.scopes)` by (
      `env_consistent env_after cx st_body` by (
        qpat_x_assum `case (INL x : unit + vyperState$exception) of INL u => _ | INR exn => _` mp_tac >>
        simp[NoAsms]) >>
      qpat_x_assum `stp = _` SUBST_ALL_TAC >>
      metis_tac[for_body_env_consistent_after_pop, env_consistent_env_maps_wf]) >>
    qpat_x_assum `!s'' x' t s''' broke t'. _`
      (qspecl_then [`st`, `()`, `stp`, `stp`, `F`,
                    `st_body with scopes := TL st_body.scopes`] mp_tac) >>
    impl_tac >- (
      conj_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
      conj_tac >- (
        `loop_res = INL F` by (
          qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
          simp[]) >>
        qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
        qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
        qpat_x_assum `stp = _` SUBST_ALL_TAC >>
        qpat_x_assum `finally _ _ _ = (INL F, _)` mp_tac >>
        strip_tac >>
        pop_assum mp_tac >>
        simp[NoAsms, bind_def, ignore_bind_def]) >>
      simp[]) >>
    `loop_res = INL F` by (
      qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body' vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                             `st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    (impl_tac >- fs[]) >>
    simp[]) >>
  `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
    irule scope_bracket_preserves_swt >> simp[] >>
    qexists_tac `cx` >> qexists_tac `INR y` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
    qexists_tac `body'` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
  `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
    simp[evaluation_state_component_equality] >>
  SUBGOAL_THEN ``env_consistent env cx (st_body with scopes := TL st_body.scopes)`` assume_tac >- (
    irule for_cons_popped_env_consistent_from_stmt_case >>
    qexists_tac `body'` >> qexists_tac `y` >> qexists_tac `id` >>
    qexists_tac `\u. env_consistent env_after cx st_body` >>
    qexists_tac `ret_ty` >> qexists_tac `st` >> qexists_tac `ty` >>
    qexists_tac `tyv` >> qexists_tac `v` >>
    conj_tac >- simp[] >>
    conj_tac >- simp[Abbr`stp`] >>
    conj_tac >- simp[] >>
    asm_rewrite_tac[]) >>
  Cases_on `y = ContinueException`
  >- (
    qpat_x_assum `y = ContinueException` SUBST_ALL_TAC >>
    qpat_x_assum `!s'' x t s'³' broke t'. _`
      (qspecl_then [`st`, `()`, `stp`, `stp`, `F`,
                    `st_body with scopes := TL st_body.scopes`] mp_tac) >>
    impl_tac >- (
      conj_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
      conj_tac >- (
        `loop_res = INL F` by (
          qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
          simp[]) >>
        qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
        qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
        qpat_x_assum `stp = _` SUBST_ALL_TAC >>
        qpat_x_assum `finally _ pop_scope _ = (INL F, _)` mp_tac >>
        strip_tac >>
        pop_assum mp_tac >>
        simp[NoAsms, bind_def, ignore_bind_def]) >>
      simp[]) >>
    `loop_res = INL F` by (
      qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body' vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                             `st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    (impl_tac >- fs[]) >>
    simp[]) >>
  Cases_on `y = BreakException`
  >- (
    qpat_x_assum `y = BreakException` SUBST_ALL_TAC >>
    `loop_res = INL T` by (
      qpat_x_assum `INR BreakException = INR BreakException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL T` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    qpat_x_assum `(case (INL T,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
    simp[NoAsms, return_def] >>
    strip_tac >>
    qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
    simp[no_type_error_result_def]) >>
  `loop_res = INR y` by (
    qpat_x_assum `!e. INR y = INR e /\ e <> ContinueException /\ e <> BreakException ==> _`
      (qspec_then `y` irule) >>
    simp[]) >>
  qpat_x_assum `loop_res = INR y` SUBST_ALL_TAC >>
  qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
  qpat_x_assum `(case (INR y,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[NoAsms] >>
  strip_tac >>
  qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!s'' x t s'³' broke t'. _` kall_tac >>
  qmatch_goalsub_abbrev_tac `state_well_typed stfinal` >>
  qunabbrev_tac `stfinal` >>
  irule for_cons_non_loop_exception_suffix_projected >>
  simp[] >>
  conj_tac >- (
    simp[no_type_error_result_def] >> strip_tac >>
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def] >>
    disch_then (qspec_then `msg` mp_tac) >> simp[]) >>
  fs[] >>
  qexists_tac `id` >> qexists_tac `ty` >>
  qexists_tac `env_exn` >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Iterator_Array]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Array e))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tvl, st1)` >>
    qpat_x_assum `!env' st' res st''. _ ==> case res of INL pv => live_memory_result st'' pv | INR _ => T`
      (qspecl_then [`env`,`st`,`INL tvl`,`st1`] mp_tac) >>
    simp[] >> strip_tac >>
    qpat_x_assum `!env' st' res st''. _ ==> typed_scope_transition st' st''` kall_tac >>
    `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
    strip_tac >>
    drule_at (Pos last) array_iterator_results_typed >>
    disch_then (qspec_then `env` mp_tac) >>
    impl_tac >- simp[] >>
    strip_tac >> gvs[no_type_error_result_def]) >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Iterator_Range]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Range e e'))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr1_res, st1)` >>
  last_x_assum drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `expr1_res`
  >- (
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    rename1 `eval_expr cx e st = (INL tv1, st1)` >>
    qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result st' pv | INR _ => T`
      (qspecl_then [`env`,`st`,`INL tv1`,`st1`] mp_tac) >>
    (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition st st'` kall_tac >>
    qpat_x_assum `case INL tv1 of INL pv => eval_result_typed _ pv _ | INR _ => T` mp_tac >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
    Cases_on `read_result cx tv1 st1` >>
    rename1 `read_result cx tv1 st1 = (val1_res, st2)` >>
    drule_all live_result_read_typed >> strip_tac >>
    Cases_on `val1_res`
    >- (
      rename1 `read_result cx tv1 st1 = (INL v1, st2)` >>
      drule read_result_state >> strip_tac >>
      qpat_x_assum `st2 = st1` SUBST_ALL_TAC >>
      qpat_x_assum `!s'' tv1 t s''' s t'. _`
        (qspecl_then [`st`, `tv1`, `st1`, `st1`, `v1`, `st1`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (expr2_res, st3)` >>
      qpat_x_assum `!env' st' res st''. _ ==> case res of INL pv => live_memory_result st'' pv | INR _ => T`
        (qspecl_then [`env`, `st1`, `expr2_res`, `st3`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `!env' st' res st''. _ ==> typed_scope_transition st' st''` kall_tac >>
      qpat_x_assum `!env' st' res st''. _ ==> (_ /\ _)`
        (qspecl_then [`env`, `st1`, `expr2_res`, `st3`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on `expr2_res`
      >- (
        qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
        rename1 `eval_expr cx e' st1 = (INL tv2, st3)` >>
        Cases_on `read_result cx tv2 st3` >>
        rename1 `read_result cx tv2 st3 = (val2_res, st4)` >>
        drule_at (Pat `read_result`) live_result_read_typed >>
        disch_then (qspecl_then [`ty`,`env`] mp_tac) >>
        (impl_tac >- gvs[]) >> strip_tac >>
        Cases_on `val2_res`
        >- (
          qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
          rename1 `read_result cx tv2 st3 = (INL v2, st4)` >>
          drule read_result_state >> strip_tac >>
          qpat_x_assum `st4 = st3` SUBST_ALL_TAC >>
          gvs[value_runtime_typed_def] >>
          `?i1. v1 = IntV i1` by metis_tac[int_typed_value_is_IntV] >>
          `?i2. v2 = IntV i2` by metis_tac[int_typed_value_is_IntV] >>
          gvs[] >>
          Cases_on `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3` >>
          rename1 `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3 = (range_res, st5)` >>
          strip_tac >>
          qspecl_then [`env.type_defs`, `expr_type e`, `tv`, `i1`, `i2`,
                       `range_res`, `st3`, `st5`, `res`, `st'`]
            mp_tac iterator_range_tail_eval_sound >>
          impl_tac >- (
            simp[] >>
            Cases_on `range_res` >> gvs[return_def, raise_def]) >>
          strip_tac >> gvs[]) >>
        strip_tac >> gvs[no_type_error_result_def]) >>
      strip_tac >> gvs[return_def, no_type_error_result_def] >> metis_tac[]) >>
    qpat_x_assum `!s'' tv1 t s''' s t'. _` kall_tac >>
    strip_tac >> gvs[no_type_error_result_def]) >>
  qpat_x_assum `!s'' tv1 t s''' s t'. _` kall_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T` kall_tac >>
  pure_rewrite_tac[sumTheory.sum_case_def, pairTheory.UNCURRY] >>
  strip_tac >> gvs[no_type_error_result_def]
QED

(* Legacy wrappers have their own, disconnected structural induction. *)


Resume eval_scc_type_sound_results_mutual[BasePlaceRoot_NameTarget]:
  rpt gen_tac >> strip_tac >>
  `?ty. vt = Type ty` by
    gvs[type_place_target_NameTarget, AllCaseEqs()] >>
  gvs[] >>
  drule_all NameTarget_sound >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, assert_def, ignore_bind_def,
    get_scopes_def, type_check_def, lift_option_type_def, lift_option_def] >>
  strip_tac >> gvs[] >>
  simp[no_type_error_result_def, runtime_place_typed_memory, subscripts_type_def] >>
  gvs[type_place_target_NameTarget, AllCaseEqs(),
      env_consistent_def, env_scopes_consistent_def, env_context_consistent_def] >>
  `EVERY scope_well_typed st.scopes` by gvs[state_well_typed_def] >>
  drule_all lookup_scopes_well_typed_type >> strip_tac >>
  metis_tac[]
QED

Resume eval_scc_type_sound_results_mutual[BasePlaceRoot_TopLevelNameTarget]:
  rpt gen_tac >> strip_tac >>
  drule eval_base_place_TopLevelNameTarget_preserves_state >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def] >> strip_tac >>
  drule_all lookup_global_target_no_type_error >> strip_tac >>
  `state_well_typed st' /\ env_consistent env cx st' /\
   accounts_well_typed st'.accounts` by
    (qpat_x_assum `st' = _` SUBST1_TAC >> simp[]) >>
  simp[] >> Cases_on `res` >> simp[] >>
  drule_all lookup_global_target_success_typed >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[BasePlaceRoot_SubscriptTarget]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_base_place cx (SubscriptTarget t e) st = (res,st')` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (SubscriptTarget t e))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target t)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target t` >> simp[]) >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx t st` >>
  rename1 `eval_base_place cx t st = (bt_res, st1)` >>
  qpat_assum `!env vt st res st'. _ ==> state_well_typed st' /\ _`
    drule_all >> strip_tac >>
  Cases_on `bt_res`
  >- (rename1 `eval_base_place cx t st = (INL pv,st1)` >>
      qpat_x_assum `!s'' pv t'. eval_base_place _ _ _ = _ ==> _` drule >> strip_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        drule_all >> pure_rewrite_tac[sumTheory.sum_case_def] >> strip_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => writable_place_result _ _ _ | INR _ => T` kall_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _` kall_tac >>
      simp_tac (srw_ss()) [] >>
      Cases_on `eval_expr cx e st1` >>
      rename1 `eval_expr cx e st1 = (er,st2)` >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (qspecl_then [`env`,`st1`,`er`,`st2`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        (qspecl_then [`env`,`st1`,`er`,`st2`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
      qpat_x_assum `well_typed_expr env e ==> _` drule >>
      simp[] >> strip_tac >>
      Cases_on `er` >> gvs[no_type_error_result_def]
      >- (rename1 `read_result cx idx st2` >>
          Cases_on `read_result cx idx st2` >>
          rename1 `read_result cx idx st2 = (rr,st3)` >>
          drule_all live_result_read_typed >> strip_tac >> gvs[] >>
          Cases_on `rr` >> gvs[no_type_error_result_def]
          >- (rename1 `read_result cx idx st2 = (INL v,st2)` >>
              `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
                (drule eval_expr_immutable_metadata_frame >> simp[]) >>
              `eval_result_typed (env,cx,st2) pv vt'` by
                (irule eval_result_typed_transport >> goal_assum drule_all) >>
              `live_memory_result st2 pv` by
                (Cases_on `pv`
                 >- simp[live_memory_result_def]
                 >- (rename1 `PlaceR p` >> Cases_on `p`
                     >- simp[live_memory_result_def]
                     >- (irule live_memory_result_transport >> goal_assum drule_all)
                     >> simp[live_memory_result_def])
                 >> simp[live_memory_result_def]) >>
              `well_formed_vtype env.type_defs vt'` by
                metis_tac[type_place_target_well_formed_vtype_stmt] >>
              `case pv of Value _ => F | _ => T` by
                (drule eval_base_place_result_shape >> strip_tac >> gvs[]) >>
              `expr_result_typed env e (Value v)` by
                gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def,
                    value_result_typed_def] >>
              strip_tac >>
              drule vyperPlaceFramesTheory.extend_place_state >> strip_tac >> gvs[] >>
              drule_all extend_target_subscript_place_sound >>
              simp[no_type_error_result_def] >> strip_tac >>
              qpat_x_assum `st' = _` SUBST1_TAC >> simp[]) >>
          strip_tac >> gvs[]) >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' pv t'. eval_base_place _ _ _ = _ ==> _` kall_tac >>
  gvs[no_type_error_result_def] >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[BasePlaceRoot_AttributeTarget]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_base_place cx (AttributeTarget bt id) st = (res,st')` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (AttributeTarget bt id))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  rewrite_tac[type_place_target_AttributeTarget] >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >>
  rename1 `eval_base_place cx bt st = (br,st1)` >>
  qpat_x_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    drule_all >> strip_tac >>
  Cases_on `br`
  >- (rename1 `eval_base_place cx bt st = (INL pv,st1)` >>
      qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        drule_all >> pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
      qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => writable_place_result _ _ _ | INR _ => T` kall_tac >>
      simp[] >> strip_tac >>
      drule vyperPlaceFramesTheory.extend_place_state >> strip_tac >> gvs[] >>
      drule eval_base_place_result_shape >> strip_tac >> gvs[eval_result_typed_def] >>
      drule_all attribute_type_runtime_step >> strip_tac >>
      drule_all extend_live_place_attribute_no_type_error >> strip_tac >>
      `state_well_typed st' /\ env_consistent env cx st' /\
       accounts_well_typed st'.accounts` by
        (qpat_x_assum `st' = _` SUBST1_TAC >> simp[]) >>
      simp[] >> Cases_on `res` >> simp[] >>
      drule extend_place_place_success_shape >> strip_tac >> gvs[] >>
      drule_all extend_place_typed >> simp[]) >>
  strip_tac >> gvs[no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Name]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      drule_all well_typed_Name_lookup >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
           bind_def, get_scopes_def, return_def] >>
      strip_tac >> gvs[] >>
      simp[no_type_error_result_def, eval_result_typed_def, expr_type_def,
           runtime_place_typed_memory, subscripts_type_def] >>
      `EVERY scope_well_typed st.scopes` by gvs[state_well_typed_def] >>
      drule_all lookup_scopes_well_typed_type >> strip_tac >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_TopLevelName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[] >>
  `state_well_typed st' /\ env_consistent env cx st' /\
   accounts_well_typed st'.accounts` by
    (qpat_x_assum `st' = _` SUBST1_TAC >> simp[]) >>
  conj_tac
  >- (strip_tac >> simp[expr_type_def] >>
      metis_tac[lookup_global_TopLevelName_sound]) >>
  rpt strip_tac >> metis_tac[lookup_global_TopLevelName_place_sound]
QED

Resume eval_scc_type_sound_results_mutual[Expr_FlagMember]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> gvs[] >> conj_tac
  >- (disch_tac >>
      drule_all flag_member_sound >> strip_tac >>
      imp_res_tac lookup_flag_mem_state >> gvs[] >>
      PairCases_on `nsid` >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      qpat_x_assum `!src fid ls. FLOOKUP env.flag_members (src,fid) = SOME ls ==> _`
        (drule_then strip_assume_tac) >>
      `LENGTH members <= 256` by (
        qpat_x_assum `well_typed_expr env (FlagMember _ _ _)` mp_tac >>
        gvs[well_typed_expr_def, well_formed_type_def, evaluate_type_def] >>
        decide_tac) >>
      qpat_x_assum `lookup_flag_mem _ _ _ _ = _` mp_tac >>
      simp[lookup_flag_mem_def, return_def, raise_def] >>
      Cases_on `INDEX_OF mid members` >> strip_tac >>
      gvs[return_def, no_type_error_result_def, expr_result_typed_def,
          expr_runtime_typed_def, expr_type_def, value_result_typed_Value,
          evaluate_type_def, value_has_type_def, INDEX_OF_eq_NONE,
          INDEX_OF_eq_SOME] >>
      irule bitTheory.TWOEXP_MONO >> simp[]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED


(* ===== If-expression case ===== *)


Resume eval_scc_type_sound_results_mutual[Expr_IfExp]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (IfExp ty e e' e''))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e'')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  reverse conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (IfExp _ _ _ _) = SOME _` mp_tac >>
    simp[type_place_expr_IfExp_NONE]) >>
  disch_then mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  rename1 `expr_type e' = ty` >>
  qpat_x_assum `!s0 pv t. eval_expr cx e s0 = (INL pv,t) ==> _`
    (mk_asm "true_branch") >>
  qpat_x_assum `!s0 pv t. eval_expr cx e s0 = (INL pv,t) ==> _`
    (mk_asm "false_branch") >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (cr,st1)` >>
  qpat_x_assum `!env st res st'. env_consistent _ _ _ /\ _ ==> _`
    (qspecl_then [`env`,`st`,`cr`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  reverse (Cases_on `cr`)
  >- (asm_x "true_branch" kall_tac >> asm_x "false_branch" kall_tac >>
      qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def] >> strip_tac >> gvs[]) >>
  rename1 `eval_expr cx e st = (INL cond_pv,st1)` >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
    (qspecl_then [`env`,`st`,`INL cond_pv`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> simp_tac bool_ss [] >> disch_tac >>
  asm_x "true_branch" mp_tac >>
  disch_then (qspecl_then [`st`,`cond_pv`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm_x "false_branch" mp_tac >>
  disch_then (qspecl_then [`st`,`cond_pv`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `switch_BoolV cx cond_pv (eval_expr cx e') (eval_expr cx e'') st1` >>
  rename1 `switch_BoolV _ _ _ _ _ = (br,st2)` >>
  `state_well_typed st2 /\ env_consistent env cx st2 /\
   accounts_well_typed st2.accounts /\ no_type_error_result br /\
   (case br of INL pv => eval_result_typed (env,cx,st2) pv (Type ty) /\
                        live_memory_result st2 pv | INR _ => T)` by
    (qho_match_abbrev_tac `P br st2` >>
     irule switch_BoolV_live_post >>
     goal_assum $ drule_at (Pat `switch_BoolV`) >>
     qexists `env` >> simp[expr_type_def] >> conj_tac
     >- (rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         simp[Abbr `P`, no_type_error_result_def]) >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_x_assum `!env st res st'. env_consistent _ _ _ /\ _ ==> (well_typed_expr env e'' ==> _) /\ _`
           (qspecl_then [`env`,`st1`,`r`,`s`] mp_tac) >>
         (impl_tac >- simp[]) >> strip_tac >>
         qpat_x_assum `well_typed_expr env e'' ==> _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >>
         qpat_x_assum `!env st res st'. (well_typed_expr env e'' \/ _) /\ _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
           (qspecl_then [`env`,`st1`,`r`,`s`] mp_tac) >>
         (impl_tac >- simp[]) >>
         rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         Cases_on `r` >> gvs[Abbr `P`]) >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_x_assum `!env st res st'. env_consistent _ _ _ /\ _ ==> (well_typed_expr env e' ==> _) /\ _`
           (qspecl_then [`env`,`st1`,`r`,`s`] mp_tac) >>
         (impl_tac >- simp[]) >> strip_tac >>
         qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
         (impl_tac >- simp[]) >> strip_tac >>
         qpat_x_assum `!env st res st'. (well_typed_expr env e' \/ _) /\ _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
           (qspecl_then [`env`,`st1`,`r`,`s`] mp_tac) >>
         (impl_tac >- simp[]) >>
         rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         Cases_on `r` >> gvs[Abbr `P`]) >>
     rpt (qpat_x_assum `!env st res st'. _` kall_tac) >> gvs[]) >>
  rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `br` >> simp[] >> strip_tac >>
  gvs[] >>
  drule_all conditional_result_live_typed >> strip_tac >>
  Cases_on `res` >> gvs[expr_type_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Literal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >>
  gvs[no_type_error_result_def, well_typed_expr_def, well_formed_type_def,
      expr_type_def, optionTheory.IS_SOME_EXISTS] >>
  rw[expr_result_typed_def, expr_runtime_typed_def, expr_type_def] >>
  drule_all literal_value_result_typed >> simp[value_result_typed_def] >>
  metis_tac[]
QED


(* ===== Struct literal case ===== *)


Resume eval_scc_type_sound_results_mutual[Expr_StructLit]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (StructLit ty callee kes))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def, GSYM int_calls_exprs_MAP_SND] >> strip_tac >>
  reverse conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (StructLit _ _ _) = SOME _` mp_tac >>
    simp[type_place_expr_StructLit_NONE_stmt]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,st1)` >>
  qpat_x_assum `!ks. ks = MAP FST kes ==> _` (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_stmt >> first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then drule_all >> strip_tac >>
  Cases_on `exprs_res` >> simp_tac(srw_ss())[]
  >- (
    strip_tac >>
    qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
    asm_simp_tac(srw_ss())[bind_def, return_def, LET_THM] >>
    strip_tac >> gvs[no_type_error_result_def] >>
    simp[expr_type_def] >>
    irule (SRULE [eval_result_typed_def] struct_lit_expr_result_typed) >>
    asm_rewrite_tac[] >> qexists `kes` >> asm_rewrite_tac[])
  >- (
    strip_tac >>
    qpat_x_assum `eval_exprs cx (MAP SND kes) st = (INR y,st1)` (fn ev_th =>
      qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
      asm_simp_tac(srw_ss())[Once bind_def, return_def, LET_THM, ev_th]) >>
    strip_tac >>
    gvs[] >>
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def])
QED


(* ===== Subscript expression case ===== *)


Resume eval_scc_type_sound_results_mutual[Expr_Subscript]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_right]) >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `well_typed_expr env (Subscript v9 e e')` mp_tac >>
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
      strip_tac
      >- (qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
          qpat_x_assum `eval_expr cx (Subscript _ e e') st = _` mp_tac >>
          simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
          Cases_on `eval_expr cx e st` >>
          rename1 `eval_expr cx e st = (br,st1)` >>
          qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
            (qspecl_then [`env`,`st`,`br`,`st1`] mp_tac) >>
          (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
          qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
          qpat_x_assum `well_typed_expr env e ==> _` drule >>
          simp_tac(srw_ss())[] >> strip_tac >>
          Cases_on `br`
          >- (rename1 `eval_expr cx e st = (INL raw_base_pv,st1)` >>
              rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
              rule_assum_tac BETA_RULE >>
              simp_tac(srw_ss())[] >>
              Cases_on `(if subscript_reads_base cx e e' then
                bind (read_result cx raw_base_pv) (\v. return (Value v))
                else return raw_base_pv) st1` >>
              rename1 `_ st1 = (base_res,base_st)` >>
              drule_all optional_read_result_live_typed >> strip_tac >>
              reverse (Cases_on `base_res`)
              >- (qpat_x_assum `!s tv t s1 tv1 t1. _` kall_tac >>
                  simp_tac(srw_ss())[] >> strip_tac >> gvs[]) >>
              rename1 `_ st1 = (INL base_pv,base_st)` >>
              qpat_x_assum `!s tv t s1 tv1 t1. _` drule_all >> strip_tac >>
              qpat_x_assum `base_st = st1` SUBST_ALL_TAC >>
              rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
              rule_assum_tac BETA_RULE >>
              simp_tac(srw_ss())[] >>
              Cases_on `eval_expr cx e' st1` >>
              rename1 `eval_expr cx e' st1 = (ir,st2)` >>
              qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
                (qspecl_then [`env`,`st1`,`ir`,`st2`] mp_tac) >>
              (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
              qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
                (qspecl_then [`env`,`st1`,`ir`,`st2`] mp_tac) >>
              (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
              qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
              qpat_x_assum `well_typed_expr env e' ==> _` drule >>
              simp_tac(srw_ss())[] >> strip_tac >>
              Cases_on `ir`
              >- (rename1 `eval_expr cx e' st1 = (INL idx,st2)` >>
                  simp_tac(srw_ss())[] >>
                  Cases_on `read_result cx idx st2` >>
                  rename1 `read_result cx idx st2 = (rr,st3)` >>
                  rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
                  rule_assum_tac BETA_RULE >>
                  qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` kall_tac >>
                  qpat_x_assum `!vt. type_place_expr env e' = SOME vt ==> _` kall_tac >>
                  drule_all live_result_read_typed >> strip_tac >> gvs[] >>
                  Cases_on `rr`
                  >- (rename1 `read_result cx idx st2 = (INL v,st2)` >>
                      `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
                        (drule eval_expr_immutable_metadata_frame >> simp[]) >>
                      `eval_result_typed (env,cx,st2) base_pv (Type (expr_type e))` by
                        (irule eval_result_typed_transport >> goal_assum drule_all) >>
                      `live_memory_result st2 base_pv` by
                        (Cases_on `base_pv`
                         >- simp[live_memory_result_def]
                         >- (rename1 `PlaceR p` >> Cases_on `p`
                             >- simp[live_memory_result_def]
                             >- (irule live_memory_result_transport >> goal_assum drule_all)
                             >> simp[live_memory_result_def])
                         >> simp[live_memory_result_def]) >>
                      `subscript_index_matches (expr_type e) e' v` by
                        (drule_all eval_expr_subscript_index_matches_stmt >> simp[]) >>
                      simp_tac(srw_ss())[] >> strip_tac >>
                      rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
                      rule_assum_tac BETA_RULE >>
                      drule_all select_ordinary_subscript_sound >> strip_tac >> gvs[expr_type_def]) >>
                  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
              simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
          qpat_x_assum `!s'' pv t. _` kall_tac >>
          simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
      simp_tac(srw_ss())[expr_type_def] >>
      suspend "Expr_Subscript_projection") >>
  gen_tac >> strip_tac >>
  qpat_x_assum `type_place_expr env (Subscript v9 e e') = SOME vt` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def, AllCaseEqs()] >>
  strip_tac >> suspend "Expr_Subscript_projection"
QED

Resume eval_scc_type_sound_results_mutual[Expr_Subscript_projection]:
  RESUME_TAC >> (
  qmatch_asmsub_rename_tac `type_place_expr env e = SOME bvt` >>
  `well_formed_vtype env.type_defs bvt` by
    metis_tac[type_place_expr_well_formed_vtype_stmt] >>
  `vtype_annotation_ok bvt (expr_type e)` by
    metis_tac[type_place_expr_annotation_ok_stmt] >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  qpat_x_assum `eval_expr cx (Subscript _ e e') st = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (br,st1)` >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (qspecl_then [`env`,`st`,`br`,`st1`] mp_tac) >>
  (impl_tac >- (conj_tac >- (disj2_tac >> goal_assum drule) >> simp[])) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` kall_tac >>
  qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _`
    (qspec_then `bvt` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `br`
  >- (rename1 `eval_expr cx e st = (INL raw_base_pv,st1)` >>
      rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
      rule_assum_tac BETA_RULE >> simp_tac(srw_ss())[] >>
      Cases_on `(if subscript_reads_base cx e e' then
        bind (read_result cx raw_base_pv) (\v. return (Value v))
        else return raw_base_pv) st1` >>
      rename1 `_ st1 = (base_res,base_st)` >>
      drule_all place_optional_read_result_live_typed >> strip_tac >>
      reverse (Cases_on `base_res`)
      >- (qpat_x_assum `!s tv t s1 tv1 t1. _` kall_tac >>
          simp_tac(srw_ss())[] >> strip_tac >> gvs[]) >>
      rename1 `_ st1 = (INL base_pv,base_st)` >>
      qpat_x_assum `!s tv t s1 tv1 t1. _` drule_all >> strip_tac >>
      qpat_x_assum `base_st = st1` SUBST_ALL_TAC >>
      rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
      rule_assum_tac BETA_RULE >>
      simp_tac(srw_ss())[] >>
      Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (ir,st2)` >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (qspecl_then [`env`,`st1`,`ir`,`st2`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        (qspecl_then [`env`,`st1`,`ir`,`st2`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
      qpat_x_assum `well_typed_expr env e' ==> _` drule >>
      simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `!vt. type_place_expr env e' = SOME vt ==> _` kall_tac >>
      Cases_on `ir`
      >- (rename1 `eval_expr cx e' st1 = (INL idx,st2)` >>
          simp_tac(srw_ss())[] >>
          Cases_on `read_result cx idx st2` >>
          rename1 `read_result cx idx st2 = (rr,st3)` >>
          rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
          rule_assum_tac BETA_RULE >>
          drule_all live_result_read_typed >> strip_tac >> gvs[] >>
          Cases_on `rr`
          >- (rename1 `read_result cx idx st2 = (INL v,st2)` >>
              `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
                (drule eval_expr_immutable_metadata_frame >> simp[]) >>
              `eval_result_typed (env,cx,st2) base_pv bvt` by
                (irule eval_result_typed_transport >> goal_assum drule_all) >>
              `live_memory_result st2 base_pv` by
                (Cases_on `base_pv`
                 >- simp[live_memory_result_def]
                 >- (rename1 `PlaceR p` >> Cases_on `p`
                     >- simp[live_memory_result_def]
                     >- (irule live_memory_result_transport >> goal_assum drule_all)
                     >> simp[live_memory_result_def])
                 >> simp[live_memory_result_def]) >>
              simp_tac(srw_ss())[] >> strip_tac >>
              rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
              rule_assum_tac BETA_RULE >>
              drule_all select_projection_subscript_sound >> strip_tac >> gvs[expr_type_def] >>
              qpat_x_assum `st' = _` SUBST1_TAC >> simp[]) >>
          simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
      simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]) >>
  qpat_x_assum `!s'' pv t. _` kall_tac >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def])
QED


(* ===== Attribute expression case ===== *)


Resume eval_scc_type_sound_results_mutual[Expr_Attribute]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Attribute ty e id))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> simp[]) >>
  reverse conj_tac >- (rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (Attribute _ _ _) = SOME _` mp_tac >>
    simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Attribute ty e id)` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
  strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  qpat_x_assum `eval_expr cx (Attribute ty e id) st = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (br,st1)` >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (qspecl_then [`env`,`st`,`br`,`st1`] mp_tac) >>
  (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` drule >>
  simp_tac(srw_ss())[] >> strip_tac >>
  Cases_on `br`
  >- (simp_tac(srw_ss())[] >> strip_tac >>
      rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
      rule_assum_tac BETA_RULE >>
      qpat_x_assum `attribute_type_ok _ _ _ _` mp_tac >>
      simp_tac(srw_ss())[attribute_type_ok_def] >> strip_tac >>
      drule_all select_attribute_sound >> strip_tac >> gvs[expr_type_def]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]
QED

(* ===== Builtin, type-builtin, and pop expression cases ===== *)


Resume eval_scc_type_sound_results_mutual[Expr_Builtin]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Builtin ty bt es))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Builtin _ _ _) = SOME _` mp_tac >>
      simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_def, env_context_consistent_def] >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (Builtin ty bt es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
                       type_check_def, assert_def] >>
  Cases_on `bt = Len`
  >- (`es <> []` by (
        Cases_on `es` >> simp[] >>
        qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type [])` mp_tac >>
        qpat_x_assum `bt = Len` (fn th => rewrite_tac[th]) >>
        simp[well_typed_builtin_app_def]) >>
      `call_evaluation_safe cx (int_calls_expr (HD es))` by
        metis_tac[call_evaluation_safe_int_calls_exprs_HD] >>
      qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
      qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                         type_check_def, assert_def] >>
      Cases_on `eval_expr cx (HD es) st` >>
      rename1 `eval_expr cx (HD es) st = (arg_res,arg_st)` >>
      qpat_x_assum `!s'' x t. _ /\ bt = Len ==> _`
        (qspecl_then [`st`,`()`,`st`] mp_tac) >>
      (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
      `well_typed_expr env (HD es)` by
        (qpat_assum `well_typed_exprs env es` mp_tac >>
         rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         qpat_x_assum `!s'' x t. _` kall_tac >>
         Cases_on `es` >> gvs[Once well_typed_expr_def]) >>
      `well_typed_builtin_app ty Len [expr_type (HD es)]` by
        (rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
         qpat_x_assum `!s'' x t. _` kall_tac >>
         Cases_on `es` >> gvs[well_typed_builtin_app_def] >>
         Cases_on `t` >> gvs[]) >>
      qpat_x_assum `!env st res st'. _ ==> (well_typed_expr _ _ ==> _) /\ _`
        (qspecl_then [`env`,`st`,`arg_res`,`arg_st`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `well_typed_expr env (HD es) ==> _` mp_tac >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result st' pv | INR _ => T`
        (qspecl_then [`env`,`st`,`arg_res`,`arg_st`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
      qpat_x_assum `!s'' x t. _` kall_tac >>
      Cases_on `arg_res`
      >- (rename1 `eval_expr cx (HD es) st = (INL arg_tv,arg_st)` >>
          gvs[] >>
          Cases_on `result_array_length cx arg_tv arg_st` >>
          rename1 `result_array_length cx arg_tv arg_st = (len_res,len_st)` >>
          drule_all Len_live_result_sound >> strip_tac >> gvs[] >>
          Cases_on `len_res` >>
          simp_tac(srw_ss())[return_def, raise_def] >> strip_tac >>
          gvs[no_type_error_result_def, expr_type_def]) >>
      simp_tac(srw_ss())[] >> strip_tac >> gvs[]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  Cases_on `bt = Env MsgGas`
  >- (qpat_x_assum `bt = Env MsgGas` SUBST_ALL_TAC >>
      simp_tac(srw_ss())[next_gas_reading_def, bind_def, ignore_bind_def,
                         assert_def, return_def, raise_def] >>
      Cases_on `st.gas_obs` >> simp_tac(srw_ss())[return_def, raise_def] >>
      strip_tac >> gvs[no_type_error_result_def, expr_result_typed_def,
                       expr_runtime_typed_def, expr_type_def,
                       value_result_typed_Value] >>
      gvs[well_typed_builtin_app_def, env_item_type_def, evaluate_type_def,
          value_has_type_def] >>
      rename1 `w2n (w:bytes32)` >>
      qspec_then `w` assume_tac wordsTheory.w2n_lt >>
      fs[wordsTheory.dimword_def]) >>
  qpat_assum `bt <> Env MsgGas` (fn th => rewrite_tac[th]) >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                     type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  qmatch_goalsub_abbrev_tac `option_CASE (code_slice_source bt es) _ SF st` >>
  Cases_on `option_CASE (code_slice_source bt es) (eval_exprs cx es) SF st` >>
  rename1 `option_CASE _ _ _ st = (args_res,args_st)` >>
  `state_well_typed args_st /\ env_consistent env cx args_st /\
   accounts_well_typed args_st.accounts /\ no_type_error_result args_res /\
   case args_res of
     INL vs =>
       exprs_runtime_typed env es vs \/
       (?code_ty addr tail_vs.
          code_slice_source bt es = SOME (code_ty, addr) /\
          well_typed_expr env (Builtin code_ty (Acc Code) [addr]) /\
          vs = BytesV cx.txn.code :: tail_vs /\
          exprs_runtime_typed env (TL es) tail_vs)
   | INR _ => T` by (
    qpat_x_assum `option_CASE _ _ _ st = _` mp_tac >> qunabbrev_tac `SF` >>
    Cases_on `code_slice_source bt es`
    >- (simp_tac(srw_ss())[] >> strip_tac >>
        qpat_x_assum `!s'' x t. _ /\ bt <> Len /\ bt <> Env MsgGas /\ NONE = NONE ==> _`
          (qspecl_then [`st`,`()`,`st`] mp_tac) >>
        (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
        qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\ case res of INL vs => exprs_runtime_typed env es vs | INR _ => T`
          (qspecl_then [`env`,`st`,`args_res`,`args_st`] mp_tac) >>
        (impl_tac >- simp[]) >>
        Cases_on `args_res` >> simp[]) >>
    rename1 `code_slice_source bt es = SOME p` >> PairCases_on `p` >>
    rename1 `code_slice_source bt es = SOME (code_ty,addr)` >>
    drule_all code_slice_operand_typing >> strip_tac >>
    drule_all code_slice_operand_call_safe >> strip_tac >>
    simp_tac(srw_ss())[bind_def, return_def, raise_def, get_accounts_def, lift_sum_def] >>
    Cases_on `eval_exprs cx (TL es) st` >>
    rename1 `eval_exprs cx (TL es) st = (tail_res,tail_st)` >>
    qpat_x_assum `!s'' x t v c a. _ /\ _ /\ _ /\ _ /\ v = (c,a) ==> _`
      (qspecl_then [`st`,`()`,`st`,`(code_ty,addr)`,`code_ty`,`addr`] mp_tac) >>
    (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
    qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\ case res of INL vs => exprs_runtime_typed env (TL es) vs | INR _ => T`
      (qspecl_then [`env`,`st`,`tail_res`,`tail_st`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    reverse (Cases_on `tail_res`)
    >- (simp_tac(srw_ss())[] >> strip_tac >>
        rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]) >>
    rename1 `eval_exprs cx (TL es) st = (INL tail_vs,tail_st)` >>
    simp_tac(srw_ss())[] >>
    Cases_on `eval_exprs cx [addr] tail_st` >>
    rename1 `eval_exprs cx [addr] tail_st = (addr_res,addr_st)` >>
    qpat_x_assum `!s'' x t v c a s3 tv t'. _ ==> _`
      (qspecl_then [`st`,`()`,`st`,`(code_ty,addr)`,`code_ty`,`addr`,`st`,`tail_vs`,`tail_st`] mp_tac) >>
    (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
    qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\ case res of INL vs => exprs_runtime_typed env [addr] vs | INR _ => T`
      (qspecl_then [`env`,`tail_st`,`addr_res`,`addr_st`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
    rpt (qpat_x_assum `!s'' x t. _` kall_tac) >>
    reverse (Cases_on `addr_res`)
    >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[]) >>
    rename1 `eval_exprs cx [addr] tail_st = (INL avs,addr_st)` >>
    simp_tac(srw_ss())[] >>
    Cases_on `is_self_addr addr`
    >- (gvs[] >> drule_all code_access_self_runtime_eval >>
        disch_then (qspec_then `addr_st.accounts` assume_tac) >>
        strip_tac >> gvs[return_def, no_type_error_result_def]) >>
    simp[evaluate_code_source_def] >>
    Cases_on `evaluate_builtin cx addr_st.accounts code_ty (Acc Code) [expr_type addr] avs` >>
    strip_tac >> gvs[return_def, raise_def]
    >- (conj_tac >- simp[no_type_error_result_def] >>
        mp_tac (Q.INST [`acc` |-> `(addr_st:evaluation_state).accounts`, `ct` |-> `code_ty`, `v` |-> `x`]
                  (SPEC_ALL code_access_runtime_success)) >>
        (impl_tac >- simp[]) >> strip_tac >>
        drule_all exprs_runtime_typed_code_slice_cons >> simp[]) >>
    mp_tac (Q.INST [`acc` |-> `(addr_st:evaluation_state).accounts`, `ct` |-> `code_ty`]
              (SPEC_ALL code_access_runtime_no_type_error)) >>
    (impl_tac >- simp[]) >> gvs[no_type_error_result_def]) >>
  rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
  rpt (qpat_x_assum `!s'' x t. _` kall_tac) >>
  Cases_on `args_res`
  >- (
    rename1 `option_CASE _ _ _ st = (INL vs,args_st)` >>
    qpat_x_assum `case INL vs of INL vs => _ | INR v1 => T`
      mp_tac >> simp_tac(srw_ss())[] >> strip_tac
    >- (
      qpat_x_assum `exprs_runtime_typed env es vs` mp_tac >>
      rewrite_tac[exprs_runtime_typed_def] >> strip_tac >>
      `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
        (gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP]) >>
      `?ret_tv. evaluate_type (get_tenv cx) ty = SOME ret_tv` by
        (gvs[well_formed_type_def, IS_SOME_EXISTS]) >>
      Cases_on `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) vs`
      >- (rename1 `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) vs = INL builtin_v` >>
          `value_has_type ret_tv builtin_v` by
            (drule_all well_typed_builtin_app_success_type >> simp[]) >>
          asm_rewrite_tac[] >> simp_tac(srw_ss())[return_def] >>
          Cases_on `precompile_call_success bt vs args_st` >>
          rename1 `precompile_call_success bt vs args_st = (pc_res,pc_st)` >>
          drule precompile_call_success_state >> strip_tac >>
          Cases_on `pc_res`
          >- (asm_rewrite_tac[] >> simp_tac(srw_ss())[] >> strip_tac >>
              gvs[no_type_error_result_def, expr_result_typed_def,
                  expr_runtime_typed_def, expr_type_def,
                  value_result_typed_Value]) >>
          drule precompile_call_success_exception >> strip_tac >>
          asm_rewrite_tac[] >> simp_tac(srw_ss())[] >> strip_tac >>
          gvs[no_type_error_result_def]) >>
      simp_tac(srw_ss())[raise_def] >> strip_tac >>
      gvs[no_type_error_result_def] >>
      strip_tac >> spose_not_then assume_tac >> gvs[] >>
      `!item. bt = Env item ==> item <> MsgGas` by (rpt strip_tac >> gvs[]) >>
      drule_all well_typed_builtin_app_no_type_error >>
      disch_then (qspec_then `msg` mp_tac) >> gvs[]) >>
    qpat_x_assum `vs = _` SUBST_ALL_TAC >>
    drule_all code_slice_self_builtin_eval >>
    disch_then (qspec_then `args_st.accounts` strip_assume_tac) >>
    Cases_on `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es)
                (BytesV cx.txn.code :: tail_vs)` >>
    strip_tac >>
    gvs[return_def, raise_def, precompile_call_success_def, precompile_builtin_def,
        no_type_error_result_def, expr_result_typed_def,
        expr_runtime_typed_def, value_runtime_typed_def, expr_type_def,
        value_result_typed_Value]) >>
  strip_tac >> gvs[eval_exprs_failure_builtin_case, no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by (
    qpat_assum `call_evaluation_safe cx
      (int_calls_expr (TypeBuiltin result_ty tb target_ty es))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (TypeBuiltin _ _ _ _) = SOME _` mp_tac >>
      simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (TypeBuiltin result_ty tb target_ty es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_def, env_context_consistent_def] >>
  `type_builtin_args_length_ok tb (LENGTH es)` by
    (drule well_typed_type_builtin_args_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (TypeBuiltin result_ty tb target_ty es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
                       type_check_def, assert_def] >>
  qpat_assum `type_builtin_args_length_ok tb (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                     type_check_def, assert_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!s'' x t. type_check _ _ _ = _ ==> _`
    (qspecl_then [`st`,`()`,`st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\ case res of INL vs => exprs_runtime_typed env es vs | INR _ => T`
    (qspecl_then [`env`,`st`,`args_res`,`args_st`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
  Cases_on `args_res`
  >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      qpat_x_assum `case INL vs of INL vs => exprs_runtime_typed env es vs | INR v1 => T`
        mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
      Cases_on `evaluate_type_builtin cx tb typ (MAP expr_type es) vs`
      >- (rename1 `evaluate_type_builtin cx tb typ (MAP expr_type es) vs = INL builtin_v` >>
          strip_tac >>
          gvs[lift_sum_def, return_def, no_type_error_result_def] >>
          simp_tac(srw_ss())[expr_type_def] >>
          metis_tac[type_builtin_exprs_runtime_success_type_stmt_adapter,
                    value_runtime_typed_def]) >>
      rename1 `evaluate_type_builtin cx tb typ (MAP expr_type es) vs = INR type_exn` >>
      strip_tac >>
      gvs[lift_sum_def, raise_def, no_type_error_result_def] >>
      strip_tac >> spose_not_then assume_tac >> gvs[] >>
      metis_tac[type_builtin_exprs_runtime_no_type_error_stmt_adapter]) >>
  strip_tac >> gvs[eval_exprs_failure_type_builtin_case, no_type_error_result_def]
QED


Resume eval_scc_type_sound_results_mutual[Expr_Pop]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_expr cx (Pop v11 bt) st = (res,st')` >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Pop v11 bt))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
  `well_typed_target env bt (ArrayT v11 (Dynamic n))` by simp[well_typed_target_def] >>
  qpat_x_assum `eval_expr cx (Pop v11 bt) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  rpt (qpat_x_assum `!env ty st res st'. _` kall_tac) >>
  Cases_on `target_res`
  >- (rename1 `eval_target_place cx bt st = (INL p,st1)` >>
      gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
      rename1 `evaluate_type env.type_defs v11 = SOME tv` >>
      `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
      `runtime_place_writable cx st1 p` by gvs[writable_place_result_def] >>
      Cases_on `pop_place cx p st1` >>
      rename1 `pop_place cx p st1 = (pop_res,pop_st)` >>
      `runtime_consistent env cx pop_st /\ no_type_error_result pop_res` by
        (irule pop_place_sound >> goal_assum (drule_at Any) >>
         Cases_on `p` >> gvs[live_memory_result_def] >> metis_tac[]) >>
      Cases_on `pop_res`
      >- (rename1 `pop_place cx p st1 = (INL pv,pop_st)` >>
          `case pv of Value v => value_has_type tv v
             | PlaceR q => runtime_place_typed cx pop_st q tv
             | HashMapRef _ _ _ _ => F` by
            (irule pop_place_result_typed >>
             goal_assum (drule_at (Pat `pop_place _ _ _ = _`)) >>
             Cases_on `p` >> gvs[live_memory_result_def] >> metis_tac[]) >>
          simp_tac(srw_ss())[] >> strip_tac >>
          gvs[runtime_consistent_def, expr_type_def, eval_result_typed_def] >>
          Cases_on `pv` >> gvs[]) >>
      simp_tac(srw_ss())[] >> strip_tac >> gvs[runtime_consistent_def]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[no_type_error_result_def]
QED


(* ===== Internal call case ===== *)


Resume eval_scc_type_sound_results_mutual[Expr_Call_IntCall]:
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` mp_tac >>
    simp[type_place_expr_Call_IntCall_NONE]) >>
  strip_tac >>
  drule intcall_call_evaluation_safe_target_not_mem >> strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ (IntCall _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (pure_ss ++ boolSimps.UNWIND_ss)
    [lock_if_nr_def, unlock_if_nr_def, is_view_mut_def]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >>
  simp_tac(srw_ss())[bind_apply, ignore_bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    gvs[type_check_def, assert_def]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    `fn_sigs_consistent env.fn_sigs cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    qpat_x_assum `fn_sigs_consistent env.fn_sigs cx` mp_tac >>
    simp[fn_sigs_consistent_def] >>
    disch_then (qspecl_then [`src_id_opt`, `fn`, `sig`] mp_tac) >>
    simp[] >> strip_tac >>
    gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    `fn_sigs_consistent env.fn_sigs cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    qpat_x_assum `lift_option_type (get_module_code cx src_id_opt) _ r = (INL x',r)`
      (fn th => assume_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
    drule_all fn_sigs_consistent_FLOOKUP >> strip_tac >>
    qpat_x_assum `get_module_code cx src_id_opt = SOME x' /\ _` strip_assume_tac >>
    drule_all intcall_lookup_function_not_INR >> strip_tac >>
    first_x_assum (qspecl_then [`r''`, `r`, `"IntCall lookup_function"`, `y`] mp_tac) >>
    simp[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    `fn_sigs_consistent env.fn_sigs cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    drule_all intcall_args_length_condition >> strip_tac >>
    gvs[type_check_def, assert_def, return_def, raise_def,
        no_type_error_result_def]) >>
  simp_tac(srw_ss())[bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `eval_exprs cx es r = (args_res,args_st)` >>
  drule intcall_call_evaluation_safe_args >> strip_tac >>
  qmatch_asmsub_rename_tac `type_check _ "IntCall args length" r = (INL tc_ok,tc_st)` >>
  `type_check
     (LENGTH es <= LENGTH (FST (SND (SND x''))) /\
      LENGTH (FST (SND (SND x''))) - LENGTH es <=
        LENGTH (FST (SND (SND (SND x'')))))
     "IntCall args length" r = (INL tc_ok,tc_st)` by
    (qpat_x_assum `type_check _ "IntCall args length" _ = _` mp_tac >> simp[]) >>
  first_x_assum (drule_all o cj 1) >> strip_tac >>
  reverse (Cases_on `args_res`) >- (
    rpt (qpat_x_assum `!a b c. _` kall_tac) >>
    gvs[no_type_error_result_def] >> strip_tac >> gvs[no_type_error_result_def]) >>
  rename1 `eval_exprs cx es r = (INL actual_vs,args_st)` >>
  RULE_ASSUM_TAC (REWRITE_RULE [sumTheory.sum_case_def]) >>
  qpat_assum `lift_option_type (get_module_code cx src_id_opt) _ _ = _`
    (mp_tac o MATCH_MP (iffLR lift_option_type_INL_eq)) >> strip_tac >>
  qpat_assum `lift_option_type (lookup_callable_function cx.in_deploy fn _) _ _ = _`
    (mp_tac o MATCH_MP (iffLR lift_option_type_INL_eq)) >> strip_tac >>
  PairCases_on `x''` >>
  RULE_ASSUM_TAC (BETA_RULE o SIMP_RULE (pure_ss ++ pairSimps.PAIR_ss) []) >>
  `IS_SOME (FLOOKUP env.fn_sigs (src_id_opt,fn))` by
    (qpat_x_assum `FLOOKUP env.fn_sigs (src_id_opt,fn) = SOME _`
       (fn th => simp[th])) >>
  drule_all callable_body_typing_from_env_consistent >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `env_body` (qx_choose_then `ret_tv` (qx_choose_then `env_after`
      (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
  simp_tac(srw_ss())[get_scopes_def, return_def] >>
  BasicProvers.TOP_CASE_TAC >>
  `get_scopes args_st = (INL args_st.scopes,args_st)` by
    simp[get_scopes_def, return_def] >>
  `set_scopes [FEMPTY] args_st = (INL (),args_st with scopes := [FEMPTY])` by
    simp[set_scopes_def, return_def] >>
  first_x_assum (drule o cj 1) >>
  ntac 6 (disch_then (drule o SIMP_RULE (pure_ss ++ pairSimps.PAIR_ss) [])) >>
  disch_then (mk_asm "default_sound") >>
  drule_all intcall_default_env_side_conditions >>
  disch_then (qspec_then `fn` strip_assume_tac) >>
  drule_all intcall_call_evaluation_safe_needed_defaults >>
  disch_then (qspec_then `LENGTH x''3 - (LENGTH x''2 - LENGTH es)` assume_tac) >>
  `env_consistent (defaults_env env_body)
      (cx with stk updated_by CONS (src_id_opt,fn))
      (args_st with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  `state_well_typed (args_st with scopes := [FEMPTY])` by
    (qpat_assum `state_well_typed args_st` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[state_well_typed_def, scope_well_typed_def]) >>
  `well_typed_exprs (defaults_env env_body)
      (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)` by
    (irule well_typed_exprs_DROP >> simp[]) >>
  qmatch_asmsub_rename_tac `finally _ _ args_st = (dflt_res,dflt_st)` >>
  `dflt_st.scopes = args_st.scopes /\ state_well_typed dflt_st /\
   env_consistent env cx dflt_st /\ accounts_well_typed dflt_st.accounts /\
   no_type_error_result dflt_res /\
   (case dflt_res of INL vs => exprs_runtime_typed (defaults_env env_body)
      (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3) vs | INR _ => T)` by
    (irule intcall_defaults_frame_sound >>
     qpat_x_assum `!a b c d e f. _` kall_tac >>
     simp[] >> qexistsl_tac [`fn`, `src_id_opt`] >>
     simp[ignore_bind_def] >>
     rpt gen_tac >> disch_tac >>
     `accounts_well_typed (args_st with scopes := [FEMPTY]).accounts` by simp[] >>
     asm "default_sound" drule_all >> simp[]) >>
  Cases_on `dflt_res` >>
  pure_rewrite_tac [sumTheory.sum_case_def]
  >- (RULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE [sumTheory.sum_case_def]) >>
      rename1 `exprs_runtime_typed _ _ dflt_vs` >>
      rename1 `exprs_runtime_typed env es actual_vs` >>
          `fn_sigs_consistent env.fn_sigs cx` by
            (qpat_assum `env_consistent env cx args_st` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             simp[env_consistent_def, env_context_consistent_def]) >>
          `sig.param_types = MAP SND x''2 /\ sig.num_defaults = LENGTH x''3 /\
           sig.ret_ty = x''4` by
            (drule_all fn_sigs_consistent_FLOOKUP >>
             qpat_assum `get_module_code cx src_id_opt = SOME x'` mp_tac >>
             qpat_assum `lookup_callable_function cx.in_deploy fn x' = SOME _` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
          drule env_consistent_type_defs_get_tenv >> strip_tac >>
          `LENGTH es <= LENGTH x''2 /\ LENGTH x''2 - LENGTH es <= LENGTH x''3` by
            (qpat_assum `type_check _ "IntCall args length" r = _` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             simp[type_check_def, assert_def] >> IF_CASES_TAC >> simp[] >> decide_tac) >>
          `LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es)
             (TAKE (LENGTH es) (MAP SND x''2))` by metis_tac[] >>
          `?call_env. bind_arguments (get_tenv cx) x''2 (actual_vs ++ dflt_vs) = SOME call_env /\
             scope_well_typed call_env /\
             env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` by
            (irule intcall_bind_arguments_from_runtime_typed >>
             qpat_x_assum `!a b c d e f. _` kall_tac >>
             asm_x "default_sound" kall_tac >> simp[] >>
             conj_tac >- metis_tac[] >>
             qexistsl_tac [`x''3`, `env`, `es`] >> simp[]) >>
          BETA_TAC >>
          qpat_assum `bind_arguments _ _ _ = SOME call_env`
            (fn th => simp_tac(srw_ss())[th, lift_option_type_def, return_def]) >>
          BasicProvers.TOP_CASE_TAC >>
          rename1 `(if x''1 then _ else _) dflt_st = (lock_res,lock_st)` >>
          Cases_on `lock_res`
          >- (Cases_on `x` >>
              `lift_option_type (bind_arguments (get_tenv cx) x''2 (actual_vs ++ dflt_vs))
                 "IntCall bind_arguments" dflt_st = (INL call_env,dflt_st)` by
                simp[lift_option_type_def, return_def] >>
              `lift_option_type (evaluate_type (get_tenv cx) x''4) "IntCall eval ret"
                 dflt_st = (INL ret_tv,dflt_st)` by simp[lift_option_type_def, return_def] >>
              `push_function (src_id_opt,fn) call_env cx lock_st =
                (INL (cx with stk updated_by CONS (src_id_opt,fn)),
                 lock_st with scopes := [call_env])` by simp[push_function_def, return_def] >>
              first_x_assum drule >>
              ntac 10 (disch_then (drule o SIMP_RULE (pure_ss ++ pairSimps.PAIR_ss) [])) >>
              disch_then (mk_asm "body_sound") >>
              asm_x "default_sound" kall_tac >>
              `env_immutables_consistent env_body
                 (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st` by
                (irule (cj 2 intcall_env_body_consistency_for_defaults) >>
                 simp[] >> qexists_tac `env` >> simp[]) >>
              drule_all intcall_call_evaluation_safe_body >> strip_tac >>
              suspend "IntCall_semantic_tail") >>
          asm_x "default_sound" kall_tac >>
          qpat_x_assum `!a b c d e f. _` kall_tac >>
          drule_all intcall_lock_attempt_sound_frame >> strip_tac >>
          gvs[no_type_error_result_def] >> strip_tac >>
          gvs[no_type_error_result_def]) >>
  qpat_x_assum `!a b c d e f. _` kall_tac >>
  gvs[no_type_error_result_def] >> strip_tac >> gvs[no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[IntCall_semantic_tail]:
  strip_tac >>
  qsuff_tac `state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL pv => expr_result_typed env
      (Call v16 (IntCall (src_id_opt,fn)) es v17) pv | INR _ => T)`
  >- (disch_tac >> Cases_on `res` >>
      gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
          eval_result_typed_def]) >>
  irule intcall_post_read_continuation_sound >>
  simp[] >> conj_tac
  >- (simp[Once well_typed_expr_def] >> metis_tac[]) >>
  qexistsl_tac [`args_st`, `x''5`, `call_env`, `dflt_st`, `env_after`,
    `env_body`, `x''0`, `INL x'' : unit + exception`, `lock_st`, `x''1`,
    `x''4`, `ret_tv`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> asm "body_sound" drule_all >> simp[]) >>
  reverse conj_tac >- (simp[expr_type_def] >> metis_tac[]) >>
  qpat_x_assum `(case INL _ of INL _ => _ | INR _ => _) = _` mp_tac >>
  qpat_x_assum `push_function _ _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  gvs[bind_apply, ignore_bind_apply, return_def, lift_option_type_def]
QED

(* ===== External and special call Resume blocks ===== *)

Resume eval_scc_type_sound_results_mutual[Expr_Call_ExtCall_result]:
  rpt gen_tac >> strip_tac >>
  drule extcall_call_evaluation_safe_args >> strip_tac >>
  rename1 `Call _ (ExtCall _ _ fsig _) _ _` >> PairCases_on `fsig` >>
  qpat_x_assum `well_typed_expr env (Call _ (ExtCall _ _ _ _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  `?ret_tv. evaluate_type env.type_defs fsig2 = SOME ret_tv` by
    (qpat_assum `well_formed_type env.type_defs v14`
       (mp_tac o REWRITE_RULE [well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
     simp[]) >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH fsig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH fsig1) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH fsig1) (DROP 1 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH fsig1) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 1 es) st` >>
  rename1 `eval_exprs cx (TAKE 1 es) st = (target_res,target_st)` >>
  qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
    (case res0 of INL vs => exprs_runtime_typed env0 (TAKE 1 es) vs | INR _ => T)`
    drule_all >> strip_tac >>
  Cases_on `target_res`
  >- (qpat_assum `eval_exprs cx (TAKE 1 es) st = _`
        (fn th => simp_tac(srw_ss())[th, sum_case_def, pair_case_def]) >>
      qpat_x_assum `!s target t nargs. eval_exprs cx (TAKE 1 es) s = (INL target,t) /\ _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
      Cases_on `eval_exprs cx (TAKE (LENGTH fsig1) (DROP 1 es)) target_st` >>
      rename1 `eval_exprs _ _ target_st = (capture_res,capture_st)` >>
      qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res0 of INL rs => exprs_runtime_typed env0 (TAKE _ _) rs | INR _ => T)`
        drule_all >> strip_tac >>
      Cases_on `capture_res`
      >- (qpat_x_assum `!s target t nargs s1 rs t1. _ ==> _`
            (drule o SIMP_RULE (srw_ss()) []) >>
          disch_then drule >> strip_tac >>
          qpat_assum `eval_exprs _ _ target_st = _`
            (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
          Cases_on `eval_exprs cx (DROP (1 + LENGTH fsig1) es) capture_st` >>
          rename1 `eval_exprs _ _ capture_st = (kw_res,kw_st)` >>
          qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
            (case res0 of INL vs => exprs_runtime_typed env0 (DROP _ es) vs | INR _ => T)`
            drule_all >> strip_tac >>
          qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (DROP _ es) /\ _ ==> typed_scope_transition st0 st0'`
            drule_all >> strip_tac >>
          drule (cj 6 eval_metadata_frame_mutual) >> strip_tac >>
          rule_assum_tac (BETA_RULE o REWRITE_RULE [sum_case_def]) >>
          Cases_on `kw_res`
          >- (qpat_assum `eval_exprs _ _ capture_st = _`
                (fn th => simp_tac(srw_ss())[th, bind_apply]) >>
              rpt (qpat_x_assum `!env0 st0 res0 st0'. _` kall_tac) >>
              gvs[no_type_error_result_def] >> strip_tac >>
                  `exprs_runtime_typed env es (x ++ x' ++ x'')` by
                    (irule exprs_runtime_typed_slices >>
                     qexistsl [`1`, `LENGTH fsig1`] >> simp[DROP_DROP]) >>
                  `runtime_consistent env cx kw_st` by simp[runtime_consistent_def] >>
                  `MAP expr_type es =
                     BaseT AddressT :: MAP expr_type (TAKE (LENGTH fsig1) (TL es)) ++
                     MAP (ext_call_kw_type fsig2) opts` by
                    (qspecl_then [`es`, `expr_type`, `LENGTH fsig1`] mp_tac
                       (Q.GENL [`xs`, `f`, `n`] MAP_HD_TAKE_DROP) >> simp[]) >>
                  drule_all eval_ext_call_result_sound >>
                  disch_then (qspec_then `NONE` mp_tac) >>
                  strip_tac >> Cases_on `res` >>
                  gvs[no_type_error_result_def, expr_result_typed_def,
                      expr_runtime_typed_def, value_result_typed_def,
                      eval_result_typed_def, expr_type_def]) >>
          rpt (qpat_x_assum `!env0 st0 res0 st0'. _` kall_tac) >>
          gvs[no_type_error_result_def] >> strip_tac >> gvs[]) >>
      rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
      gvs[LET_THM, bind_apply, no_type_error_result_def] >> strip_tac >> gvs[]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  gvs[no_type_error_result_def] >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_Send]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule send_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (Send _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    `LENGTH es = if has_gas then 3 else 2` by
      (qpat_x_assum `MAP expr_type es = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
       rw[]) >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    asm_simp_tac bool_ss [Once evaluate_def, bind_def, ignore_bind_def,
                          type_check_def, assert_def, return_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!s'' x t. type_check _ "Send args" s'' = (INL x,t) ==> _`
      (qspecl_then [`st`, `()`, `st`] mp_tac) >>
    impl_tac >- simp[type_check_def, assert_def, return_def] >>
    disch_then (fn th =>
      qspecl_then [`env`, `st`, `args_res`, `args_st`] mp_tac (cj 1 th)) >>
    simp[] >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (strip_tac >>
        `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
        `MAP expr_type es = [BaseT AddressT; BaseT (UintT 256)] ++
           (if has_gas then [BaseT (UintT 256)] else [])` by fs[] >>
        drule_all eval_send_result_sound >>
        disch_then (qspec_then `NONE` mp_tac) >>
        strip_tac >> Cases_on `res` >>
        gvs[no_type_error_result_def, expr_result_typed_def,
            expr_runtime_typed_def, value_result_typed_def,
            eval_result_typed_def, expr_type_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_RawCallTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawcall_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (RawCallTarget _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    (Cases_on `args_res`
    >- (gvs[no_type_error_result_def] >>
      rename1 `exprs_runtime_typed env es vs` >>
      rename1 `EL 1 (MAP expr_type es) = BaseT (BytesT (Dynamic data_bound))` >>
      mp_tac (Q.INST [`bd` |-> `Dynamic data_bound`]
        raw_call_args_runtime_typed_dest) >>
      impl_tac >- simp[] >>
      strip_tac >> gvs[] >>
      drule_then (qspec_then `2` assume_tac) exprs_runtime_typed_DROP >>
      drule_all raw_call_value_typed >> strip_tac >>
      TRY (qpat_x_assum `_ = (res,st')` mp_tac) >>
      simp[bind_def, return_def] >> strip_tac >>
      `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
      drule_at (Pat `eval_raw_call _ _ _ _ _ _ _ = _`) eval_raw_call_result_sound >>
      disch_then (qspec_then `env` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on `res` >>
      gvs[runtime_consistent_def, no_type_error_result_def, expr_type_def] >>
      qpat_x_assum `!e. expr_type e = raw_call_return_type flags ==> _`
        (qspec_then `Literal (raw_call_return_type flags) (IntL 0)` mp_tac) >>
      simp[expr_type_def, expr_result_typed_def, expr_runtime_typed_def,
           value_result_typed_def] >>
      strip_tac >> gvs[eval_result_typed_def]) >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[]))) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_RawCallCalldataTarget]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx
      (int_calls_expr (Call _ (RawCallCalldataTarget _) es _))` mp_tac >>
    simp[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (RawCallCalldataTarget _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def, lift_option_type_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    (Cases_on `args_res`
    >- (gvs[no_type_error_result_def] >>
      rename1 `exprs_runtime_typed env es vs` >>
      mp_tac raw_call_calldata_args_runtime_typed_dest >>
      (impl_tac >- (Cases_on `es` >> gvs[])) >> strip_tac >>
      drule_then (qspec_then `1` assume_tac) exprs_runtime_typed_DROP >>
      drule_all raw_call_value_typed >> strip_tac >>
      TRY (qpat_x_assum `_ = (res,st')` mp_tac) >>
      simp[bind_def, return_def] >> strip_tac >>
      `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
      drule_at (Pat `eval_raw_call _ _ _ _ _ _ _ = _`) eval_raw_call_result_sound >>
      disch_then (qspec_then `env` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on `res` >>
      gvs[runtime_consistent_def, no_type_error_result_def, expr_type_def] >>
      qpat_x_assum `!e. expr_type e = raw_call_return_type flags ==> _`
        (qspec_then `Literal (raw_call_return_type flags) (IntL 0)` mp_tac) >>
      simp[expr_type_def, expr_result_typed_def, expr_runtime_typed_def,
           value_result_typed_def] >>
      strip_tac >> gvs[eval_result_typed_def]) >>
      gvs[no_type_error_result_def] >> strip_tac >> gvs[]))) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED


Resume eval_scc_type_sound_results_mutual[Expr_Call_RawLog]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawlog_call_evaluation_safe_args >> strip_tac >>
    drule raw_log_well_typed_args >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, push_log_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      mp_tac raw_log_args_runtime_typed_dest >> simp[] >> strip_tac >> gvs[] >>
      strip_tac >>
      qpat_x_assum `LENGTH (case topics of _ => _) <= 4` $
        mk_asm "topics_bound" >>
      Cases_on `cx.txn.is_static`
      >- (asm "topics_bound" (fn th =>
            fs[th, type_check_def, bind_def, ignore_bind_def, assert_def,
               return_def]) >>
          gvs[no_type_error_result_def]) >>
      asm "topics_bound" (fn th =>
        fs[th, type_check_def, bind_def, ignore_bind_def, assert_def,
           return_def]) >>
      qspecl_then [`env`, `cx`, `es`, `vs`, `args_st`, `topics`, `data`, `res`, `st'`, `bd`, `bd'`]
        mp_tac raw_log_tail_result_sound_simp >>
      asm "topics_bound" (fn th =>
        simp[th, type_check_def, bind_def, ignore_bind_def, assert_def,
             return_def, runtime_consistent_def]) >>
      strip_tac >> Cases_on `res` >>
      gvs[expr_result_typed_def, expr_runtime_typed_def,
          value_result_typed_def, eval_result_typed_def, expr_type_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_RawRevert]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawrevert_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ RawRevert _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      `LENGTH vs = 1` by
        (gvs[exprs_runtime_typed_def] >>
         metis_tac[listTheory.LIST_REL_LENGTH]) >>
      drule_at (Pos (el 2)) raw_revert_tail_sound >>
      disch_then (qspecl_then [`cx`, `args_st`] mp_tac) >>
      simp[type_check_def, bind_def, ignore_bind_def, assert_def, raise_def,
           return_def, no_type_error_result_def, runtime_consistent_def] >>
      Cases_on `dest_BytesV (HD vs)` >>
      gvs[lift_option_type_def, raise_def, return_def] >> strip_tac >> gvs[]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_SelfDestructTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule selfdestruct_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ SelfDestructTarget _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, get_accounts_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
      (case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T)`
      drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      strip_tac >>
      Cases_on `cx.txn.is_static`
      >- (drule_all selfdestruct_args_runtime_typed_dest >> strip_tac >>
          gvs[type_check_def, assert_def, lift_option_type_def, return_def,
              bind_def, ignore_bind_def, raise_def,
              no_type_error_result_def]) >>
      (* Not static: check_not_static passes, leaving the shared tail. *)
      qpat_assum `~cx.txn.is_static` (fn not_static =>
        qpat_assum `_ = (res,st')`
          (assume_tac o SRULE [not_static, bind_def, ignore_bind_def,
            type_check_def, assert_def, return_def, raise_def,
            lift_option_type_def, get_accounts_def])) >>
      qspecl_then [`env`, `cx`, `es`, `vs`, `args_st`, `res`, `st'`]
        mp_tac (SRULE [bind_def, ignore_bind_def, type_check_def, assert_def,
          return_def, raise_def, lift_option_type_def, get_accounts_def]
          selfdestruct_tail_sound) >>
      simp[type_check_def, assert_def, runtime_consistent_def] >>
      rpt strip_tac >> gvs[runtime_consistent_def, no_type_error_result_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_scc_type_sound_results_mutual[Expr_Call_CreateTarget]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      drule create_call_evaluation_safe_args >> strip_tac >>
      qpat_x_assum `well_typed_expr env (Call _ (CreateTarget _ _ _ _) _ _)` mp_tac >>
      rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
      `well_typed_exprs env (create_operand_order kind has_salt es)` by
        metis_tac[well_typed_exprs_create_operand_order] >>
      `call_evaluation_safe cx (int_calls_exprs (create_operand_order kind has_salt es))` by
        metis_tac[call_evaluation_safe_create_operand_order] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
      Cases_on `eval_exprs cx (create_operand_order kind has_salt es) st` >>
      rename1 `eval_exprs cx (create_operand_order kind has_salt es) st = (args_res,args_st)` >>
      qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res of INL vs => exprs_runtime_typed _ _ vs | INR _ => T)`
        drule_all >> strip_tac >>
      Cases_on `args_res` >> gvs[no_type_error_result_def]
      >- (rename1 `exprs_runtime_typed env (create_operand_order kind has_salt es) vs` >>
          `exprs_runtime_typed env es (create_operand_layout kind has_salt vs)` by
            metis_tac[exprs_runtime_typed_create_operand_layout, create_operand_layout_order] >>
          `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
          strip_tac >> drule_all create_operands_result_sound >>
          disch_then (mp_tac o SPEC_ALL) >> simp[no_type_error_result_def] >>
          strip_tac >> Cases_on `res` >>
          gvs[expr_result_typed_def, expr_runtime_typed_def,
              value_result_typed_def, eval_result_typed_def, expr_type_def]) >>
      strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr env (Call _ _ _ _) = SOME _` mp_tac >>
  simp[Once well_typed_expr_def]
QED





Resume eval_scc_type_sound_results_mutual[Exprs_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >>
  gvs[no_type_error_result_def, exprs_runtime_typed_def]
QED

Resume eval_scc_type_sound_results_mutual[Exprs_cons]:
  rpt gen_tac >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (r1,st1)` >>
  qpat_x_assum `!env0 st0 res0 st0'. _ ==>
    (well_typed_expr env0 e ==> _) /\ _` drule_all >>
  strip_tac >>
  Cases_on `r1`
  >- (
    `live_memory_result st1 x` by (
      qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
        (qspecl_then [`env`,`st`,`INL x`,`st1`] mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >>
      simp[]) >>
    qpat_x_assum `well_typed_expr env e ==> _` drule >>
    simp_tac(srw_ss())[] >> strip_tac >>
    `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (mr,stm)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    Cases_on `mr`
    >- (
      Cases_on `eval_exprs cx es st1` >>
      rename1 `eval_exprs cx es st1 = (r2,st2)` >>
      qpat_x_assum `!s tv t sr v tr. _ ==> _ /\ _` drule_all >>
      disch_then (strip_assume_tac o cj 1) >>
      qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res of INL vs => exprs_runtime_typed _ _ vs | INR _ => T)`
        drule_all >> strip_tac >>
      Cases_on `r2` >> gvs[no_type_error_result_def]
      >- (strip_tac >>
          gvs[exprs_runtime_typed_def, value_runtime_typed_def] >>
          qexists_tac `tv::tvs` >> simp[]) >>
      strip_tac >> gvs[]) >>
    strip_tac >> gvs[no_type_error_result_def]) >>
  (* the expression raised: the induction hypotheses are not needed, and
     gvs over them runs past the step budget *)
  strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
  gvs[no_type_error_result_def]
QED

(* Each transition root has exactly one semantic key and one suspended goal. *)
val trace_root_labels = [
  "Trace_Target", "Trace_Base_SubscriptTarget", "Trace_Base_AttributeTarget",
  "Trace_Base_TopLevelNameTarget", "Trace_Base_NameTarget",
  "Trace_Exprs_cons", "Trace_Exprs_nil",
  "Trace_Expr_Call_CreateTarget", "Trace_Expr_Call_SelfDestructTarget",
  "Trace_Expr_Call_RawRevert", "Trace_Expr_Call_RawLog",
  "Trace_Expr_Call_RawCallCalldataTarget", "Trace_Expr_Call_RawCallTarget",
  "Trace_Expr_Call_IntCall", "Trace_Expr_Call_ExtCall", "Trace_Expr_Call_Send",
  "Trace_Expr_TypeBuiltin", "Trace_Expr_Pop", "Trace_Expr_Builtin",
  "Trace_Expr_Attribute", "Trace_Expr_Subscript", "Trace_Expr_StructLit",
  "Trace_Expr_Literal", "Trace_Expr_IfExp", "Trace_Expr_FlagMember",
  "Trace_Expr_TopLevelName", "Trace_Expr_Name"];
val _ = let
  val SOME (_,parent) = markerLib.lookup_suspension "eval_scc_type_sound_results_mutual"
  fun check label =
    let val roots = markerLib.extract_suspended_goal [parent] label
        val _ = if length roots = 1 then () else raise Fail ("non-singleton " ^ label)
        val (_,tm) = markerLib.resumption_to_goal roots
        val _ = if trace_root_key tm = label then ()
                else raise Fail ("Wrong transition key: " ^ label)
    in print ("Singleton transition obligation " ^ label ^ "\n") end
  val actual = map #1 (!trace_root_inventory)
  val _ = if List.all (fn key => List.exists (fn x => x = key) actual) trace_root_labels
             andalso List.all (fn key => List.exists (fn x => x = key) trace_root_labels) actual
          then () else raise Fail "Transition inventory mismatch"
in List.app check trace_root_labels end;






(* The semantic root selects its handler before any recursive equation unfolds. *)
fun trace_value_start_tac g = (
  rpt gen_tac >> strip_tac >>
  IF (qpat_assum `type_place_expr _ _ = SOME _` (K all_tac))
    (qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
     simp[NoAsms, Once well_typed_expr_def])
    all_tac) g;

fun trace_result_tac label g = let val suspend = trace_result_tac in
  (case label of
    "Trace_Target" => (rpt gen_tac >> strip_tac >> suspend "TraceTarget")
  | "Trace_Base_NameTarget" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, bind_def, return_def, raise_def,
           AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      irule typed_scope_transition_refl)
  | "Trace_Base_TopLevelNameTarget" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      rewrite_tac[Once evaluate_def] >> strip_tac >>
      drule lookup_global_state >> strip_tac >>
      irule typed_scope_transition_scopes >>
      qpat_x_assum `st' = _` SUBST1_TAC >> simp[])
  | "Trace_Base_AttributeTarget" => (rpt gen_tac >> strip_tac >>
      suspend "TraceBaseAttribute")
  | "Trace_Base_SubscriptTarget" => (rpt gen_tac >> strip_tac >>
      markerLib.suspend "Trace_Base_Subscript_Selection")
  | "Trace_Exprs_nil" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_exprs _ [] _ = _` mp_tac >>
      simp[Once evaluate_def, return_def] >> strip_tac >> gvs[] >>
      irule typed_scope_transition_refl)
  | "Trace_Exprs_cons" => (rpt gen_tac >> strip_tac >> suspend "TraceExprsCons")
  | "Trace_Expr_Name" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, bind_def, return_def, raise_def,
           AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      irule typed_scope_transition_refl)
  | "Trace_Expr_TopLevelName" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      rewrite_tac[Once evaluate_def] >> strip_tac >>
      drule lookup_global_state >> strip_tac >>
      irule typed_scope_transition_scopes >>
      qpat_x_assum `st' = _` SUBST1_TAC >> simp[])
  | "Trace_Expr_FlagMember" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, lift_option_type_def,
           return_def, raise_def, AllCaseEqs()] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >> irule typed_scope_transition_refl)
  | "Trace_Expr_Literal" => (rpt gen_tac >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, return_def] >> strip_tac >> gvs[] >>
      irule typed_scope_transition_refl)
  | "Trace_Expr_Call_ExtCall" => (trace_value_start_tac >>
      markerLib.suspend "Trace_ExtCall_Operands")
  | "Trace_Expr_Call_IntCall" => (trace_value_start_tac >> markerLib.suspend "Trace_IntCall_Operands")
  | "Trace_Expr_Call_CreateTarget" => (trace_value_start_tac >>
      markerLib.suspend "Trace_Create_Operands")
  | "Trace_Expr_Call_Send" => (trace_value_start_tac >> suspend "TraceSend")
  | "Trace_Expr_Call_RawLog" => (trace_value_start_tac >> suspend "TraceRawLog")
  | "Trace_Expr_Call_RawRevert" => (trace_value_start_tac >> suspend "TraceRawRevert")
  | "Trace_Expr_Call_SelfDestructTarget" => (trace_value_start_tac >> suspend "TraceSelfDestruct")
  | "Trace_Expr_Call_RawCallCalldataTarget" => (trace_value_start_tac >> suspend "TraceRawCalldata")
  | "Trace_Expr_Call_RawCallTarget" => (trace_value_start_tac >> suspend "TraceRawCall")
  | "Trace_Expr_TypeBuiltin" => (trace_value_start_tac >> suspend "TraceTypeBuiltin")
  | "Trace_Expr_Builtin" => (trace_value_start_tac >> suspend "TraceBuiltin")
  | "Trace_Expr_StructLit" => (trace_value_start_tac >> suspend "TraceStructLit")
  | "Trace_Expr_Attribute" => (rpt gen_tac >> strip_tac >>
      markerLib.suspend "Trace_Attribute_Selection")
  | "Trace_Expr_IfExp" => (trace_value_start_tac >> suspend "TraceExprIfExp")
  | "Trace_Expr_Pop" => (rpt gen_tac >> strip_tac >>
      markerLib.suspend "Trace_Pop_Target")
  | "TraceTarget" => (
      qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
      Cases_on `eval_base_place cx bt st` >>
      rename1 `eval_base_place cx bt st = (base_res,mid)` >>
      Cases_on `base_res` >>
      simp[Once evaluate_def, bind_def, get_place_def, AllCaseEqs()] >>
      strip_tac >> gvs[well_typed_target_def] >>
      imp_res_tac vyperPlaceFramesTheory.get_place_state >> rpt BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _` drule_all >>
      simp[])
  | "TraceBaseAttribute" => (
      qpat_x_assum `type_place_target _ (AttributeTarget _ _) = SOME _` mp_tac >>
      rewrite_tac[type_place_target_AttributeTarget] >> strip_tac >>
      markerLib.suspend "Trace_Base_Attribute_Selection")
  | "TraceExprsCons" => (
      qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
      simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
      drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
      drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
      qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
      imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
      FIRST [first_assum ACCEPT_TAC,
        qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
          (drule_at (Pat `eval_expr _ _ _ = _`)) >>
        disch_then (qspec_then `env` mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
        qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
        (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
        qpat_x_assum `!s0 tv t s1 v t1. eval_expr _ _ _ = _ /\ read_result _ _ _ = _ ==> _`
          (drule_all_then strip_assume_tac) >>
        qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
          (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
        disch_then (qspec_then `env` mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
        rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
        metis_tac[typed_scope_transition_trans]])
  | "TraceSend" => (
  drule send_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  `LENGTH es = if has_gas then 3 else 2` by
    (qpat_x_assum `MAP expr_type es = _` (mp_tac o Q.AP_TERM `LENGTH`) >> rw[]) >>
  qpat_x_assum `!s'' x t. type_check _ _ s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  asm_rewrite_tac[] >>
  imp_res_tac eval_send_preserves_non_accounts >>
  metis_tac[typed_scope_transition_trans, typed_scope_transition_scopes]
)
  | "TraceRawLog" => (
  drule rawlog_call_evaluation_safe_args >> strip_tac >>
  drule raw_log_well_typed_args >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  asm_rewrite_tac[] >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `push_log _ _ = _` mp_tac >>
  simp[NoAsms, push_log_def, return_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  conj_tac >- (irule typed_scope_transition_scopes >> simp[]) >>
  first_assum ACCEPT_TAC
)
  | "TraceRawRevert" => (
  drule rawrevert_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  rpt BasicProvers.VAR_EQ_TAC >> first_assum ACCEPT_TAC
)
  | "TraceSelfDestruct" => (
  drule selfdestruct_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `get_accounts _ = _` mp_tac >>
  simp[NoAsms, get_accounts_def, return_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  gvs[update_accounts_def, update_pending_deletions_def, bind_def,
      ignore_bind_def, return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  (conj_tac >- (irule typed_scope_transition_scopes >> first_assum ACCEPT_TAC) >>
   first_assum ACCEPT_TAC)
)
  | "TraceBuiltin" => bossLib.suspend "TraceBuiltinBody"
  | "TraceBuiltinLen" => (
  `es <> []` by
    (Cases_on `es` >> simp[] >>
     qpat_x_assum `well_typed_builtin_app _ _ _` mp_tac >>
     simp[well_typed_builtin_app_def]) >>
  `call_evaluation_safe cx (int_calls_expr (HD es))` by
    metis_tac[call_evaluation_safe_int_calls_exprs_HD] >>
  `well_typed_expr env (HD es)` by
    (qpat_x_assum `well_typed_exprs env es` mp_tac >>
     qpat_x_assum `es <> []` mp_tac >>
     Cases_on `es` >> simp[Once well_typed_expr_def]) >>
  qpat_x_assum `!s'' x t. _ /\ bt = Len ==> _`
    (qspecl_then [`st`,`()`,`st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th =>
    simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def, raise_def,
      type_check_def, assert_def, th]) >>
  qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
  simp[NoAsms, bind_def, ignore_bind_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  imp_res_tac lift_sum_state >> imp_res_tac result_array_length_state >>
  rpt BasicProvers.VAR_EQ_TAC >> first_assum ACCEPT_TAC
)
  | "TraceStructLit" => (
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def, GSYM int_calls_exprs_MAP_SND] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_stmt >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!ks. ks = MAP FST kes ==> _`
    (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, LET_THM, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
)
  | "TraceRawCalldata" => (
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  (conj_tac >- (irule typed_scope_transition_scopes >> first_assum ACCEPT_TAC) >>
   first_assum ACCEPT_TAC)
)
  | "TraceRawCall" => (
  drule rawcall_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  (conj_tac >- (irule typed_scope_transition_scopes >> first_assum ACCEPT_TAC) >>
   first_assum ACCEPT_TAC)
)
  | "TraceTypeBuiltin" => (
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  `type_builtin_args_length_ok tb (LENGTH es)` by
    (drule well_typed_type_builtin_args_length >> simp[]) >>
  qpat_x_assum `!s'' x t. type_check _ _ _ = _ ==> _`
    (qspecl_then [`st`,`()`,`st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  qpat_assum `type_builtin_args_length_ok tb (LENGTH es)` (fn th =>
    simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def,
      return_def, raise_def, type_check_def, assert_def, th, AllCaseEqs()]) >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  imp_res_tac lift_sum_state >> rpt BasicProvers.VAR_EQ_TAC >>
  first_assum ACCEPT_TAC
)
  | "TraceExprIfExp" => (
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!env st res st'. _ ==> (_ ==> _) /\ _` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!s'' tv t. eval_expr _ _ s'' = (INL tv,t) ==> _` drule >> strip_tac) >>
  qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
  simp[NoAsms, switch_BoolV_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[NoAsms, COND_RATOR, raise_def] >> rpt IF_CASES_TAC >>
  simp[NoAsms, raise_def] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac conditional_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  irule typed_scope_transition_trans >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[]
)
  | _ => raise Fail ("Unknown Trace route: " ^ label)) g end;

Resume eval_scc_type_sound_results_mutual[Trace_Target]:
  RESUME_TAC >> trace_result_tac "Trace_Target"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Base_SubscriptTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Base_SubscriptTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Base_AttributeTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Base_AttributeTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Base_TopLevelNameTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Base_TopLevelNameTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Base_NameTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Base_NameTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Exprs_cons]:
  RESUME_TAC >> trace_result_tac "Trace_Exprs_cons"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Exprs_nil]:
  RESUME_TAC >> trace_result_tac "Trace_Exprs_nil"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_CreateTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_CreateTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_SelfDestructTarget]:
  RESUME_TAC >> trace_value_start_tac >>
  drule selfdestruct_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!env st res st'. _` kall_tac) >>
  gvs[get_accounts_def, update_accounts_def, update_pending_deletions_def,
      bind_def, ignore_bind_def, return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `eval_exprs cx es st = (INL vs,mid)` >>
  irule typed_scope_transition_trans >> qexists_tac `mid` >>
  (conj_tac >- (irule typed_scope_transition_scopes >>
                 imp_res_tac transfer_value_scopes >> simp[]) >>
   first_assum ACCEPT_TAC)
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_RawRevert]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_RawRevert"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_RawLog]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_RawLog"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_RawCallCalldataTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_RawCallCalldataTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_RawCallTarget]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_RawCallTarget"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_IntCall]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_IntCall"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_ExtCall]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_ExtCall"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Call_Send]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Call_Send"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_TypeBuiltin]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_TypeBuiltin"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Pop]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Pop"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Builtin]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Builtin"
QED
Resume eval_scc_type_sound_results_mutual[TraceBuiltinBody]:
  RESUME_TAC >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  Cases_on `bt = Len`
  >- trace_result_tac "TraceBuiltinLen" >>
  Cases_on `bt = Env MsgGas`
  >- (qpat_x_assum `bt = Env MsgGas` SUBST_ALL_TAC >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      qpat_assum `builtin_args_length_ok _ (LENGTH es)` (fn th =>
        simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def, raise_def,
          type_check_def, assert_def, th]) >>
      simp[NoAsms, bind_def, ignore_bind_def, return_def, raise_def,
           AllCaseEqs()] >>
      strip_tac >> imp_res_tac next_gas_reading_state >>
      irule typed_scope_transition_scopes >> gvs[assert_def, return_def]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th =>
    simp_tac (srw_ss()) [Once evaluate_def, bind_def, return_def, raise_def,
      type_check_def, assert_def, th]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  qpat_assum `bt <> Env MsgGas` (fn th => rewrite_tac[th]) >>
  simp_tac (srw_ss()) [bind_def, ignore_bind_def, return_def, raise_def,
    type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  qmatch_goalsub_abbrev_tac `option_CASE (code_slice_source bt es) _ SF st` >>
  Cases_on `option_CASE (code_slice_source bt es) (eval_exprs cx es) SF st` >>
  rename1 `option_CASE _ _ _ st = (args_res,args_st)` >>
  `typed_scope_transition st args_st` by (
    qpat_x_assum `option_CASE _ _ _ st = _` mp_tac >> qunabbrev_tac `SF` >>
    Cases_on `code_slice_source bt es`
    >- (simp_tac(srw_ss())[] >> strip_tac >>
        qpat_x_assum `!s'' x t. _ /\ bt <> Len /\ bt <> Env MsgGas /\ NONE = NONE ==> _`
          (qspecl_then [`st`,`()`,`st`] mp_tac) >>
        (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
        qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
          (qspecl_then [`env`,`st`,`args_res`,`args_st`] mp_tac) >>
        (impl_tac >- simp[]) >> simp[]) >>
    rename1 `code_slice_source bt es = SOME p` >> PairCases_on `p` >>
    rename1 `code_slice_source bt es = SOME (code_ty,addr)` >>
    drule_all code_slice_operand_typing >> strip_tac >>
    drule_all code_slice_operand_call_safe >> strip_tac >>
    simp_tac(srw_ss())[bind_def, return_def, raise_def, get_accounts_def, lift_sum_def] >>
    Cases_on `eval_exprs cx (TL es) st` >>
    rename1 `eval_exprs cx (TL es) st = (tail_res,tail_st)` >>
    qpat_x_assum `!s'' x t v c a. _ /\ _ /\ _ /\ _ /\ v = (c,a) ==> _`
      (qspecl_then [`st`,`()`,`st`,`(code_ty,addr)`,`code_ty`,`addr`] mp_tac) >>
    (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
    qpat_x_assum `!env st res st'. _ ==> _ /\ _ /\ _ /\ _ /\ case res of INL vs => exprs_runtime_typed env (TL es) vs | INR _ => T`
      (qspecl_then [`env`,`st`,`tail_res`,`tail_st`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
      (qspecl_then [`env`,`st`,`tail_res`,`tail_st`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    reverse (Cases_on `tail_res`)
    >- (simp_tac(srw_ss())[] >> strip_tac >>
        rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]) >>
    rename1 `eval_exprs cx (TL es) st = (INL tail_vs,tail_st)` >>
    simp_tac(srw_ss())[] >>
    Cases_on `eval_exprs cx [addr] tail_st` >>
    rename1 `eval_exprs cx [addr] tail_st = (addr_res,addr_st)` >>
    qpat_x_assum `!s'' x t v c a s3 tv t'. _ ==> _`
      (qspecl_then [`st`,`()`,`st`,`(code_ty,addr)`,`code_ty`,`addr`,`st`,`tail_vs`,`tail_st`] mp_tac) >>
    (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
      (qspecl_then [`env`,`tail_st`,`addr_res`,`addr_st`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    `typed_scope_transition st addr_st` by metis_tac[typed_scope_transition_trans] >>
    rpt (qpat_x_assum `!x. _` kall_tac) >>
    reverse (Cases_on `addr_res`) >> simp_tac(srw_ss())[]
    >- (strip_tac >> gvs[]) >>
    rename1 `eval_exprs cx [addr] tail_st = (INL avs,addr_st)` >>
    Cases_on `evaluate_code_source cx addr_st.accounts (is_self_addr addr)
                code_ty (expr_type addr) avs` >>
    simp_tac(srw_ss())[return_def, raise_def] >> strip_tac >> gvs[]) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  reverse (Cases_on `args_res`) >> simp_tac(srw_ss())[]
  >- (strip_tac >> gvs[]) >>
  rename1 `option_CASE _ _ _ st = (INL vs,args_st)` >>
  Cases_on `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) vs` >>
  simp_tac(srw_ss())[return_def, raise_def]
  >- (Cases_on `precompile_call_success bt vs args_st` >>
      rename1 `precompile_call_success bt vs args_st = (pc_res,pc_st)` >>
      drule precompile_call_success_state >> strip_tac >>
      Cases_on `pc_res` >> simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      irule typed_scope_transition_trans >>
      qexists_tac `args_st` >> simp[typed_scope_transition_scopes]) >>
  strip_tac >> gvs[]
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Attribute]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Attribute"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Subscript]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
      IF (qpat_assum `well_typed_expr _ (Subscript _ _ _)` (K all_tac))
        (qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac)
        (qpat_x_assum `type_place_expr _ (Subscript _ _ _) = SOME _` mp_tac) >>
      simp[NoAsms, Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
      qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
      simp[NoAsms, int_calls_expr_def] >> strip_tac >>
      drule call_evaluation_safe_append_left >> strip_tac >>
      drule call_evaluation_safe_append_right >> strip_tac >>
      Cases_on `eval_expr cx e st` >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        disj1_tac >> first_assum ACCEPT_TAC,
        disj2_tac >> goal_assum drule])) >> strip_tac >>
      qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
        (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
      FIRST [
        qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` drule >> strip_tac,
        qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
          (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac] >>
      qpat_x_assum `!env st res st'. _ ==> (case res of INL pv => live_memory_result _ _ | INR _ => T)` kall_tac >>
      (reverse (Cases_on `q`)
      >- (qpat_x_assum `!s tv t s1 tv1 t1. _` kall_tac >>
          qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
          simp[NoAsms, Once evaluate_def, bind_def] >>
          asm_rewrite_tac[] >> simp[NoAsms, raise_def] >>
          strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> first_assum ACCEPT_TAC) >>
      Cases_on `(if subscript_reads_base cx e e' then
        bind (read_result cx x) (\v. return (Value v)) else return x) r` >>
      rename1 `_ r = (base_res,base_st)` >>
      `base_st = r` by
        (qpat_assum `_ r = (base_res,base_st)` mp_tac >>
         rpt (pop_assum kall_tac) >>
         Cases_on `subscript_reads_base cx e e'` >>
         simp[bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >>
         imp_res_tac read_result_state >> gvs[]) >>
      qpat_x_assum `base_st = r` SUBST_ALL_TAC >>
      (reverse (Cases_on `base_res`)
      >- (qpat_x_assum `!s tv t s1 tv1 t1. _` kall_tac >>
          qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
          simp[NoAsms, Once evaluate_def, bind_def] >>
          asm_rewrite_tac[] >> simp[NoAsms] >>
          strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
          gvs[]) >>
      qpat_x_assum `!s tv t s1 tv1 t1. _` drule_all >> strip_tac) >>
      Cases_on `eval_expr cx e' r` >>
      qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
        (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      disch_then (qspec_then `env` mp_tac) >>
      (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
      rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      imp_res_tac read_result_state >> imp_res_tac vyperPlaceFramesTheory.select_result_state >>
      gvs[typed_scope_transition_def] >>
      imp_res_tac typed_scope_trace_append >>
      gvs[evaluation_state_component_equality] >>
      goal_assum drule >> simp[EVERY_APPEND])
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_StructLit]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_StructLit"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Literal]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Literal"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_IfExp]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_IfExp"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_FlagMember]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  drule lookup_flag_mem_state >> strip_tac >> gvs[] >>
  irule typed_scope_transition_refl
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_TopLevelName]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_TopLevelName"
QED
Resume eval_scc_type_sound_results_mutual[Trace_Expr_Name]:
  RESUME_TAC >> trace_result_tac "Trace_Expr_Name"
QED

Resume eval_scc_type_sound_results_mutual[Trace_IntCall_Operands]:
  RESUME_TAC >>
  ntac 2 (pop_last_assum kall_tac) >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def,
       type_check_def, assert_def,
       return_def, raise_def, get_scopes_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac lift_option_type_state >> rpt BasicProvers.VAR_EQ_TAC >>
  simp[NoAsms, typed_scope_transition_refl] >>
  qpat_x_assum `!s0 x t s1 ts t1 s2 tup t2 mut stup nr stup2 args sstup dflts sstup2 ret body s3 x1 t3. _`
    mp_tac >>
  simp_tac std_ss [type_check_def, assert_def, return_def, raise_def,
    lift_option_type_INL_eq] >>
  imp_res_tac lift_option_type_INL_eq >>
  disch_then drule_all >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
     simp[NoAsms, call_evaluation_safe_def] >> metis_tac[]) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac read_results_state >>
  imp_res_tac finally_set_scopes >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM DE_MORGAN_THM]) >>
  imp_res_tac finally_unless_halt_pop_release_cases >>
  imp_res_tac finally_conditional_lock_scopes >>
  qpat_assum `typed_scope_transition _ _`
    (mp_then Any irule typed_scope_transition_trans) >>
  irule typed_scope_transition_scopes >>
  simp[] >>
  gvs[push_function_def, return_def, AllCaseEqs()] >>
  Cases_on `FST (SND tup)` >> gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  gvs[bind_def, AllCaseEqs()] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  Cases_on `FST tup = View \/ FST tup = Pure` >>
  gvs[return_def, AllCaseEqs()]
QED

(* External calls evaluate every operand before the shared call helper. *)
Resume eval_scc_type_sound_results_mutual[Trace_ExtCall_Operands]:
  RESUME_TAC >>
  drule extcall_call_evaluation_safe_args >> strip_tac >>
  PairCases_on `sig` >>
  qpat_x_assum `well_typed_expr env (Call _ (ExtCall _ _ _ _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH sig1) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 1 es) st` >>
  rename1 `eval_exprs cx (TAKE 1 es) st = (target_res,target_st)` >>
  qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
    (case res0 of INL vs => exprs_runtime_typed env0 (TAKE 1 es) vs | INR _ => T)`
    drule_all >> strip_tac >>
  qpat_assum `!env0 st0 res0 st0'. _ ==> typed_scope_transition _ _`
    drule_all >> strip_tac >>
  Cases_on `target_res`
  >- (qpat_assum `eval_exprs cx (TAKE 1 es) st = _`
        (fn th => simp_tac(srw_ss())[th, sum_case_def, pair_case_def]) >>
      qpat_x_assum `!s target t nargs. eval_exprs cx (TAKE 1 es) s = (INL target,t) /\ _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
      Cases_on `eval_exprs cx (TAKE (LENGTH sig1) (DROP 1 es)) target_st` >>
      rename1 `eval_exprs _ _ target_st = (capture_res,capture_st)` >>
      qpat_assum `!env0 st0 res0 st0'. _ ==> _ /\ _ /\ _ /\ _ /\
        (case res0 of INL vs => exprs_runtime_typed env0 (TAKE _ (DROP _ es)) vs | INR _ => T)`
        drule_all >> strip_tac >>
      qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE _ (DROP _ es)) /\ _ ==> typed_scope_transition _ _`
        drule_all >> strip_tac >>
      Cases_on `capture_res`
      >- (qpat_x_assum `!s target t nargs s1 vs t1. _ ==> _`
            (drule o SIMP_RULE (srw_ss()) []) >>
          disch_then drule >> strip_tac >>
          qpat_assum `eval_exprs _ _ target_st = _`
            (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
          Cases_on `eval_exprs cx (DROP (1 + LENGTH sig1) es) capture_st` >>
          rename1 `eval_exprs _ _ capture_st = (kw_res,kw_st)` >>
          qpat_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (DROP _ es) /\ _ ==> typed_scope_transition _ _`
            drule_all >> strip_tac >>
          rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
          Cases_on `kw_res` >> simp_tac(srw_ss())[sum_case_def, pair_case_def]
          >- (strip_tac >>
              drule eval_ext_call_preserves_non_accounts >> strip_tac >>
              metis_tac[typed_scope_transition_trans, typed_scope_transition_scopes]) >>
          strip_tac >> gvs[] >> metis_tac[typed_scope_transition_trans]) >>
      rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
      gvs[LET_THM, bind_apply] >> strip_tac >> gvs[] >>
      metis_tac[typed_scope_transition_trans]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  gvs[] >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Trace_Create_Operands]:
  RESUME_TAC >>
  drule create_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (create_operand_order kind has_salt es)` by
    metis_tac[well_typed_exprs_create_operand_order] >>
  `call_evaluation_safe cx (int_calls_exprs (create_operand_order kind has_salt es))` by
    metis_tac[call_evaluation_safe_create_operand_order] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_exprs cx (create_operand_order kind has_salt es) st` >>
  rename1 `eval_exprs cx (create_operand_order kind has_salt es) st = (args_res,args_st)` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` drule_all >>
  strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  Cases_on `args_res` >> gvs[] >> strip_tac >> gvs[] >>
  Cases_on `kind` >>
  gvs[eval_create_operands_def, bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  drule eval_create_preserves_scopes_immutables >> strip_tac >>
  metis_tac[typed_scope_transition_trans, typed_scope_transition_scopes]
QED



val live_root_labels = [
  "LiveRootExpr_Name", "LiveRootExpr_TopLevelName", "LiveRootExpr_FlagMember",
  "LiveRootExpr_IfExp", "LiveRootExpr_Literal", "LiveRootExpr_StructLit",
  "LiveRootExpr_Subscript", "LiveRootExpr_Attribute", "LiveRootExpr_Builtin",
  "LiveRootExpr_TypeBuiltin", "LiveRootExpr_Pop",
  "LiveRootExpr_Call_IntCall", "LiveRootExpr_Call_ExtCall", "LiveRootExpr_Call_Send",
  "LiveRootExpr_Call_RawCallTarget", "LiveRootExpr_Call_RawCallCalldataTarget",
  "LiveRootExpr_Call_RawLog", "LiveRootExpr_Call_RawRevert",
  "LiveRootExpr_Call_SelfDestructTarget", "LiveRootExpr_Call_CreateTarget",
  "LiveRootBase_NameTarget", "LiveRootBase_TopLevelNameTarget",
  "LiveRootBase_AttributeTarget", "LiveRootBase_SubscriptTarget", "LiveRootTarget"];
val _ = let
  val SOME (_,parent) = markerLib.lookup_suspension "eval_scc_type_sound_results_mutual"
  val actual = map #1 (!live_root_inventory)
  fun check label =
    if length (markerLib.extract_suspended_goal [parent] label) = 1
    then print ("Singleton live-result obligation: " ^ label ^ "\n")
    else raise Fail ("Non-singleton live-result obligation: " ^ label)
  val _ = if List.all (fn key => List.exists (fn x => x = key) actual) live_root_labels
             andalso List.all (fn key => List.exists (fn x => x = key) live_root_labels) actual
          then () else raise Fail "Live-result inventory mismatch"
 in List.app check live_root_labels end;

Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Name]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, get_scopes_def, type_check_def,
       assert_def, check_def, ignore_bind_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> gvs[IS_SOME_EXISTS] >>
  irule live_memory_result_fresh >> goal_assum (drule_at Any) >>
  simp[memory_eval_path_def, subscripts_type_def, evaluate_subscripts_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_TopLevelName]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[evaluate_def] >> metis_tac[lookup_global_live]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_FlagMember]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, lookup_flag_mem_def, lift_option_type_def,
       bind_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `get_module_code cx nsid0` >> gvs[raise_def] >>
  Cases_on `lookup_flag nsid1 x` >> gvs[raise_def] >>
  Cases_on `INDEX_OF mid x'` >>
  gvs[return_def, raise_def, live_memory_result_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_IfExp]:
  RESUME_TAC >> trace_value_start_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  suspend "Live_IfExp_Selected_Conversion"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Literal]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, return_def] >> strip_tac >>
  gvs[live_memory_result_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_StructLit]:
  RESUME_TAC >> trace_value_start_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[live_memory_result_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Subscript]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  suspend "Live_Subscript_Capture_Index_Selection"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Attribute]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  suspend "Live_Attribute_Capture_Selection"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Builtin]:
  RESUME_TAC >> trace_value_start_tac >>
  suspend "Live_Builtin_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_TypeBuiltin]:
  RESUME_TAC >> trace_value_start_tac >>
  suspend "Live_TypeBuiltin_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Pop]:
  RESUME_TAC >> trace_value_start_tac >>
  suspend "Live_Pop_Retained_Owner"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_IntCall]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_IntCall_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_ExtCall]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_ExtCall_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_Send]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_Send_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_RawCallTarget]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_RawCall_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_RawCallCalldataTarget]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_RawCallCalldata_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_RawLog]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_RawLog_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_RawRevert]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_RawRevert_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_SelfDestructTarget]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_SelfDestruct_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootExpr_Call_CreateTarget]:
  RESUME_TAC >> trace_value_start_tac >> suspend "Live_Create_Returned_Result"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootBase_NameTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def,
       ignore_bind_def, type_check_def, assert_def, check_def,
       return_def, raise_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[IS_SOME_EXISTS] >> irule live_memory_result_fresh >>
  goal_assum (drule_at Any) >>
  simp[evaluate_subscripts_def, memory_eval_path_def, subscripts_type_def, subscript_type_def]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootBase_TopLevelNameTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[evaluate_def] >> metis_tac[lookup_global_live]
QED
Resume eval_scc_type_sound_results_mutual[LiveRootBase_AttributeTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = SOME _` mp_tac >>
  rewrite_tac[type_place_target_AttributeTarget] >> strip_tac >>
  suspend "Live_Base_Attribute_Selection"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootBase_SubscriptTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = SOME _` mp_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  suspend "Live_Base_Subscript_Capture_Index_Selection"
QED
Resume eval_scc_type_sound_results_mutual[LiveRootTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.get_place_state >> gvs[] >>
  gvs[well_typed_target_def] >>
  qpat_x_assum `!env vt st res st'. _ ==> (case _ of INL pv => live_memory_result _ _ | INR _ => T)`
    (drule_all_then assume_tac) >>
  Cases_on `res` >> gvs[get_place_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def]
QED

Resume eval_scc_type_sound_results_mutual[TargetPlace]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_target_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.get_place_state >> gvs[] >>
  qpat_x_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  all_tac >~ [`eval_base_place _ _ _ = (INR _,_)`]
  >- gvs[no_type_error_result_def] >>
  drule eval_base_place_result_shape >> strip_tac >>
  gvs[get_place_def, return_def, raise_def, AllCaseEqs(), is_HashMapRef_def,
      eval_result_typed_def, no_type_error_result_def]
QED


Resume eval_scc_type_sound_results_mutual[Assign_Base_sequence]:
  RESUME_TAC >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  `?tty. well_typed_atarget env (BaseTarget bt) tty /\
         type_widens_to env.type_defs (expr_type e) tty /\
         assignable_type env.type_defs tty` by
    metis_tac[atarget_accepts_well_typed_atarget] >>
  qpat_x_assum `well_typed_atarget env (BaseTarget bt) tty`
    (assume_tac o REWRITE_RULE [well_typed_atarget_def]) >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (rhs_res,rhs_st)` >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  reverse (Cases_on `rhs_res`)
  >- (POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
      simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule eval_expr_exception_return_typed >> simp[]) >>
  qpat_x_assum `!env st res st'. _ ==> (case _ of INL pv => live_memory_result _ _ | INR _ => T)`
    (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  rename1 `eval_expr cx e st = (INL pv,rhs_st)` >>
  simp_tac (srw_ss()) [] >>
  Cases_on `read_result cx pv rhs_st` >>
  rename1 `read_result cx pv rhs_st = (read_res,read_st)` >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  rename1 `read_result cx pv rhs_st = (read_res,rhs_st)` >>
  reverse (Cases_on `read_res`)
  >- (simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def] >>
      irule no_control_exc_return_exception_typed >>
      drule read_result_no_control >> simp[]) >>
  simp_tac (srw_ss()) [] >>
  qpat_x_assum `!s'' pv t' s3 v t''. eval_expr _ _ _ = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  Cases_on `eval_target_place cx bt rhs_st` >>
  rename1 `eval_target_place cx bt rhs_st = (target_res,target_st)` >>
  qpat_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env ty st res st'. _ ==> (case _ of INL p => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then strip_assume_tac) >>
  reverse (Cases_on `target_res`)
  >- (simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def] >>
      irule no_control_exc_return_exception_typed >>
      drule eval_target_place_no_control >> simp[]) >>
  simp_tac (srw_ss()) [] >> suspend "Assign_Base_write"
QED

(* The RHS value is read before the target resolves, so only the target's
   state reaches the write. *)
Resume eval_scc_type_sound_results_mutual[Assign_Base_write]:
  RESUME_TAC >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qmatch_assum_rename_tac `read_result cx pv rhs_st = (INL v,rhs_st)` >>
  qmatch_assum_rename_tac `eval_target_place cx bt rhs_st = (INL p,target_st)` >>
  strip_tac >>
  `value_runtime_typed env tty v` by
    (fs[value_runtime_typed_def] >>
     drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `eval_result_typed (env,cx,target_st) (PlaceR p) (Type tty)` by
    simp[eval_result_typed_def] >>
  drule_all typed_target_place_write_sound >> strip_tac >>
  simp[no_type_error_result_def] >>
  Cases_on `res` >> fs[no_type_error_result_def] >>
  irule no_control_exc_return_exception_typed >>
  drule write_place_no_control >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[AugAssign_place]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> (case _ of INL p => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> (case _ of INL p => live_memory_result _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
  reverse (Cases_on `target_res`)
  >- (POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
      simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def] >>
      irule no_control_exc_return_exception_typed >>
      drule eval_target_place_no_control >> simp[]) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `?tv. evaluate_type _ _ = SOME tv /\ _` strip_assume_tac >>
  qmatch_assum_rename_tac `runtime_place_typed cx target_st p ptv` >>
  `place_type_value cx p target_st = (INL ptv,target_st)` by
    (qpat_assum `runtime_place_typed cx target_st p ptv`
      (ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE [runtime_place_typed_def])) >>
  simp_tac (srw_ss()) [] >> Cases_on `read_place cx p target_st` >>
  rename1 `read_place cx p target_st = (read_res,read_st)` >>
  drule_all live_place_read_sound >> strip_tac >>
  qpat_x_assum `read_st = target_st` SUBST_ALL_TAC >>
  (reverse (Cases_on `read_res`) >| [
    POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
      simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def] >>
      irule no_control_exc_return_exception_typed >>
      drule read_place_no_control >> simp[],
    simp_tac (srw_ss()) [] >> suspend "AugAssign_rhs"])
QED

Resume eval_scc_type_sound_results_mutual[AugAssign_rhs]:
  RESUME_TAC >>
  qmatch_assum_rename_tac `read_place cx p target_st = (INL cur,target_st)` >>
  qpat_x_assum `!s'' p t' s3 cur t2 s4 ptv t3. _`
    (drule_all_then strip_assume_tac) >>
  simp_tac (srw_ss()) [] >>
  Cases_on `eval_expr cx e target_st` >>
  rename1 `eval_expr cx e target_st = (rhs_res,rhs_st)` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_all_then (CONJUNCTS_THEN2 (drule_then strip_assume_tac) kall_tac)) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (qspecl_then [`env`, `target_st`, `rhs_res`, `rhs_st`] mp_tac) >> simp[] >> strip_tac >>
  (reverse (Cases_on `rhs_res`) >| [
    simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule eval_expr_exception_return_typed >> simp[],
    simp_tac (srw_ss()) [] >> suspend "AugAssign_write"])
QED

Resume eval_scc_type_sound_results_mutual[AugAssign_write]:
  RESUME_TAC >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qmatch_assum_rename_tac `eval_expr cx e target_st = (INL rhs,rhs_st)` >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame target_st rhs_st` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `runtime_place_typed cx rhs_st p ptv` by
    (irule runtime_place_typed_transport >> qexists_tac `target_st` >> simp[]) >>
  `writable_place_result cx rhs_st (PlaceR p)` by
    (irule writable_place_result_transport >> qexists_tac `target_st` >> simp[]) >>
  `runtime_place_writable cx rhs_st p` by fs[writable_place_result_def] >>
  `runtime_consistent env cx rhs_st` by simp[runtime_consistent_def] >>
  Cases_on `read_result cx rhs rhs_st` >>
  rename1 `read_result cx rhs rhs_st = (loaded,read_st)` >>
  drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  reverse (Cases_on `loaded`)
  >- (simp[] >> strip_tac >> gvs[no_type_error_result_def] >>
      drule read_result_no_control >> simp[no_control_exc_return_exception_typed]) >>
  simp[] >> strip_tac >> suspend "AugAssign_value_write"
QED

Resume eval_scc_type_sound_results_mutual[AugAssign_value_write]:
  RESUME_TAC >>
  qmatch_assum_rename_tac `read_result cx rhs rhs_st = (INL right,rhs_st)` >>
  fs[value_runtime_typed_def] >>
  qmatch_assum_rename_tac `evaluate_type env.type_defs (expr_type e) = SOME rhs_tv` >>
  `!msg. evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur right <>
    INR (TypeError msg)` by
    (irule well_typed_binop_no_type_error >>
     qexistsl_tac [`ptv`,`ty`,`expr_type e`,`env.type_defs`,`ptv`,`rhs_tv`,`ty`] >> simp[]) >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp_tac (srw_ss()) [bind_def, lift_sum_def] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0) ptv bop cur right` >>
  simp[return_def, raise_def] >> strip_tac >> gvs[no_type_error_result_def]
  >- (qmatch_assum_rename_tac `evaluate_binop _ ptv bop cur right = INL result` >>
      `value_has_type ptv result` by
        (irule well_typed_binop_success_type >>
         qexistsl_tac [`bop`,`ty`,`expr_type e`,`env.type_defs`,`ptv`,`ptv`,`rhs_tv`,`ty`,
           `case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0`,
           `cur`,`right`] >> simp[]) >>
      drule_all write_place_sound >> strip_tac >> gvs[runtime_consistent_def] >>
      Cases_on `res` >> gvs[no_type_error_result_def] >>
      drule write_place_no_control >> simp[no_control_exc_return_exception_typed]) >>
  simp[return_exception_typed_def]
QED


Resume eval_scc_type_sound_results_mutual[TupleStore_BaseTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_atarget _ _ _` mp_tac >>
  simp_tac (srw_ss()) [well_typed_atarget_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atarget _)` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (answer,middle)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> (case _ of INL p => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  reverse (Cases_on `answer`)
  >- (simp_tac (srw_ss()) [] >> strip_tac >> gvs[no_type_error_result_def]) >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `eval_target_place cx bt st = (INL p,middle)` >>
  `eval_result_typed (env,cx,middle) (PlaceR p) (Type ty)` by
    simp[eval_result_typed_def] >>
  drule_all typed_target_place_write_sound >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStore_TupleTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def, int_calls_atarget_def] >>
  drule value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStores_nil_nil]:
  RESUME_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, return_def, no_type_error_result_def]
QED

Resume eval_scc_type_sound_results_mutual[TupleStores_nil_cons]:
  RESUME_TAC >> rpt strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStores_cons_nil]:
  RESUME_TAC >> rpt strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[TupleStores_cons_cons]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  rename1 `assign_tuple_target_list cx (g::gs) (v::vs) st = (res,st')` >>
  Cases_on `tys`
  >- (qpat_x_assum `LIST_REL _ (g::gs) []` mp_tac >> simp[]) >>
  rename1 `LIST_REL _ (g::gs) (head_ty::tail_tys)` >>
  qpat_x_assum `LIST_REL _ (g::gs) (head_ty::tail_tys)` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `LIST_REL _ (head_ty::tail_tys) (v::vs)` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atargets (g::gs))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `assign_tuple_targets cx g v st` >>
  rename1 `assign_tuple_targets cx g v st = (answer,middle)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  reverse (Cases_on `answer`)
  >- (POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
      simp_tac (srw_ss()) [] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' x t. assign_tuple_targets _ _ _ s'' = (INL x,t) ==> _`
    (drule_then strip_assume_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED


Resume eval_scc_type_sound_results_mutual[WritableRootBase_NameTarget]:
  RESUME_TAC >> rpt strip_tac >>
  `?ty. vt = Type ty` by gvs[well_typed_expr_def, AllCaseEqs()] >>
  gvs[] >> drule_all NameTarget_sound >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, assert_def, ignore_bind_def,
       get_scopes_def, type_check_def] >> strip_tac >> gvs[] >>
  simp[writable_place_result_def, runtime_place_writable_def,
       mutable_place_path_def] >> metis_tac[]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootBase_TopLevelNameTarget]:
  RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >> metis_tac[lookup_global_writable]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootBase_AttributeTarget]:
  RESUME_TAC >> rpt gen_tac >>
  rewrite_tac[type_place_target_AttributeTarget] >> strip_tac >>
  gvs[int_calls_expr_def] >>
  Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  first_assum (drule_all_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> (case _ of INL pv => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >> gvs[] >>
  irule extend_place_writable >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  qexists_tac `Type ty` >> Cases_on `tgt_ty` >>
  gvs[target_path_step_type_def, attribute_type_def]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootBase_SubscriptTarget]:
  RESUME_TAC >> rpt gen_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  qmatch_assum_rename_tac `type_place_target env bt = SOME base_vt` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (SubscriptTarget bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!s pv t. eval_base_place _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> (case _ of INL pv => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> _ /\ !vt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  gvs[] >>
  qmatch_assum_rename_tac `eval_base_place cx bt st = (INL base_pv,st1)` >>
  qmatch_assum_rename_tac `eval_expr cx e st1 = (INL idx,st2)` >>
  drule_all typed_result_read_sound >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `eval_expr cx e st1 = (INL idx,st2)` >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st1 st2` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `eval_result_typed (env,cx,st2) base_pv base_vt` by
    (irule eval_result_typed_transport >> qexists_tac `st1` >> simp[eval_result_typed_def]) >>
  `writable_place_result cx st2 base_pv` by
    metis_tac[writable_place_result_transport] >>
  drule_all subscript_vtype_result_step_type >> strip_tac >>
  drule_all extend_place_writable >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[WritableRootTarget]:
  RESUME_TAC >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_target_def] >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, get_place_def, return_def,
       raise_def, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env vt st res st'. _ ==> (case _ of INL pv => writable_place_result _ _ _ | INR _ => T)`
    (drule_all_then strip_assume_tac) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  qmatch_assum_rename_tac `get_place resolved_pv from_st = (INL resolved_place,target_st)` >>
  Cases_on `resolved_pv` >> gvs[get_place_def, return_def, raise_def]
QED

(* Exhaustive coverage audit, including descendant labels. This is diagnostic:
   Finalise below remains the only assembly operation. *)
val _ = let
  val SOME (thy,parent) = markerLib.lookup_suspension "eval_scc_type_sound_results_mutual"
  val seen = ref ([] : string list)
  fun label tm =
    let val (h,args) = strip_comb tm
    in if #Name (dest_thy_const h) = "suspendlabel" then
         SOME (#1 (boolLib.decode_suspend_label (#1 (dest_var (hd args)))))
       else NONE end handle HOL_ERR _ => NONE
  fun walk th = List.app visit (List.mapPartial label (hyp th))
  and visit name = if List.exists (fn x => x = name) (!seen) then () else
    let val _ = seen := name :: !seen
        val candidates = markerLib.lookup_resumption
          {parent_thy=thy,parent_name="eval_scc_type_sound_results_mutual",label=name}
        val proofs = List.filter (fn th => label (concl th) = SOME name) candidates
        val _ = print ("SCC coverage " ^ name ^ ": " ^
          Int.toString (length proofs) ^ " registered bodies\n")
        val _ = if null proofs then
          List.app (fn (_,tm) => print ("MISSING SCC ROOT " ^ name ^ ": " ^
             term_to_string tm ^ "\n"))
            (markerLib.extract_suspended_goal (parent::candidates) name handle HOL_ERR _ => [])
          else ()
    in List.app walk proofs end
in walk parent end;





Resume eval_scc_type_sound_results_mutual[Live_Base_Attribute_Selection]:
  RESUME_TAC >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[int_calls_expr_def] >>
  qpat_assum `!env vt st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!env vt st res st'. _ ==> (case _ of INL pv => live_memory_result _ _ | INR _ => T)`
    (drule_all_then assume_tac) >>
  Cases_on `res` >> gvs[] >>
  drule_all extend_typed_result_live >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Live_IntCall_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Trace_Base_Attribute_Selection]:
  RESUME_TAC >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[int_calls_expr_def] >>
  imp_res_tac vyperPlaceFramesTheory.extend_place_state >> gvs[] >>
  qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then assume_tac) >>
  qpat_x_assum `st' = _` SUBST1_TAC >>
  gvs[typed_scope_transition_def] >> goal_assum drule >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Live_Create_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  Cases_on `kind` >>
  simp[eval_create_operands_def, bind_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_create_success_value >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_ExtCall_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs(),
       live_memory_result_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_ext_call_success_value >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_RawLog_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_RawRevert_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_SelfDestruct_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[selfdestruct_no_success]
QED

Resume eval_scc_type_sound_results_mutual[Live_Send_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs(),
       live_memory_result_def, ignore_bind_def, type_check_def, assert_def,
       raise_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_send_success_value >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_RawCall_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_raw_call_success_value >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_RawCallCalldata_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule eval_raw_call_success_value >> strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_Builtin_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Live_TypeBuiltin_Returned_Result]:
  RESUME_TAC >> Cases_on `res` >> simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), live_memory_result_def] >>
  strip_tac >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[Trace_Attribute_Selection]:
  RESUME_TAC >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Attribute _ _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  FIRST [
    qpat_x_assum `well_typed_expr env (Attribute _ _ _)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [Once well_typed_expr_def]),
    qpat_x_assum `type_place_expr env (Attribute _ _ _) = SOME vt`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [Once well_typed_expr_def, AllCaseEqs()])] >>
  Cases_on `eval_expr cx e st` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC,
    disj2_tac >> goal_assum drule])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >>
  qpat_x_assum `st' = _` SUBST1_TAC >>
  gvs[typed_scope_transition_def] >> goal_assum drule >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Live_Attribute_Capture_Selection]:
  RESUME_TAC >>
  FIRST [
    qpat_x_assum `well_typed_expr env (Attribute _ _ _)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [Once well_typed_expr_def]),
    qpat_x_assum `type_place_expr env (Attribute _ _ _) = SOME vt` mp_tac >>
      simp[Once well_typed_expr_def]] >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Attribute _ _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  Cases_on `eval_expr cx e st` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >> Cases_on `res` >> gvs[] >>
  irule transported_typed_result_extend_live >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl_tac [`env`, `Type (expr_type e)`] >>
  simp[typed_scope_transition_refl, vyperImmutableMetadataFrameTheory.immutable_metadata_frame_refl]
QED

Resume eval_scc_type_sound_results_mutual[Live_Pop_Retained_Owner]:
  RESUME_TAC >>
  rename1 `eval_expr cx (Pop ty bt) st = (res,st')` >>
  drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
  `well_typed_target env bt (ArrayT ty (Dynamic n))` by simp[well_typed_target_def] >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Pop _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  rpt (qpat_x_assum `!env ty st res st'. _` kall_tac) >>
  qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  (reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[])) >>
  simp[] >> strip_tac >>
  gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  rename1 `evaluate_type env.type_defs ty = SOME tv` >>
  `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
  `runtime_place_writable cx st1 x` by gvs[writable_place_result_def] >>
  Cases_on `res` >> simp[] >> rename1 `pop_place cx x st1 = (INL pv,st')` >>
  Cases_on `pv` >> simp[live_memory_result_def] >>
  drule_at (Pat `pop_place _ _ _ = _`) pop_place_result_live >>
  disch_then (qspecl_then [`n`,`tv`,`env`] mp_tac) >>
  impl_tac >- (Cases_on `x` >> gvs[live_memory_result_def] >> metis_tac[]) >>
  simp[live_memory_result_def]
QED

Resume eval_scc_type_sound_results_mutual[Trace_Pop_Target]:
  RESUME_TAC >>
  rename1 `eval_expr cx (Pop ty bt) st = (res,st')` >>
  FIRST [drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac,
    qpat_x_assum `type_place_expr env (Pop _ _) = SOME vt` mp_tac >>
      simp[Once well_typed_expr_def]] >>
  `well_typed_target env bt (ArrayT ty (Dynamic n))` by simp[well_typed_target_def] >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Pop _ _))`
    (assume_tac o REWRITE_RULE [int_calls_expr_def]) >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  qpat_x_assum `!env ty st res st'. _ ==> state_well_typed _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => live_memory_result _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> case res of INL p => writable_place_result _ _ _ | INR _ => T`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env ty st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  (reverse (Cases_on `target_res`) >- (simp[] >> strip_tac >> gvs[])) >>
  simp[] >> strip_tac >>
  gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  rename1 `evaluate_type env.type_defs ty = SOME tv` >>
  `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
  `runtime_place_writable cx st1 x` by gvs[writable_place_result_def] >>
  irule typed_scope_transition_trans >> qexists_tac `st1` >> simp[] >>
  irule pop_place_typed_transition >>
  goal_assum (drule_at (Pat `pop_place _ _ _ = _`)) >>
  qexistsl_tac [`env`,`tv`,`n`] >> simp[]
QED

Resume eval_scc_type_sound_results_mutual[Live_Subscript_Capture_Index_Selection]:
  RESUME_TAC >>
  IF (qpat_assum `well_typed_expr _ (Subscript _ _ _)` (K all_tac))
    (qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac)
    (qpat_x_assum `type_place_expr _ (Subscript _ _ _) = SOME _` mp_tac) >>
  simp[NoAsms, Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_expr cx e st` >>
  qpat_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  FIRST [
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _` drule >> strip_tac,
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac] >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC,
    disj2_tac >> goal_assum drule])) >> strip_tac >>
  (reverse (Cases_on `q`)
  >- (qpat_x_assum `!s'' res t. _` kall_tac >>
      rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, raise_def] >> strip_tac >> gvs[]) >>
  rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
  rule_assum_tac BETA_RULE >>
  Cases_on `(if subscript_reads_base cx e e' then
    bind (read_result cx x) (\v. return (Value v)) else return x) r` >>
  rename1 `_ r = (base_res,base_st)` >>
  FIRST [drule_all place_optional_read_result_live_typed >> strip_tac,
         drule_all optional_read_result_live_typed >> strip_tac] >>
  (reverse (Cases_on `base_res`)
  >- (rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s tv t s1 tv1 t1. _` drule_all >> strip_tac) >>
  qpat_x_assum `base_st = r` SUBST_ALL_TAC >>
  rule_assum_tac (REWRITE_RULE [sumTheory.sum_case_def]) >>
  rule_assum_tac BETA_RULE >>
  Cases_on `eval_expr cx e' r` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `res` >> simp[] >>
  irule transported_typed_result_extend_live >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  drule eval_expr_immutable_metadata_frame >> simp[])
QED

Resume eval_scc_type_sound_results_mutual[Trace_Base_Subscript_Selection]:
  RESUME_TAC >>
  qpat_x_assum `type_place_target env (SubscriptTarget _ _) = SOME _` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_base_place cx bt st` >>
  qpat_x_assum `!env vt st res st'. _ ==> typed_scope_transition _ _`
    (drule_all_then assume_tac) >>
  qpat_x_assum `!env vt st res st'. _ ==> _ /\ _`
    (drule_all_then strip_assume_tac) >>
  (reverse (Cases_on `q`)
  >- (rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, raise_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' pv t'. eval_base_place _ _ _ = _ ==> _`
    (qspecl_then [`st`,`x`,`r`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `eval_expr cx e r` >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> imp_res_tac vyperPlaceFramesTheory.extend_place_state >>
  gvs[evaluation_state_component_equality, typed_scope_transition_def] >>
  metis_tac[typed_scope_trace_append])
QED

Resume eval_scc_type_sound_results_mutual[Live_Base_Subscript_Capture_Index_Selection]:
  RESUME_TAC >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  Cases_on `eval_base_place cx bt st` >>
  qpat_x_assum `!env vt st res st'. _ ==> _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!env vt st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_all_then assume_tac) >>
  (reverse (Cases_on `q`)
  >- (rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
      qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
      simp[NoAsms, raise_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s'' pv t'. eval_base_place _ _ _ = _ ==> _`
    (qspecl_then [`st`,`x`,`r`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `eval_expr cx e r` >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `res` >> simp[] >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame r r''` by
    (drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `eval_result_typed (env,cx,r'') x vt'` by
    (irule eval_result_typed_transport >> goal_assum (drule_at Any) >> simp[]) >>
  `live_memory_result r'' x` by
    (Cases_on `x` >> simp[live_memory_result_def] >>
     rename1 `PlaceR p` >> Cases_on `p` >> simp[live_memory_result_def] >>
     drule_all live_memory_result_transport >> simp[live_memory_result_def]) >>
  irule extend_typed_result_live >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum drule)
QED

Resume eval_scc_type_sound_results_mutual[Live_IfExp_Selected_Conversion]:
  RESUME_TAC >>
  qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
  simp[NoAsms, int_calls_expr_def] >> strip_tac >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> (_ ==> _) /\ _` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!s'' tv t. eval_expr _ _ s'' = (INL tv,t) ==> _` drule >> strip_tac) >>
  qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
  simp[NoAsms, switch_BoolV_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac read_result_state >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[NoAsms, COND_RATOR, raise_def] >> rpt IF_CASES_TAC >>
  simp[NoAsms, raise_def] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!env st res st'. (well_typed_expr env e \/ _) /\ _ ==> _` kall_tac) >>
  qpat_x_assum `!env st res st'. _ ==> (_ ==> _) /\ _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  gvs[] >> drule_all conditional_result_live_typed >> strip_tac >> gvs[] >>
  Cases_on `res` >> gvs[]
QED

Resume eval_scc_type_sound_results_mutual[RaiseCustomError]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `call_evaluation_safe cx
       (int_calls_stmt (Raise (RaiseCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >>
  strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def, well_typed_custom_error_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  Cases_on `err` >>
  Cases_on `get_module_code cx (FST p)`
  >- gvs[evaluate_def, raise_def, no_type_error_result_def,
          return_exception_typed_def] >>
  rename1 `get_module_code cx (FST p) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND p) tops`
  >- gvs[evaluate_def, raise_def, no_type_error_result_def,
          return_exception_typed_def] >>
  rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError p l l0)`
  >- gvs[evaluate_def, raise_def, no_type_error_result_def,
          return_exception_typed_def] >>
  rename1
    `order_custom_error_args params (CustomError p positional kwargs) =
       SOME es` >>
  qpat_x_assum `!id positional' kwargs' tops params es. _`
    (qspecl_then [`p`, `positional`, `kwargs`, `tops`, `params`, `es`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def] >>
  `PERM (custom_error_exprs (CustomError p positional kwargs)) es` by
    (drule order_custom_error_args_perm >> simp[]) >>
  `well_typed_exprs env es` by
    (drule well_typed_exprs_perm >>
     disch_then (qspec_then `env` mp_tac) >>
     simp[custom_error_exprs_def]) >>
  `call_evaluation_safe cx
      (int_calls_exprs (custom_error_exprs
        (CustomError p positional kwargs)))` by
    simp[custom_error_exprs_def] >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qspecl_then
       [`cx`, `custom_error_exprs (CustomError p positional kwargs)`, `es`]
       mp_tac call_evaluation_safe_exprs_perm >>
     simp[custom_error_exprs_def]) >>
  pure_rewrite_tac[bind_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res,st1)` >>
  qpat_x_assum `!env st res st'. _ ==> (state_well_typed st' /\ _)`
    drule_all >>
  strip_tac >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  Cases_on `exprs_res`
  >- (
    Cases_on
      `build_custom_error_data (get_tenv cx) (SND p)
         (MAP SND params) x` >>
    gvs[bind_def, no_type_error_result_def, lift_option_def, return_def, raise_def,
        return_exception_typed_def] >>
    rpt strip_tac >>
    gvs[bind_def, no_type_error_result_def, lift_option_def, return_def, raise_def,
        return_exception_typed_def]) >>
  rpt strip_tac >>
  gvs[no_type_error_result_def, bind_def, return_exception_typed_def] >>
  drule_all eval_exprs_exception_return_typed >>
  disch_then (qspecl_then [`ret_ty`, `env`] mp_tac) >>
  simp[return_exception_typed_def]
QED


Resume eval_scc_type_sound_results_mutual[AssertCustomError]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `call_evaluation_safe cx
       (int_calls_stmt (Assert e (AssertCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_exprs (custom_error_exprs err)` >> simp[]) >>
  `call_evaluation_safe cx
      (int_calls_exprs (custom_error_exprs err))` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())
    [type_stmt_def, well_typed_custom_error_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())
    [evaluate_def, bind_def, return_def, raise_def, AllCaseEqs(),
     PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _`
    (drule_then strip_assume_tac) >>
  Cases_on `expr_res` >> rewrite_tac[no_type_error_result_def]
  >- (
    qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _` kall_tac >>
    qpat_x_assum `!vt. _` kall_tac >>
    qpat_x_assum `case INL x of INL pv => eval_result_typed _ pv _ | INR _ => T` mp_tac >>
    simp_tac (srw_ss()) [] >> strip_tac >>
    `live_memory_result st1 x` by (
      qpat_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ pv | INR _ => T`
        (qspecl_then [`env`, `st`, `INL x`, `st1`] mp_tac) >> simp[]) >>
    qpat_x_assum `!s tv t id positional kwargs tops params es. _`
      (drule_then (mk_asm "custom_ih")) >>
    Cases_on `read_result cx x st1` >>
    rename1 `read_result cx x st1 = (loaded,st2)` >>
    drule_all live_result_read_typed >> strip_tac >> gvs[] >>
    reverse (Cases_on `loaded`)
    >- (drule read_result_no_control >> strip_tac >>
        Cases_on `y` >>
        gvs[switch_BoolV_def, bind_def, raise_def, no_control_exc_def,
            no_type_error_result_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    gvs[value_runtime_typed_def, evaluate_type_def] >>
    drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
    Cases_on `b` >> simp[switch_BoolV_def, bind_def, return_def]
    >- (rpt strip_tac >> gvs[no_type_error_result_def]) >>
    asm_x "custom_ih" strip_assume_tac >>
    Cases_on `err` >>
    Cases_on `get_module_code cx (FST p)`
    >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
        rpt strip_tac >>
        gvs[raise_def, no_type_error_result_def,
            return_exception_typed_def]) >>
    rename1 `get_module_code cx (FST p) = SOME tops` >>
    Cases_on `lookup_custom_error_args_in (SND p) tops`
    >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
        rpt strip_tac >>
        gvs[raise_def, no_type_error_result_def,
            return_exception_typed_def]) >>
    rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
    Cases_on `order_custom_error_args params (CustomError p l l0)`
    >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
        rpt strip_tac >>
        gvs[raise_def, no_type_error_result_def,
            return_exception_typed_def]) >>
    rename1
      `order_custom_error_args params
         (CustomError p positional kwargs) = SOME es` >>
    qpat_x_assum `!id positional' kwargs' tops params es. _`
      (qspecl_then [`p`, `positional`, `kwargs`, `tops`, `params`, `es`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    `PERM (custom_error_exprs (CustomError p positional kwargs)) es` by
      (drule order_custom_error_args_perm >> simp[]) >>
    `well_typed_exprs env es` by
      (drule well_typed_exprs_perm >>
       disch_then (qspec_then `env` mp_tac) >>
       simp[custom_error_exprs_def]) >>
    `call_evaluation_safe cx
        (int_calls_exprs (custom_error_exprs
          (CustomError p positional kwargs)))` by
      simp[custom_error_exprs_def] >>
    `call_evaluation_safe cx (int_calls_exprs es)` by
      (qspecl_then
         [`cx`, `custom_error_exprs (CustomError p positional kwargs)`, `es`]
         mp_tac call_evaluation_safe_exprs_perm >>
       simp[custom_error_exprs_def]) >>
    Cases_on `eval_exprs cx es st1` >>
    rename1 `eval_exprs cx es st1 = (args_res,st2)` >>
    qpat_x_assum `!env st res st'. _ ==> (state_well_typed st' /\ _)`
      drule_all >> strip_tac >>
    rpt (qpat_x_assum `!x. _` kall_tac) >>
    Cases_on `args_res`
    >- (Cases_on `build_custom_error_data (get_tenv cx) (SND p) (MAP SND params) x'` >>
        gvs[bind_def, no_type_error_result_def, lift_option_def, return_def,
            raise_def, return_exception_typed_def] >>
        rpt strip_tac >> gvs[]) >>
    rpt strip_tac >>
    gvs[no_type_error_result_def, bind_def, return_exception_typed_def] >>
    drule_all eval_exprs_exception_return_typed >>
    disch_then (qspecl_then [`ret_ty`, `env`] mp_tac) >>
    simp[return_exception_typed_def]) >>
  rpt strip_tac >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  gvs[no_type_error_result_def] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED


Finalise eval_scc_type_sound_results_mutual

Theorem eval_scc_type_sound_mutual =
  LIST_CONJ (List.take (CONJUNCTS eval_scc_type_sound_results_mutual, 10));

(* Forcing is part of the public expression guarantee, not a caller premise. *)
Theorem eval_expr_read_type_sound:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do result <- eval_expr cx e; read_result cx result od) st = (res,st') ==>
  state_well_typed st' /\ no_type_error_result res /\
  (case res of INL v => value_runtime_typed env (expr_type e) v | INR _ => T)
Proof
  rpt strip_tac >>
  qspecl_then [`cx`,`e`] strip_assume_tac (cj 5 eval_scc_type_sound_mutual) >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!env st res st'. _ ==> case res of INL pv => live_memory_result _ _ | INR _ => T`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC])) >> strip_tac >>
  rpt (first_x_assum (fn th => if is_forall (concl th) then kall_tac th else NO_TAC)) >>
  imp_res_tac read_result_state >> gvs[]
  >~ [`no_type_error_result (INR _)`]
  >- gvs[no_type_error_result_def] >>
  drule_all live_result_read_typed >> strip_tac >> simp[]
QED
