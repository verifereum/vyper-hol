Theory vyperEvalExprPreservesScopesDom
Ancestors
  pair sum vyperMisc vyperContext vyperState vyperCreate vyperCreateFrame vyperInterpreter vyperLookup
  vyperScopePreservation vyperStatePreservation vyperPlaceFrames vyperCallFrame vyperCallOutcomeFrame
  vyperCallOutcome[ignore_grammar]

(* ========================================================================
   Utility: eval_exprs preserves scopes dom from per-element IH
   (kept for downstream use)
   ======================================================================== *)

Theorem eval_exprs_preserves_scopes_dom_helper[local]:
  ∀es cx st res st'.
    (∀e. MEM e es ⇒ ∀cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  Induct >> simp[evaluate_def, return_def] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_scopes >> gvs[]
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
      first_x_assum (qspecl_then [`cx`, `s'³'`, `INL vs`, `s'⁴'`] mp_tac) >> simp[] >>
      disch_then irule >> rpt strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`cx'`, `e`, `res`] >> simp[])
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
      first_x_assum (qspecl_then [`cx`, `s'³'`, `INR e`, `s'⁴'`] mp_tac) >> simp[] >>
      disch_then irule >> rpt strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`cx'`, `e'`, `res`] >> simp[])
  >- (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[])
  >- (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[])
QED

(* Domain preservation follows the evaluator's mutual induction.
   Statements are deliberately unconstrained: declarations add locals. *)
Theorem Send_outcome_preserves_locals:
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >>
  drule_all (Send_outcome_transport |> Q.INST
    [`R` |-> `\s t. t.scopes = s.scopes /\ t.immutables = s.immutables`]
    |> SRULE []) >> simp[]
QED

Theorem eval_mutual_preserves_scopes_dom[local]:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:value list. T) /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def,
          lift_option_type_def, return_def, raise_def, AllCaseEqs()])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_global_scopes >> gvs[])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_flag_mem_scopes >> gvs[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def,
          switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >>
      imp_res_tac conditional_result_state >> gvs[] >>
      gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac select_result_state >>
      gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >- suspend "Builtin"
  >- (rpt strip_tac >>
      qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac pop_place_scopes_dom >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
      rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac lift_sum_state >> gvs[] >>
      first_x_assum drule >> simp[type_check_def, assert_def, return_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `LENGTH es = if has_gas then 3 else 2` >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def] >>
      first_x_assum (qspecl_then [`st`, `st`] mp_tac) >>
      simp[type_check_def, assert_def, return_def] >> strip_tac >>
      rpt CASE_TAC >> rpt strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      drule eval_send_preserves_non_accounts >> strip_tac >> gvs[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_expr cx (Call _ (ExtCall _ _ _ _) _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
      imp_res_tac read_results_state >>
      gvs[] >>
      rpt (qpat_x_assum `∀a b c d e f. _` drule_all >> strip_tac) >>
      rpt (qpat_x_assum `∀a b c. _` drule_all >> strip_tac) >>
      metis_tac[])
  >- suspend "IntCall"
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, type_check_def, assert_def, lift_option_type_def,
           option_CASE_rator] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, type_check_def, assert_def, lift_option_type_def,
           option_CASE_rator] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def, lift_option_def,
           lift_option_type_def, push_log_def, option_CASE_rator] >>
      strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
          raise_def, check_def, type_check_def, assert_def] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def, lift_option_def,
           lift_option_type_def, get_accounts_def, option_CASE_rator] >>
      strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac transfer_value_scopes >> gvs[] >> metis_tac[])
  >- suspend "CreateTarget"
  >- simp[Once evaluate_def, return_def]
  >- (rpt strip_tac >>
      qpat_x_assum `eval_exprs cx (_::_) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac read_result_state >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_global_scopes >> gvs[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place cx (AttributeTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac extend_place_state >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
      gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
  qpat_x_assum `eval_target_place cx _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[])
  >- simp[Once evaluate_def, return_def]
  >> rpt strip_tac >>
  qpat_x_assum `eval_expr_results cx (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> metis_tac[]
QED

Resume eval_mutual_preserves_scopes_dom[Builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len`
      >- suspend "BuiltinLen"
      >> Cases_on `bt = Env MsgGas`
      >- suspend "BuiltinGas"
      >> suspend "BuiltinRest")
  >> simp[Once evaluate_def, type_check_def, assert_def, bind_def,
          ignore_bind_def, raise_def]
QED

Resume eval_mutual_preserves_scopes_dom[BuiltinLen]:
  qpat_x_assum `!s t. _ /\ bt = Len ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac result_array_length_state >>
  gvs[] >>
  first_x_assum (qspecl_then [`st`, `st`] mp_tac) >>
  simp[type_check_def, assert_def, return_def]
QED

Resume eval_mutual_preserves_scopes_dom[BuiltinGas]:
  rpt (qpat_x_assum `!s t. _` kall_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac next_gas_reading_state >> gvs[]
QED

Resume eval_mutual_preserves_scopes_dom[BuiltinRest]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `bt`
  >- (qpat_x_assum `Len <> Len` mp_tac >> simp[NoAsms])
  >- suspend "RestCalldataLen"
  >- suspend "RestCalldataSlice"
  >- suspend "RestNot"
  >- suspend "RestNeg"
  >- suspend "RestAbs"
  >- suspend "RestKeccak"
  >- suspend "RestSha"
  >- suspend "RestWei"
  >- suspend "RestConcat"
  >- suspend "RestSlice"
  >- suspend "RestUint"
  >- suspend "RestArray"
  >- suspend "RestCeil"
  >- suspend "RestFloor"
  >- suspend "RestAddMod"
  >- suspend "RestMulMod"
  >- suspend "RestBop"
  >- suspend "RestBlockHash"
  >- suspend "RestBlobHash"
  >- suspend "RestEnv"
  >- suspend "RestAcc"
  >- suspend "RestMethod"
  >- suspend "RestRecover"
  >- suspend "RestECAdd"
  >- suspend "RestECMul"
  >> suspend "RestPow"
QED

Resume eval_mutual_preserves_scopes_dom[RestCalldataLen]:
  gvs[type_check_def, assert_def, return_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac get_accounts_state >> imp_res_tac lift_sum_state >>
  gvs[] >> metis_tac[]
QED

val scopes_builtin_ordinary_tac =
  strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac get_accounts_state >> imp_res_tac lift_sum_state >>
  gvs[] >> metis_tac[];

Resume eval_mutual_preserves_scopes_dom[RestCalldataSlice]:
  qpat_x_assum `!s t n'. _ /\ _ /\ _ /\ CalldataSlice n = CalldataSlice n' ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestNot]:
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestNeg]:
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestAbs]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ Abs = Abs ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestKeccak]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ Keccak256 = Keccak256 ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestSha]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ Sha256 = Sha256 ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestWei]:
  qpat_x_assum `!s t w. _ /\ _ /\ _ /\ AsWeiValue _ = AsWeiValue w ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestConcat]:
  qpat_x_assum `!s t w. _ /\ _ /\ _ /\ Concat _ = Concat w ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestSlice]:
  qpat_assum `builtin_args_length_ok _ _` mp_tac >>
  simp[NoAsms, builtin_args_length_ok_def] >> strip_tac >>
  namedCases_on `es` ["", "operand rest1"]
  >- (qpat_x_assum `LENGTH [] = 3` mp_tac >> simp[NoAsms])
  >> namedCases_on `rest1` ["", "start rest2"]
  >- (qpat_x_assum `LENGTH [_] = 3` mp_tac >> simp[NoAsms])
  >> namedCases_on `rest2` ["", "len rest3"]
  >- (qpat_x_assum `LENGTH [_;_] = 3` mp_tac >> simp[NoAsms])
  >> Cases_on `rest3`
  >- suspend "SliceThree"
  >> qpat_x_assum `LENGTH _ = 3` mp_tac >> simp[NoAsms]
QED
Resume eval_mutual_preserves_scopes_dom[SliceThree]:
  namedCases_on `operand`
    ["ty id", "ty id", "ty id flag", "ty test yes no",
     "ty lit", "ty name fields", "ty base ix", "ty base field",
     "ct builtin args", "ty tb tv args", "ty target", "ty call args keys"]
  >- suspend "SliceName"
  >- suspend "SliceTopName"
  >- suspend "SliceFlag"
  >- suspend "SliceIf"
  >- suspend "SliceLiteral"
  >- suspend "SliceStruct"
  >- suspend "SliceSubscript"
  >- suspend "SliceAttribute"
  >- suspend "SliceBuiltin"
  >- suspend "SliceTypeBuiltin"
  >- suspend "SlicePop"
  >> suspend "SliceCall"
QED

Resume eval_mutual_preserves_scopes_dom[SliceName]:
  qpat_x_assum `!s t n' tl ty id. _ /\ _ /\ _ /\ _ /\ _ = Name ty id::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED

Resume eval_mutual_preserves_scopes_dom[SliceTopName]:
  qpat_x_assum `!s t n' tl a b. _ /\ _ /\ _ /\ _ /\ _ = TopLevelName a b::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceFlag]:
  qpat_x_assum `!s t n' tl a b c. _ /\ _ /\ _ /\ _ /\ _ = FlagMember a b c::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceIf]:
  qpat_x_assum `!s t n' tl a b c d. _ /\ _ /\ _ /\ _ /\ _ = IfExp a b c d::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceLiteral]:
  qpat_x_assum `!s t n' tl a b. _ /\ _ /\ _ /\ _ /\ _ = Literal a b::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceStruct]:
  qpat_x_assum `!s t n' tl a b c. _ /\ _ /\ _ /\ _ /\ _ = StructLit a b c::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceSubscript]:
  qpat_x_assum `!s t n' tl a b c. _ /\ _ /\ _ /\ _ /\ _ = Subscript a b c::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceAttribute]:
  qpat_x_assum `!s t n' tl a b c. _ /\ _ /\ _ /\ _ /\ _ = Attribute a b c::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceTypeBuiltin]:
  qpat_x_assum `!s t n' tl a b c d. _ /\ _ /\ _ /\ _ /\ _ = TypeBuiltin a b c d::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SlicePop]:
  qpat_x_assum `!s t n' tl a b. _ /\ _ /\ _ /\ _ /\ _ = Pop a b::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceCall]:
  qpat_x_assum `!s t n' tl a b c d. _ /\ _ /\ _ /\ _ /\ _ = Call a b c d::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceBuiltin]:
  Cases_on `builtin = Acc Code`
  >- (namedCases_on `args` ["", "addr rest"]
      >- suspend "SliceCodeEmpty"
      >> Cases_on `rest`
      >- suspend "SliceCodeOne"
      >> suspend "SliceCodeMany")
  >> suspend "SliceOtherBuiltin"
QED
Resume eval_mutual_preserves_scopes_dom[SliceCodeOne]:
  qpat_x_assum `!s u n' ct a x y ps vs pt. _ /\ _ /\ _ /\ (_ /\ _ = [Builtin ct (Acc Code) [a]; x; y]) /\ _ ==> _` mp_tac >>
  qpat_x_assum `!s u n' ct a x y. _ /\ _ /\ _ /\ _ /\ _ = [Builtin ct (Acc Code) [a]; x; y] ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >>
  ntac 2 strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  simp[bind_def, return_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  imp_res_tac get_accounts_state >> imp_res_tac lift_sum_state >>
  gvs[] >> metis_tac[]
QED

Resume eval_mutual_preserves_scopes_dom[SliceCodeEmpty]:
  qpat_x_assum `!s u n' tl ct. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Acc Code) []::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceCodeMany]:
  qpat_x_assum `!s u n' tl ct a x xs. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Acc Code) (a::x::xs)::tl ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[SliceOtherBuiltin]:
  Cases_on `builtin`
  >- suspend "NestedLen"
  >- suspend "NestedCalldataLen"
  >- suspend "NestedCalldataSlice"
  >- suspend "NestedNot"
  >- suspend "NestedNeg"
  >- suspend "NestedAbs"
  >- suspend "NestedKeccak"
  >- suspend "NestedSha"
  >- suspend "NestedWei"
  >- suspend "NestedConcat"
  >- suspend "NestedSlice"
  >- suspend "NestedUint"
  >- suspend "NestedArray"
  >- suspend "NestedCeil"
  >- suspend "NestedFloor"
  >- suspend "NestedAddMod"
  >- suspend "NestedMulMod"
  >- suspend "NestedBop"
  >- suspend "NestedBlockHash"
  >- suspend "NestedBlobHash"
  >- suspend "NestedEnv"
  >- suspend "NestedAcc"
  >- suspend "NestedMethod"
  >- suspend "NestedRecover"
  >- suspend "NestedECAdd"
  >- suspend "NestedECMul"
  >> suspend "NestedPow"
QED
fun scopes_keep_operand pat =
  qpat_x_assum pat mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac;

Resume eval_mutual_preserves_scopes_dom[NestedLen]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct Len args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedCalldataLen]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct CalldataLen args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedCalldataSlice]:
  scopes_keep_operand `!s u n' tl ct args k. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (CalldataSlice k) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedNot]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct Not args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedNeg]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct Neg args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedAbs]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct Abs args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedKeccak]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct Keccak256 args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedSha]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct Sha256 args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedWei]:
  scopes_keep_operand `!s u n' tl ct args k. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (AsWeiValue k) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedConcat]:
  scopes_keep_operand `!s u n' tl ct args k. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Concat k) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedSlice]:
  scopes_keep_operand `!s u n' tl ct args k. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Slice k) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedUint]:
  scopes_keep_operand `!s u n' tl ct args k. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Uint2Str k) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedArray]:
  scopes_keep_operand `!s u n' tl ct args k m. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (MakeArray k m) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedCeil]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct Ceil args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedFloor]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct Floor args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedAddMod]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct AddMod args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedMulMod]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct MulMod args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedBop]:
  scopes_keep_operand `!s u n' tl ct args k. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Bop k) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedBlockHash]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct BlockHash args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedBlobHash]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct BlobHash args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedEnv]:
  scopes_keep_operand `!s u n' tl ct args k. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Env k) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedAcc]:
  Cases_on `a`
  >- suspend "NestedAddress"
  >- suspend "NestedBalance"
  >- suspend "NestedCodehash"
  >- suspend "NestedCodesize"
  >- suspend "NestedIsContract"
  >> (qpat_x_assum `Acc Code <> Acc Code` mp_tac >> simp[NoAsms])
QED
Resume eval_mutual_preserves_scopes_dom[NestedAddress]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Acc Address) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedBalance]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Acc Balance) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedCodehash]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Acc Codehash) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedCodesize]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Acc Codesize) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedIsContract]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct (Acc IsContract) args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedMethod]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct MethodId args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedRecover]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct ECRecover args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedECAdd]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct ECAdd args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedECMul]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct ECMul args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[NestedPow]:
  scopes_keep_operand `!s u n' tl ct args. _ /\ _ /\ _ /\ _ /\ _ = Builtin ct PowMod256 args::tl ==> _` >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED



Resume eval_mutual_preserves_scopes_dom[RestUint]:
  qpat_x_assum `!s t w. _ /\ _ /\ _ /\ Uint2Str _ = Uint2Str w ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestArray]:
  qpat_x_assum `!s t a b. _ /\ _ /\ _ /\ MakeArray _ _ = MakeArray a b ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >>
  scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestCeil]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ Ceil = Ceil ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestFloor]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ Floor = Floor ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestAddMod]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ AddMod = AddMod ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestMulMod]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ MulMod = MulMod ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestBop]:
  qpat_x_assum `!s t w. _ /\ _ /\ _ /\ Bop _ = Bop w ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestBlockHash]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ BlockHash = BlockHash ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestBlobHash]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ BlobHash = BlobHash ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestEnv]:
  qpat_x_assum `!s t w. _ /\ _ /\ _ /\ Env _ = Env w ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestAcc]:
  qpat_x_assum `!s t w. _ /\ _ /\ _ /\ Acc _ = Acc w ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestMethod]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ MethodId = MethodId ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestRecover]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ ECRecover = ECRecover ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestECAdd]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ ECAdd = ECAdd ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestECMul]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ ECMul = ECMul ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED
Resume eval_mutual_preserves_scopes_dom[RestPow]:
  qpat_x_assum `!s t. _ /\ _ /\ _ /\ PowMod256 = PowMod256 ==> _` mp_tac >>
  rpt (qpat_x_assum `!s t. _` kall_tac) >> strip_tac >>
  gvs[type_check_def, assert_def, return_def] >> scopes_builtin_ordinary_tac
QED

Resume eval_mutual_preserves_scopes_dom[CreateTarget]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
  res_tac >>
  imp_res_tac eval_create_preserves_scopes_immutables >> gvs[] >>
  metis_tac[]
QED
(* Lock operations preserve scopes: needed for IntCall handler.
   Uses bind form (not ignore_bind) because earlier SIMP_TAC expands ignore_bind.
   Uses ≠ form because simp normalizes ¬(A ∨ B) to ¬A ∧ ¬B. *)
Theorem finally_intcall_handler_scopes[local]:
  ∀f nr mut cx prev s res s'.
    finally f
      (bind (set_scopes prev) (λx.
          if nr ∧ mut ≠ View ∧ mut ≠ Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ())) s = (res, s') ⇒
    MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rw[finally_def, bind_def, ignore_bind_def,
     set_scopes_def, return_def, raise_def, AllCaseEqs()]
  \\ gvs[]
  \\ Cases_on `cx.nonreentrant_slot` \\ gvs[return_def]
  \\ imp_res_tac release_nonreentrant_lock_scopes \\ gvs[]
QED

Theorem finally_set_scopes_scopes[local]:
  ∀f prev s res s'.
    finally f (set_scopes prev) s = (res,s') ⇒
    MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rw[finally_def, bind_def, ignore_bind_def,
     set_scopes_def, return_def, raise_def, AllCaseEqs()]
  \\ gvs[]
QED

Theorem lock_acquire_cond_scopes_dom[local]:
  ∀nr slot_opt addr is_view st res st'.
    (if nr then
       case slot_opt of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock addr slot is_view
     else return ()) st = (res,st') ⇒
    MAP FDOM st'.scopes = MAP FDOM st.scopes
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[raise_def]
  \\ imp_res_tac acquire_nonreentrant_lock_scopes \\ gvs[]
QED

Resume eval_mutual_preserves_scopes_dom[IntCall]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `!s t s1 ts t1 s2 tup t2 s3 t3. _ ==>
       !st res st'. eval_expr_results cx es st = (res,st') ==> _`
    (mp_tac o SRULE [type_check_def, assert_def, lift_option_type_def,
                     option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  disch_then assume_tac >>
  qpat_x_assum
    `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
  rpt gen_tac >> rewrite_tac[Once evaluate_def] >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (drule type_check_scopes >> rw[] >> gvs[]) >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `_ r' = (res,st')` mp_tac >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  unabbrev_all_tac >>
  rule_assum_tac (SRULE [type_check_def, assert_def, lift_option_type_def,
                        option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  gvs[] >>
  BasicProvers.TOP_CASE_TAC >>
  first_x_assum drule >> strip_tac >>
  reverse (Cases_on `q`)
  >- (rw[] >> gvs[]) >>
  simp[bind_def, ignore_bind_def, get_scopes_def, return_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> drule finally_set_scopes_scopes >> simp[] >>
      strip_tac >> gvs[]) >>
  strip_tac >>
  imp_res_tac finally_set_scopes_scopes >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp[pop_function_def, push_function_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac lift_option_type_scopes >>
  imp_res_tac read_results_state >>
  imp_res_tac lock_acquire_cond_scopes_dom >>
  imp_res_tac finally_intcall_handler_scopes >>
  gvs[]
QED

Finalise eval_mutual_preserves_scopes_dom

(* ========================================================================
   Main theorems (exported)
   ======================================================================== *)

Theorem eval_expr_preserves_scopes_dom:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_expr_preserves_var_in_scope:
  ∀cx st st' n e res.
    eval_expr cx e st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_expr_preserves_scopes_dom]
QED

Theorem eval_expr_preserves_scopes_len:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_expr_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_base_place_preserves_scopes_dom:
  ∀cx bt st res st'. eval_base_place cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_base_place_preserves_var_in_scope:
  ∀cx st st' n bt res.
    eval_base_place cx bt st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_base_place_preserves_scopes_dom]
QED

Theorem eval_base_place_preserves_scopes_len:
  ∀bt cx st res st'.
    eval_base_place cx bt st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_base_place_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_exprs_preserves_scopes_dom:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_expr_results_preserves_scopes_dom:
  eval_expr_results cx es st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_exprs_preserves_var_in_scope:
  ∀cx st st' n es res.
    eval_exprs cx es st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_exprs_preserves_scopes_dom]
QED

Theorem eval_exprs_preserves_scopes_len:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_exprs_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_target_place_preserves_scopes_dom:
  !cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_target_place_preserves_var_in_scope:
  !cx bt st res st' n. eval_target_place cx bt st = (res,st') ==>
    (var_in_scope st n <=> var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_target_place_preserves_scopes_dom]
QED

Theorem eval_target_place_preserves_scopes_len:
  !cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_target_place_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED
