(* Join the linked Range operand, setup, and round paths at their actual cuts. *)
Theory bodyForRangeFragMods
Ancestors
  bodyForRangeRoundMods bodyForRangeNilMods bodyForRoundsBindMods
  bodyForRangeLiteralStartMods bodyForRangeLiteralCodeMods
  bodyForRangeEndpointRunMods bodyForRangeCheckedCodeMods
  bodyForRangeCheckedStartMods bodyForRangeAllocMods bodyForRangeRouteMods
  bodyForEntryInputsMods gasOutcomeFullZeroPrefixMods bodyFullForFacts
  bodyFullPostsMods bodyInvMetadataProps bodySimDeclCases stmtSimProps
  bodyExprPreFacts bodySimModsProps supportedStmtTraverse supportedStmts
  vyperTypeInvariants vyperTypeSystem vyperValue vyperInterpreter finite_map
  compileEnv valueEncoding loweringSlice exprBodyPreProps vyperState stmtSimForParts
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem range_value_layout[local]:
  is_int_type typ /\ evaluate_type tenv typ = SOME tyv ==>
  type_memory_bytes cenv typ = 32 /\ type_memory_size tyv = 32 /\ word_memory_type tyv
Proof
  Cases_on `typ` >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def] >>
  rpt strip_tac >> gvs[type_memory_size_def, word_memory_type_def]
QED

Theorem range_checked_bound[local]:
  type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env' /\
  ~(?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)) ==>
  n < dimword (:256)
Proof
  strip_tac >>
  drule (SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX))) body_range_typing)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  Cases_on `typ` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_formed_type_def, evaluate_type_def, AllCaseEqs(), well_typed_literal_def,
      within_int_bound_def, LET_THM] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  goal_assum (drule_at (Pat `n < _`)) >> simp[bitTheory.TWOEXP_MONO2] >> decide_tac
QED

Theorem range_scope_unused[local]:
  expr_sim_inv_mods mods cenv cx env es /\ id NOTIN FDOM env.var_types ==>
  lookup_scopes id es.scopes = NONE
Proof
  strip_tac >> drule expr_sim_inv_mods_env >>
  simp[env_consistent_def, env_scopes_consistent_def] >>
  strip_tac >> Cases_on `lookup_scopes id es.scopes` >> simp[] >>
  qpat_assum `!i entry. lookup_scopes i es.scopes = SOME entry ==> _` drule >>
  simp[FLOOKUP_DEF]
QED

Theorem range_checked_source_ready[local]:
  n1 <= n2 /\ Num (n2 - n1) <= bound ==>
  (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
      check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
      eval_for cx tyv id body
        (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od) =
  eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))
Proof
  simp[get_range_limits_def, lift_sum_def, vyperValueTheory.compatible_bound_def,
       check_def, assert_def, ignore_bind_def, FUN_EQ_THM, bind_def, return_def]
QED

Theorem range_literal_source_ready[local]:
  supported_iterator tops typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound /\
  evaluate_type (get_tenv cx) typ = SOME tyv ==>
  n1 <= n2 /\ Num (n2 - n1) <= bound /\
  (!es. eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) es =
     (INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))),es)) /\
  eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) =
    eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))
Proof
  simp[supported_iterator_def] >> strip_tac >>
  simp[eval_iterator_range_lit] >>
  pure_once_rewrite_tac[evaluate_def] >>
  simp[LET_THM, lift_option_type_def, lift_option_def, bind_def, ignore_bind_def,
       eval_iterator_range_lit, return_def, check_def, assert_def,
       vyperValueTheory.compatible_bound_def, FUN_EQ_THM]
QED
