Theory bodyLogSourceEncodingMods
Ancestors
  bodyFullLog[qualified,ignore_grammar] bodyCopyReadPhysicalTypeMods
  bodyCopyArgReadTypesMods exprBodyPreProps exprSimHypsDefs
  vyperTypeEvalCaseProofs vyperTypeExprSoundness vyperTypeSystem vyperInterpreter
  vyperEventArgCompat vyperEventCompatibility vyperEvent vyperABI
  eventEncodingProps eventLogSplitProps abiLogSourceEncoding typedLogSplitComplete
  bodySimLogArgs placeRelayoutSemantic typedCopyCompatibility vyperTypeArgFits
  compileEnv loweringStateRelDefs exprLowering vyperAST vyperState list

Theorem log_read_types_mods[local]:
  expr_sim_inv_mods mods ce cx env st /\
  EVERY (\e. expr_body_pre_mods mods ce cx env e st) args /\
  eval_exprs cx args st = (INL vs,fin) ==>
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v)
    (MAP (lowered_value_type ce) args) vs
Proof
  strip_tac >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!e. MEM e args ==> well_typed_expr env e /\ alloc_limits_expr ce e /\
      call_evaluation_safe cx (int_calls_expr e)` by
    (rpt strip_tac >> qpat_assum `EVERY _ args` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[expr_body_pre_mods_def]) >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs` by
    (irule copy_arg_read_types_from_members_mods >>
     qexistsl_tac [`cx`,`fin`,`mods`,`st`] >> simp[EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >>
     irule copy_read_lowered_type_mods >> simp[] >>
     qexistsl_tac [`cx`,`t`,`s`,`mods`] >> simp[]) >>
  qpat_x_assum `LIST_REL _ args vs` mp_tac >>
  simp[LIST_REL_MAP1, combinTheory.o_DEF, value_runtime_typed_def]
QED

Theorem log_lowered_compat_mods[local]:
  expr_sim_inv_mods mods ce cx env st /\
  EVERY (\e. expr_body_pre_mods mods ce cx env e st) args /\
  LIST_REL (\dty e. event_arg_compatible dty (expr_type e)) dtys args ==>
  LIST_REL event_arg_compatible dtys (MAP (lowered_value_type ce) args)
Proof
  simp[EVERY_MEM, LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
  `MEM (EL n args) args` by metis_tac[EL_MEM] >>
  `arg_type_fits (lowered_value_type ce (EL n args)) (expr_type (EL n args))` by
    (irule copy_lowered_fits_mods >>
     qexistsl_tac [`cx`,`env`,`st`,`mods`] >>
     simp[] >> metis_tac[expr_body_pre_mods_well_typed]) >>
  fs[event_arg_compatible_alias_def] >> metis_tac[cj 1 arg_type_fits_trans]
QED

Theorem log_select_typed[local]:
  !flags tys vs. LENGTH flags = LENGTH tys /\ LIST_REL R tys vs ==>
    LIST_REL R (select_log_args F flags tys) (select_log_args F flags vs)
Proof
  rpt strip_tac >> irule select_log_args_rel >> simp[] >>
  fs[LIST_REL_EL_EQN, LENGTH_ZIP, EL_ZIP]
QED

Theorem log_typed_declared[local]:
  !dtys atys vs.
    LIST_REL event_arg_compatible dtys atys /\
    EVERY (assignable_type tenv) dtys /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) atys vs ==>
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) dtys vs
Proof
  Induct >> Cases_on `atys` >> Cases_on `vs` >> simp[] >> rpt strip_tac
  >- (drule_then assume_tac assignable_type_well_formed >>
      fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
      drule_all log_compatible_declared_value >> simp[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem log_selected_compat[local]:
  LIST_REL event_arg_compatible dtys atys /\ EVERY (assignable_type tenv) dtys ==>
  event_arg_compatible_list (log_non_indexed_types flags dtys)
    (log_non_indexed_types flags atys) /\
  EVERY (assignable_type tenv) (log_non_indexed_types flags dtys)
Proof
  strip_tac >> simp[event_compatible_list_rel] >>
  `EVERY (\ty:type. T) atys` by simp[EVERY_MEM] >>
  drule_all_then strip_assume_tac (Q.SPEC `flags` (Q.GEN `flags` log_non_indexed_types_preserve)) >>
  simp[]
QED

Theorem log_selected_assignable[local]:
  event_arg_compatible_list dtys atys /\ EVERY (assignable_type tenv) dtys /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) atys vs ==>
  EVERY (assignable_type tenv) atys
Proof
  strip_tac >> irule (cj 2 arg_type_fits_source_assignable) >>
  reverse conj_tac
  >- (qexists_tac `dtys` >> fs[event_arg_compatible_list_alias_def]) >>
  fs[LIST_REL_EL_EQN, EVERY_EL, well_formed_type_def] >> metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem log_source_encoding_mods:
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,dtys,flags) /\
  LENGTH flags = LENGTH dtys /\
  LIST_REL (\dty e. event_arg_compatible dty (expr_type e)) dtys args /\
  EVERY (assignable_type (get_tenv cx)) dtys /\
  EVERY (\(ty,indexed). indexed ==> supported_event_leaf_type ty) (ZIP (dtys,flags)) /\
  expr_sim_inv_mods mods ce cx env st /\
  EVERY (\e. expr_body_pre_mods mods ce cx env e st) args /\
  eval_exprs cx args st = (INL vs,fin) ==>
  let atys = MAP (lowered_value_type ce) args in
    ?topics avs.
      encode_indexed_event_topics flags atys vs = SOME topics /\
      vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags atys)
        (log_non_indexed_values flags vs) = SOME avs /\
      encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs =
        SOME <|logger := cx.txn.target; topics := n2w h::topics;
          data := enc (Tuple (vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags atys)))
            (ListV avs)|> /\
      EVERY (assignable_type (get_tenv cx)) (log_non_indexed_types flags atys) /\
      LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v) atys vs
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  drule_all_then assume_tac log_read_types_mods >>
  drule_all_then assume_tac log_lowered_compat_mods >>
  qmatch_goalsub_abbrev_tac `encode_indexed_event_topics flags atys vs` >>
  qabbrev_tac `tenv = get_tenv cx` >>
  `LENGTH flags = LENGTH atys` by metis_tac[LIST_REL_LENGTH] >>
  `LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) dtys vs` by
    (irule log_typed_declared >> simp[] >> qexists_tac `atys` >> simp[]) >>
  qabbrev_tac `src = log_non_indexed_types flags atys` >>
  qabbrev_tac `decl = log_non_indexed_types flags dtys` >>
  qabbrev_tac `data_vs = log_non_indexed_values flags vs` >>
  `LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) src data_vs` by
    (simp[Abbr `src`, Abbr `data_vs`, log_non_indexed_types_select, log_non_indexed_values_select] >>
     irule log_select_typed >> simp[]) >>
  `LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) decl data_vs` by
    (simp[Abbr `decl`, Abbr `data_vs`, log_non_indexed_types_select, log_non_indexed_values_select] >>
     irule log_select_typed >> simp[]) >>
  `event_arg_compatible_list decl src /\ EVERY (assignable_type tenv) decl` by
    (simp[Abbr `decl`, Abbr `src`] >> irule log_selected_compat >> simp[]) >>
  `EVERY (assignable_type tenv) src` by
    (irule log_selected_assignable >> conj_tac
     >- (qexists_tac `decl` >> simp[]) >>
     qexists_tac `data_vs` >> simp[]) >>
  `EVERY (well_formed_type tenv) src /\ EVERY (well_formed_type tenv) decl` by
    metis_tac[MONO_EVERY, assignable_type_well_formed] >>
  `vyper_to_abi_types tenv decl = vyper_to_abi_types tenv src` by
    metis_tac[cj 2 event_arg_compatible_abi_type] >>
  `vyper_to_abi_list tenv decl data_vs = vyper_to_abi_list tenv src data_vs` by
    metis_tac[cj 2 event_arg_compatible_abi_value] >>
  `?topics avs.
      encode_indexed_event_topics flags atys vs = SOME topics /\
      vyper_to_abi_list tenv decl data_vs = SOME avs /\
      encode_source_event tenv cx.sources cx.txn.target id vs =
        SOME <|logger := cx.txn.target; topics := n2w h::topics;
          data := enc (Tuple (vyper_to_abi_types tenv decl)) (ListV avs)|>` by
    (simp_tac bool_ss [Abbr `decl`, Abbr `data_vs`] >>
     irule bodyFullLogTheory.log_full_compatible_source_event_encoded >>
     simp[]) >>
  qexistsl_tac [`topics`,`avs`] >> simp[] >>
  qpat_assum `vyper_to_abi_list tenv decl data_vs = vyper_to_abi_list tenv src data_vs`
    (fn th => simp[GSYM th])
QED
