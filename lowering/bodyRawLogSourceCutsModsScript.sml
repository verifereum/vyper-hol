(* Linked RawLog source cuts, before any compiler or target execution. *)
Theory bodyRawLogSourceCutsMods
Ancestors
  bodyFullPredsMods bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  exprBodyPreProps exprSimCallRawLog exprSimSource exprSimHypsDefs
  supportedExprTraverse allocLimits vyperTypeArgFits vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperTypeSystem vyperInterpreter
  vyperContext vyperValue vyperState vyperAST list rich_list
Libs monadsyntax

Theorem raw_log_literal_shape[local]:
  (case e of Builtin _ (MakeArray _ _) topics => LENGTH topics <= 4 | _ => F) ==>
  ?a elem bd topics. e = Builtin a (MakeArray elem bd) topics
Proof
  Cases_on `e` >> simp[] >> rename1 `b = MakeArray _ _` >>
  Cases_on `b` >> simp[]
QED

Theorem raw_log_typing_cut[local]:
  well_typed_expr env (Call ann RawLog args dflt) ==>
  ?n topics data.
    ann = NoneT /\ dflt = NONE /\
    args = [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
               (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
            data] /\
    LENGTH topics <= n /\ n <= 4 /\
    EVERY (\e. well_typed_expr env e /\ expr_type e = BaseT (BytesT (Fixed 32))) topics /\
    (expr_type data = BaseT (BytesT (Fixed 32)) \/
     ?m. expr_type data = BaseT (BytesT (Dynamic m)))
Proof
  simp[Once well_typed_expr_def] >> strip_tac >> gvs[LENGTH_EQ_NUM_compute] >>
  drule_then strip_assume_tac raw_log_literal_shape >>
  gvs[expr_type_def] >>
  Cases_on `elem` >> gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
  fs[compatible_bound_def] >> simp[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  (conj_tac >- drule_all_then ACCEPT_TAC well_typed_exprs_member) >>
  irule arg_type_fits_prim_word >> simp[is_prim_word_type_def] >>
  fs[EVERY_MAP, EVERY_MEM]
QED

Theorem raw_log_arg_pre_mods[local]:
  expr_body_pre_mods mods ce cx env (Call ann RawLog args NONE) es /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env mid ==>
  expr_body_pre_mods mods ce cx env e mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
       supported_exprs_exists_every, expr_has_evm_run_thm, EXISTS_MEM] >>
  strip_tac >>
  drule_all_then assume_tac well_typed_exprs_member >>
  drule_all_then assume_tac byte_widths_exprs_mem >>
  drule_all_then assume_tac alloc_limits_exprs_mem >>
  drule_all_then assume_tac call_evaluation_safe_exprs_mem >>
  drule_all_then assume_tac int_calls_exprs_every_mem >>
  simp[] >> metis_tac[]
QED

Theorem raw_log_topic_pre_mods[local]:
  expr_body_pre_mods mods ce cx env (Builtin a (MakeArray elem bd) topics) es /\
  MEM e topics /\ expr_sim_inv_mods mods ce cx env mid ==>
  expr_body_pre_mods mods ce cx env e mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
       supported_exprs_exists_every, expr_has_evm_run_thm, EXISTS_MEM] >>
  strip_tac >>
  drule_all_then assume_tac well_typed_exprs_member >>
  drule_all_then assume_tac byte_widths_exprs_mem >>
  drule_all_then assume_tac alloc_limits_exprs_mem >>
  drule_all_then assume_tac call_evaluation_safe_exprs_mem >>
  drule_all_then assume_tac int_calls_exprs_every_mem >>
  simp[] >> metis_tac[]
QED

(* Walk only the prefix that actually returned, preserving the residual IH. *)
Theorem raw_log_topics_prefix[local]:
  !pre rest st vs mid.
    expr_sim_inv_mods mods ce cx env st /\
    body_const_cells_agree_mods mods cx env st /\
    body_exprs_full_ok_mods mods exps cx (pre ++ rest) /\
    (!e s. MEM e (pre ++ rest) /\ expr_sim_inv_mods mods ce cx env s ==>
           expr_body_pre_mods mods ce cx env e s) /\
    eval_exprs cx pre st = (INL vs,mid) ==>
    expr_sim_inv_mods mods ce cx env mid /\
    body_const_cells_agree_mods mods cx env mid /\
    body_exprs_full_ok_mods mods exps cx rest
Proof
  Induct >> rpt gen_tac
  >- (simp[Once evaluate_def, return_def] >> strip_tac >> gvs[]) >>
  simp[Once evaluate_def, bind_assoc] >>
  simp[bind_apply, return_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `eval_expr cx e st = (INL raw,at_raw)` >>
  rename1 `read_result cx raw at_raw = (INL v,cut)` >>
  `expr_body_pre_mods mods ce cx env e st` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) st = (INL v,cut)` by simp[bind_def] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `body_exprs_full_ok_mods mods exps cx (pre ++ rest)` by
    (qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
     simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
     first_x_assum irule >>
     qexistsl_tac [`st`,`raw`,`at_raw`,`at_raw`,`v`,`cut`] >> simp[]) >>
  rename1 `eval_exprs cx pre cut = (INL tail_values,mid)` >>
  qpat_x_assum `!rest st vs mid. _ ==> _`
    (qspecl_then [`rest`,`cut`,`tail_values`,`mid`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> first_assum irule >> simp[])) >> simp[]
QED

Theorem raw_log_children_mods[local]:
  body_exprs_full_ok_mods mods exps cx
    [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
     data] /\ LENGTH topics <= n ==>
  body_exprs_full_ok_mods mods exps cx topics /\
  (!s vs mid. eval_exprs cx topics s = (INL vs,mid) ==>
    body_expr_full_ok_mods mods exps cx data)
Proof
  simp[body_exprs_full_ok_mods_def] >> strip_tac >>
  conj_tac
  >- (qpat_assum `body_expr_full_ok_mods _ _ _ (Builtin _ _ _)`
        (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
      simp[builtin_args_length_ok_def, compatible_bound_def]) >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  qexistsl_tac [`s`,`Value (ArrayV (DynArrayV vs))`,`mid`,
                `mid`,`ArrayV (DynArrayV vs)`,`mid`] >>
  simp[Once evaluate_def, builtin_args_length_ok_def, compatible_bound_def,
       type_check_def, assert_def, ignore_bind_def, bind_def, return_def,
       get_accounts_def, lift_sum_def, evaluate_builtin_def,
       evaluate_type_def, make_array_value_def, is_self_codesize_def,
       read_result_def]
QED

Theorem raw_log_source_cuts_mods:
  expr_body_pre_mods mods ce cx env (Call ann RawLog args dflt) es /\
  body_const_cells_agree_mods mods cx env es /\
  body_exprs_full_ok_mods mods exps cx args ==>
  ?n topics data.
    ann = NoneT /\ dflt = NONE /\
    args = [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
               (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
            data] /\
    LENGTH topics <= n /\ n <= 4 /\
    EVERY (\e. well_typed_expr env e /\ expr_type e = BaseT (BytesT (Fixed 32))) topics /\
    (expr_type data = BaseT (BytesT (Fixed 32)) \/
     ?m. expr_type data = BaseT (BytesT (Dynamic m))) /\
    body_exprs_full_ok_mods mods exps cx topics /\
    bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx) =
      bind (eval_exprs cx topics)
        (\vs. bind (bind (eval_expr cx data) (read_result cx))
          (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
                  type_check (LENGTH vs <= 4) "raw_log too many topics";
                  check_not_static cx;
                  push_log (encode_raw_event_values cx.txn.target vs bs);
                  return NoneV od)) /\
    (!pre rest obs vs mid.
       topics = pre ++ rest /\
       eval_exprs cx pre (es with gas_obs := obs) = (INL vs,mid) ==>
       expr_sim_inv_mods mods ce cx env mid /\
       body_const_cells_agree_mods mods cx env mid /\
       body_exprs_full_ok_mods mods exps cx rest /\
       (rest <> [] ==> expr_body_pre_mods mods ce cx env (HD rest) mid) /\
       (rest = [] ==> expr_body_pre_mods mods ce cx env data mid /\
                      body_expr_full_ok_mods mods exps cx data))
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then (strip_assume_tac o MATCH_MP raw_log_typing_cut) expr_body_pre_mods_well_typed >>
  gvs[] >>
  drule_all_then strip_assume_tac raw_log_children_mods >>
  simp[raw_log_eval, compatible_bound_def, bind_assoc, SF ETA_ss] >>
  suspend "reached"
QED

Resume raw_log_source_cuts_mods[reached]:
  markerLib.RESUME_TAC >> (
  `!e st. MEM e topics /\ expr_sim_inv_mods mods ce cx env st ==>
          expr_body_pre_mods mods ce cx env e st` by
    (rpt strip_tac >>
     `expr_body_pre_mods mods ce cx env
        (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
          (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics) es` by
       (drule raw_log_arg_pre_mods >> simp[]) >>
     drule_all_then ACCEPT_TAC raw_log_topic_pre_mods) >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv_mods mods ce cx env mid /\
   body_const_cells_agree_mods mods cx env mid /\
   body_exprs_full_ok_mods mods exps cx rest` by
    (irule raw_log_topics_prefix >>
     qpat_assum `eval_exprs _ _ _ = _` (irule_at Any) >>
     qpat_assum `topics = pre ++ rest` (once_rewrite_tac o single o GSYM) >>
     simp[]) >>
  simp[] >> conj_tac
  >- (Cases_on `rest` >> gvs[]) >>
  strip_tac >> gvs[] >> conj_tac
  >- (drule raw_log_arg_pre_mods >> simp[]) >>
  qpat_assum `!s xs st. eval_exprs _ _ s = _ ==> body_expr_full_ok_mods _ _ _ _`
    (drule_then ACCEPT_TAC))
QED

Finalise raw_log_source_cuts_mods
