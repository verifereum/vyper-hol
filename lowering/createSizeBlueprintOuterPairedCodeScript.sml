(* Static pairing of the caller's blueprint actions at the chosen normal cuts. *)
Theory createSizeBlueprintOuterPairedCode
Ancestors
  createSizeItinerary createSizeDispatch exprSimFullBundleProps exprSimSend
  externalEntryShape exprLowering builtinCreate compileEnv fragExec
  gasShadowCompileStmtHelpers gasShadowCompile gasShadowCompileHelpers gasShadowCompileBase gasShadowState
  gasShadow gasShadowCompileBuiltinCreate list rich_list words pair vyperPinFold vyperOriginFold exprSimAccounts
Libs createSizeCodeSpineLib

(* Apply the shadow action law to a pair of inputs with known normal result. *)
fun blueprint_pair_exists run a h law =
  Cases_on run >>
  qspecl_then [a,h] mp_tac (REWRITE_RULE[gas_shadow_compiles_def] law) >>
  simp[];

Theorem blueprint_outer_args_run[local]:
  create_blueprint_args_itinerary ce raw later xs a prep args_buf len b ==>
  compile_create_blueprint_args compile_expr ce raw later xs a = ((args_buf,len),b)
Proof
  simp[create_blueprint_args_itinerary_def] >> strip_tac >> gvs[] >>
  TRY (Cases_on `xs` >> TRY (rename1 `!e. h::tl <> [e]` >> Cases_on `tl`) >> gvs[]) >>
  fs[compile_create_blueprint_args_def,comp_bind_def,comp_ignore_bind_def,comp_return_def]
QED

Theorem blueprint_outer_append_run[local]:
  create_blueprint_append_itinerary target off code args_buf alen f app buf len /\
  LAST app = sc /\
  create_size_dispatch_tail rof sc sd created buf len value salt result sb ==>
  compile_create_blueprint_append target value salt off code args_buf alen rof f = (result,sb)
Proof
  Cases_on `alen = Lit 0w` >> Cases_on `salt` >>
  simp[create_blueprint_append_itinerary_def,create_size_dispatch_tail_def] >>
  strip_tac >> gvs[compile_create_blueprint_append_def,comp_bind_def,comp_ignore_bind_def,comp_return_def]
QED

Theorem blueprint_outer_offset_pair[local]:
  create_blueprint_offset_run ce off d offset e /\ gas_shadow_state d hd ==>
  ?he. gas_shadow_state e he /\
    create_blueprint_offset_run (gas_shadow_env T ce) (gas_shadow_expr off) hd offset he /\
    is_int_literal (origin_fold_value (gas_shadow_expr off)) =
      is_int_literal (origin_fold_value off) /\
    ((?ann i. origin_fold_value off = Literal ann (IntL i) /\
       offset = Lit (i2w i) /\ e = d /\ he = hd) \/
     (lower_value compile_expr ce (expr_type off) off d = (offset,e) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) hd = (offset,he)))
Proof
  `gas_shadow_compiles (lower_value compile_expr ce (expr_type off) off)
    (lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off))` by
    simp[gas_shadow_stmt_lower_value_env] >>
  Cases_on `origin_fold_value off` >>
  TRY (rename1 `origin_fold_value off = Literal ann lit` >> Cases_on `lit`) >>
  simp[create_blueprint_offset_run_def,gas_shadow_origin_fold_value,
       gas_shadow_expr_def,is_int_literal_def,comp_return_def] >>
  strip_tac >> gvs[] >>
  qpat_assum `gas_shadow_compiles _ _`
    (blueprint_pair_exists `lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) hd` `d` `hd`)
QED

Theorem blueprint_outer_shadow_args[local]:
  !ce raw later xs. gas_shadow_compiles
    (compile_create_blueprint_args compile_expr ce raw later xs)
    (compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw
      (MAP gas_shadow_expr later) (MAP gas_shadow_expr xs))
Proof
  rpt gen_tac >>
  irule (SRULE []
    (Q.INST [`sd` |-> `T`,`sh` |-> `T`] gas_shadow_compiles_create_blueprint_args)) >>
  simp[cj 1 gas_shadow_compile_expr_env]
QED

Theorem blueprint_outer_shadow_append_run[local]:
  args = target::amount::((if hs then [se] else []) ++ off::ctors) /\
  later = amount::((if hs then [se] else []) ++ [off]) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr
    (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df)) hsa = (vv,hsb) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type target) (gas_shadow_expr target) hsa = (target_op,hca) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw
    (MAP gas_shadow_expr later)
    (MAP gas_shadow_expr ctors) hca = ((args_buf,args_len),hb) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) hb = (value_op,hc) /\
  compile_create_salt compile_expr (gas_shadow_env T ce) (OPTION_MAP gas_shadow_expr (if hs then SOME se else NONE))
    hc = (salt_op,hd) /\
  create_blueprint_offset_run (gas_shadow_env T ce) (gas_shadow_expr off) hd offset_op he /\
  is_int_literal (origin_fold_value (gas_shadow_expr off)) = is_int_literal (origin_fold_value off) /\
  compile_create_blueprint_check (is_int_literal (origin_fold_value off)) target_op offset_op he = (code,hf) /\
  compile_create_blueprint_append target_op value_op salt_op offset_op code args_buf args_len rof hf =
    (result,hend) ==>
  hend = hsb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  qpat_x_assum `later = _` SUBST_ALL_TAC >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  Cases_on `hs` >>
  fs[gas_shadow_expr_def,compile_expr_call,compile_call_def,compile_create_call_def,
       comp_bind_def,create_blueprint_offset_run_def,as_stack_val_def]
QED

Theorem blueprint_outer_action_extends[local]:
  (!ce ty x a. cs_extends a (SND (lower_value compile_expr ce ty x a))) /\
  (!ce raw later xs a. cs_extends a (SND (compile_create_blueprint_args compile_expr ce raw later xs a))) /\
  (!ce opt a. cs_extends a (SND (compile_create_salt compile_expr ce opt a))) /\
  (!ce off a x b. create_blueprint_offset_run ce off a x b ==> cs_extends a b) /\
  (!lit target off a. cs_extends a (SND (compile_create_blueprint_check lit target off a))) /\
  (!target value salt off code args_buf args_len rof a.
    cs_extends a (SND (compile_create_blueprint_append target value salt off code args_buf args_len rof a)))
Proof
  simp[lower_value_labels,compile_expr_labels,compile_create_blueprint_args_labels,
       compile_create_salt_labels,compile_create_blueprint_check_labels,compile_create_blueprint_append_labels] >>
  rpt gen_tac >> Cases_on `origin_fold_value off` >>
  TRY (rename1 `origin_fold_value off = Literal ann lit` >> Cases_on `lit`) >>
  simp[create_blueprint_offset_run_def,comp_return_def,cs_extends_refl] >>
  metis_tac[SND,lower_value_labels,compile_expr_labels]
QED

Theorem blueprint_outer_append_extends[local]:
  create_blueprint_append_itinerary target off code args_buf args_len f app buf len /\
  LAST app = sc /\
  create_size_dispatch_tail rof sc sd created buf len value salt result sb ==>
  cs_extends f sc /\ cs_extends sc sb
Proof
  Cases_on `args_len = Lit 0w` >> Cases_on `salt` >>
  simp[create_blueprint_append_itinerary_def,create_size_dispatch_tail_def] >>
  strip_tac >> gvs[] >>
  imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
  `cs_extends m n /\ cs_extends n p /\ cs_extends sd sb` by
    (rpt conj_tac >>
     metis_tac[SND,compile_alloc_dynamic_labels,emit_void_labels,
               compile_check_create_result_labels]) >>
  metis_tac[SND,compile_copy_memory_dynamic_labels,cs_extends_trans]
QED

Theorem blueprint_outer_salt_run[local]:
  create_itinerary_salt ce opt c salt d ==>
  compile_create_salt compile_expr ce opt c = (salt,d)
Proof
  Cases_on `opt` >>
  simp[create_itinerary_salt_def,compile_create_salt_def,comp_bind_def,comp_return_def] >>
  strip_tac >> simp[]
QED

Theorem create_blueprint_outer_paired_code:
  args = target::amount::((if hs then [se] else []) ++ off::ctors) /\
  later = amount::((if hs then [se] else []) ++ [off]) /\
  compile_expr ce ty (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr
    (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df)) hsa = (vv,hsb) /\
  expr_sim_full_code (ctx,sctx,fnc,sfnc) (sa,sb,hsa,hsb) /\
  lower_value compile_expr ce (expr_type target) target sa = (target_op,ca) /\
  create_blueprint_args_itinerary ce raw later ctors ca prep args_buf args_len b /\
  lower_value compile_expr ce (expr_type amount) amount b = (value_op,c) /\
  create_itinerary_salt ce (if hs then SOME se else NONE) c salt_op d /\
  create_blueprint_offset_run ce off d offset_op e /\
  compile_create_blueprint_check (is_int_literal (origin_fold_value off)) target_op offset_op e = (code,f) /\
  create_blueprint_append_itinerary target_op offset_op code args_buf args_len f app bufop len /\
  LAST app = sc /\
  create_size_dispatch_tail rof sc sd created bufop len value_op salt_op result sb ==>
  ?hca hb hc hd he hf.
    lower_value compile_expr (gas_shadow_env T ce) (expr_type target) (gas_shadow_expr target) hsa = (target_op,hca) /\
    expr_sim_full_code (ctx,sctx,fnc,sfnc) (sa,ca,hsa,hca) /\
    compile_create_blueprint_args compile_expr ce raw later ctors ca = ((args_buf,args_len),b) /\
    compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw
      (MAP gas_shadow_expr later) (MAP gas_shadow_expr ctors) hca = ((args_buf,args_len),hb) /\
    expr_sim_full_code (ctx,sctx,fnc,sfnc) (ca,b,hca,hb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) hb = (value_op,hc) /\
    expr_sim_full_code (ctx,sctx,fnc,sfnc) (b,c,hb,hc) /\
    (if hs then ?sop. salt_op = SOME sop /\
      lower_value compile_expr ce (expr_type se) se c = (sop,d) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type se) (gas_shadow_expr se) hc = (sop,hd) /\
      expr_sim_full_code (ctx,sctx,fnc,sfnc) (c,d,hc,hd)
     else salt_op = NONE /\ d = c /\ hd = hc) /\
    ((?ann' i. origin_fold_value off = Literal ann' (IntL i) /\
       offset_op = Lit (i2w i) /\ e = d /\ he = hd) \/
     (lower_value compile_expr ce (expr_type off) off d = (offset_op,e) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) hd = (offset_op,he) /\
      expr_sim_full_code (ctx,sctx,fnc,sfnc) (d,e,hd,he))) /\
    compile_create_blueprint_check (is_int_literal (origin_fold_value off)) target_op offset_op he = (code,hf) /\
    expr_sim_full_code (ctx,sctx,fnc,sfnc) (e,f,he,hf) /\
    compile_create_blueprint_append target_op value_op salt_op offset_op code args_buf args_len rof hf =
      (result,hsb) /\
    fn_has_code f sc fnc /\ cs_extends sc sb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_sim_full_code _ _` (strip_assume_tac o REWRITE_RULE[expr_sim_full_code_def]) >>
  drule blueprint_outer_args_run >> strip_tac >>
  drule_all blueprint_outer_append_run >> strip_tac >>
  drule_all blueprint_outer_append_extends >> strip_tac >>
  drule blueprint_outer_salt_run >> strip_tac >>
  suspend "pair"
QED

Resume create_blueprint_outer_paired_code[pair]:
  `?hca. lower_value compile_expr (gas_shadow_env T ce) (expr_type target) (gas_shadow_expr target) hsa = (target_op,hca) /\
         gas_shadow_state ca hca` by
    (blueprint_pair_exists `lower_value compile_expr (gas_shadow_env T ce) (expr_type target) (gas_shadow_expr target) hsa`
      `sa` `hsa` (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type target`, `e` |-> `target`, `sd` |-> `T`]
        gas_shadow_stmt_lower_value_env)) >>
  `?hb. compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw
          (MAP gas_shadow_expr later) (MAP gas_shadow_expr ctors) hca = ((args_buf,args_len),hb) /\
        gas_shadow_state b hb` by
    (blueprint_pair_exists `compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw
          (MAP gas_shadow_expr later) (MAP gas_shadow_expr ctors) hca` `ca` `hca`
      (Q.SPECL [`ce`,`raw`,`later`,`ctors`] blueprint_outer_shadow_args)) >>
  `?hc. lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) hb = (value_op,hc) /\
        gas_shadow_state c hc` by
    (blueprint_pair_exists `lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) hb`
      `b` `hb` (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type amount`, `e` |-> `amount`, `sd` |-> `T`]
        gas_shadow_stmt_lower_value_env)) >>
  `?hd. compile_create_salt compile_expr (gas_shadow_env T ce) (OPTION_MAP gas_shadow_expr (if hs then SOME se else NONE)) hc =
          (salt_op,hd) /\ gas_shadow_state d hd` by
    (blueprint_pair_exists `compile_create_salt compile_expr (gas_shadow_env T ce)
        (OPTION_MAP gas_shadow_expr (if hs then SOME se else NONE)) hc` `c` `hc`
      (Q.SPECL [`ce`,`if hs then SOME se else NONE`] createSizeCodeSpineLib.shadow_create_salt)) >>
  drule_all blueprint_outer_offset_pair >>
  disch_then (qx_choose_then `he` (map_every assume_tac o CONJUNCTS)) >>
  `?hf. compile_create_blueprint_check (is_int_literal (origin_fold_value off)) target_op offset_op he = (code,hf) /\
        gas_shadow_state f hf` by
    (blueprint_pair_exists `compile_create_blueprint_check (is_int_literal (origin_fold_value off)) target_op offset_op he`
      `e` `he` (Q.INST [`is_lit` |-> `is_int_literal (origin_fold_value off)`,
                        `target_op` |-> `target_op`, `code_offset_op` |-> `offset_op`]
                       gas_shadow_compiles_create_blueprint_check)) >>
  `?hend. compile_create_blueprint_append target_op value_op salt_op offset_op code args_buf args_len rof hf =
          (result,hend) /\ gas_shadow_state sb hend` by
    (blueprint_pair_exists `compile_create_blueprint_append target_op value_op salt_op offset_op code args_buf args_len rof hf`
      `f` `hf` (Q.INST [`salt_opt` |-> `salt_op`, `code_offset_op` |-> `offset_op`,
                        `code_size` |-> `code`, `args_ptr` |-> `args_buf`,
                        `revert_on_failure` |-> `rof`] gas_shadow_compiles_create_blueprint_append)) >>
  `hend = hsb` by (drule_all blueprint_outer_shadow_append_run >> simp[]) >>
  qpat_x_assum `hend = hsb` SUBST_ALL_TAC >>
  suspend "code"
QED

Resume create_blueprint_outer_paired_code[code]:
  `cs_extends sa ca /\ cs_extends ca b /\ cs_extends b c /\ cs_extends c d /\
   cs_extends d e /\ cs_extends e f /\
   cs_extends hsa hca /\ cs_extends hca hb /\ cs_extends hb hc /\ cs_extends hc hd /\
   cs_extends hd he /\ cs_extends he hf /\ cs_extends hf hsb` by
    (rpt conj_tac >> metis_tac[SND,blueprint_outer_action_extends]) >>
  createSizeCodeSpineLib.split_code_spine "fnc" ["sa","ca","b","c","d","e","f","sc","sb"] >>
  createSizeCodeSpineLib.split_code_spine "sfnc" ["hsa","hca","hb","hc","hd","he","hf","hsb"] >>
  qexistsl [`hca`,`hb`,`hc`,`hd`,`he`,`hf`] >>
  asm_simp_tac bool_ss [expr_sim_full_code_def] >>
  Cases_on `hs` >> fs[compile_create_salt_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> gvs[]
QED

Finalise create_blueprint_outer_paired_code
