(* Pair the raw blueprint payload at the cuts selected by the normal compiler. *)
Theory createSizeBlueprintRawPayloadCode
Ancestors
  gasShadowCompileBase
  exprLowering compileEnv exprSimFullBundleProps externalEntryShape fragExec
  exprSimAccounts gasShadowCompile gasShadowCompileHelpers
  gasShadowCompileContext gasShadowCompileConvert gasShadowState pair

(* Each compiler operation preserves its result and relates its two endpoints.
   Case analysis exposes the result of the shadow action, not a runtime value. *)
fun blueprint_raw_pair states shadow_action law =
  Cases_on shadow_action >>
  qspecl_then states mp_tac (REWRITE_RULE [gas_shadow_compiles_def] law) >>
  simp[] >> strip_tac >> gvs[];

Theorem create_blueprint_raw_payload_paired_code:
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\
  emit_op ADD [raw_op;Lit 32w] cl = (data,cprep) /\
  compile_create_blueprint_args compile_expr ce T later [e] ca = ((data,len),cprep) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T ce) T (MAP gas_shadow_expr later)
    [gas_shadow_expr e] sca = ((data,len),scprep) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cprep,sca,scprep) ==>
  ?scm ssaved scs scu.
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) vv scm = (ssaved,scs) /\
    unwrap_value ce ssaved scs = (raw_op,scu) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cu,sca,scu) /\
    fn_has_code cm cs fnc /\ fn_has_code cu cprep fnc
Proof
  disch_then (strip_assume_tac o REWRITE_RULE[expr_sim_full_code_def]) >>
  `?scm. compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
         gas_shadow_state cm scm` by
    blueprint_raw_pair [`ca`,`sca`] `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca`
      (Q.SPECL [`ce`,`expr_type e`,`e`,`T`] (cj 1 (Q.INST [`sd` |-> `T`] gas_shadow_compile_expr_env)) |> SRULE []) >>
  `?scs. compile_snapshot_vv ce (exprs_can_mutate ce later) vv scm = (saved,scs) /\
         gas_shadow_state cs scs` by
    blueprint_raw_pair [`cm`,`scm`] `compile_snapshot_vv ce (exprs_can_mutate ce later) vv scm`
      (Q.INST [`cenv` |-> `ce`, `copy_flag` |-> `exprs_can_mutate ce later`, `vv` |-> `vv`]
        gas_shadow_compiles_snapshot_vv) >>
  `?scu. unwrap_value ce saved scs = (raw_op,scu) /\ gas_shadow_state cu scu` by
    blueprint_raw_pair [`cs`,`scs`] `unwrap_value ce saved scs`
      (Q.INST [`cenv` |-> `ce`, `vv` |-> `saved`] gas_shadow_compiles_unwrap_value) >>
  `?scl. emit_op MLOAD [raw_op] scu = (len,scl) /\ gas_shadow_state cl scl` by
    blueprint_raw_pair [`cu`,`scu`] `emit_op MLOAD [raw_op] scu`
      (Q.INST [`opc` |-> `MLOAD`, `ops` |-> `[raw_op]`] gas_shadow_compiles_emit_op_same) >>
  `cs_extends ca cm /\ cs_extends sca scm /\ cs_extends cm cs /\ cs_extends scm scs /\
   cs_extends cs cu /\ cs_extends scs scu` by
    (rpt conj_tac >>
     metis_tac[SND,compile_expr_labels,compile_snapshot_vv_labels,unwrap_value_labels]) >>
  `cs_extends cu cl /\ cs_extends cl cprep /\ cs_extends scu scl` by
    metis_tac[emit_op_extends_next_var] >>
  `emit_op ADD [raw_op;Lit 32w] scl = (data,scprep)` by
    (qpat_x_assum `compile_create_blueprint_args _ _ T (MAP _ _) _ _ = _` mp_tac >>
     Cases_on `emit_op ADD [raw_op;Lit 32w] scl` >>
     simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def,
          gas_shadow_expr_can_mutate]) >>
  `cs_extends scl scprep` by metis_tac[emit_op_extends_next_var] >>
  `cs_extends cu cprep /\ cs_extends scu scprep` by metis_tac[cs_extends_trans] >>
  `cs_extends cm cu /\ cs_extends scm scu /\ cs_extends ca cu /\ cs_extends sca scu` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code ca cu fnc /\ fn_has_code cu cprep fnc /\
   fn_has_code sca scu shfnc /\ fn_has_code scu scprep shfnc` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code ca cm fnc /\ fn_has_code cm cu fnc /\ fn_has_code sca scm shfnc` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code cm cs fnc` by metis_tac[fn_has_code_split] >>
  qexistsl_tac [`scm`,`saved`,`scs`,`scu`] >>
  simp[expr_sim_full_code_def,gas_shadow_expr_can_mutate]
QED
