(* The linked array route composes the reached VV landing with the search. *)
Theory bodyMembershipArrayValueMods
Ancestors
  bodyMembershipArrayLayoutMods bodyMembershipOperandEntryMods
  bodyMembershipArrayPrefixMods bodyMembershipArraySuffixMods
  bodyFullPredsMods bodyFullPostsMods exprSimFullBundleProps
  exprLowering gasContext vyperInterpreter vyperState vyperStorageFootprint
Libs monadsyntax

Theorem membership_array_value_mods:
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  body_exprs_full_ok_mods mods exps cx [e1;e2] /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def] >>
  qx_genl_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`op`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (strip_assume_tac o Q.SPEC `st0`) membership_operand_entry_mods >>
  drule_all_then strip_assume_tac membership_array_layout_mods >>
  irule (BETA_RULE membership_array_prefix_mods) >>
  qpat_assum `lower_value compile_expr cenv _ e1 sa = _` (irule_at Any) >>
  qpat_assum `compile_expr cenv _ e2 s1 = _` (irule_at Any) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr e2) _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) _ = _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree_mods _ _ _ es` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
  qexists_tac `shadow_func` >> asm_rewrite_tac[expr_sim_full_code_def] >>
  qx_genl_tac [`left`,`v`,`mid`,`G1`,`tn1`,`t`,`right`,`tv`,`fin`,`G2`,`tn2`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!obs needle mid. _ ==> body_expr_full_ok_mods _ _ _ e2 /\ _`
    (qspecl_then [`gas_explicit left s0.vs_gas_readings`,`v`,`mid`] mp_tac) >>
  (impl_tac >- (conj_tac
    >- (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
          fs[storage_trace_domain_def] >>
        qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
          (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
    first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `expr_type e2 = ArrayT _ _` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule (BETA_RULE membership_array_suffix_mods) >>
  qpat_assum `compile_var_array_membership cenv _ _ _ _ sm = _` (irule_at Any) >>
  qpat_assum `expr_body_pre_mods _ cenv cx env e1 es` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv _ e1 sa = _` (irule_at Any) >>
  qpat_assum `expr_body_pre_mods _ cenv cx env e2 mid` (irule_at Any) >>
  qexistsl_tac [`tn1`,`t`,`gas_explicit right t.vs_gas_readings`,
               `gas_explicit left s0.vs_gas_readings`,`G1`] >>
  asm_rewrite_tac[] >>
  rpt conj_tac >> gen_tac >> disch_tac
  >- (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
  >- (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
        (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[]
QED
