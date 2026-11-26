(* Linked execution of the runtime-code array selector. *)
Theory bodySubscriptArrayFramedCodeMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodyFullPredsMods bodyFullPostsMods
  bodyArrayNoCopySourceMods bodyArrayNoCopyCodeMods bodyArrayNoCopyBindMods
  bodyArrayFramedCodeInputsMods bodyArrayFramedCodeSelectMods
  bodyArrayFramedCodeReadMods bodyArrayFramedCodeWordMods
  bodyFullIfExpReach exprSimCopy compilerInstructionSuffix compileEnv
  exprLowering exprLoweringProps exprSimDefs loweringShapeDefs
  vyperAST venomExecSemantics venomInst context pair list

Theorem framed_code_child_sims[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx sh fn sf ce env ty es.
                _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (irule o SPEC_ALL) >>
  simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
  qexists_tac `env` >> simp[]
QED

Theorem subscript_array_framed_code_full_mods:
  !mods exps cx ann obj idx DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd.
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  subscript_array_framed_code_case_mods cenv cx obj idx bd ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Subscript ann obj idx) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >> conj_asm2_tac >- suspend "value" >>
  `~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
   (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode)` by
    fs[subscript_array_framed_code_case_mods_def] >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac array_nocopy_paired_parts_mods >>
  `expr_body_pre_mods mods cenv cx env obj es` by
    (`vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode` by simp[] >>
     drule_all_then ACCEPT_TAC framed_code_subscript_base_pre) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty obj es` by
    (irule (framed_code_child_sims |> CONV_RULE (REWR_CONV IMP_CONJ_THM) |> cj 2) >>
     qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `!obs raw mid. eval_expr cx obj (es with gas_obs := obs) = (INL raw,mid) ==>
     expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty idx mid` by
    (rpt gen_tac >> strip_tac >> drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
     irule (framed_code_child_sims |> CONV_RULE (REWR_CONV IMP_CONJ_THM) |> cj 1) >>
     qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  irule (PURE_REWRITE_RULE [LET_THM] array_nocopy_children_bind_mods |> BETA_RULE) >>
  suspend "bind"
QED

Resume subscript_array_framed_code_full_mods[bind]:
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bd`,`bvv`,`et`,`iop`,`shadow_func`,`shadow_sa`,`shadow_sb`,
                `shadow_sm`,`shadow_st2`,`sm`,`st2`,`ty`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC framed_code_select_cut_mods
QED

Resume subscript_array_framed_code_full_mods[value]:
  irule framed_code_value_from_vv_mods >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`bd`,`env`,`et`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `local_ptrs_reserved cenv sm` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `copy_old_operand sm p.ptr_operand` by asm_rewrite_tac[copy_old_operand_def] >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x n. cenv.ce_return_buf = _ ==> _` (drule_then assume_tac) >>
     drule_all_then ACCEPT_TAC not_fresh_at_mono) >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x n. cenv.ce_return_pc = _ ==> _` (drule_then assume_tac) >>
     drule_all_then ACCEPT_TAC not_fresh_at_mono) >>
  drule_all framed_code_word_read_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`z`,`Gf`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`z`,`Gf`,`tf`] >> asm_rewrite_tac[]
QED

Finalise subscript_array_framed_code_full_mods
