Theory extRetWordStmtPtr
Ancestors
  extRetWordStmtPartsPtr extRetWordExprConsumerPtr exprOpenMain
  exprOpenTerminals exprLowering exprSimHypsDefs bodyPtrDefs
  compileEnv loweringPosts vyperInterpreter vyperState finite_map stmtSimReturn
  extRetNormalEvidencePtr extRetSomeComposePtr extRetCountedPtr
  extRetWordInputsPtr typedCopyPtr gasSummaryComposePtr exprSimSource

Theorem external_return_lower_value_open:
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_body_pre cenv cx env e es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  eval_expr cx e es = (INL tv,es1) /\
  lower_value compile_expr cenv aty e sa = (op,sb) /\
  ~block_is_terminated sa ==> ~block_is_terminated sb
Proof
  strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `~block_is_terminated cs'` by
    (irule compile_expr_open_general >> metis_tac[]) >>
  drule_all unwrap_value_open >> simp[]
QED


Theorem external_return_word_stmt_frag_ptr:
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_body_pre cenv cx env e es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  cenv.ce_return_pc = NONE /\ is_word_type ty /\
  is_word_type (expr_type e) /\ ~cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\ well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  expr_sim_ptr d ctx PG func cenv cx ty e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> rw[stmt_frag_ptr_def] >>
  drule_all external_return_word_stmt_parts >> strip_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule gas_outcome_ptr_normal_evidence >> strip_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    external_return_some_outcome_ptr >>
  disch_then irule >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `eval_expr _ _ _ = (raw,es1)` >>
  Cases_on `raw` >> simp[] >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `~block_is_terminated sm` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`)
       external_return_lower_value_open >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  drule_all expr_post_ptr_return_inputs >> strip_tac >>
  drule_all external_return_word_allocation_inputs >> strip_tac >>
  irule compile_external_return_word_gas_path_ptr >> simp[] >> metis_tac[]
QED
