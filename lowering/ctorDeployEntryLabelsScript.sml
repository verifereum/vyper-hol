Theory ctorDeployEntryLabels
Ancestors
  externalEntryShape compileVyper moduleLowering compileEnv
  loweringShapeDefs loweringShapeRules vyperCompiler list
  entryInternalAppend fragExec
Libs
  monadsyntax

(* Discharge the label obligations of constructor code using the same
   comp_bind and comp_ignore_bind rules as the runtime body. *)
fun deploy_labels rws =
  let
    val rules = comp_return_labels :: rws
    val step =
      FIRST [irule fresh_label_bind_labels,
             irule new_block_action_labels,
             irule comp_bind_labels >> conj_tac,
             irule comp_ignore_bind_labels >> conj_tac,
             FIRST_ASSUM MATCH_ACCEPT_TAC,
             disch_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC] >>
      rpt gen_tac >> PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >> simp rules
  in
    rpt gen_tac >> simp rules >> rpt step
  end

val deploy_label_rules =
  [compile_alloc_buffer_labels, emit_op_labels, emit_void_labels, emit_inst_labels,
   compile_decode_args_labels, compile_nonreentrant_lock_labels,
   compile_fixed_region_with_id_labels, CONJUNCT2 compile_stmt_labels,
   List.last (CONJUNCTS stmt_context_helpers_labels), comp_get_labels,
   pairTheory.ELIM_UNCURRY]

Theorem register_constructor_args_labels[local]:
  !args cenv off bytes s.
    cs_extends s (SND (compile_register_constructor_args cenv args off bytes s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_register_constructor_args cenv args off bytes s)))
Proof
  Induct >> simp[compile_register_constructor_args_def, comp_return_labels] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >>
  once_rewrite_tac[compile_register_constructor_args_def] >>
  deploy_labels deploy_label_rules
QED

Theorem compile_deploy_entry_labels:
  !code_size cap args data_size ce ss pay nr key trans s.
    cs_extends s
      (SND (compile_generate_deploy T code_size cap args data_size [] ce ss
             pay nr key trans s)) /\
    EVERY (isPREFIX "@")
      (added_labels s
        (SND (compile_generate_deploy T code_size cap args data_size [] ce ss
               pay nr key trans s)))
Proof
  rpt gen_tac >>
  once_rewrite_tac[compile_generate_deploy_def] >>
  deploy_labels
    (register_constructor_args_labels :: compile_constructor_epilogue_def ::
     compile_internal_fn_bodies_def :: deploy_label_rules)
QED

Theorem deploy_entry_blocks_not_internal:
  compile_generate_deploy T code_size cap args data_size [] ce ss pay nr key trans
    (initial_compile_state "__deploy") = ((),final) ==>
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks final)
Proof
  strip_tac >>
  qspecl_then [`code_size`, `cap`, `args`, `data_size`, `ce`, `ss`, `pay`,
    `nr`, `key`, `trans`, `initial_compile_state "__deploy"`]
    mp_tac compile_deploy_entry_labels >>
  simp[] >> strip_tac >> drule cs_extends_block_stream_labels >> strip_tac >>
  qpat_x_assum `MAP _ _ = added_labels _ _` (assume_tac o SYM) >>
  gvs[initial_compile_state_def, EVERY_MEM, internal_label_ok_def] >>
  qx_gen_tac `candidate` >> rpt strip_tac >> gvs[] >>
  `MEM candidate.bb_label (MAP (\b. b.bb_label) tail)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  res_tac >> Cases_on `candidate.bb_label` >> gvs[]
QED

Theorem compile_deploy_internal_suffix:
  compile_generate_deploy T code_size cap args data_size ips ce ss pay nr key trans st =
  compile_internal_fn_bodies ips
    (SND (compile_generate_deploy T code_size cap args data_size [] ce ss pay nr key trans st))
Proof
  simp[compile_generate_deploy_def, LET_THM, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_simple_deploy_entry_labels[local]:
  !code_size cap args data_size ce ss pay nr key trans s.
    cs_extends s
      (SND (compile_generate_deploy F code_size cap args data_size [] ce ss
             pay nr key trans s)) /\
    EVERY (isPREFIX "@")
      (added_labels s
        (SND (compile_generate_deploy F code_size cap args data_size [] ce ss
               pay nr key trans s)))
Proof
  rpt gen_tac >>
  once_rewrite_tac[compile_generate_deploy_def] >>
  deploy_labels (compile_simple_deploy_def :: deploy_label_rules)
QED

Theorem compile_deploy_first_block:
  compile_generate_deploy has sz cap args data_size ifns ce stmts pay nr key trans
    (initial_compile_state "__deploy") = ((),final) ==>
  ?bb rest. all_blocks final = bb::rest /\ bb.bb_label = "__deploy"
Proof
  strip_tac >>
  `cs_extends (initial_compile_state "__deploy") final` by
    (reverse (Cases_on `has`)
     >- (qpat_assum `compile_generate_deploy F _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         pure_rewrite_tac[compile_generate_deploy_def, COND_CLAUSES] >>
         strip_tac >>
         mp_tac (Q.SPECL [`sz`, `cap`, `args`, `data_size`, `ce`, `stmts`,
           `pay`, `nr`, `key`, `trans`, `initial_compile_state "__deploy"`]
           compile_simple_deploy_entry_labels) >>
         pure_rewrite_tac[compile_generate_deploy_def, COND_CLAUSES] >> simp[]) >>
     qpat_assum `compile_generate_deploy T _ _ _ _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o ONCE_REWRITE_RULE [compile_deploy_internal_suffix]) >> strip_tac >>
     drule (SRULE [cs_appends_def] cs_appends_internal_fn_bodies) >>
     strip_tac >>
     irule cs_extends_trans >> goal_assum (drule_at Any) >>
     simp[compile_deploy_entry_labels]) >>
  drule cs_extends_block_stream_labels >>
  simp[initial_compile_state_def] >> strip_tac >>
  qexistsl [`bb`, `tail`] >> simp[]
QED
