(* Empty emits only the selected straight-line default buffer. *)
Theory entryCreateTypeEmpty
Ancestors
  bodyFullTypeBuiltinEmpty bodyPtrTypeBuiltinsEmptyWords typeBuiltinPrereqs
  entryCreateAdminSequence entryCreatePendingScope entryCreateSubscriptUncopiedMemory
  createSizeOperandCode createSizeCutCode exprSimAbiGasBridge
  exprSimBufferEmptyExec emitHelperProps exprSimFullBundleProps
  s1PrefixDefs gasStorage gasSummary fragGasOriginPtr
  entryCreateFocusSpec entryCreateCompletedCut bodyFullEmptyLeafData gasOutcomeFull
  abiEncoderProps fragExec exprLoweringProps exprSimHyps vyperAST compileEnv venomInst list rich_list

Theorem zero_words_empty_opcodes[local]:
  !n op a b. compile_zero_words op n a = ((),b) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MSTORE]) (emitted_insts a b)
Proof
  Induct >- simp[builtinSimpleTheory.compile_zero_words_def, comp_return_def, emitted_insts_refl] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_zero_words op n a` >>
  rename1 `compile_zero_words op n a = (u,m)` >> Cases_on `u` >>
  drule_all empty_zero_words_successor_code >> disch_then SUBST1_TAC >>
  first_x_assum drule >> simp[mk_inst_def]
QED

Theorem empty_compiled_admin[local]:
  ~is_word_type typ /\ fn_has_code sa sb func /\
  compile_expr cenv ty (TypeBuiltin typ Empty typ []) sa = (vv,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule_all empty_type_builtin_compile >> strip_tac >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  drule_all empty_buffer_compile_prefix >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_assum `isPREFIX _ _` (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
     simp[NoAsms,emitted_insts_def] >>
     qpat_assum `sb.cs_current_insts = sa.cs_current_insts ++ _` SUBST1_TAC >>
     simp[DROP_LENGTH_APPEND]) >>
  qabbrev_tac `header = (is_bytestring_type typ \/ (case typ of ArrayT _ (Dynamic _) => T | _ => F))` >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; MSTORE]) (emitted_insts sa sb)` by
    (Cases_on `header` >> qpat_x_assum `Abbrev _` kall_tac >> fs[mk_inst_def] >>
     FIRST [(drule emitted_insts_emit_void >> simp[mk_inst_def]),
            (drule zero_words_empty_opcodes >> simp[EVERY_MEM] >> metis_tac[])]) >>
  `create_cut_code {} sa sb` by
    (mp_tac (CONJUNCT1 create_operand_cut_code) >>
     disch_then (qspecl_then [`cenv`,`ty`,`TypeBuiltin typ Empty typ []`,`sa`] mp_tac) >> simp[]) >>
  `frag_code sa sb = emitted_insts sa sb` by
    simp[frag_code_def, emitted_blocks_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
  `MEM i (frag_code sa sb)` by
    (qpat_assum `frag_code sa sb = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `create_cut_code _ _ _` (strip_assume_tac o REWRITE_RULE[create_cut_code_def]) >>
  qpat_assum `!i. MEM i (frag_code _ _) ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `EVERY (\i. MEM i.inst_opcode _) _`
    (drule_then mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  simp[] >> strip_tac >> simp[is_terminator_def]
QED

Theorem empty_initial_storage_focus[local]:
  ~s0.vs_halted /\ ~storage_trace_domain cx st0 es.storage_trace /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb
    source (es,s0,G0,tn0) Q R
Proof
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_bad_storage_at_def, gas_explicit_def] >> conj_tac
  >- (irule create_operand_focus_scope_caller >> qexists_tac `s0` >> simp[]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G0`,`tn0`,`s0`] >>
  simp[gas_origin_ptr_focus_nil]
QED

Theorem empty_create_full_pre[local]:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx ty e es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) <=>
  expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx ty e es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0)
Proof
  simp[expr_vv_sim_full_pre_def, expr_vv_sim_full_hypotheses_def,
       expr_sim_full_code_def, CONJ_ASSOC]
QED

Theorem create_empty_buffer_vv_case:
  expr_body_pre cenv cx env (TypeBuiltin ann Empty typ args) es /\ ~is_word_type typ ==>
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx ty
    (TypeBuiltin ann Empty typ args) es /\
  !st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx ty
      (TypeBuiltin ann Empty typ args) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (TypeBuiltin ann Empty typ args)) (es,s0)
Proof
  strip_tac >> drule empty_type_builtin_args >> strip_tac >> gvs[] >>
  simp[expr_vv_sim_scoped_def, empty_create_full_pre] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      fs[expr_vv_sim_full_hypotheses_def, expr_sim_full_code_def] >>
      drule_all empty_compiled_admin >> strip_tac >>
      irule create_admin_sequence_cut >> fs[create_operand_at_def, EVERY_MEM]) >>
  rpt gen_tac >> strip_tac >> reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule empty_initial_storage_focus >> simp[] >>
      fs[expr_vv_sim_full_hypotheses_def] >>
      drule expr_body_pre_type_evaluates >> simp[expr_type_def, optionTheory.IS_SOME_EXISTS] >>
      metis_tac[empty_type_builtin_eval]) >>
  drule_all empty_type_builtin_run >> strip_tac >>
  fs[expr_vv_sim_full_hypotheses_def, expr_sim_full_code_def] >>
  drule_all empty_compiled_admin >> strip_tac >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  `EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
              i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all create_admin_sequence_scope >> strip_tac >>
  irule nocopy_selector_scoped_landing >>
  first_assum (irule_at Any) >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >> simp[exit_result_def] >>
  qexistsl_tac [`tnf`,`Gf`] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `expr_vv_sim_full_post _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, expr_vv_sim_full_post_def, expr_sim_full_endpoint_def, create_operand_vv_post_def] >>
  strip_tac >> asm_rewrite_tac[]
QED
