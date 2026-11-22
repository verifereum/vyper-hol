Theory entryBlueprintBudgetExtent
Ancestors
  dallocaCreateBlueprint builtinCreate context compileEnv emitHelper
  emitHelperProps exprLoweringProps loweringStateRelDefs venomExecSemantics
  venomInst venomState list rich_list words finite_map arithmetic

(* The unsigned branch checks the extent with GT before doing the SUB. *)
Theorem blueprint_unsigned_checked_extent[local]:
  compile_create_blueprint_check F target off ca = (code,cb) /\
  run_inst_seq (emitted_insts ca cb) s = OK t /\
  (!addr. LENGTH (lookup_account addr s.vs_accounts).code < 2 ** 255) ==>
  ?cw. eval_operand code t = SOME cw /\ w2n cw < 2 ** 255
Proof
  simp[compile_create_blueprint_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_read1_def, exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, fresh_var_distinct, AllCaseEqs()] >>
  `v2 = y \/ v2 = 1w` by
    (Cases_on `off` >>
     gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, AllCaseEqs(),
         bool_to_word_def, venomExecProofsTheory.bool_to_word_neq_0w]) >>
  qmatch_goalsub_abbrev_tac `w2n (full - v2)` >>
  `w2n full < 2 ** 255` by
    (simp[Abbr `full`, w2n_n2w] >>
     metis_tac[MOD_LESS_EQ, ZERO_LT_dimword, LESS_EQ_LESS_TRANS]) >>
  `w2n y < w2n full` by
    fs[Abbr `full`, w2n_n2w, GREATER_DEF,
       venomExecProofsTheory.bool_to_word_neq_0w] >>
  `v2 <=+ full` by (simp[WORD_LS] >> decide_tac) >>
  gs[word_sub_w2n] >> decide_tac
QED

Theorem blueprint_total_add_word[local]:
  emit_op ADD [code;args_len] sa = (size_op,sm) /\
  run_inst_seq (emitted_insts sa sm) u = OK pre /\
  eval_operand code u = SOME cw /\ eval_operand args_len u = SOME aw ==>
  eval_operand size_op pre = SOME (cw + aw)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, AllCaseEqs()]
QED

(* The two runs end before DALLOCA. No allocation or CREATE success is used. *)
Theorem blueprint_pending_extent_bound:
  compile_create_blueprint_check lit target off ca = (code,cb) /\
  run_inst_seq (emitted_insts ca cb) s = OK t /\
  (!addr. LENGTH (lookup_account addr s.vs_accounts).code < 2 ** 255) /\
  eval_operand code u = eval_operand code t /\
  eval_operand args_len u = SOME aw /\ w2n aw < 2 ** 64 /\
  emit_op ADD [code;args_len] sa = (size_op,sm) /\
  run_inst_seq (emitted_insts sa sm) u = OK pre ==>
  ?sz. eval_operand size_op pre = SOME sz /\ w2n sz <= 2 ** 255 + 2 ** 64
Proof
  strip_tac >>
  `?cw. eval_operand code t = SOME cw /\ w2n cw < 2 ** 255` by
    (Cases_on `lit`
     >- (drule_all create_blueprint_check_prefix >>
         disch_then (qx_choose_then `cw` strip_assume_tac) >>
         qexists `cw` >> gs[])
     >> drule_all blueprint_unsigned_checked_extent >> simp[]) >>
  fs[] >> drule_all blueprint_total_add_word >> strip_tac >>
  qexists `cw + aw` >> simp[] >>
  qspecl_then [`cw`, `aw`] mp_tac word_add_le >> gs[] >> decide_tac
QED
