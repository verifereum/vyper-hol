(* Runtime DLOAD is a readonly step, separate from fresh arithmetic. *)
Theory bodyIntCallFamAggSubscriptArrayRun
Ancestors
  bodyIntCallFamAggSubscriptReadOnly exprSimSubscriptArrayFramed
  bodyIntCallJointContract emitHelperProps context venomState venomInst
  compileEnv exprLoweringProps

Theorem intcall_runtime_load_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  sa.cs_next_var <= si.cs_next_var /\
  compile_imm_load_word F imm base_op si = (op,sb) /\
  eval_operand base_op s = SOME b /\ fn_has_code si sb fp.jc_func ==>
  ?t. run_inst_seq (emitted_insts si sb) s = OK t /\
    eval_operand op t = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at si x ==> lookup_var x t = lookup_var x s) /\
    gas_marked_path F fp.jc_ctx fp.jc_func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    intcall_expr_cont fp ce env es0 sa s0 es sb
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  drule_all compile_imm_load_word_runtime_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK t` >>
  `!x. not_fresh_at si x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> simp[Abbr `t`] >>
     gvs[] >> drule moduleLoweringPropsTheory.lookup_var_update_not_fresh >> simp[]) >>
  `(t with vs_vars := s.vs_vars) = s` by
    simp[Abbr `t`, update_var_def] >>
  `eval_operand op t = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w)))` by
    simp[Abbr `t`, eval_operand_def, lookup_var_def,
      update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qexists_tac `t` >> asm_rewrite_tac [] >>
  irule intcall_readonly_run_landing >> simp[] >>
  qexists_tac `si` >> simp[] >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_load_word_runtime] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  gvs[same_blocks_def, mk_inst_def, is_terminator_def]
QED
