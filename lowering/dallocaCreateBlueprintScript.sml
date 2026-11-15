(* Constructor argument lowering separates the signed code-size check from
   the allocation. Its operand frame and length bound remain staging inputs. *)
Theory dallocaCreateBlueprint
Ancestors
  builtinCreate context exprLoweringProps emitHelper emitHelperProps compileEnv
  loweringStateRelDefs dallocaBounds
  venomExecSemantics venomInst venomState list rich_list words finite_map

Theorem create_blueprint_check_prefix:
  !target offset sa code_op sb s t.
    compile_create_blueprint_check target offset sa = (code_op,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?code.
      eval_operand code_op t = SOME code /\
      0 < w2n code /\ w2n code < 2 ** 255 /\
      t.vs_accounts = s.vs_accounts /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_fmp = s.vs_fmp
Proof
  rpt gen_tac >>
  simp[compile_create_blueprint_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_read1_def, exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, fresh_var_distinct, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `bool_to_word good` >>
  Cases_on `good` >> gvs[bool_to_word_def, markerTheory.Abbrev_def, WORD_GT] >>
  fs[WORD_MSB_INT_MIN_LS, WORD_LS, word_L_def, INT_MIN_def,
     dimword_def, venomMemPropsTheory.dimindex_256, w2n_n2w]
QED

Theorem create_blueprint_alloc_prefix:
  !target value salt offset code args_ptr args_len rof sa result sb.
    compile_create_blueprint_append target value salt offset
      code args_ptr args_len rof sa = (result,sb) ==>
    ?total sm ptr sn.
      emit_op ADD [code;args_len] sa = (total,sm) /\
      compile_alloc_dynamic total sm = (ptr,sn)
Proof
  rpt gen_tac >>
  simp[compile_create_blueprint_append_def, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum $ drule_at Any)
QED

Theorem create_blueprint_prefix:
  !target offset ca code_op cb s0 s1 s2 args_len args sa total sb t.
    compile_create_blueprint_check target offset ca = (code_op,cb) /\
    run_inst_seq (emitted_insts ca cb) s0 = OK s1 /\
    eval_operand code_op s2 = eval_operand code_op s1 /\
    eval_operand args_len s2 = SOME args /\ w2n args < 2 ** 64 /\
    emit_op ADD [code_op;args_len] sa = (total,sb) /\
    run_inst_seq (emitted_insts sa sb) s2 = OK t ==>
    ?size.
      eval_operand total t = SOME size /\
      w2n size <= 2 ** 255 + 2 ** 64 /\
      venomLayout$ceil32 (w2n size) <= 2 ** 255 + 2 ** 64 /\
      t.vs_accounts = s2.vs_accounts /\
      t.vs_call_ctx = s2.vs_call_ctx /\ t.vs_fmp = s2.vs_fmp
Proof
  rpt gen_tac >> strip_tac >>
  drule_all create_blueprint_check_prefix >>
  disch_then (qx_choose_then `code` strip_assume_tac) >>
  `eval_operand code_op s2 = SOME code` by fs[] >>
  `venomLayout$ceil32 (w2n ((code:bytes32) + args)) <= 2 ** 255 + 2 ** 64` by
    (mp_tac (Q.INST [`code_size` |-> `code`, `args_len` |-> `args`]
       dalloca_trailing_blueprint_size_bound) >> simp[]) >>
  `w2n ((code:bytes32) + args) <= 2 ** 255 + 2 ** 64` by
    (mp_tac (Q.INST [`n` |-> `w2n ((code:bytes32) + args)`]
       venomLayoutTheory.ceil32_ge) >> decide_tac) >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ s2 = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]
QED
