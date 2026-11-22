(* The CopyOf length at the dispatch cut, without executing CREATE. *)
Theory createSizeCopyLength
Ancestors
  dallocaCreateCopy dallocaCreateGeometry instSeqComposePtr
  accountsRelProps loweringStateRelDefs vyperTypeInvariants vfmConstants
  exprLoweringProps builtinCreate context compileEnv emitHelper emitHelperProps
  venomExecSemantics venomInst venomState words arithmetic list rich_list

Theorem create_copy_pre_dispatch_length_bound:
  emit_op EXTCODESIZE [target] sa = (code,a1) /\
  emit_void ASSERT [code] a1 = ((),a2) /\
  emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
  emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
  emit_op ADD [code;Lit 32w] a4 = (request,a5) /\
  compile_alloc_dynamic request a5 = (alloc_ptr,a6) /\
  emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
  emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
  emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
  emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
  emit_op ADD [code;Lit 11w] a10 = (len,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t /\
  accounts_agree H cx.txn.target acc s.vs_accounts /\
  accounts_well_typed acc /\ eval_operand len t = SOME w ==>
  w2n w <= 2 * max_code_size
Proof
  strip_tac >>
  `emitted_insts sa sc = emitted_insts sa a4 ++ emitted_insts a4 a5 ++
    emitted_insts a5 sc /\
   emitted_insts sa a5 = emitted_insts sa a4 ++ emitted_insts a4 a5 /\
   ?rest. emitted_insts sa a4 =
     mk_inst sa.cs_next_id EXTCODESIZE [target]
       [STRING #"%" (toString sa.cs_next_var)] :: rest` by
    (fs[compile_alloc_dynamic_def, emit_op_def, emit_void_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
        emit_def] >> gvs[] >>
     SIMP_TAC pure_ss [emitted_insts_def, compile_state_accfupds,
                       GSYM APPEND_ASSOC, APPEND, DROP_LENGTH_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `?seed pre. run_inst_seq (emitted_insts sa a4) s = OK seed /\
    run_inst_seq (emitted_insts a4 a5) seed = OK pre /\
    run_inst_seq (emitted_insts a5 sc) pre = OK t` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     qpat_assum `emitted_insts sa sc = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     strip_tac >>
     drule run_inst_seq_append_ok_split >> strip_tac >>
     drule run_inst_seq_append_ok_split >> metis_tac[]) >>
  `?addr. eval_operand target s = SOME addr` by
    (qpat_assum `run_inst_seq (emitted_insts sa a4) s = _` mp_tac >>
     qpat_assum `emitted_insts sa a4 = _::_`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     Cases_on `eval_operand target s` >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read1_def]) >>
  `LENGTH (lookup_account (w2w addr) s.vs_accounts).code <= 24576` by
    (drule accounts_agree_lookup >>
     disch_then (qspec_then `w2w addr` strip_assume_tac) >>
     fs[accounts_well_typed_def, account_well_typed_def]) >>
  `run_inst_seq (emitted_insts sa a5) s = OK pre` by
    metis_tac[run_inst_seq_append] >>
  drule_all create_copy_prefix >> strip_tac >>
  drule_all create_copy_allocation_geometry >> strip_tac >>
  qabbrev_tac `n = LENGTH (lookup_account (w2w addr) s.vs_accounts).code` >>
  `n2w (n + 32) = w + 21w : bytes32` by metis_tac[optionTheory.SOME_11] >>
  `n2w (n + 11) + 21w = w + 21w : bytes32` by
    (qpat_assum `n2w (n + 32) = w + 21w`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> simp[word_add_n2w]) >>
  pop_assum (mp_tac o Q.AP_TERM `\x:bytes32. x - 21w`) >>
  simp[WORD_ADD_SUB] >> disch_then (SUBST1_TAC o SYM) >>
  `((n + 11) MOD dimword (:256)) <= n + 11` by simp[MOD_LESS_EQ] >>
  simp[max_code_size_def] >> decide_tac
QED
