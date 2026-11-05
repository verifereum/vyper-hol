Theory bodyEmptyBufferMemory
Ancestors
  builtinSimple exprSimBufferEmptyExec bodyLiteralBufferMemory
  abiEmptySequence exprLoweringProps emitHelperProps freshWrites
  fragExecMem instMemFrontier venomExecSemantics venomState venomInst
  compileEnv context emitHelper finite_map words list rich_list arithmetic

Theorem compile_zero_words_seq_mem:
  !n pop sa sb s w.
    compile_zero_words pop n sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!x. pop = Var x ==> not_fresh_at sa x) /\
    w2n w + 32*n <= s.vs_alloca_next /\
    w2n w + 32*n < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      t.vs_alloca_next = s.vs_alloca_next /\ eval_operand pop t = SOME w)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def,
    emitted_insts_def, run_inst_seq_mem_ok_def, run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_zero_words _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_zero_words_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words pop n sa = (ignored,sm)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  first_x_assum (qspecl_then [`pop`, `sa`, `sm`, `s`, `w`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND, LESS_EQ_ADD]) >>
  `LENGTH sa.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `LENGTH sa.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (simp[emitted_insts_def, DROP_APPEND, LENGTH_APPEND, SUB_EQ_0]) >>
  `emitted_insts sm sb =
    [mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))]
       [STRING #"%" (toString sm.cs_next_var)];
     mk_inst cs''.cs_next_id MSTORE [dst; Lit 0w] []]` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `!t. run_inst_seq (emitted_insts sa sm) s = OK t ==>
     run_inst_seq_mem_ok (emitted_insts sm sb) t /\
     (!u. run_inst_seq (emitted_insts sm sb) t = OK u ==>
       u.vs_alloca_next = s.vs_alloca_next /\ eval_operand pop u = SOME w)` by
    (gen_tac >> disch_tac >>
     first_x_assum drule >> strip_tac >>
     qabbrev_tac `p = STRING #"%" (toString sm.cs_next_var)` >>
     `step_inst_base (mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))] [p]) t =
       OK (update_var p (w + n2w (32*n)) t)` by
       (irule step_ADD >> simp[eval_operand_def]) >>
     `w2n (w + n2w (32*n)) = w2n w + 32*n` by
       (`w2n w + 32*n < dimword (:256)` by decide_tac >>
        `32*n < dimword (:256)` by decide_tac >>
        simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, LESS_MOD]) >>
     conj_tac
     >- (asm_rewrite_tac[] >>
         simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
           below_frontier_MSTORE, eval_operand_def, lookup_var_update_var,
           update_var_def] >>
         simp[mk_inst_def, below_frontier_no_ranges, lookup_var_def,
           FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[] >> decide_tac) >>
     `step_inst_base (mk_inst cs''.cs_next_id MSTORE [Var p; Lit 0w] [])
        (update_var p (w + n2w (32*n)) t) =
        OK (mstore (w2n (w + n2w (32*n))) 0w
          (update_var p (w + n2w (32*n)) t))` by
       (irule step_MSTORE >> simp[eval_operand_def, lookup_var_update_var]) >>
     gen_tac >> disch_tac >>
     `u = mstore (w2n (w + n2w (32*n))) 0w
          (update_var p (w + n2w (32*n)) t)` by
       (qpat_x_assum `run_inst_seq (emitted_insts sm sb) t = OK u` mp_tac >>
        gvs[] >> simp[run_inst_seq_def]) >>
     conj_tac >- simp[mstore_def, update_var_def] >>
     Cases_on `pop` >>
     gvs[eval_operand_def, mstore_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, not_fresh_at_def, Abbr `p`] >>
     NO_TAC) >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
      irule run_inst_seq_mem_ok_append >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> gvs[]) >>
  gen_tac >> disch_tac >>
  Cases_on `run_inst_seq (emitted_insts sa sm) s`
  >- (drule run_inst_seq_append >>
      disch_then (qspec_then `emitted_insts sm sb` assume_tac) >>
      gvs[] >> metis_tac[]) >>
  `!u. run_inst_seq (emitted_insts sa sm) s <> OK u` by simp[] >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `emitted_insts sm sb` assume_tac) >> gvs[]
QED

Theorem compile_zero_words_no_gas:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >>
  simp_tac bool_ss [Once compile_zero_words_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words pop n sa = (ignored,sm)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND, LESS_EQ_ADD]) >>
  `LENGTH sa.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `LENGTH sa.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++
    [mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))]
      [STRING #"%" (toString sm.cs_next_var)];
     mk_inst cs''.cs_next_id MSTORE [dst; Lit 0w] []]` by
    simp[emitted_insts_def, DROP_APPEND, LENGTH_APPEND] >>
  asm_rewrite_tac[] >> simp[mk_inst_def]
QED
