Theory bodyMemBiBlobHashFrag
Ancestors
  bodyUnopFragMemory exprSimBuiltins exprSimAccounts
  instMemFrontier memSafeRun allocaHistory fragGasSeqAbort
  emitHelperProps fragGasPathMem
  exprUnopSimDefs exprSimSource exprSimHypsDefs loweringPosts
  exprSimProps exprSimDefs exprLowering emitHelper exprLoweringProps
  compileEnv loweringStateRelDefs vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation valueEncoding venomExecSemantics venomInst venomState
  vyperTyping vyperTypeSystem exprSimUnopProps exprSimMemorySource
  gasSummary fragGasMode instIdxIndep fragExec
  builtinSimple builtinProps arithmeticProps vyperArith
  arithmetic list rich_list integer words integer_word byte finite_map
Libs
  intLib

Theorem blobhash_read_frag_mem:
  !ctx func cenv cx w1 r t v es0.
    is_word_type t /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          r = typed_val_to_w256 tv v) /\
    (!x ss n out.
       eval_operand x ss = SOME w1 /\ stmt_state_rel ctx func cenv cx es0 ss ==>
       step_inst_base (mk_inst n BLOBHASH [x] [out]) ss =
         OK (update_var out r ss)) ==>
    unop_frag_mem ctx func cenv cx (\x. emit_op BLOBHASH [x]) w1 t (INL v) es0
Proof
  rpt gen_tac >> strip_tac >> simp[unop_frag_mem_def] >> rpt gen_tac >>
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `get_instruction bb s0.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id BLOBHASH [x] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `out`]) >>
  `step_inst_base (mk_inst sa.cs_next_id BLOBHASH [x] [out]) s0 =
    OK (update_var out r s0)` by metis_tac[] >>
  qabbrev_tac `u = update_var out r s0 with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `gas_marked_path T ctx func s0 0 (OK u)` by
    (drule_at (Pat `step_inst_base _ _ = OK _`) gas_marked_path_step >>
     disch_then (qspecl_then [`T`, `ctx`, `func`, `bb`, `0`, `OK u`] mp_tac) >>
     simp[mk_inst_def, is_terminator_def, below_frontier_no_ranges,
          inst_dload_in_section_other, Abbr `u`, gas_marked_path_def] >>
     impl_tac >- (irule (cj 1 gas_path_mem_rules) >> simp[update_var_def]) >>
     simp[]) >>
  `alloca_inv s0` by fs[stmt_state_rel_def, state_rel_def] >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `alloca_history func u` by
    (drule_all alloca_history_base_step >>
     simp[mk_inst_def, is_terminator_def, Abbr `u`] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  `!z. not_fresh_at sa z ==> z <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  `not_local_ptr cenv es0.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[LESS_EQ_REFL]) >>
  `op = Var out` by
    gvs[Abbr `out`, emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `stmt_state_rel ctx func cenv cx es0 (update_var out r s0)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  qexists_tac `OK u` >> simp[] >>
  simp[Abbr `u`, stmt_state_rel_inst_idx, expr_val_rel_def, expr_val_at_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[stmt_state_rel_update_var]
QED

Theorem compile_blobhash_frag_mem:
  !ctx func cenv cx i es0.
    0 <= i /\ i < 2 ** 256 ==>
    unop_frag_mem ctx func cenv cx (\x. emit_op BLOBHASH [x])
      (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i))
      (BaseT (BytesT (Fixed 32)))
      (unop_result cx (BaseT (BytesT (Fixed 32))) BlobHash
         [BaseT (UintT 256)] (IntV i) es0) es0
Proof
  rpt strip_tac >>
  simp[unop_result_def, evaluate_builtin_def, evaluate_blob_hash_def] >>
  irule blobhash_read_frag_mem >>
  simp[vyperValueTheory.evaluate_type_def, is_word_type_def,
       typed_val_to_w256_def, PAD_RIGHT,
       length_word_to_bytes_be, word_of_bytes_be_to_bytes] >>
  rpt strip_tac >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
      stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  gvs[val_to_w256_def, integer_wordTheory.i2w_pos, wordsTheory.dimword_def]
QED
