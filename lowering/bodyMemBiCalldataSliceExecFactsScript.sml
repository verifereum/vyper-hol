(* Minimal execution prerequisites from inaccessible locals in
   exprSimCalldataSliceScript.sml (proof source: alan-ref/base/).
   Address/size execution and bounds freshness are already exported by
   bodyMemBiCalldataSliceSuffixMemory; do not duplicate them here. *)
Theory bodyMemBiCalldataSliceExecFacts
Ancestors
  bodyMemBiCalldataSliceSuffixMemory exprSimCalldataSlice
  freshWrites exprSimDefs emitHelperProps builtinBytes loweringSlice
  fragExec venomExecSemantics venomInst venomState words list arithmetic
  emitHelper compileEnv exprLoweringProps finite_map exprSimWordBuiltins

(* Original: exprSimCalldataSlice.slice_bounds_mod [local]. *)
Theorem slice_bounds_mod[local]:
  a < modulus /\ n < modulus /\ limit < modulus ==>
  ((a + n) MOD modulus < a \/ limit < (a + n) MOD modulus <=>
   modulus <= a + n \/ limit < a + n)
Proof
  strip_tac >> Cases_on `a + n < modulus`
  >- simp[arithmeticTheory.LESS_MOD] >>
  `a + n < 2 * modulus` by decide_tac >>
  `(a + n) MOD modulus = a + n - modulus` by
    (irule arithmeticTheory.MOD_UNIQUE >> qexists_tac `1` >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED

(* Original: exprSimCalldataSlice.slice_bounds_word [local]. *)
Theorem slice_bounds_word:
  a < 2 ** 256 /\ n < 2 ** 256 /\ limit < 2 ** 256 ==>
  (((n2w a + n2w n):bytes32) <+ n2w a \/
    (n2w limit:bytes32) <+ n2w a + n2w n <=>
   2 ** 256 <= a + n \/ limit < a + n)
Proof
  strip_tac >> fs[] >>
  simp[wordsTheory.WORD_LO, wordsTheory.word_add_n2w,
       wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  irule slice_bounds_mod >> simp[]
QED

(* Original: exprSimCalldataSlice.slice_bounds_shape [local]. *)
Theorem slice_bounds_shape[local]:
  compile_assert_slice_bounds a n limit sa = ((), sb) ==>
  sb.cs_next_var = sa.cs_next_var + 5 /\
  sb.cs_next_id = sa.cs_next_id + 6 /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [a; n]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) LT
       [Var (STRING #"%" (toString sa.cs_next_var)); a]
       [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) GT
       [Var (STRING #"%" (toString sa.cs_next_var)); limit]
       [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) OR
       [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
        Var (STRING #"%" (toString (sa.cs_next_var + 2)))]
       [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) ISZERO
       [Var (STRING #"%" (toString (sa.cs_next_var + 3)))]
       [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 5) ASSERT
       [Var (STRING #"%" (toString (sa.cs_next_var + 4)))] []]
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

(* Original: exprSimCalldataSlice.slice_bounds_run [local]. *)
Theorem slice_bounds_run[local]:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. n = Var z ==> not_fresh_at sa z) /\
  (!z. limit = Var z ==> not_fresh_at sa z) ==>
  if wa + wn <+ wa \/ wl <+ wa + wn then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t. run_inst_seq (emitted_insts sa sb) s = OK t
Proof
  strip_tac >> drule slice_bounds_shape >> strip_tac >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  Cases_on `wa + wn <+ wa` >> Cases_on `wl <+ wa + wn` >>
  gvs[wordsTheory.WORD_LO] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_pure1_def, bool_to_word_def,
       eval_operand_def, lookup_var_update_var, wordsTheory.WORD_OR_CLAUSES]
QED

(* Original: exprSimCalldataSlice.slice_bounds_run_frame [local].
   Reuses the already reconstructed freshness interface. *)
Theorem slice_bounds_run_frame:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. n = Var z ==> not_fresh_at sa z) /\
  (!z. limit = Var z ==> not_fresh_at sa z) ==>
  if wa + wn <+ wa \/ wl <+ wa + wn then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
           t = s with vs_vars := t.vs_vars /\
           !x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> drule_all slice_bounds_run >>
  Cases_on `wa + wn <+ wa \/ wl <+ wa + wn` >> simp[] >> strip_tac >>
  drule calldata_slice_bounds_fresh >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

(* Original: exprSimCalldataSlice.calldata_slice_no_padding [local]. *)
Theorem calldata_slice_no_padding[local]:
  a + n <= LENGTH bs ==>
  TAKE n (DROP a bs ++ REPLICATE n z) = TAKE n (DROP a bs)
Proof
  strip_tac >> irule rich_listTheory.TAKE_APPEND1 >> simp[]
QED

(* Original: exprSimCalldataSlice.calldata_copy_step [local]. *)
Theorem calldata_copy_step[local]:
  !dst off count s wd wa wn iid.
  eval_operand dst s = SOME wd /\ eval_operand off s = SOME wa /\
  eval_operand count s = SOME wn /\
  w2n wa + w2n wn <= LENGTH s.vs_call_ctx.cc_calldata ==>
  step_inst_base (mk_inst iid CALLDATACOPY [dst; off; count] []) s =
  OK (write_memory_with_expansion (w2n wd)
       (TAKE (w2n wn) (DROP (w2n wa) s.vs_call_ctx.cc_calldata)) s)
Proof
  rpt strip_tac >> simp[step_inst_base_opcode_eqs, mk_inst_def,
                       calldata_slice_no_padding]
QED

(* Original: exprSimCalldataSlice.slice_calldata_copy_store_run [local]. *)
Theorem slice_calldata_copy_store_run:
  !dst src num_op buf_op sa sm sb s wd wa wn wp.
  emit_void CALLDATACOPY [dst; src; num_op] sa = ((),sm) /\
  emit_void MSTORE [buf_op; num_op] sm = ((),sb) /\
  eval_operand dst s = SOME wd /\ eval_operand src s = SOME wa /\
  eval_operand num_op s = SOME wn /\ eval_operand buf_op s = SOME wp /\
  w2n wa + w2n wn <= LENGTH s.vs_call_ctx.cc_calldata ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n wp) wn
      (write_memory_with_expansion (w2n wd)
        (TAKE (w2n wn) (DROP (w2n wa) s.vs_call_ctx.cc_calldata)) s))
Proof
  rpt strip_tac >>
  qpat_x_assum `emit_void CALLDATACOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  `!iid. step_inst_base (mk_inst iid CALLDATACOPY [dst; src; num_op] []) s =
    OK (write_memory_with_expansion (w2n wd)
      (TAKE (w2n wn) (DROP (w2n wa) s.vs_call_ctx.cc_calldata)) s)` by
    (gen_tac >> irule calldata_copy_step >> simp[]) >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       write_memory_with_expansion_def, write_memory_def, eval_operand_def]
QED
