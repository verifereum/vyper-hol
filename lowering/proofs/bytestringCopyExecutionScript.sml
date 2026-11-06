Theory bytestringCopyExecution
Ancestors
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomExecProofs venomState venomInst loweringSlice
  vyperValue vfmConstants words arithmetic list rich_list

Theorem bytestring_word_count_exact:
  len + 63 < dimword (:256) ==>
  ((n2w len + 63w : bytes32) >>> 5) = n2w (1 + word_size len)
Proof
  strip_tac >>
  `((len + 31) + 32) DIV 32 = 1 + (len + 31) DIV 32` by
    (mp_tac (Q.SPECL [`len + 31`, `32`]
       (MATCH_MP ADD_DIV_RWT (DECIDE ``0 < 32``))) >> simp[] >> decide_tac) >>
  `(len + 31) DIV 32 <= len + 31` by simp[DIV_LESS_EQ] >>
  `1 + word_size len < dimword (:256)` by
    (simp[word_size_def] >> decide_tac) >>
  once_rewrite_tac[GSYM wordsTheory.w2n_11] >>
  rewrite_tac[wordsTheory.word_add_n2w, wordsTheory.w2n_lsr, wordsTheory.w2n_n2w] >>
  fs[word_size_def, LESS_MOD]
QED

Theorem bytestring_word_count_shape:
  compile_bytestring_word_count src sa = (out,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sb.cs_next_var = sa.cs_next_var + 3 /\
  sb.cs_next_id = sa.cs_next_id + 3 /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sa sb)
Proof
  simp[compile_bytestring_word_count_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[same_blocks_def, emitted_insts_def, DROP_APPEND, SUB_PLUS,
       mk_inst_def, is_terminator_def]
QED

Theorem bytestring_word_count_run:
  compile_bytestring_word_count src sa = (out,sb) /\
  eval_operand src s = SOME w /\ mload (w2n w) s = n2w len /\
  len + 63 < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (n2w (1 + word_size len)) /\
      (t with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  gvs[compile_bytestring_word_count_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  drule_then assume_tac step_MLOAD >>
  simp[emitted_insts_def, DROP_APPEND, SUB_PLUS, run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `step_inst_base (mk_inst aid ADD ops [v1]) s1` >>
  `step_inst_base (mk_inst aid ADD ops [v1]) s1 =
     OK (update_var v1 ((n2w len:bytes32) + 63w) s1)` by
    (simp[Abbr `ops`] >> irule step_ADD >>
     simp[Abbr `s1`, eval_operand_def, lookup_var_update_var]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `step_inst_base (mk_inst bid SHR ops2 [v2]) s2` >>
  `step_inst_base (mk_inst bid SHR ops2 [v2]) s2 =
     OK (update_var v2 (((n2w len:bytes32) + 63w) >>> 5) s2)` by
    (simp[Abbr `ops2`, mk_inst_def, step_inst_base_opcode_eqs,
          exec_pure2_def, Abbr `s2`, eval_operand_def, lookup_var_update_var]) >>
  simp[] >> conj_tac
  >- simp[bytestring_word_count_exact, eval_operand_def, lookup_var_update_var] >>
  simp[Abbr `s2`, Abbr `s1`, update_var_def] >> rpt strip_tac >>
  gvs[not_fresh_at_def, Abbr `v1`, Abbr `v2`,
      ASCIInumbersTheory.toString_11, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* A representable padded allocation leaves room for the ADD 63 used to
   compute the live word count, even when it reaches the largest word. *)
Theorem bytestring_word_count_no_wrap:
  32 + 32 * word_size len < dimword (:256) ==>
  len + 63 < dimword (:256)
Proof
  strip_tac >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `len + 31` strip_assume_tac) >>
  `(len + 31) MOD 32 < 32` by simp[] >>
  gvs[word_size_def, wordsTheory.dimword_def,
      fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  intLib.ARITH_TAC
QED
