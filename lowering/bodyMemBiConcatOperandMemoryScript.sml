(* Concat frontier checks require only noncollision of the input operands. *)
Theory bodyMemBiConcatOperandMemory
Ancestors
  allocaFootprint concatMemory exprSimConcatStep fragExecMem instMemFrontier abiDecoderIndexInit
  emitHelperProps emitHelper venomInst venomMemProps venomExecSemantics venomState words arithmetic compileEnv
Libs
  monadsyntax

Theorem concat_fixed_operands_mem_ok:
  !data_ptr off_ptr v m sa sb s dp off.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; v];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    (!z. data_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sa z) /\
    eval_operand data_ptr s = SOME dp /\ eval_operand off_ptr s = SOME off /\
    w2n off + 32 <= s.vs_alloca_next /\
    w2n dp + w2n (mload (w2n off) s) + 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule concat_fixed_shape >> disch_then SUBST1_TAC >>
  `!a n u t. (!z. a = Var z ==> not_fresh_at sa z) /\ sa.cs_next_var <= n ==>
      eval_operand a (update_var (STRING #"%" (toString n)) u t) =
      eval_operand a t` by metis_tac[concat_operand_update_fresh] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s1` >>
  `eval_operand data_ptr s1 = SOME dp` by simp[Abbr `s1`] >>
  simp[Once run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, Abbr `s1`] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s2` >>
  `s2.vs_alloca_next = s.vs_alloca_next` by simp[Abbr `s2`] >>
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var + 1)))) s2 =
     SOME (dp + mload (w2n off) s)` by
    simp[Abbr `s2`, eval_operand_def, lookup_var_update_var] >>
  `w2n (dp + mload (w2n off) s) + 32 <= s2.vs_alloca_next` by
    (`(w2n dp + w2n (mload (w2n off) s)) MOD dimword (:256) <=
       w2n dp + w2n (mload (w2n off) s)` by simp[MOD_LESS_EQ] >>
     simp[word_add_def] >> decide_tac) >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE] >>
  Cases_on `eval_operand v s2` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s3` >>
  `eval_operand off_ptr s3 = SOME off` by
    simp[Abbr `s3`, abi_decoder_operand_mstore, Abbr `s2`] >>
  `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) s3 =
      SOME (mload (w2n off) s)` by
    simp[Abbr `s3`, abi_decoder_operand_mstore, Abbr `s2`,
         eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
       Abbr `s3`, abi_decoder_operand_mstore, Abbr `s2`, mstore_def]
QED

Theorem concat_bytes_operands_mem_ok:
  !mem_ptr data_ptr off_ptr sa sb s src dp off.
    (do arg_len <- emit_op MLOAD [mem_ptr];
        arg_data <- emit_op ADD [mem_ptr; Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MCOPY [dst; arg_data; arg_len];
        new_offset <- emit_op ADD [offset_op; arg_len];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    (!z. mem_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. data_ptr = Var z ==> not_fresh_at sa z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sa z) /\
    eval_operand mem_ptr s = SOME src /\
    eval_operand data_ptr s = SOME dp /\ eval_operand off_ptr s = SOME off /\
    w2n src + 32 + w2n (mload (w2n src) s) <= s.vs_alloca_next /\
    w2n off + 32 <= s.vs_alloca_next /\
    w2n dp + w2n (mload (w2n off) s) + w2n (mload (w2n src) s)
      <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule concat_bytes_shape >> disch_then SUBST1_TAC >>
  `!a n u t. (!z. a = Var z ==> not_fresh_at sa z) /\ sa.cs_next_var <= n ==>
      eval_operand a (update_var (STRING #"%" (toString n)) u t) =
      eval_operand a t` by metis_tac[concat_operand_update_fresh] >>
  `w2n src + 32 <= s.vs_alloca_next` by decide_tac >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s1` >>
  `eval_operand mem_ptr s1 = SOME src` by simp[Abbr `s1`] >>
  simp[Once run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s2` >>
  `eval_operand off_ptr s2 = SOME off` by simp[Abbr `s2`, Abbr `s1`] >>
  `s2.vs_alloca_next = s.vs_alloca_next` by simp[Abbr `s2`, Abbr `s1`] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s3` >>
  `eval_operand data_ptr s3 = SOME dp` by
    simp[Abbr `s3`, Abbr `s2`, Abbr `s1`] >>
  simp[Once run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, Abbr `s3`] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s4` >>
  suspend "copy_and_offset"
QED

Resume concat_bytes_operands_mem_ok[copy_and_offset]:
  `mload (w2n off) s2 = mload (w2n off) s` by
    simp[Abbr `s2`, Abbr `s1`, mload_def, update_var_def] >>
  `s4.vs_alloca_next = s.vs_alloca_next` by simp[Abbr `s4`] >>
  `!j. j <= 3 ==>
     eval_operand (Var (STRING #"%" (toString (sa.cs_next_var + j)))) s4 =
       SOME (if j = 0 then mload (w2n src) s
             else if j = 1 then src + 32w
             else if j = 2 then mload (w2n off) s
             else dp + mload (w2n off) s)` by
    (rpt strip_tac >>
     `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` by decide_tac >>
     gvs[Abbr `s4`, Abbr `s2`, Abbr `s1`,
         eval_operand_def, lookup_var_update_var]) >>
  `!a b : bytes32. w2n (a + b) <= w2n a + w2n b` by
    simp[word_add_def, MOD_LESS_EQ] >>
  `w2n (src + 32w) + w2n (mload (w2n src) s) <= s.vs_alloca_next` by
    (first_x_assum (qspecl_then [`src`, `32w`] mp_tac) >>
     simp[dimword_def] >> decide_tac) >>
  `w2n (dp + mload (w2n off) s) + w2n (mload (w2n src) s)
      <= s.vs_alloca_next` by
    (first_x_assum (qspecl_then [`dp`, `mload (w2n off) s`] mp_tac) >>
     decide_tac) >>
  map_every (fn j => qpat_assum `!j. _` (qspec_then j assume_tac))
    [`0`, `1`, `2`, `3`] >> fs[] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MCOPY] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s5` >>
  `!x d src n t. eval_operand x (mcopy d src n t) = eval_operand x t` by
    (rpt gen_tac >> irule eval_operand_same_vars >>
     simp[mcopy_def, write_memory_with_expansion_def]) >>
  `eval_operand off_ptr s5 = SOME off` by
    simp[Abbr `s5`, Abbr `s4`, Abbr `s2`, Abbr `s1`] >>
  simp[Once run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, Abbr `s5`] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
       mcopy_def, write_memory_with_expansion_def]
QED

Finalise concat_bytes_operands_mem_ok
