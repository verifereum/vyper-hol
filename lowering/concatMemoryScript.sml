(* Frontier checks for the fixed and dynamic byte arms of compile_concat. *)
Theory concatMemory
Ancestors
  fragExecMem instMemFrontier allocaFootprint exprLoweringProps
  emitHelper emitHelperProps compileEnv context venomInst venomState
  venomExecSemantics venomMemDefs words arithmetic finite_map list
Libs
  monadsyntax

Theorem concat_operand_frame[local]:
  !sa s a w n u t.
    fresh_vars_wrt sa s /\ eval_operand a s = SOME w /\
    sa.cs_next_var <= n ==>
    eval_operand a (update_var (STRING #"%" (toString n)) u t) =
    eval_operand a t
Proof
  rpt gen_tac >> strip_tac >>
  `STRING #"%" (toString n) NOTIN FDOM s.vs_vars` by
    metis_tac[fresh_vars_wrt_next] >>
  Cases_on `a` >>
  gvs[eval_operand_def, lookup_var_def] >>
  rename1 `FLOOKUP s.vs_vars x = SOME w` >>
  `x <> STRING #"%" (toString n)` by
    (gvs[FLOOKUP_DEF] >> metis_tac[]) >>
  simp[update_var_def, FLOOKUP_UPDATE]
QED

Theorem concat_store_frontier[local]:
  !p w t. (mstore p w t).vs_alloca_next = t.vs_alloca_next
Proof
  simp[mstore_def, write_memory_def]
QED

Theorem concat_word_add_upper[local]:
  !a b : bytes32. w2n (a + b) <= w2n a + w2n b
Proof
  simp[word_add_def, w2n_n2w, MOD_LESS_EQ]
QED

Theorem concat_fixed_shape[local]:
  (do offset_op <- emit_op MLOAD [off_ptr];
      dst <- emit_op ADD [data_ptr; offset_op];
      emit_void MSTORE [dst; v];
      new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
      emit_void MSTORE [off_ptr; new_offset]
   od) sa = ((), sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id MLOAD [off_ptr]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ADD
       [data_ptr; Var (STRING #"%" (toString sa.cs_next_var))]
       [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) MSTORE
       [Var (STRING #"%" (toString (sa.cs_next_var + 1))); v] [];
     mk_inst (sa.cs_next_id + 3) ADD
       [Var (STRING #"%" (toString sa.cs_next_var)); Lit (n2w m)]
       [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 4) MSTORE
       [off_ptr; Var (STRING #"%" (toString (sa.cs_next_var + 2)))] []]
Proof
  simp[comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

(* The offset is captured before the data store. Its register survives even
   when the full-word store overlaps the offset scratch word. *)
Theorem compile_concat_fixed_step_mem_ok:
  !data_ptr off_ptr v m sa sb s dp off.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; v];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    fresh_vars_wrt sa s /\
    eval_operand data_ptr s = SOME dp /\
    eval_operand off_ptr s = SOME off /\
    w2n off + 32 <= s.vs_alloca_next /\
    w2n dp + w2n (mload (w2n off) s) + 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule concat_fixed_shape >> disch_then SUBST1_TAC >>
  `!a w n u t. eval_operand a s = SOME w /\ sa.cs_next_var <= n ==>
      eval_operand a (update_var (STRING #"%" (toString n)) u t) =
      eval_operand a t` by metis_tac[concat_operand_frame] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s1` >>
  `eval_operand data_ptr s1 = SOME dp` by
    simp[Abbr `s1`] >>
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
    (qspec_then `dp` (qspec_then `mload (w2n off) s` mp_tac)
       concat_word_add_upper >> decide_tac) >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE] >>
  Cases_on `eval_operand v s2` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s3` >>
  `eval_operand off_ptr s3 = SOME off` by
    simp[Abbr `s3`, eval_operand_mstore_eq, Abbr `s2`] >>
  `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) s3 =
      SOME (mload (w2n off) s)` by
    simp[Abbr `s3`, eval_operand_mstore_eq, Abbr `s2`,
         eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
  simp[Abbr `s3`, eval_operand_mstore_eq, Abbr `s2`,
       concat_store_frontier]
QED

val () =
  let val th = compile_concat_fixed_step_mem_ok
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "CONCAT_MEMORY_KERNEL_AUDIT OK\n"
     else raise Fail "concat memory footprint inherited admission"
  end;

Theorem concat_bytes_shape[local]:
  (do arg_len <- emit_op MLOAD [mem_ptr];
      arg_data <- emit_op ADD [mem_ptr; Lit 32w];
      offset_op <- emit_op MLOAD [off_ptr];
      dst <- emit_op ADD [data_ptr; offset_op];
      emit_void MCOPY [dst; arg_data; arg_len];
      new_offset <- emit_op ADD [offset_op; arg_len];
      emit_void MSTORE [off_ptr; new_offset]
   od) sa = ((), sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id MLOAD [mem_ptr]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ADD [mem_ptr; Lit 32w]
       [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) MLOAD [off_ptr]
       [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) ADD
       [data_ptr; Var (STRING #"%" (toString (sa.cs_next_var + 2)))]
       [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) MCOPY
       [Var (STRING #"%" (toString (sa.cs_next_var + 3)));
        Var (STRING #"%" (toString (sa.cs_next_var + 1)));
        Var (STRING #"%" (toString sa.cs_next_var))] [];
     mk_inst (sa.cs_next_id + 5) ADD
       [Var (STRING #"%" (toString (sa.cs_next_var + 2)));
        Var (STRING #"%" (toString sa.cs_next_var))]
       [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 6) MSTORE
       [off_ptr; Var (STRING #"%" (toString (sa.cs_next_var + 4)))] []]
Proof
  simp[comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem concat_mcopy_operand_frame[local]:
  !x dst src n s. eval_operand x (mcopy dst src n s) = eval_operand x s
Proof
  rpt gen_tac >> irule eval_operand_same_vars >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem concat_mcopy_frontier[local]:
  !dst src n s. (mcopy dst src n s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

(* The dynamic-bytes arm after lower_value returns. *)
Theorem compile_concat_bytes_step_mem_ok:
  !mem_ptr data_ptr off_ptr sa sb s src dp off.
    (do arg_len <- emit_op MLOAD [mem_ptr];
        arg_data <- emit_op ADD [mem_ptr; Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MCOPY [dst; arg_data; arg_len];
        new_offset <- emit_op ADD [offset_op; arg_len];
        emit_void MSTORE [off_ptr; new_offset]
     od) sa = ((), sb) /\
    fresh_vars_wrt sa s /\
    eval_operand mem_ptr s = SOME src /\
    eval_operand data_ptr s = SOME dp /\
    eval_operand off_ptr s = SOME off /\
    w2n src + 32 + w2n (mload (w2n src) s) <= s.vs_alloca_next /\
    w2n off + 32 <= s.vs_alloca_next /\
    w2n dp + w2n (mload (w2n off) s) + w2n (mload (w2n src) s)
      <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s

Proof
  rpt strip_tac >> drule concat_bytes_shape >> disch_then SUBST1_TAC >>
  `!a w n u t. eval_operand a s = SOME w /\ sa.cs_next_var <= n ==>
      eval_operand a (update_var (STRING #"%" (toString n)) u t) =
      eval_operand a t` by metis_tac[concat_operand_frame] >>
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
  `mload (w2n off) s2 = mload (w2n off) s` by
    simp[Abbr `s2`, Abbr `s1`, mload_def, update_var_def] >>
  `s4.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `s4`] >>
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
  `w2n (src + 32w) + w2n (mload (w2n src) s) <= s.vs_alloca_next` by
    (qspec_then `src` (qspec_then `32w` mp_tac) concat_word_add_upper >>
     simp[dimword_def] >> decide_tac) >>
  `w2n (dp + mload (w2n off) s) + w2n (mload (w2n src) s)
      <= s.vs_alloca_next` by
    (qspec_then `dp` (qspec_then `mload (w2n off) s` mp_tac)
       concat_word_add_upper >> decide_tac) >>
  map_every (fn j => qpat_assum `!j. _` (qspec_then j assume_tac))
    [`0`, `1`, `2`, `3`] >>
  fs[] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MCOPY] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s5` >>
  `eval_operand off_ptr s5 = SOME off` by
    simp[Abbr `s5`, concat_mcopy_operand_frame, Abbr `s4`,
         Abbr `s2`, Abbr `s1`] >>
  simp[Once run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       Abbr `s5`, concat_mcopy_operand_frame] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
       concat_mcopy_frontier]

QED

val () =
  let val th = compile_concat_bytes_step_mem_ok
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "CONCAT_BYTES_MEMORY_KERNEL_AUDIT OK\n"
     else raise Fail "concat bytes footprint inherited admission"
  end;
