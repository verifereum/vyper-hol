(* The emitted Bool-array preheader, including both rejecting guards. *)
Theory ctorDeployMemoryRunPtrPrefixBoolPreheader
Ancestors
  ctorDeployMemoryRunPtrPrefixBoolLoop ctorDeployMemoryRunPtrPrefixBoolBody
  ctorDeployMemoryRunPtrPrefixBoolShape ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixBoolWord ctorDeployMemoryRunPtrPrefixSequence
  abiDecoderExecution abiDecoderContract venomMemProofs valueEncodingProps fragExec
  ptrSafeRun ptrDiscipline rich_list
  venomExecSemantics venomExecProps venomState venomInst words arithmetic list finite_map
  codegenRel contextCodegenRel emitHelper exprLoweringProps

Theorem prefix_preheader_eval_index[local]:
  eval_operand op (s with vs_inst_idx := k) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem prefix_preheader_update_index[local]:
  update_var x w (s with vs_inst_idx := k) =
  (update_var x w s) with vs_inst_idx := k
Proof
  simp[update_var_def]
QED

Theorem prefix_preheader_mstore_index[local]:
  mstore a w (s with vs_inst_idx := k) =
  (mstore a w s) with vs_inst_idx := k
Proof
  simp[mstore_def]
QED

Theorem prefix_preheader_taint_index[local]:
  i.inst_opcode IN {DLOAD; MSTORE; ALLOCA} ==>
  step_taint i (s with vs_inst_idx := k) (t with vs_inst_idx := j) tn =
  step_taint i s t tn
Proof
  strip_tac >>
  `!op. eval_operand op (s with vs_inst_idx := k) = eval_operand op s`
    by simp[prefix_preheader_eval_index] >>
  gvs[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, written_taint_def, out_taint_def,
       adopt_reset_def, store_taint_def, imm_taint_def]
QED

Theorem prefix_bool_preheader_gt_step:
  eval_operand u s = SOME w /\ eval_operand v s = SOME z ==>
  step_inst_base (mk_inst iid GT [u;v] [x]) s =
    OK (update_var x (bool_to_word (w2n z < w2n w)) s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def, GREATER_DEF]
QED

Theorem prefix_bool_preheader_guard_dispatch[local]:
  step_inst_base (mk_inst iid GT ops outs) s =
    exec_pure2 (\w z. bool_to_word (w2n w > w2n z)) (mk_inst iid GT ops outs) s /\
  step_inst_base (mk_inst iid ISZERO ops outs) s =
    exec_pure1 (\w. bool_to_word (w = 0w)) (mk_inst iid ISZERO ops outs) s
Proof
  simp[step_inst_base_def, mk_inst_def]
QED

Theorem prefix_bool_preheader_count_guard:
  eval_operand (Var src) s = SOME (n2w a) /\
  ALL_DISTINCT [src;cnt;cmp;ok] /\ max_count < dimword(:256) ==>
  let n = abi_decode_load DLOAD (n2w a:bytes32) s;
      s1 = update_var cnt n s;
      s2 = update_var cmp (bool_to_word (max_count < w2n n)) s1;
      s3 = update_var ok (bool_to_word (~(max_count < w2n n))) s2
  in run_inst_seq
       [mk_inst iid DLOAD [Var src] [cnt];
        mk_inst (iid+1) GT [Var cnt; Lit(n2w max_count)] [cmp];
        mk_inst (iid+2) ISZERO [Var cmp] [ok];
        mk_inst (iid+3) ASSERT [Var ok] []] s =
     if w2n n <= max_count then OK s3
     else Abort Revert_abort (revert_state (set_returndata [] s3))
Proof
  rpt strip_tac >>
  drule prefix_dload_step >>
  disch_then (qspecl_then [`iid`,`cnt`] assume_tac) >>
  gvs[ALL_DISTINCT] >>
  simp[abi_decode_load_def, abi_decode_source_def] >>
  simp[run_inst_seq_def, prefix_bool_preheader_gt_step,
       prefix_boolword_iszero_step, prefix_assert_step,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, word_lo_def, w2n_n2w] >>
  simp[prefix_bool_preheader_guard_dispatch, exec_pure2_def, exec_pure1_def,
       mk_inst_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       update_var_def, w2n_n2w, GREATER_DEF, bool_to_word_def] >>
  qmatch_goalsub_abbrev_tac `if n<=max_count then _ else _` >>
  Cases_on `n<=max_count` >>
  simp[step_inst_base_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       bool_to_word_def]
QED

Theorem prefix_bool_preheader_extent_word:
  n <= max_count /\ a+32*(max_count+1) < dimword(:256) ==>
  w2n ((n2w a:bytes32) + (n2w n * 32w + 32w)) = a+32*(n+1)
Proof
  rpt strip_tac >>
  `a+32*(n+1) < dimword(:256)` by decide_tac >>
  pure_rewrite_tac[word_mul_n2w, word_add_n2w, w2n_n2w] >>
  `a+(n*32+32) = a+32*(n+1)` by decide_tac >>
  simp[]
QED

Theorem prefix_bool_preheader_count_steps:
  eval_operand (Var src) s = SOME (n2w a) /\
  op_taint tn (Var src) = {} /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ max_count < dimword(:256) ==>
  let n = abi_decode_load DLOAD (n2w a:bytes32) s;
      i = mk_inst iid DLOAD [Var src] [cnt];
      j = mk_inst (iid+1) GT [Var cnt; Lit(n2w max_count)] [cmp];
      k = mk_inst (iid+2) ISZERO [Var cmp] [ok];
      l = mk_inst (iid+3) ASSERT [Var ok] [];
      s1 = update_var cnt n s;
      s2 = update_var cmp (bool_to_word (max_count < w2n n)) s1;
      s3 = update_var ok (bool_to_word (~(max_count < w2n n))) s2;
      G1 = DRESTRICT G (COMPL {cnt});
      G2 = DRESTRICT G1 (COMPL {cmp});
      G3 = DRESTRICT G2 (COMPL {ok});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j s1 s2 tn1;
      tn3 = step_taint k s2 s3 tn2
  in
    step_inst_base i s = OK s1 /\
    step_inst_base j s1 = OK s2 /\
    step_inst_base k s2 = OK s3 /\
    step_inst_base l s3 =
      (if w2n n <= max_count then OK s3
       else Abort Revert_abort (revert_state (set_returndata [] s3))) /\
    ghost_step fuel ctx PG G tn i s = (G1,tn1) /\
    ghost_step fuel ctx PG G1 tn1 j s1 = (G2,tn2) /\
    ghost_step fuel ctx PG G2 tn2 k s2 = (G3,tn3) /\
    ghost_step fuel ctx PG G3 tn3 l s3 = (G3,tn3) /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    ptr_safe_step D lo fuel ctx fn PG G1 tn1 j s1 /\
    ptr_safe_step D lo fuel ctx fn PG G2 tn2 k s2 /\
    ptr_safe_step D lo fuel ctx fn PG G3 tn3 l s3 /\
    op_taint tn3 (Var ok) = {} /\ allocas_from lo s3
Proof
  rpt strip_tac >> simp[] >>
  qabbrev_tac `n = abi_decode_load DLOAD (n2w a:bytes32) s` >>
  `step_inst_base (mk_inst iid DLOAD [Var src] [cnt]) s =
     OK (update_var cnt n s)` by
    (drule prefix_dload_step >>
     disch_then (qspecl_then [`iid`,`cnt`] mp_tac) >>
     simp[Abbr `n`, abi_decode_load_def, abi_decode_source_def]) >>
  `eval_operand (Var cnt) (update_var cnt n s) = SOME n` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `allocas_from lo (update_var cnt n s) /\
   allocas_from lo (update_var cmp (bool_to_word (max_count < w2n n))
     (update_var cnt n s)) /\
   allocas_from lo (update_var ok (bool_to_word (~(max_count < w2n n)))
     (update_var cmp (bool_to_word (max_count < w2n n)) (update_var cnt n s)))` by
    (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  `eval_operand (Var cmp)
     (update_var cmp (bool_to_word (max_count < w2n n)) (update_var cnt n s)) =
     SOME (bool_to_word (max_count < w2n n)) /\
   eval_operand (Var ok)
     (update_var ok (bool_to_word (~(max_count < w2n n)))
       (update_var cmp (bool_to_word (max_count < w2n n)) (update_var cnt n s))) =
     SOME (bool_to_word (~(max_count < w2n n)))` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (iid+1) GT [Var cnt; Lit(n2w max_count)] [cmp])
     (update_var cnt n s) =
     OK (update_var cmp (bool_to_word (max_count < w2n n)) (update_var cnt n s))` by
    simp[prefix_bool_preheader_guard_dispatch, exec_pure2_def, mk_inst_def,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
         w2n_n2w, GREATER_DEF] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (Cases_on `max_count < w2n n` >>
      simp[prefix_bool_preheader_guard_dispatch, exec_pure1_def, mk_inst_def,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
           bool_to_word_def]) >>
  conj_tac
  >- (qpat_assum `eval_operand (Var ok) _ = SOME _`
        (mp_then Any (qspec_then `iid+3` mp_tac) prefix_assert_step) >>
      Cases_on `w2n n <= max_count` >> simp[bool_to_word_def]) >>
  conj_tac
  >- (qpat_assum `eval_operand (Var src) s = SOME _`
        (mp_then Any mp_tac prefix_dload_ghost_step) >>
      disch_then (qspecl_then [`iid`,`cnt`] mp_tac) >>
      simp[Abbr `n`, abi_decode_load_def, abi_decode_source_def]) >>
  conj_tac
  >- (once_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
      irule prefix_compare_ghost_step >> simp[]) >>
  conj_tac
  >- (pure_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
      irule prefix_iszero_ghost_step >>
      Cases_on `max_count < w2n n` >>
      simp[prefix_bool_preheader_guard_dispatch, exec_pure1_def, mk_inst_def,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
           bool_to_word_def]) >>
  simp[prefix_assert_ghost_step, prefix_dload_ptr_step,
       prefix_dload_output_taint, prefix_guard_output_taint,
       prefix_iszero_ptr_step, prefix_assert_ptr_step] >>
  irule prefix_compare_ptr_step >>
  simp[prefix_dload_output_taint, op_taint_def, op_prov_def,
       FLOOKUP_DRESTRICT]
QED

Theorem prefix_bool_preheader_arith_dispatch[local]:
  step_inst_base (mk_inst iid MUL ops outs) s =
    exec_pure2 $* (mk_inst iid MUL ops outs) s /\
  step_inst_base (mk_inst iid ADD ops outs) s =
    exec_pure2 $+ (mk_inst iid ADD ops outs) s
Proof
  simp[step_inst_base_def, mk_inst_def]
QED

Theorem prefix_bool_preheader_extent_guard:
  ALL_DISTINCT [src;cnt;vm;va;vend;cmp;ok] /\
  eval_operand (Var src) s = SOME (n2w a) /\
  eval_operand (Var cnt) s = SOME (n2w n) /\
  n <= max_count /\ a+32*(max_count+1) < dimword(:256) /\
  data_size < dimword(:256) ==>
  let s1 = update_var vm (n2w (n*32)) s;
      s2 = update_var va (n2w (n*32+32)) s1;
      s3 = update_var vend (n2w (a+32*(n+1))) s2;
      s4 = update_var cmp (bool_to_word (data_size < a+32*(n+1))) s3;
      s5 = update_var ok (bool_to_word (~(data_size < a+32*(n+1)))) s4
  in run_inst_seq
       [mk_inst iid MUL [Var cnt; Lit 32w] [vm];
        mk_inst (iid+1) ADD [Var vm; Lit 32w] [va];
        mk_inst (iid+2) ADD [Var src; Var va] [vend];
        mk_inst (iid+3) GT [Var vend; Lit(n2w data_size)] [cmp];
        mk_inst (iid+4) ISZERO [Var cmp] [ok];
        mk_inst (iid+5) ASSERT [Var ok] []] s =
     if a+32*(n+1) <= data_size then OK s5
     else Abort Revert_abort (revert_state (set_returndata [] s5))
Proof
  rpt strip_tac >>
  `a+32*(n+1) < dimword(:256)` by decide_tac >>
  `a+(n*32+32) = a+32*(n+1)` by decide_tac >>
  `step_inst_base (mk_inst iid MUL [Var cnt; Lit 32w] [vm]) s =
     OK (update_var vm (n2w (n*32)) s)` by
    (irule prefix_bool_body_mul_n2w >> simp[eval_operand_def]) >>
  `!v x w t. eval_operand (Var v) (update_var x w t) =
     if v = x then SOME w else eval_operand (Var v) t` by
    (rpt gen_tac >> Cases_on `v=x` >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `!w t. eval_operand (Lit w) t = SOME w` by simp[eval_operand_def] >>
  gvs[ALL_DISTINCT] >>
  simp[run_inst_seq_def, prefix_bool_preheader_arith_dispatch,
       prefix_bool_preheader_guard_dispatch, exec_pure2_def, exec_pure1_def,
       mk_inst_def, word_mul_n2w, word_add_n2w, w2n_n2w, GREATER_DEF] >>
  `a+(32*n+32) = a+32*(n+1)` by decide_tac >>
  asm_rewrite_tac[] >>
  Cases_on `a+32*(n+1) <= data_size` >>
  simp[step_inst_base_def, bool_to_word_def]
QED

Theorem prefix_bool_preheader_limit_continuation:
  eval_operand u s = SOME w /\ op_taint tn u = {} /\ op_prov G u = NONE /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ limit < dimword(:256) /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid GT [u;Lit(n2w limit)] [cmp]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (iid+1) ISZERO [Var cmp] [ok]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst (iid+2) ASSERT [Var ok] []) ==>
  let i = mk_inst iid GT [u;Lit(n2w limit)] [cmp];
      j = mk_inst (iid+1) ISZERO [Var cmp] [ok];
      s1 = update_var cmp (bool_to_word (limit < w2n w)) s;
      t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx;
      s2 = update_var ok (bool_to_word (~(limit < w2n w))) t1;
      t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx);
      G1 = DRESTRICT G (COMPL {cmp});
      G2 = DRESTRICT G1 (COMPL {ok});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j t1 s2 tn1
  in
    ((w2n w <= limit ==>
       ptr_safe_block D lo fuel ctx fn PG G2 tn2 bb
         (t2 with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx)))) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  rpt strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `step_taint i s s1 tn` >>
  qabbrev_tac `t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qmatch_goalsub_abbrev_tac `step_taint j t1 s2 tn1` >>
  qabbrev_tac `t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `eval_operand (Var cmp) t1 = SOME (bool_to_word (limit < w2n w)) /\
   eval_operand (Var ok) t2 = SOME (bool_to_word (~(limit < w2n w)))` by
    simp[Abbr `t1`, Abbr `s1`, Abbr `t2`, Abbr `s2`,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `allocas_from lo t1 /\ allocas_from lo t2` by
    (gvs[Abbr `t1`, Abbr `s1`, Abbr `t2`, Abbr `s2`,
         allocas_from_def, update_var_def] >> metis_tac[]) >>
  `op_taint tn1 (Var cmp) = {} /\
   op_taint (step_taint j t1 s2 tn1) (Var ok) = {}` by
    simp[Abbr `tn1`, Abbr `i`, Abbr `j`, prefix_guard_output_taint] >>
  `i.inst_opcode = GT /\ j.inst_opcode = ISZERO` by
    simp[Abbr `i`, Abbr `j`, mk_inst_def] >>
  `step_inst_base i s = OK s1` by
    (simp[Abbr `i`, Abbr `s1`, prefix_bool_preheader_guard_dispatch,
          exec_pure2_def, mk_inst_def, eval_operand_def, w2n_n2w, GREATER_DEF]) >>
  `step_inst_base j t1 = OK s2` by
    (Cases_on `limit < w2n w` >>
     simp[Abbr `j`, Abbr `s2`, prefix_bool_preheader_guard_dispatch,
          exec_pure1_def, mk_inst_def, bool_to_word_def]) >>
  `step_inst fuel ctx i s = OK s1 /\ step_inst fuel ctx j t1 = OK s2` by
    simp[step_inst_non_invoke] >>
  `ghost_step fuel ctx PG G tn i s = (DRESTRICT G (COMPL {cmp}),tn1)` by
    (simp[ghost_step_def, step_inst_non_invoke, Abbr `tn1`] >>
     simp[Abbr `i`, prefix_guard_prov]) >>
  `ghost_step fuel ctx PG (DRESTRICT G (COMPL {cmp})) tn1 j t1 =
     (DRESTRICT G (COMPL {cmp} INTER COMPL {ok}), step_taint j t1 s2 tn1)` by
    (simp[ghost_step_def, step_inst_non_invoke] >>
     simp[Abbr `j`, prefix_guard_prov]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s /\
   ptr_safe_step D lo fuel ctx fn PG (DRESTRICT G (COMPL {cmp})) tn1 j t1 /\
   ptr_safe_step D lo fuel ctx fn PG (DRESTRICT G (COMPL {cmp} INTER COMPL {ok}))
     (step_taint j t1 s2 tn1) (mk_inst (iid+2) ASSERT [Var ok] []) t2` by
    simp[Abbr `i`, Abbr `j`, prefix_compare_ptr_step, prefix_iszero_ptr_step,
         prefix_assert_ptr_step, op_taint_def, op_prov_def] >>
  strip_tac >> once_rewrite_tac[ptr_safe_block_def] >>
  simp[is_terminator_def] >>
  qpat_x_assum `Abbrev (t1 = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[] >>
  `t1.vs_inst_idx = SUC s.vs_inst_idx /\
   t2.vs_inst_idx = SUC (SUC s.vs_inst_idx)` by
    (qpat_assum `_ with vs_inst_idx := _ = t1` (SUBST1_TAC o SYM) >>
     simp[Abbr `t2`]) >>
  once_rewrite_tac[ptr_safe_block_def] >> simp[is_terminator_def] >>
  qpat_assum `eval_operand (Var ok) t2 = SOME _`
    (mp_then Any (qspec_then `iid+2` assume_tac) prefix_assert_step) >>
  qpat_assum `eval_operand (Var ok) t2 = SOME _`
    (mp_then Any (qspec_then `iid+2` assume_tac) prefix_assert_ghost_step) >>
  once_rewrite_tac[ptr_safe_block_def] >> simp[] >>
  simp[step_inst_non_invoke, mk_inst_def, is_terminator_def] >>
  Cases_on `w2n w <= limit` >>
  gvs[bool_to_word_def, Abbr `t2`]
QED

Theorem prefix_bool_preheader_count_continuation:
  eval_operand (Var src) s = SOME (n2w a) /\ op_taint tn (Var src) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ max_count < dimword(:256) /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid DLOAD [Var src] [cnt]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (iid+1) GT [Var cnt;Lit(n2w max_count)] [cmp]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst (iid+2) ISZERO [Var cmp] [ok]) /\
  get_instruction bb (SUC (SUC (SUC s.vs_inst_idx))) =
    SOME (mk_inst (iid+3) ASSERT [Var ok] []) ==>
  let n = abi_decode_load DLOAD (n2w a:bytes32) s;
      i = mk_inst iid DLOAD [Var src] [cnt];
      j = mk_inst (iid+1) GT [Var cnt;Lit(n2w max_count)] [cmp];
      k = mk_inst (iid+2) ISZERO [Var cmp] [ok];
      s1 = update_var cnt n s;
      t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx;
      s2 = update_var cmp (bool_to_word (max_count < w2n n)) t1;
      t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx);
      s3 = update_var ok (bool_to_word (~(max_count < w2n n))) t2;
      t3 = s3 with vs_inst_idx := SUC (SUC (SUC (SUC s.vs_inst_idx)));
      G1 = DRESTRICT G (COMPL {cnt});
      G2 = DRESTRICT G1 (COMPL {cmp});
      G3 = DRESTRICT G2 (COMPL {ok});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j t1 s2 tn1;
      tn3 = step_taint k t2 s3 tn2
  in
    ((w2n n <= max_count ==> ptr_safe_block D lo fuel ctx fn PG G3 tn3 bb t3) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  rpt strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `step_taint i s s1 tn` >>
  qabbrev_tac `t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base i s = OK s1` by
    (qpat_assum `eval_operand (Var src) s = SOME _`
       (mp_then Any (qspecl_then [`iid`,`cnt`] mp_tac) prefix_dload_step) >>
     simp[Abbr `i`, Abbr `s1`, abi_decode_load_def, abi_decode_source_def]) >>
  `i.inst_opcode = DLOAD` by simp[Abbr `i`, mk_inst_def] >>
  `step_inst fuel ctx i s = OK s1` by simp[step_inst_non_invoke] >>
  `ghost_step fuel ctx PG G tn i s =
     (DRESTRICT G (COMPL {cnt}), step_taint i s s1 tn)` by
    (simp[ghost_step_def, step_inst_non_invoke] >>
     simp[Abbr `i`, mk_inst_def, step_prov_def, out_prov_def, set_prov_def]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s` by
    simp[Abbr `i`, prefix_dload_ptr_step] >>
  strip_tac >> once_rewrite_tac[ptr_safe_block_def] >>
  simp[is_terminator_def] >>
  qpat_x_assum `Abbrev (t1 = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[] >>
  irule (BETA_RULE (REWRITE_RULE [LET_THM] prefix_bool_preheader_limit_continuation)) >>
  simp[] >>
  reverse conj_tac
  >- (qpat_assum `_ with vs_inst_idx := _ = t1` (SUBST1_TAC o SYM) >>
      simp[Abbr `s1`, allocas_from_def, update_var_def] >>
      gvs[allocas_from_def] >> metis_tac[]) >>
  qexistsl [`cmp`,`iid+1`,`max_count`,`ok`,`Var cnt`,
            `abi_decode_load DLOAD (n2w a:bytes32) s`] >>
  `t1.vs_inst_idx = SUC s.vs_inst_idx` by
    (qpat_assum `_ with vs_inst_idx := _ = t1` (SUBST1_TAC o SYM) >> simp[]) >>
  simp[Abbr `i`, prefix_dload_output_taint, op_prov_def, FLOOKUP_DRESTRICT,
       ADD_ASSOC] >>
  conj_tac
  >- (qpat_assum `_ with vs_inst_idx := _ = t1` (SUBST1_TAC o SYM) >>
      simp[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def,
           FLOOKUP_UPDATE]) >>
  strip_tac >>
  qpat_x_assum `w2n _ <= max_count ==> _` mp_tac >>
  simp[DRESTRICT_DRESTRICT, pred_setTheory.INTER_ASSOC]
QED

Theorem prefix_bool_preheader_scratch_steps:
  FLOOKUP s.vs_allocas aid = NONE /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s.vs_alloca_next+32 < dimword(:256) /\
  ~ctx_has_dalloca ctx ==>
  let a = s.vs_alloca_next;
      i = mk_inst aid ALLOCA [Lit 32w] [ip];
      j = mk_inst (aid+1) MSTORE [Var ip;Lit 0w] [];
      t = update_var ip (n2w a)
        (s with <|vs_allocas := s.vs_allocas |+ (aid,(a,32));
                  vs_alloca_next := a+32|>);
      v = mstore a 0w t;
      H = G |+ (ip,(a,32));
      q = step_taint i s t tn;
      r = step_taint j t v q
  in
    step_inst_base i s = OK t /\ step_inst_base j t = OK v /\
    ghost_step fuel ctx PG G tn i s = (H,q) /\
    ghost_step fuel ctx PG H q j t = (H,r) /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    ptr_safe_step D lo fuel ctx fn PG H q j t /\
    allocas_from lo v /\ v.vs_alloca_next = a+32 /\
    eval_operand (Var ip) v = SOME (n2w a) /\
    FLOOKUP H ip = SOME (a,32) /\ op_taint r (Var ip) = {} /\
    (!k. k < 32 ==> a+k NOTIN r.t_mem) /\
    mload a v = 0w /\ v.vs_data_section = s.vs_data_section /\
    v.vs_gas_readings = s.vs_gas_readings /\
    v.vs_allocas = s.vs_allocas |+ (aid,(a,32)) /\
    r.t_stor = tn.t_stor /\ r.t_trans = tn.t_trans /\ r.t_imm = tn.t_imm /\
    (!p len. p+len<=a \/ a+32<=p ==>
       mem_bytes_at p len v.vs_memory = mem_bytes_at p len s.vs_memory)
Proof
  rpt strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `a = s.vs_alloca_next` >>
  qmatch_goalsub_abbrev_tac `step_inst_base i s = OK t` >>
  qmatch_goalsub_abbrev_tac `step_inst_base j t = OK v` >>
  qabbrev_tac `q = step_taint i s t tn` >>
  `a < dimword(:256)` by (gvs[Abbr `a`] >> decide_tac) >>
  `step_inst_base i s = OK t` by
    simp[Abbr `i`, Abbr `t`, Abbr `a`, prefix_alloca_step] >>
  `eval_operand (Var ip) t = SOME (n2w a) /\
   eval_operand (Lit 0w) t = SOME 0w /\
   FLOOKUP (G |+ (ip,(a,32))) ip = SOME (a,32)` by
    simp[Abbr `t`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `allocas_from lo t` by
    (qspecl_then [`aid`, `32w:bytes32`, `ip`, `s`, `lo`] mp_tac
       prefix_alloca_frontier >>
     simp[Abbr `t`, Abbr `a`]) >>
  `op_taint q (Var ip) = {}` by
    simp[Abbr `q`, Abbr `i`, prefix_alloca_output_taint] >>
  `step_inst fuel ctx j t = OK v` by
    (qpat_assum `eval_operand (Var ip) t = _`
       (mp_then Any mp_tac prefix_mstore_endpoint) >>
     simp[Abbr `j`, Abbr `v`, w2n_n2w]) >>
  asm_rewrite_tac[] >>
  conj_tac >- gvs[Abbr `j`, step_inst_non_invoke, mk_inst_def] >>
  conj_tac >-
    simp[Abbr `i`, Abbr `q`, Abbr `t`, Abbr `a`, BETA_RULE (REWRITE_RULE [LET_THM] prefix_alloca_ghost_step)] >>
  conj_tac >- (gvs[Abbr `j`] >> irule prefix_mstore_ghost_step >> simp[]) >>
  conj_tac >- simp[Abbr `i`, prefix_alloca_ptr_step] >>
  conj_tac >-
    (simp[Abbr `j`] >> irule prefix_mstore_ptr_step >>
     simp[w2n_n2w, op_taint_def, FLOOKUP_UPDATE]) >>
  conj_tac >-
    (gvs[Abbr `v`, mstore_def, allocas_from_def] >> metis_tac[]) >>
  conj_tac >- simp[Abbr `v`, Abbr `t`, mstore_def, update_var_def] >>
  conj_tac >- gvs[Abbr `v`, mstore_def, eval_operand_def, lookup_var_def] >>
  conj_tac >-
    (simp[Abbr `j`, op_taint_def,
       BETA_RULE (REWRITE_RULE [LET_THM] prefix_mstore_taint_frame)] >>
     gvs[op_taint_def]) >>
  conj_tac >-
    (qpat_assum `eval_operand (Var ip) t = _`
       (mp_then Any mp_tac prefix_mstore_mem_taint) >>
     simp[Abbr `j`, Abbr `v`, w2n_n2w, op_taint_def]) >>
  `!p len. p+len<=a \/ a+32<=p ==>
     mem_bytes_at p len v.vs_memory = mem_bytes_at p len s.vs_memory` by
    (rpt strip_tac >>
     `t.vs_memory = s.vs_memory` by simp[Abbr `t`, update_var_def] >>
     qpat_x_assum `t.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     simp[Abbr `v`] >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  asm_rewrite_tac[] >>
  simp[Abbr `v`, mload_mstore_same_proof, Abbr `t`, update_var_def,
       mstore_def] >>
  simp[Abbr `j`, BETA_RULE (REWRITE_RULE [LET_THM] prefix_mstore_taint_frame)] >>
  simp[Abbr `q`, Abbr `i`, step_taint_def, mk_inst_def,
       store_taint_def, imm_taint_def, adopt_reset_def]
QED

Theorem prefix_bool_preheader_abort_uniform[local]:
  run_inst_seq is s = Abort Revert_abort v /\
  isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is ==>
  ?vh. !f. exec_block f ctx bb s = Abort Revert_abort vh
Proof
  rpt strip_tac >>
  drule_all (cj 2 exec_block_run_inst_seq) >>
  disch_then (qspecl_then [`0`,`ctx`] strip_assume_tac) >>
  qexists_tac `v with vs_inst_idx := n` >> gen_tac >>
  irule (cj 2 fuel_mono) >> simp[NoAsms] >>
  qexists_tac `0` >> simp[NoAsms] >> first_assum ACCEPT_TAC
QED

Theorem prefix_bool_preheader_fragment_lookup[local]:
  isPREFIX is (DROP k bb.bb_instructions) /\ j < LENGTH is ==>
  get_instruction bb (k+j) = SOME (EL j is)
Proof
  simp[IS_PREFIX_APPEND] >> rpt strip_tac >>
  `j < LENGTH (DROP k bb.bb_instructions)` by
    (asm_rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  `k+j < LENGTH bb.bb_instructions` by
    (gvs[LENGTH_DROP] >> decide_tac) >>
  simp[get_instruction_def] >>
  `EL j (DROP k bb.bb_instructions) = EL j is` by
    simp[EL_APPEND_EQN] >>
  gvs[EL_DROP]
QED

Theorem prefix_bool_preheader_gt_taint_frame[local]:
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  let q = step_taint (mk_inst iid GT [a;b] [x]) s t tn in
    q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
    q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm
Proof
  rpt strip_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, mem_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, DRESTRICT_UNIV,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, FLOOKUP_DEF] >>
  simp[pred_setTheory.EXTENSION, SF CONJ_ss]
QED

Theorem prefix_bool_preheader_arith_cut[local]:
  (opc = ADD \/ opc = MUL) /\
  eval_operand a s = SOME u /\ eval_operand b s = SOME v /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid opc [a;b] [x]) ==>
  ?t H q.
    (!f. exec_block f ctx bb s = exec_block f ctx bb t) /\
    ((!f. ptr_safe_block D lo f ctx fn PG H q bb t) ==>
     !f. ptr_safe_block D lo f ctx fn PG G tn bb s) /\
    t.vs_inst_idx = s.vs_inst_idx+1 /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_gas_readings = s.vs_gas_readings /\ allocas_from lo t /\
    q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
    q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
    eval_operand (Var x) t = SOME (if opc = ADD then u+v else u*v) /\
    FLOOKUP H x = (if opc = ADD then first_prov G [a;b] else NONE) /\
    op_taint q (Var x) = {} /\
    (!y. y <> x ==>
      eval_operand (Var y) t = eval_operand (Var y) s /\
      FLOOKUP H y = FLOOKUP G y /\ op_taint q (Var y) = op_taint tn (Var y))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `i = mk_inst iid opc [a;b] [x]` >>
  qabbrev_tac `r = update_var x (if opc = ADD then u+v else u*v) s` >>
  qabbrev_tac `H = set_prov G [x] (if opc = ADD then first_prov G [a;b] else NONE)` >>
  qabbrev_tac `q = step_taint i s r tn` >>
  `!f. step_inst_base i s = OK r /\ step_inst f ctx i s = OK r /\
       ptr_safe_step D lo f ctx fn PG G tn i s /\
       ghost_step f ctx PG G tn i s = (H,q)` by
    (gen_tac >>
     mp_tac (BETA_RULE (REWRITE_RULE [LET_THM] prefix_bool_body_arith_certificate)) >>
     simp[Abbr `i`, Abbr `r`, Abbr `H`, Abbr `q`]) >>
  qexistsl_tac [`r with vs_inst_idx := s.vs_inst_idx+1`,`H`,`q`] >>
  conj_tac >- suspend "execution" >>
  conj_tac >- suspend "safety" >>
  suspend "frames"
QED

Resume prefix_bool_preheader_arith_cut[execution]:
  `run_inst_seq [i] s = OK r` by simp[run_inst_seq_def] >>
  `isPREFIX [i] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[get_instruction_def, Abbr `i`] >>
     simp[Once DROP_CONS_EL]) >>
  gen_tac >>
  irule (SRULE [] (Q.SPEC `[i]` (cj 2 (cj 1 exec_block_run_inst_seq)))) >>
  qexists_tac `i` >>
  Cases_on `opc = ADD` >> gvs[Abbr `i`, mk_inst_def, is_terminator_def]
QED

Resume prefix_bool_preheader_arith_cut[safety]:
  strip_tac >> gen_tac >> once_rewrite_tac[ptr_safe_block_def] >>
  Cases_on `opc = ADD` >> gvs[Abbr `i`, mk_inst_def, is_terminator_def, ADD1]
QED

Resume prefix_bool_preheader_arith_cut[frames]:
  mp_tac (BETA_RULE (REWRITE_RULE [LET_THM] prefix_bool_body_arith_certificate)) >>
  simp[Abbr `r`, Abbr `H`, Abbr `q`, Abbr `i`, update_var_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, allocas_from_def] >>
  metis_tac[allocas_from_def]
QED

Finalise prefix_bool_preheader_arith_cut

Theorem prefix_bool_preheader_limit_cut[local]:
  isPREFIX [mk_inst iid GT [u;Lit(n2w limit)] [cmp];
    mk_inst (iid+1) ISZERO [Var cmp] [ok];
    mk_inst (iid+2) ASSERT [Var ok] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand u s = SOME w /\ op_taint tn u = {} /\ op_prov G u = NONE /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ limit < dimword(:256) ==>
  if w2n w <= limit then
    ?t H q.
      (!f. exec_block f ctx bb s = exec_block f ctx bb t) /\
      ((!f. ptr_safe_block D lo f ctx fn PG H q bb t) ==>
       !f. ptr_safe_block D lo f ctx fn PG G tn bb s) /\
      t.vs_inst_idx = s.vs_inst_idx+3 /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_gas_readings = s.vs_gas_readings /\
      allocas_from lo t /\ q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
      q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
      (!y. ~MEM y [cmp;ok] ==>
        eval_operand (Var y) t = eval_operand (Var y) s /\
        FLOOKUP H y = FLOOKUP G y /\ op_taint q (Var y) = op_taint tn (Var y))
  else ?vh. (!f. exec_block f ctx bb s = Abort Revert_abort vh) /\
       (!f. ptr_safe_block D lo f ctx fn PG G tn bb s)
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `isPREFIX is _` >>
  `!j. j < LENGTH is ==>
     get_instruction bb (s.vs_inst_idx+j) = SOME (EL j is)` by
    (rpt strip_tac >> irule prefix_bool_preheader_fragment_lookup >> simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME (EL 0 is) /\
   get_instruction bb (s.vs_inst_idx+1) = SOME (EL 1 is) /\
   get_instruction bb (s.vs_inst_idx+2) = SOME (EL 2 is)` by
    (conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `is`]) >>
     rpt conj_tac >> first_x_assum irule >> simp[Abbr `is`]) >>
  mp_tac (Q.GEN `fuel`
    (BETA_RULE (REWRITE_RULE [LET_THM]
      prefix_bool_preheader_limit_continuation))) >>
  simp[Abbr `is`, ADD1] >> strip_tac >>
  reverse (Cases_on `w2n w <= limit`)
  >- suspend "reject" >>
  suspend "accept"
QED

Resume prefix_bool_preheader_limit_cut[reject]:
  qmatch_asmsub_abbrev_tac `isPREFIX is _` >> simp[] >>
  qabbrev_tac `r = update_var ok 0w (update_var cmp 1w s)` >>
  `run_inst_seq is s = Abort Revert_abort (revert_state (set_returndata [] r))` by
    (simp[Abbr `is`, Abbr `r`, run_inst_seq_def,
          prefix_bool_preheader_guard_dispatch, exec_pure2_def, exec_pure1_def,
          mk_inst_def, eval_operand_def, w2n_n2w, GREATER_DEF,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def,
          step_inst_base_def]) >>
  `?vh. !f. exec_block f ctx bb s = Abort Revert_abort vh` by
    (irule prefix_bool_preheader_abort_uniform >>
     goal_assum (drule_at Any) >>
     simp[Abbr `is`, mk_inst_def, is_terminator_def]) >>
  qexists_tac `vh` >> simp[]
QED

Resume prefix_bool_preheader_limit_cut[accept]:
  simp[] >>
  first_assum (qspec_then `0` assume_tac) >>
  qmatch_asmsub_abbrev_tac `ptr_safe_block D lo 0 ctx fn PG H q bb t` >>
  qexistsl_tac [`t`,`H`,`q`] >>
  conj_tac >- suspend "execution" >>
  conj_tac >- metis_tac[] >>
  suspend "frames"
QED

Resume prefix_bool_preheader_limit_cut[execution]:
  qmatch_asmsub_abbrev_tac `isPREFIX is _` >>
  qabbrev_tac `r = update_var ok 1w (update_var cmp 0w s)` >>
  `run_inst_seq is s = OK r` by
    (simp[Abbr `is`, Abbr `r`, run_inst_seq_def,
          prefix_bool_preheader_guard_dispatch, exec_pure2_def, exec_pure1_def,
          mk_inst_def, eval_operand_def, w2n_n2w, GREATER_DEF,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def,
          step_inst_base_def]) >>
  `t = r with vs_inst_idx := s.vs_inst_idx+LENGTH is` by
    simp[Abbr `t`, Abbr `r`, Abbr `is`, update_var_def, bool_to_word_def] >>
  gen_tac >> asm_rewrite_tac[] >>
  irule (Q.SPEC `is` (cj 2 (cj 1 exec_block_run_inst_seq))) >>
  simp[Abbr `is`, mk_inst_def, is_terminator_def]
QED

Resume prefix_bool_preheader_limit_cut[frames]:
  rpt (qpat_x_assum `get_instruction _ _ = _` kall_tac) >>
  qpat_x_assum `!j. _` kall_tac >>
  qpat_x_assum `!fuel. _` kall_tac >>
  qpat_x_assum `(_ ==> ptr_safe_block _ _ _ _ _ _ _ _ _ _) ==> _` kall_tac >>
  qpat_x_assum `isPREFIX _ _` kall_tac >>
  gvs[Abbr `t`, Abbr `H`, update_var_def,
      eval_operand_def, lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
      allocas_from_def] >>
  simp[Abbr `q`,
       BETA_RULE (REWRITE_RULE [LET_THM] prefix_boolword_pure_taint_frame),
       BETA_RULE (REWRITE_RULE [LET_THM] prefix_bool_preheader_gt_taint_frame),
       prefix_guard_taint_other] >>
  first_assum ACCEPT_TAC
QED

Finalise prefix_bool_preheader_limit_cut

Theorem prefix_bool_preheader_extent_cut:
  isPREFIX [mk_inst iid MUL [Var cnt;Lit 32w] [vm];
    mk_inst (iid+1) ADD [Var vm;Lit 32w] [va];
    mk_inst (iid+2) ADD [Var src;Var va] [vend];
    mk_inst (iid+3) GT [Var vend;Lit(n2w data_size)] [cmp];
    mk_inst (iid+4) ISZERO [Var cmp] [ok];
    mk_inst (iid+5) ASSERT [Var ok] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ALL_DISTINCT [src;cnt;vm;va;vend;cmp;ok] /\
  eval_operand (Var src) s = SOME(n2w a) /\
  eval_operand (Var cnt) s = SOME(n2w ncount) /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var cnt) = {} /\
  FLOOKUP G src = NONE /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ncount <= max_count /\ a+32*(max_count+1) < dimword(:256) /\
  data_size < dimword(:256) ==>
  if a+32*(ncount+1) <= data_size then
    ?t H q.
      (!f. exec_block f ctx bb s = exec_block f ctx bb t) /\
      ((!f. ptr_safe_block D lo f ctx fn PG H q bb t) ==>
       !f. ptr_safe_block D lo f ctx fn PG G tn bb s) /\
      t.vs_inst_idx = s.vs_inst_idx+6 /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_gas_readings = s.vs_gas_readings /\
      allocas_from lo t /\ q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
      q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
      (!y. ~MEM y [vm;va;vend;cmp;ok] ==>
        eval_operand (Var y) t = eval_operand (Var y) s /\
        FLOOKUP H y = FLOOKUP G y /\ op_taint q (Var y) = op_taint tn (Var y))
  else ?vh. (!f. exec_block f ctx bb s = Abort Revert_abort vh) /\
       (!f. ptr_safe_block D lo f ctx fn PG G tn bb s)
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `isPREFIX is _` >>
  `!j. j < LENGTH is ==>
     get_instruction bb (s.vs_inst_idx+j) = SOME (EL j is)` by
    (rpt strip_tac >> irule prefix_bool_preheader_fragment_lookup >> simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst iid MUL [Var cnt;Lit 32w] [vm])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `is`]) >>
  `eval_operand (Lit 32w) s = SOME 32w /\ op_taint tn (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`] prefix_bool_preheader_arith_cut)) >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`]
    (qx_choose_then `s1` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `get_instruction bb s1.vs_inst_idx = SOME (mk_inst (iid+1) ADD [Var vm;Lit 32w] [va])` by
    (qpat_x_assum `!j. _` (qspec_then `1` mp_tac) >> simp[Abbr `is`]) >>
  `eval_operand (Lit 32w) s1 = SOME 32w /\ op_taint tn1 (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] prefix_bool_preheader_arith_cut)) >>
  disch_then (qspecl_then [`fn`,`PG`,`G1`,`D`]
    (qx_choose_then `s2` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  `eval_operand (Var src) s2 = SOME(n2w a) /\
   op_taint tn2 (Var src) = {} /\ FLOOKUP G2 src = NONE` by
    metis_tac[ALL_DISTINCT, MEM] >>
  `get_instruction bb s2.vs_inst_idx = SOME (mk_inst (iid+2) ADD [Var src;Var va] [vend])` by
    (qpat_x_assum `!j. _` (qspec_then `2` mp_tac) >> simp[Abbr `is`]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] prefix_bool_preheader_arith_cut)) >>
  disch_then (qspecl_then [`fn`,`PG`,`G2`,`D`]
    (qx_choose_then `s3` (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac)))) >>
  suspend "limit"
QED

Resume prefix_bool_preheader_extent_cut[limit]:
  `a+32*(ncount+1) < dimword(:256)` by decide_tac >>
  `a+(ncount*32+32) = a+32*(ncount+1)` by decide_tac >>
  `eval_operand (Var vend) s3 = SOME(n2w (a+32*(ncount+1)))` by
    simp[word_add_n2w, word_mul_n2w] >>
  `FLOOKUP G2 va = NONE /\ FLOOKUP G3 vend = NONE` by
    (gvs[first_prov_def, op_prov_def] >> simp[]) >>
  `isPREFIX [mk_inst (iid+3) GT [Var vend;Lit(n2w data_size)] [cmp];
    mk_inst (iid+3+1) ISZERO [Var cmp] [ok];
    mk_inst (iid+3+2) ASSERT [Var ok] []]
    (DROP s3.vs_inst_idx bb.bb_instructions)` by suspend "tail" >>
  `op_prov G3 (Var vend) = NONE` by simp[op_prov_def] >>
  drule_all (Q.INST [`iid` |-> `iid+3`] prefix_bool_preheader_limit_cut) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  simp[w2n_n2w] >>
  reverse (Cases_on `a+32*(ncount+1) <= data_size`) >> simp[]
  >- suspend "reject" >>
  disch_then (qx_choose_then `t` (qx_choose_then `H` (qx_choose_then `q` strip_assume_tac))) >>
  qexistsl_tac [`t`,`H`,`q`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  suspend "frames"
QED

Resume prefix_bool_preheader_extent_cut[tail]:
  `s3.vs_inst_idx = s.vs_inst_idx+3` by decide_tac >>
  `DROP s3.vs_inst_idx bb.bb_instructions =
   DROP 3 (DROP s.vs_inst_idx bb.bb_instructions)` by simp[DROP_DROP_T, ADD_COMM] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `isPREFIX is _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  simp[Abbr `is`, DROP_APPEND]
QED

Resume prefix_bool_preheader_extent_cut[reject]:
  strip_tac >> qexists_tac `vh` >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED

Resume prefix_bool_preheader_extent_cut[frames]:
  gvs[] >> rpt conj_tac >> metis_tac[]
QED

Finalise prefix_bool_preheader_extent_cut

Theorem prefix_bool_preheader_count_cut:
  isPREFIX [mk_inst iid DLOAD [Var src] [cnt];
    mk_inst (iid+1) GT [Var cnt;Lit(n2w max_count)] [cmp];
    mk_inst (iid+2) ISZERO [Var cmp] [ok];
    mk_inst (iid+3) ASSERT [Var ok] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ALL_DISTINCT [src;cnt;cmp;ok] /\
  eval_operand (Var src) s = SOME(n2w a) /\ op_taint tn (Var src) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ max_count < dimword(:256) ==>
  let ncount = w2n (abi_decode_load DLOAD (n2w a:bytes32) s) in
  if ncount <= max_count then
    ?t H q.
      (!f. exec_block f ctx bb s = exec_block f ctx bb t) /\
      ((!f. ptr_safe_block D lo f ctx fn PG H q bb t) ==>
       !f. ptr_safe_block D lo f ctx fn PG G tn bb s) /\
      t.vs_inst_idx = s.vs_inst_idx+4 /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_gas_readings = s.vs_gas_readings /\
      allocas_from lo t /\ q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
      q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
      eval_operand (Var cnt) t = SOME(n2w ncount) /\ FLOOKUP H cnt = NONE /\
      op_taint q (Var cnt) = {} /\
      (!y. ~MEM y [cnt;cmp;ok] ==>
        eval_operand (Var y) t = eval_operand (Var y) s /\
        FLOOKUP H y = FLOOKUP G y /\ op_taint q (Var y) = op_taint tn (Var y))
  else ?vh. (!f. exec_block f ctx bb s = Abort Revert_abort vh) /\
       (!f. ptr_safe_block D lo f ctx fn PG G tn bb s)
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `isPREFIX is _` >>
  qabbrev_tac `n = abi_decode_load DLOAD (n2w a:bytes32) s` >>
  simp[] >> reverse (Cases_on `w2n n <= max_count`)
  >- suspend "reject"
  >> suspend "accept"
QED

Resume prefix_bool_preheader_count_cut[reject]:
  simp[] >>
  `run_inst_seq is s = Abort Revert_abort
    (revert_state (set_returndata []
      (update_var ok 0w (update_var cmp 1w (update_var cnt n s)))))` by
    (mp_tac prefix_bool_preheader_count_guard >>
     simp[Abbr `is`, Abbr `n`, bool_to_word_def]) >>
  `?vh. !f. exec_block f ctx bb s = Abort Revert_abort vh` by
    (irule prefix_bool_preheader_abort_uniform >>
     goal_assum (drule_at Any) >>
     simp[Abbr `is`, mk_inst_def, is_terminator_def]) >>
  qexists_tac `vh` >> conj_tac >- first_assum ACCEPT_TAC >>
  `!j. j < LENGTH is ==>
     get_instruction bb (s.vs_inst_idx+j) = SOME (EL j is)` by
    (rpt strip_tac >> irule prefix_bool_preheader_fragment_lookup >> simp[]) >>
  gen_tac >>
  mp_tac (Q.INST [`fuel` |-> `f`]
    (BETA_RULE (REWRITE_RULE [LET_THM]
      prefix_bool_preheader_count_continuation))) >>
  `get_instruction bb s.vs_inst_idx = SOME (EL 0 is) /\
   get_instruction bb (s.vs_inst_idx+1) = SOME (EL 1 is) /\
   get_instruction bb (s.vs_inst_idx+2) = SOME (EL 2 is) /\
   get_instruction bb (s.vs_inst_idx+3) = SOME (EL 3 is)` by
    (conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `is`]) >>
     rpt conj_tac >> first_x_assum irule >> simp[Abbr `is`]) >>
  simp[Abbr `is`, Abbr `n`, ADD1]
QED

Resume prefix_bool_preheader_count_cut[accept]:
  simp[] >>
  `!j. j < LENGTH is ==>
     get_instruction bb (s.vs_inst_idx+j) = SOME (EL j is)` by
    (rpt strip_tac >> irule prefix_bool_preheader_fragment_lookup >> simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME (EL 0 is) /\
   get_instruction bb (s.vs_inst_idx+1) = SOME (EL 1 is) /\
   get_instruction bb (s.vs_inst_idx+2) = SOME (EL 2 is) /\
   get_instruction bb (s.vs_inst_idx+3) = SOME (EL 3 is)` by
    (conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `is`]) >>
     rpt conj_tac >> first_x_assum irule >> simp[Abbr `is`]) >>
  mp_tac (Q.GEN `fuel`
    (BETA_RULE (REWRITE_RULE [LET_THM]
      prefix_bool_preheader_count_continuation))) >>
  simp[Abbr `is`, Abbr `n`, ADD1, bool_to_word_def] >> strip_tac >>
  first_assum (qspec_then `0` assume_tac) >>
  qmatch_asmsub_abbrev_tac `ptr_safe_block D lo 0 ctx fn PG H q bb t` >>
  qexistsl_tac [`t`,`H`,`q`] >>
  conj_tac >- suspend "execution" >>
  conj_tac >- metis_tac[] >>
  suspend "frames"
QED

Resume prefix_bool_preheader_count_cut[execution]:
  qmatch_asmsub_abbrev_tac `isPREFIX is _` >>
  qabbrev_tac `r = update_var ok 1w (update_var cmp 0w
    (update_var cnt (abi_decode_load DLOAD (n2w a:bytes32) s) s))` >>
  `run_inst_seq is s = OK r` by
    (mp_tac prefix_bool_preheader_count_guard >>
     simp[Abbr `is`, Abbr `r`, bool_to_word_def]) >>
  `t = r with vs_inst_idx := s.vs_inst_idx + LENGTH is` by
    simp[Abbr `t`, Abbr `r`, Abbr `is`, update_var_def] >>
  gen_tac >> asm_rewrite_tac[] >>
  irule (Q.SPEC `is` (cj 2 (cj 1 exec_block_run_inst_seq))) >>
  simp[Abbr `is`, mk_inst_def, is_terminator_def]
QED

Resume prefix_bool_preheader_count_cut[frames]:
  rpt (qpat_x_assum `get_instruction _ _ = _` kall_tac) >>
  qpat_x_assum `!j. _` kall_tac >>
  qpat_x_assum `!fuel. _` kall_tac >>
  qpat_x_assum `ptr_safe_block _ _ _ _ _ _ _ _ _ _ ==> _` kall_tac >>
  qpat_x_assum `isPREFIX _ _` kall_tac >>
  gvs[ALL_DISTINCT, Abbr `t`, Abbr `H`, update_var_def,
      eval_operand_def, lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
      allocas_from_def] >>
  simp[Abbr `q`,
       BETA_RULE (REWRITE_RULE [LET_THM] prefix_boolword_pure_taint_frame),
       BETA_RULE (REWRITE_RULE [LET_THM] prefix_bool_preheader_gt_taint_frame),
       prefix_guard_taint_other, prefix_dload_output_taint] >>
  first_assum ACCEPT_TAC
QED

Finalise prefix_bool_preheader_count_cut

Theorem prefix_bool_preheader_guards_cut:
  isPREFIX [mk_inst iid DLOAD [Var src] [cnt];
    mk_inst (iid+1) GT [Var cnt;Lit(n2w max_count)] [cmp0];
    mk_inst (iid+2) ISZERO [Var cmp0] [ok0];
    mk_inst (iid+3) ASSERT [Var ok0] [];
    mk_inst (iid+4) MUL [Var cnt;Lit 32w] [vm];
    mk_inst (iid+5) ADD [Var vm;Lit 32w] [va];
    mk_inst (iid+6) ADD [Var src;Var va] [vend];
    mk_inst (iid+7) GT [Var vend;Lit(n2w data_size)] [cmp1];
    mk_inst (iid+8) ISZERO [Var cmp1] [ok1];
    mk_inst (iid+9) ASSERT [Var ok1] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ALL_DISTINCT [src;cnt;cmp0;ok0;vm;va;vend;cmp1;ok1] /\
  eval_operand (Var src) s = SOME(n2w a) /\ op_taint tn (Var src) = {} /\
  FLOOKUP G src = NONE /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  max_count < dimword(:256) /\ a+32*(max_count+1) < dimword(:256) /\
  data_size < dimword(:256) ==>
  let ncount = w2n (abi_decode_load DLOAD (n2w a:bytes32) s) in
  if ncount <= max_count /\ a+32*(ncount+1) <= data_size then
    ?t H q.
      (!f. exec_block f ctx bb s = exec_block f ctx bb t) /\
      ((!f. ptr_safe_block D lo f ctx fn PG H q bb t) ==>
       !f. ptr_safe_block D lo f ctx fn PG G tn bb s) /\
      t.vs_inst_idx = s.vs_inst_idx+10 /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_gas_readings = s.vs_gas_readings /\
      allocas_from lo t /\ q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
      q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
      eval_operand (Var cnt) t = SOME(n2w ncount) /\ FLOOKUP H cnt = NONE /\
      op_taint q (Var cnt) = {} /\
      (!y. ~MEM y [cnt;cmp0;ok0;vm;va;vend;cmp1;ok1] ==>
        eval_operand (Var y) t = eval_operand (Var y) s /\
        FLOOKUP H y = FLOOKUP G y /\ op_taint q (Var y) = op_taint tn (Var y))
  else ?vh. (!f. exec_block f ctx bb s = Abort Revert_abort vh) /\
       (!f. ptr_safe_block D lo f ctx fn PG G tn bb s)
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `isPREFIX is _` >>
  `isPREFIX [mk_inst iid DLOAD [Var src] [cnt];
    mk_inst (iid+1) GT [Var cnt;Lit(n2w max_count)] [cmp0];
    mk_inst (iid+2) ISZERO [Var cmp0] [ok0];
    mk_inst (iid+3) ASSERT [Var ok0] []]
    (DROP s.vs_inst_idx bb.bb_instructions)` by suspend "head" >>
  `ALL_DISTINCT [src;cnt;cmp0;ok0]` by gvs[ALL_DISTINCT] >>
  drule_all prefix_bool_preheader_count_cut >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] mp_tac) >>
  qabbrev_tac `ncount = w2n (abi_decode_load DLOAD (n2w a:bytes32) s)` >>
  simp[] >> reverse (Cases_on `ncount <= max_count`) >> simp[] >>
  disch_then (qx_choose_then `c` (qx_choose_then `Gc` (qx_choose_then `qc` strip_assume_tac))) >>
  `eval_operand (Var src) c = SOME(n2w a) /\ op_taint qc (Var src) = {} /\
   FLOOKUP Gc src = NONE` by metis_tac[ALL_DISTINCT, MEM] >>
  `ALL_DISTINCT [src;cnt;vm;va;vend;cmp1;ok1]` by gvs[ALL_DISTINCT] >>
  `isPREFIX [mk_inst (iid+4) MUL [Var cnt;Lit 32w] [vm];
    mk_inst (iid+4+1) ADD [Var vm;Lit 32w] [va];
    mk_inst (iid+4+2) ADD [Var src;Var va] [vend];
    mk_inst (iid+4+3) GT [Var vend;Lit(n2w data_size)] [cmp1];
    mk_inst (iid+4+4) ISZERO [Var cmp1] [ok1];
    mk_inst (iid+4+5) ASSERT [Var ok1] []]
    (DROP c.vs_inst_idx bb.bb_instructions)` by suspend "tail" >>
  drule_all (Q.INST [`iid` |-> `iid+4`] prefix_bool_preheader_extent_cut) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  reverse (Cases_on `a+32*(ncount+1) <= data_size`) >> simp[]
  >- metis_tac[] >>
  disch_then (qx_choose_then `t` (qx_choose_then `H` (qx_choose_then `q` strip_assume_tac))) >>
  qexistsl_tac [`t`,`H`,`q`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  suspend "frames"
QED

Resume prefix_bool_preheader_guards_cut[head]:
  qpat_x_assum `isPREFIX is _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >> simp[Abbr `is`]
QED

Resume prefix_bool_preheader_guards_cut[tail]:
  `DROP c.vs_inst_idx bb.bb_instructions =
   DROP 4 (DROP s.vs_inst_idx bb.bb_instructions)` by simp[DROP_DROP_T, ADD_COMM] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `isPREFIX is _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >> simp[Abbr `is`, DROP_APPEND]
QED

Resume prefix_bool_preheader_guards_cut[frames]:
  gvs[] >> rpt conj_tac >> metis_tac[ALL_DISTINCT, MEM]
QED

Finalise prefix_bool_preheader_guards_cut

(* An interface test: the continuation consumes only observable cut facts;
   no intermediate state expression or ghost transformer is reconstructed. *)
Theorem prefix_bool_preheader_guards_consumer[local]:
  isPREFIX [mk_inst iid DLOAD [Var src] [cnt];
    mk_inst (iid+1) GT [Var cnt;Lit(n2w max_count)] [cmp0];
    mk_inst (iid+2) ISZERO [Var cmp0] [ok0];
    mk_inst (iid+3) ASSERT [Var ok0] [];
    mk_inst (iid+4) MUL [Var cnt;Lit 32w] [vm];
    mk_inst (iid+5) ADD [Var vm;Lit 32w] [va];
    mk_inst (iid+6) ADD [Var src;Var va] [vend];
    mk_inst (iid+7) GT [Var vend;Lit(n2w data_size)] [cmp1];
    mk_inst (iid+8) ISZERO [Var cmp1] [ok1];
    mk_inst (iid+9) ASSERT [Var ok1] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ALL_DISTINCT [src;cnt;cmp0;ok0;vm;va;vend;cmp1;ok1] /\
  eval_operand (Var src) s = SOME(n2w a) /\ op_taint tn (Var src) = {} /\
  FLOOKUP G src = NONE /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  max_count < dimword(:256) /\ a+32*(max_count+1) < dimword(:256) /\
  data_size < dimword(:256) ==>
  (!t H q. t.vs_inst_idx = s.vs_inst_idx+10 /\
     allocas_from lo t /\ t.vs_allocas = s.vs_allocas /\
     eval_operand (Var src) t = SOME(n2w a) /\
     FLOOKUP H src = NONE /\ op_taint q (Var src) = {} /\
     FLOOKUP H cnt = NONE /\ op_taint q (Var cnt) = {} ==>
     !f. ptr_safe_block D lo f ctx fn PG H q bb t) ==>
  !f. ptr_safe_block D lo f ctx fn PG G tn bb s
Proof
  strip_tac >>
  drule_all prefix_bool_preheader_guards_cut >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  simp[] >>
  IF_CASES_TAC >> simp[]
  >- (disch_then (qx_choose_then `t` (qx_choose_then `H`
        (qx_choose_then `q` strip_assume_tac))) >>
      strip_tac >>
      `eval_operand (Var src) t = SOME(n2w a) /\
       FLOOKUP H src = NONE /\ op_taint q (Var src) = {}`
        by metis_tac[ALL_DISTINCT, MEM] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem prefix_bool_preheader_initialize_execution[local]:
  ALL_DISTINCT [src;dst;loaded;ip] /\
  eval_operand (Var src) s = SOME(n2w a) /\
  eval_operand (Var dst) s = SOME(n2w d) /\
  abi_decode_load DLOAD (n2w a:bytes32) s = n2w ncount /\
  d < dimword(:256) /\ s.vs_alloca_next+32 < dimword(:256) /\
  FLOOKUP s.vs_allocas (iid+2) = NONE ==>
  let l = update_var loaded (n2w ncount) s;
      t = mstore d (n2w ncount) l;
      u = update_var ip (n2w s.vs_alloca_next)
        (t with <|vs_allocas := s.vs_allocas |+ (iid+2,(s.vs_alloca_next,32));
                  vs_alloca_next := s.vs_alloca_next+32|>);
      v = mstore s.vs_alloca_next 0w u
  in
    run_inst_seq [mk_inst iid DLOAD [Var src] [loaded];
      mk_inst (iid+1) MSTORE [Var dst;Var loaded] [];
      mk_inst (iid+2) ALLOCA [Lit 32w] [ip];
      mk_inst (iid+3) MSTORE [Var ip;Lit 0w] []] s = OK v /\
    run_inst_seq [mk_inst iid DLOAD [Var src] [loaded];
      mk_inst (iid+1) MSTORE [Var dst;Var loaded] [];
      mk_inst (iid+2) ALLOCA [Lit 32w] [ip];
      mk_inst (iid+3) MSTORE [Var ip;Lit 0w] [];
      mk_inst (iid+4) JMP [Label hdr] []] s = OK (jump_to hdr v)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `l = update_var loaded (n2w ncount) s` >>
  qabbrev_tac `t = mstore d (n2w ncount) l` >>
  qabbrev_tac `u = update_var ip (n2w s.vs_alloca_next)
        (t with <|vs_allocas := s.vs_allocas |+ (iid+2,(s.vs_alloca_next,32));
                  vs_alloca_next := s.vs_alloca_next+32|>)` >>
  qabbrev_tac `v = mstore s.vs_alloca_next 0w u` >>
  `step_inst_base (mk_inst iid DLOAD [Var src] [loaded]) s = OK l` by
    (qpat_assum `eval_operand (Var src) s = _`
       (mp_then Any mp_tac prefix_dload_step) >>
     disch_then (qspecl_then [`iid`,`loaded`] mp_tac) >>
     gvs[Abbr `l`, abi_decode_load_def, abi_decode_source_def]) >>
  `eval_operand (Var dst) l = SOME(n2w d) /\
   eval_operand (Var loaded) l = SOME(n2w ncount)` by
    gvs[Abbr `l`, ALL_DISTINCT, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (iid+1) MSTORE [Var dst;Var loaded] []) l = OK t` by
    (qpat_assum `eval_operand (Var dst) l = _`
       (mp_then Any mp_tac prefix_mstore_step) >>
     disch_then drule >> disch_then (qspec_then `iid+1` mp_tac) >>
     simp[Abbr `t`, w2n_n2w]) >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas` by
    simp[Abbr `t`, Abbr `l`, mstore_def, update_var_def] >>
  `step_inst_base (mk_inst (iid+2) ALLOCA [Lit 32w] [ip]) t = OK u` by
    simp[prefix_alloca_step, Abbr `u`] >>
  `eval_operand (Var ip) u = SOME(n2w s.vs_alloca_next)` by
    simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `s.vs_alloca_next < dimword(:256)` by decide_tac >>
  `step_inst_base (mk_inst (iid+3) MSTORE [Var ip;Lit 0w] []) u = OK v` by
    (qpat_assum `eval_operand (Var ip) u = _`
       (mp_then Any mp_tac prefix_mstore_step) >>
     disch_then (qspecl_then [`iid+3`,`Lit 0w`] mp_tac) >>
     simp[Abbr `v`, eval_operand_def, w2n_n2w]) >>
  `step_inst_base (mk_inst (iid+4) JMP [Label hdr] []) v = OK (jump_to hdr v)` by
    simp[mk_inst_def, venomExecProofsTheory.step_jmp_behavior] >>
  simp[run_inst_seq_def]
QED

Theorem prefix_bool_preheader_initialize_frames[local]:
  ALL_DISTINCT [src;dst;loaded;ip] /\
  eval_operand (Var src) s = SOME(n2w a) /\
  eval_operand (Var dst) s = SOME(n2w d) /\
  d+32 <= s.vs_alloca_next /\ ~s.vs_halted /\ allocas_from lo s /\
  lo <= s.vs_alloca_next ==>
  let scratch = s.vs_alloca_next;
      l = update_var loaded (n2w ncount) s;
      t = mstore d (n2w ncount) l;
      u = update_var ip (n2w scratch)
        (t with <|vs_allocas := s.vs_allocas |+ (iid+2,(scratch,32));
                  vs_alloca_next := scratch+32|>);
      v = mstore scratch 0w u;
      h = jump_to hdr v
  in
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    eval_operand (Var src) h = SOME(n2w a) /\
    eval_operand (Var dst) h = SOME(n2w d) /\
    eval_operand (Var ip) h = SOME(n2w scratch) /\
    mload scratch h = 0w /\ mload d h = n2w ncount /\
    h.vs_data_section = s.vs_data_section /\
    h.vs_allocas = s.vs_allocas |+ (iid+2,(scratch,32)) /\
    h.vs_alloca_next = scratch+32 /\ allocas_from lo h /\
    (!p len. (p+len<=d \/ d+32<=p) /\
             (p+len<=scratch \/ scratch+32<=p) ==>
       mem_bytes_at p len h.vs_memory = mem_bytes_at p len s.vs_memory) /\
    h.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `scratch = s.vs_alloca_next` >>
  qabbrev_tac `l = update_var loaded (n2w ncount) s` >>
  qabbrev_tac `t = mstore d (n2w ncount) l` >>
  qabbrev_tac `u = update_var ip (n2w scratch)
        (t with <|vs_allocas := s.vs_allocas |+ (iid+2,(scratch,32));
                  vs_alloca_next := scratch+32|>)` >>
  qabbrev_tac `v = mstore scratch 0w u` >>
  qabbrev_tac `h = jump_to hdr v` >>
  `!p len. (p+len<=d \/ d+32<=p) /\
             (p+len<=scratch \/ scratch+32<=p) ==>
       mem_bytes_at p len h.vs_memory = mem_bytes_at p len s.vs_memory`
    by suspend "memory" >>
  `mload scratch h = 0w /\ mload d h = n2w ncount` by suspend "loads" >>
  `allocas_from lo h` by suspend "allocas" >>
  gvs[ALL_DISTINCT] >> asm_rewrite_tac[] >> rpt conj_tac >>
  simp[Abbr `h`, jump_to_def, eval_operand_def, lookup_var_def] >>
  simp[Abbr `v`, mstore_def] >>
  simp[Abbr `u`, update_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `t`, mstore_def] >>
  simp[Abbr `l`, update_var_def, FLOOKUP_UPDATE] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Resume prefix_bool_preheader_initialize_frames[memory]:
  rpt strip_tac >>
  `mem_bytes_at p len h.vs_memory = mem_bytes_at p len u.vs_memory` by
    (simp[Abbr `h`, Abbr `v`, jump_to_def] >>
     irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  `u.vs_memory = t.vs_memory` by simp[Abbr `u`, update_var_def] >>
  `l.vs_memory = s.vs_memory` by simp[Abbr `l`, update_var_def] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `l.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  simp[Abbr `t`] >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Resume prefix_bool_preheader_initialize_frames[loads]:
  `mload d (mstore scratch 0w u) = mload d u` by
    (irule mload_mstore_disjoint_proof >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> gvs[Abbr `scratch`]) >>
  `u.vs_memory = t.vs_memory /\ l.vs_memory = s.vs_memory` by
    simp[Abbr `u`, Abbr `l`, update_var_def] >>
  `!p. mload p h = mload p (mstore scratch 0w u)` by
    simp[Abbr `h`, Abbr `v`, jump_to_def, mload_def] >>
  `mload d u = mload d t` by simp[mload_def] >>
  asm_rewrite_tac[mload_mstore_same_proof] >>
  simp[Abbr `t`, mload_mstore_same_proof]
QED

Resume prefix_bool_preheader_initialize_frames[allocas]:
  simp[allocas_from_def] >>
  simp[Abbr `h`, jump_to_def] >>
  simp[Abbr `v`, mstore_def] >>
  simp[Abbr `u`, update_var_def, FLOOKUP_UPDATE] >>
  gvs[allocas_from_def, Abbr `scratch`] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Finalise prefix_bool_preheader_initialize_frames

Theorem prefix_bool_preheader_alloca_taint_frame[local]:
  let q = step_taint (mk_inst iid ALLOCA [Lit 32w] [ip]) s t tn in
    q.t_mem = tn.t_mem UNION new_site_bytes s t /\ q.t_stor = tn.t_stor /\
    q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
    (!y. y <> ip ==> op_taint q (Var y) = op_taint tn (Var y))
Proof
  simp[LET_THM, step_taint_def, mk_inst_def, store_taint_def,
       imm_taint_def, adopt_reset_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def]
QED

Theorem prefix_bool_preheader_alloca_new_bytes[local]:
  FLOOKUP s.vs_allocas aid = NONE ==>
  let a = s.vs_alloca_next;
      t = update_var ip (n2w a)
        (s with <|vs_allocas := s.vs_allocas |+ (aid,(a,32));
                  vs_alloca_next := a+32|>)
  in new_site_bytes s t = {p | a <= p /\ p < a+32}
Proof
  strip_tac >>
  simp[LET_THM, new_site_bytes_def, update_var_def,
       pred_setTheory.EXTENSION, FLOOKUP_UPDATE] >>
  gen_tac >> eq_tac
  >- (strip_tac >> Cases_on `aid = aid'` >> gvs[FLOOKUP_DEF]) >>
  strip_tac >> qexistsl_tac [`aid`,`s.vs_alloca_next`,`32`] >>
  gvs[FLOOKUP_DEF]
QED

Theorem prefix_bool_preheader_scratch_memory[local]:
  FLOOKUP s.vs_allocas aid = NONE /\
  s.vs_alloca_next+32 < dimword(:256) ==>
  let a = s.vs_alloca_next;
      t = update_var ip (n2w a)
        (s with <|vs_allocas := s.vs_allocas |+ (aid,(a,32));
                  vs_alloca_next := a+32|>);
      q = step_taint (mk_inst aid ALLOCA [Lit 32w] [ip]) s t tn;
      r = step_taint (mk_inst (aid+1) MSTORE [Var ip;Lit 0w] [])
            t (mstore a 0w t) q
  in r.t_mem = tn.t_mem DIFF {p | a <= p /\ p < a+32}
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `a = s.vs_alloca_next` >>
  qabbrev_tac `t = update_var ip (n2w a)
        (s with <|vs_allocas := s.vs_allocas |+ (aid,(a,32));
                  vs_alloca_next := a+32|>)` >>
  qabbrev_tac `q = step_taint (mk_inst aid ALLOCA [Lit 32w] [ip]) s t tn` >>
  `a < dimword(:256)` by (gvs[Abbr `a`] >> decide_tac) >>
  `eval_operand (Var ip) t = SOME(n2w a)` by
    simp[Abbr `t`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `new_site_bytes s t = {p | a <= p /\ p < a+32}` by
    (simp[Abbr `t`, Abbr `a`] >>
     irule (BETA_RULE (REWRITE_RULE [LET_THM] prefix_bool_preheader_alloca_new_bytes)) >>
     simp[]) >>
  `q.t_mem = tn.t_mem UNION {p | a <= p /\ p < a+32}` by
    simp[Abbr `q`, BETA_RULE (REWRITE_RULE [LET_THM]
      prefix_bool_preheader_alloca_taint_frame)] >>
  qpat_assum `eval_operand (Var ip) t = _`
    (mp_then Any mp_tac prefix_mstore_mem_taint) >>
  disch_then (qspecl_then [`aid+1`,`Lit 0w`,`0w`,`q`] mp_tac) >>
  simp[eval_operand_def, op_taint_def, w2n_n2w] >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem prefix_bool_preheader_initialize_paired:
  bb.bb_instructions = prefix ++
    [mk_inst iid DLOAD [Var src] [loaded];
     mk_inst (iid+1) MSTORE [Var dst;Var loaded] [];
     mk_inst (iid+2) ALLOCA [Lit 32w] [ip];
     mk_inst (iid+3) MSTORE [Var ip;Lit 0w] [];
     mk_inst (iid+4) JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ s.vs_current_bb = bb.bb_label /\
  ALL_DISTINCT [src;dst;loaded;ip] /\
  eval_operand (Var src) s = SOME(n2w a) /\
  eval_operand (Var dst) s = SOME(n2w d) /\
  abi_decode_load DLOAD (n2w a:bytes32) s = n2w ncount /\
  FLOOKUP G src = NONE /\ FLOOKUP G dst = SOME(b,sz) /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  b <= d /\ d+32 <= b+sz /\ b+sz <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s.vs_alloca_next+32 < dimword(:256) /\
  FLOOKUP s.vs_allocas (iid+2) = NONE /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?h Gh th.
    (!f. exec_block f ctx bb s = OK h) /\
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    ((!f. ptr_safe_blocks D lo f ctx fn PG
        (entry_prov fn h Gh) (entry_taint_vars fn h th) h) ==>
      !f. ptr_safe_block D lo f ctx fn PG G tn bb s) /\
    eval_operand (Var src) h = SOME(n2w a) /\
    eval_operand (Var dst) h = SOME(n2w d) /\
    eval_operand (Var ip) h = SOME(n2w s.vs_alloca_next) /\
    FLOOKUP Gh src = NONE /\ FLOOKUP Gh dst = SOME(b,sz) /\
    FLOOKUP Gh ip = SOME(s.vs_alloca_next,32) /\
    op_taint th (Var src) = {} /\ op_taint th (Var dst) = {} /\
    op_taint th (Var ip) = {} /\
    mload s.vs_alloca_next h = 0w /\ mload d h = n2w ncount /\
    (!k. k < 32 ==> d+k NOTIN th.t_mem /\ s.vs_alloca_next+k NOTIN th.t_mem) /\
    h.vs_data_section = s.vs_data_section /\
    h.vs_allocas = s.vs_allocas |+ (iid+2,(s.vs_alloca_next,32)) /\
    h.vs_alloca_next = s.vs_alloca_next+32 /\ allocas_from lo h /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p len. (p+len<=d \/ d+32<=p) /\
             (p+len<=s.vs_alloca_next \/ s.vs_alloca_next+32<=p) ==>
      mem_bytes_at p len h.vs_memory = mem_bytes_at p len s.vs_memory) /\
    h.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >>
  qabbrev_tac `l = update_var loaded (n2w ncount) s` >>
  qabbrev_tac `t = mstore d (n2w ncount) l` >>
  qabbrev_tac `u = update_var ip (n2w s.vs_alloca_next)
        (t with <|vs_allocas := s.vs_allocas |+ (iid+2,(s.vs_alloca_next,32));
                  vs_alloca_next := s.vs_alloca_next+32|>)` >>
  qabbrev_tac `v = mstore s.vs_alloca_next 0w u` >>
  qabbrev_tac `h = jump_to hdr v` >>
  qabbrev_tac `q = step_taint (mk_inst iid DLOAD [Var src] [loaded]) s l tn` >>
  qabbrev_tac `r = step_taint (mk_inst (iid+1) MSTORE [Var dst;Var loaded] []) l t q` >>
  qabbrev_tac `z = step_taint (mk_inst (iid+2) ALLOCA [Lit 32w] [ip]) t u r` >>
  qabbrev_tac `th = step_taint (mk_inst (iid+3) MSTORE [Var ip;Lit 0w] []) u v z` >>
  qabbrev_tac `Gh = DRESTRICT G (COMPL {loaded}) |+ (ip,(s.vs_alloca_next,32))` >>
  qexistsl [`h`,`Gh`,`th`] >>
  `(!f. exec_block f ctx bb s = OK h)` by suspend "execution" >>
  `((!f. ptr_safe_blocks D lo f ctx fn PG
        (entry_prov fn h Gh) (entry_taint_vars fn h th) h) ==>
      !f. ptr_safe_block D lo f ctx fn PG G tn bb s)` by suspend "safety" >>
  `op_taint th (Var src) = {} /\ op_taint th (Var dst) = {} /\
   op_taint th (Var ip) = {} /\
   th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm`
    by suspend "taint_frames" >>
  `!k. k < 32 ==> d+k NOTIN th.t_mem /\ s.vs_alloca_next+k NOTIN th.t_mem`
    by suspend "memory_clean" >>
  `d+32 <= s.vs_alloca_next` by decide_tac >>
  drule_all prefix_bool_preheader_initialize_frames >>
  disch_then (qspecl_then [`ncount`,`iid`,`hdr`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  strip_tac >>
  gvs[Abbr `h`, Abbr `v`, Abbr `u`, Abbr `t`, Abbr `l`,
      Abbr `Gh`, ALL_DISTINCT, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  first_assum ACCEPT_TAC
QED

Resume prefix_bool_preheader_initialize_paired[taint_frames]:
  `th.t_var = z.t_var /\ th.t_stor = z.t_stor /\
   th.t_trans = z.t_trans /\ th.t_imm = z.t_imm` by
    simp[Abbr `th`, BETA_RULE (REWRITE_RULE [LET_THM] prefix_mstore_taint_frame)] >>
  `r.t_var = q.t_var /\ r.t_stor = q.t_stor /\
   r.t_trans = q.t_trans /\ r.t_imm = q.t_imm` by
    simp[Abbr `r`, BETA_RULE (REWRITE_RULE [LET_THM] prefix_mstore_taint_frame)] >>
  `z.t_stor = r.t_stor /\ z.t_trans = r.t_trans /\ z.t_imm = r.t_imm /\
   (!y. y <> ip ==> op_taint z (Var y) = op_taint r (Var y))` by
    simp[Abbr `z`, BETA_RULE (REWRITE_RULE [LET_THM]
      prefix_bool_preheader_alloca_taint_frame)] >>
  `op_taint z (Var ip) = {}` by simp[Abbr `z`, prefix_alloca_output_taint] >>
  `q.t_stor = tn.t_stor /\ q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
   (!y. y <> loaded ==> op_taint q (Var y) = op_taint tn (Var y))` by
    (simp[Abbr `q`, step_taint_def, mk_inst_def, set_var_taint_def,
          store_taint_def, imm_taint_def, adopt_reset_def, op_taint_def,
          FLOOKUP_UPDATE]) >>
  `op_taint z (Var src) = {} /\ op_taint z (Var dst) = {}` by
    (gvs[ALL_DISTINCT] >>
     `op_taint r (Var src) = {} /\ op_taint r (Var dst) = {}` by
       (simp[op_taint_def] >> gvs[ALL_DISTINCT, op_taint_def]) >>
     metis_tac[]) >>
  simp[op_taint_def] >> gvs[op_taint_def]
QED
Resume prefix_bool_preheader_initialize_paired[memory_clean]:
  `d < dimword(:256)` by decide_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `t`, Abbr `l`, mstore_def, update_var_def] >>
  `eval_operand (Var dst) l = SOME(n2w d) /\
   eval_operand (Var loaded) l = SOME(n2w ncount)` by
    gvs[Abbr `l`, ALL_DISTINCT, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE] >>
  `op_taint q (Var loaded) = {}` by simp[Abbr `q`, prefix_dload_output_taint] >>
  `r.t_mem = q.t_mem DIFF {p | d <= p /\ p < d+32}` by
    (qpat_assum `eval_operand (Var dst) l = _`
      (mp_then Any mp_tac prefix_mstore_mem_taint) >>
     disch_then (qspecl_then [`iid+1`,`Var loaded`,`n2w ncount`,`q`] mp_tac) >>
     simp[w2n_n2w, Abbr `r`, Abbr `t`]) >>
  `th.t_mem = r.t_mem DIFF {p | s.vs_alloca_next <= p /\ p < s.vs_alloca_next+32}` by
    (`FLOOKUP t.vs_allocas (iid+2) = NONE` by simp[] >>
     qpat_assum `FLOOKUP t.vs_allocas (iid+2) = NONE`
       (mp_then Any mp_tac prefix_bool_preheader_scratch_memory) >>
     simp[] >> disch_then (qspecl_then [`r`,`ip`] mp_tac) >>
     simp[LET_THM, Abbr `th`, Abbr `z`, Abbr `v`, Abbr `u`, ADD_ASSOC]) >>
  simp[pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION]
QED
Resume prefix_bool_preheader_initialize_paired[execution]:
  `d < dimword(:256)` by decide_tac >>
  drule_all prefix_bool_preheader_initialize_execution >>
  disch_then (qspec_then `hdr` mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  strip_tac >>
  qabbrev_tac `is = [mk_inst iid DLOAD [Var src] [loaded];
     mk_inst (iid+1) MSTORE [Var dst;Var loaded] [];
     mk_inst (iid+2) ALLOCA [Lit 32w] [ip];
     mk_inst (iid+3) MSTORE [Var ip;Lit 0w] []]` >>
  `run_inst_seq is s = OK v` by
    gvs[Abbr `is`, Abbr `v`, Abbr `u`, Abbr `t`, Abbr `l`] >>
  `isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is` by
    simp[Abbr `is`, mk_inst_def, is_terminator_def, isPREFIX, DROP_APPEND] >>
  gen_tac >> drule_all exec_block_run_inst_seq >>
  disch_then (qspecl_then [`f`,`ctx`] mp_tac) >>
  strip_tac >>
  qpat_x_assum `!s'. run_inst_seq is s = OK s' ==> _`
    (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  `~v.vs_halted` by
    (simp[Abbr `v`, mstore_def] >>
     simp[Abbr `u`, update_var_def] >>
     simp[Abbr `t`, mstore_def] >>
     simp[Abbr `l`, update_var_def]) >>
  `jump_to hdr (v with vs_inst_idx := LENGTH prefix+4) = h` by
    simp[Abbr `h`, jump_to_def] >>
  asm_rewrite_tac[] >>
  simp[Once exec_block_def, get_instruction_def, EL_APPEND_EQN,
       Abbr `is`, step_inst_non_invoke, mk_inst_def,
       venomExecProofsTheory.step_jmp_behavior, is_terminator_def] >>
  simp[Abbr `h`, jump_to_def]
QED
Resume prefix_bool_preheader_initialize_paired[safety]:
  strip_tac >> gen_tac >>
  `d < dimword(:256)` by decide_tac >>
  `step_inst_base (mk_inst iid DLOAD [Var src] [loaded]) s = OK l` by
    (qpat_assum `eval_operand (Var src) s = _`
       (mp_then Any mp_tac prefix_dload_step) >>
     disch_then (qspecl_then [`iid`,`loaded`] mp_tac) >>
     gvs[Abbr `l`, abi_decode_load_def, abi_decode_source_def]) >>
  `s with vs_inst_idx := LENGTH prefix = s` by
    (qpat_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
  `ghost_step f ctx PG G tn (mk_inst iid DLOAD [Var src] [loaded])
      (s with vs_inst_idx := LENGTH prefix) =
      (DRESTRICT G (COMPL {loaded}),q)` by
    (simp[ghost_step_def, step_inst_non_invoke, mk_inst_def] >>
     simp[step_prov_def, out_prov_def, set_prov_def, GSYM mk_inst_def,
          Abbr `q`]) >>
  `eval_operand (Var dst) l = SOME(n2w d) /\
   eval_operand (Var loaded) l = SOME(n2w ncount) /\
   allocas_from lo l /\ l.vs_allocas = s.vs_allocas /\
   l.vs_alloca_next = s.vs_alloca_next` by
    (gvs[Abbr `l`, ALL_DISTINCT, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE, allocas_from_def] >> metis_tac[]) >>
  `op_taint q (Var dst) = {} /\ op_taint q (Var loaded) = {}` by
    (simp[Abbr `q`, prefix_dload_output_taint] >>
     gvs[ALL_DISTINCT, step_taint_def, mk_inst_def, op_taint_def,
         set_var_taint_def, out_taint_def, FLOOKUP_UPDATE]) >>
  `step_inst f ctx (mk_inst (iid+1) MSTORE [Var dst;Var loaded] [])
      (l with vs_inst_idx := LENGTH prefix+1) =
      OK (t with vs_inst_idx := LENGTH prefix+1)` by
    simp[step_inst_non_invoke, mk_inst_def,
         step_inst_base_def, exec_write2_def,
         prefix_preheader_eval_index, prefix_preheader_mstore_index,
         w2n_n2w, Abbr `t`] >>
  `ghost_step f ctx PG (DRESTRICT G (COMPL {loaded})) q
      (mk_inst (iid+1) MSTORE [Var dst;Var loaded] [])
      (l with vs_inst_idx := LENGTH prefix+1) =
      (DRESTRICT G (COMPL {loaded}),r)` by
    (drule prefix_mstore_ghost_step >>
     simp[Abbr `r`, prefix_preheader_taint_index, mk_inst_def]) >>
  `ptr_safe_step D lo f ctx fn PG (DRESTRICT G (COMPL {loaded})) q
      (mk_inst (iid+1) MSTORE [Var dst;Var loaded] [])
      (l with vs_inst_idx := LENGTH prefix+1)` by
    (irule prefix_mstore_ptr_step >>
     simp[prefix_preheader_eval_index, FLOOKUP_DRESTRICT,
          allocas_from_def, w2n_n2w] >>
     gvs[ALL_DISTINCT, allocas_from_def] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   allocas_from lo t` by
    (simp[Abbr `t`, mstore_def, allocas_from_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (iid+2) ALLOCA [Lit 32w] [ip])
      (t with vs_inst_idx := LENGTH prefix+2) =
      OK (u with vs_inst_idx := LENGTH prefix+2)` by
    simp[prefix_alloca_step, Abbr `u`, update_var_def] >>
  `step_taint (mk_inst (iid+2) ALLOCA [Lit 32w] [ip])
      (t with vs_inst_idx := LENGTH prefix+2)
      (u with vs_inst_idx := LENGTH prefix+2) r = z` by
    (simp[Abbr `z`, prefix_preheader_taint_index, mk_inst_def]) >>
  `ghost_step f ctx PG (DRESTRICT G (COMPL {loaded})) r
      (mk_inst (iid+2) ALLOCA [Lit 32w] [ip])
      (t with vs_inst_idx := LENGTH prefix+2) = (Gh,z)` by
    (`step_inst f ctx (mk_inst (iid+2) ALLOCA [Lit 32w] [ip])
        (t with vs_inst_idx := LENGTH prefix+2) =
        OK (u with vs_inst_idx := LENGTH prefix+2)` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     `(mk_inst (iid+2) ALLOCA [Lit 32w] [ip]).inst_opcode = ALLOCA` by
       simp[mk_inst_def] >>
     simp[ghost_step_def] >>
     simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
          Abbr `Gh`, Abbr `u`, update_var_def, FLOOKUP_UPDATE]) >>
  `eval_operand (Var ip) u = SOME(n2w s.vs_alloca_next) /\
   allocas_from lo u /\ op_taint z (Var ip) = {}` by
    (simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, Abbr `z`, prefix_alloca_output_taint,
          allocas_from_def] >>
     gvs[allocas_from_def] >> rpt strip_tac >>
     Cases_on `aid = iid+2` >> gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  `step_inst f ctx (mk_inst (iid+3) MSTORE [Var ip;Lit 0w] [])
      (u with vs_inst_idx := LENGTH prefix+3) =
      OK (v with vs_inst_idx := LENGTH prefix+3)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def, exec_write2_def,
         prefix_preheader_eval_index, eval_operand_def,
         prefix_preheader_mstore_index, w2n_n2w, Abbr `v`] >>
  `ghost_step f ctx PG Gh z (mk_inst (iid+3) MSTORE [Var ip;Lit 0w] [])
      (u with vs_inst_idx := LENGTH prefix+3) = (Gh,th)` by
    (drule prefix_mstore_ghost_step >>
     simp[Abbr `th`, prefix_preheader_taint_index, mk_inst_def]) >>
  `ptr_safe_step D lo f ctx fn PG Gh z
      (mk_inst (iid+3) MSTORE [Var ip;Lit 0w] [])
      (u with vs_inst_idx := LENGTH prefix+3)` by
    (`!st. eval_operand (Lit 0w) st = SOME 0w` by simp[eval_operand_def] >>
     `op_taint z (Lit 0w) = {}` by simp[op_taint_def] >>
     irule prefix_mstore_ptr_step >>
     simp[prefix_preheader_eval_index, Abbr `Gh`, FLOOKUP_UPDATE,
          w2n_n2w, allocas_from_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (iid+1) MSTORE [Var dst;Var loaded] []) l = OK t /\
   step_inst_base (mk_inst (iid+2) ALLOCA [Lit 32w] [ip]) t = OK u /\
   step_inst_base (mk_inst (iid+3) MSTORE [Var ip;Lit 0w] []) u = OK v` by
    (conj_tac
     >- simp[step_inst_base_def, exec_write2_def, mk_inst_def,
             Abbr `t`, w2n_n2w] >>
     conj_tac
     >- simp[prefix_alloca_step, Abbr `u`] >>
     `eval_operand (Lit 0w) u = SOME 0w` by simp[eval_operand_def] >>
     simp[step_inst_base_def, exec_write2_def, mk_inst_def,
          Abbr `v`, w2n_n2w]) >>
  `ptr_safe_step D lo f ctx fn PG G tn
      (mk_inst iid DLOAD [Var src] [loaded]) s` by
    simp[prefix_dload_ptr_step] >>
  `ptr_safe_step D lo f ctx fn PG (DRESTRICT G (COMPL {loaded})) r
      (mk_inst (iid+2) ALLOCA [Lit 32w] [ip])
      (t with vs_inst_idx := LENGTH prefix+2)` by
    (irule prefix_alloca_ptr_step >> simp[allocas_from_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  `l with vs_inst_idx := LENGTH prefix = l` by
    (`l.vs_inst_idx = LENGTH prefix` by simp[Abbr `l`, update_var_def] >>
     qpat_assum `l.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
  irule (cj 2 prefix_trace_ptr_safe_block) >>
  qexistsl [`\j. EL j [G;DRESTRICT G (COMPL {loaded});DRESTRICT G (COMPL {loaded});Gh;Gh]`,
             `\j. EL j [tn;q;r;z;th]`, `\j. EL j [s;l;t;u;v]`,
             `[mk_inst iid DLOAD [Var src] [loaded];
               mk_inst (iid+1) MSTORE [Var dst;Var loaded] [];
               mk_inst (iid+2) ALLOCA [Lit 32w] [ip];
               mk_inst (iid+3) MSTORE [Var ip;Lit 0w] []]`] >>
  simp_tac bool_ss [LENGTH, EL, HD, TL, ADD_0] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` by decide_tac >>
      gvs[] >> simp[step_inst_non_invoke, mk_inst_def]) >>
  simp[mk_inst_def, is_terminator_def, DROP_APPEND, isPREFIX] >>
  `jump_to hdr (v with vs_inst_idx := LENGTH prefix+4) = h` by
    simp[Abbr `h`, jump_to_def] >>
  simp[Once ptr_safe_block_def, get_instruction_def, EL_APPEND_EQN,
       step_inst_non_invoke, mk_inst_def,
       venomExecProofsTheory.step_jmp_behavior, is_terminator_def] >>
  `allocas_from lo v` by
    (simp[Abbr `v`, mstore_def, allocas_from_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       step_inst_non_invoke, venomExecProofsTheory.step_jmp_behavior,
       jump_to_def, allocas_from_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def,
       op_taint_def, Abbr `h`] >>
  gvs[allocas_from_def]
QED
Finalise prefix_bool_preheader_initialize_paired

Theorem prefix_bool_preheader_paired:
  let pre = [
        mk_inst iid DLOAD [Var src] [cnt];
        mk_inst (iid+1) GT [Var cnt; Lit(n2w max_count)] [cmp0];
        mk_inst (iid+2) ISZERO [Var cmp0] [ok0];
        mk_inst (iid+3) ASSERT [Var ok0] [];
        mk_inst (iid+4) MUL [Var cnt; Lit 32w] [vm];
        mk_inst (iid+5) ADD [Var vm; Lit 32w] [va];
        mk_inst (iid+6) ADD [Var src; Var va] [vend];
        mk_inst (iid+7) GT [Var vend; Lit(n2w data_size)] [cmp1];
        mk_inst (iid+8) ISZERO [Var cmp1] [ok1];
        mk_inst (iid+9) ASSERT [Var ok1] [];
        mk_inst (iid+10) DLOAD [Var src] [loaded];
        mk_inst (iid+11) MSTORE [Var dst; Var loaded] [];
        mk_inst (iid+12) ALLOCA [Lit 32w] [ip];
        mk_inst (iid+13) MSTORE [Var ip; Lit 0w] [];
        mk_inst (iid+14) JMP [Label hdr] []];
      scratch = s.vs_alloca_next;
      ncount = w2n (abi_decode_load DLOAD (n2w a:bytes32) s)
  in
    bb.bb_instructions = prefix ++ pre /\
    s.vs_inst_idx = LENGTH prefix /\ s.vs_current_bb = bb.bb_label /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    ALL_DISTINCT [src;dst;cnt;cmp0;ok0;vm;va;vend;cmp1;ok1;loaded;ip] /\
    eval_operand (Var src) s = SOME (n2w a) /\
    eval_operand (Var dst) s = SOME (n2w d) /\
    FLOOKUP G src = NONE /\ FLOOKUP G dst = SOME (b,sz) /\
    op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
    allocas_from lo s /\ lo <= scratch /\ scratch+32 < dimword(:256) /\
    FLOOKUP s.vs_allocas (iid+12) = NONE /\
    b <= d /\ d+32*(max_count+1) <= b+sz /\ b+sz <= scratch /\
    max_count < dimword(:256) /\ a+32*(max_count+1) < dimword(:256) /\
    data_size < dimword(:256) ==>
    (?vh. (!f. exec_block f ctx bb s = Abort Revert_abort vh) /\
       (max_count < ncount \/
        (ncount <= max_count /\ data_size < a+32*(ncount+1))) /\
       (!f. ptr_safe_block D lo f ctx fn PG G tn bb s)) \/
    (?h Gh th.
       ncount <= max_count /\ a+32*(ncount+1) <= data_size /\
       (!f. exec_block f ctx bb s = OK h) /\
       ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
       ((!f. ptr_safe_blocks D lo f ctx fn PG
          (entry_prov fn h Gh) (entry_taint_vars fn h th) h) ==>
        !f. ptr_safe_block D lo f ctx fn PG G tn bb s) /\
       eval_operand (Var src) h = SOME (n2w a) /\
       eval_operand (Var dst) h = SOME (n2w d) /\
       eval_operand (Var ip) h = SOME (n2w scratch) /\
       FLOOKUP Gh src = NONE /\ FLOOKUP Gh dst = SOME (b,sz) /\
       FLOOKUP Gh ip = SOME (scratch,32) /\
       op_taint th (Var src) = {} /\ op_taint th (Var dst) = {} /\
       op_taint th (Var ip) = {} /\
       mload scratch h = 0w /\ mload d h = n2w ncount /\
       (!k. k < 32 ==> d+k NOTIN th.t_mem /\ scratch+k NOTIN th.t_mem) /\
       h.vs_data_section = s.vs_data_section /\
       h.vs_allocas = s.vs_allocas |+ (iid+12,(scratch,32)) /\
       h.vs_alloca_next = scratch+32 /\ allocas_from lo h /\
       th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
       (!p len. (p+len<=d \/ d+32<=p) /\
                (p+len<=scratch \/ scratch+32<=p) ==>
          mem_bytes_at p len h.vs_memory = mem_bytes_at p len s.vs_memory) /\
       h.vs_gas_readings = s.vs_gas_readings)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `bb.bb_instructions = prefix ++ pre` >>
  `isPREFIX (TAKE 10 pre) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[Abbr `pre`, DROP_APPEND, isPREFIX] >>
  qunabbrev_tac `pre` >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp_tac std_ss [TAKE_cons, TAKE_0] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `bb.bb_instructions = prefix ++ pre` >>
  `ALL_DISTINCT [src;cnt;cmp0;ok0;vm;va;vend;cmp1;ok1]` by
    gvs[ALL_DISTINCT] >>
  drule_all prefix_bool_preheader_guards_cut >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  qabbrev_tac `ncount = w2n (abi_decode_load DLOAD (n2w a:bytes32) s)` >>
  simp[] >>
  reverse (Cases_on `ncount <= max_count /\ a+32*(ncount+1) <= data_size`) >>
  simp[] >>
  disch_then (qx_choose_then `t` (qx_choose_then `H`
    (qx_choose_then `q` strip_assume_tac))) >>
  `bb.bb_instructions = (prefix ++ TAKE 10 pre) ++
    [mk_inst (iid+10) DLOAD [Var src] [loaded];
     mk_inst (iid+10+1) MSTORE [Var dst;Var loaded] [];
     mk_inst (iid+10+2) ALLOCA [Lit 32w] [ip];
     mk_inst (iid+10+3) MSTORE [Var ip;Lit 0w] [];
     mk_inst (iid+10+4) JMP [Label hdr] []]` by suspend "layout" >>
  `t.vs_inst_idx = LENGTH (prefix ++ TAKE 10 pre) /\
   t.vs_current_bb = bb.bb_label /\ ~t.vs_halted /\
   ALL_DISTINCT [src;dst;loaded;ip] /\
   eval_operand (Var src) t = SOME(n2w a) /\
   eval_operand (Var dst) t = SOME(n2w d) /\
   abi_decode_load DLOAD (n2w a:bytes32) t = n2w ncount /\
   FLOOKUP H src = NONE /\ FLOOKUP H dst = SOME(b,sz) /\
   op_taint q (Var src) = {} /\ op_taint q (Var dst) = {} /\
   b <= d /\ d+32 <= b+sz /\ b+sz <= t.vs_alloca_next /\
   lo <= t.vs_alloca_next /\ t.vs_alloca_next+32 < dimword(:256) /\
   FLOOKUP t.vs_allocas (iid+10+2) = NONE` by suspend "cut_frames" >>
  drule_all prefix_bool_preheader_initialize_paired >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  disch_then (qx_choose_then `h` (qx_choose_then `Gh`
    (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl [`h`,`Gh`,`th`] >>
  suspend "compose"
QED

Resume prefix_bool_preheader_paired[layout]:
  simp[Abbr `pre`, TAKE, APPEND_ASSOC]
QED
Resume prefix_bool_preheader_paired[cut_frames]:
  `abi_decode_load DLOAD (n2w a:bytes32) t = n2w ncount` by
    simp[Abbr `ncount`, abi_decode_load_def, abi_decode_source_def] >>
  simp[Abbr `pre`, ALL_DISTINCT] >>
  rpt conj_tac >> metis_tac[ALL_DISTINCT, MEM]
QED
Resume prefix_bool_preheader_paired[compose]:
  gvs[] >> rpt conj_tac >> metis_tac[]
QED
Finalise prefix_bool_preheader_paired

val _ = export_theory();
