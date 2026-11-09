(* BoolClamp word decoder instruction boundaries. *)
Theory ctorDeployMemoryRunPtrPrefixBoolWord
Ancestors
  ctorDeployMemoryRunPtrPrefixWord ctorDeployMemoryRunPtrPrefixSequence
  ctorDeployMemoryRunPtrPrefixSteps
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  codegenRel contextCodegenRel memLocDefs finite_map words
  abiEncoder emitHelper compileEnv exprLoweringProps

Theorem prefix_shr_dispatch[local]:
  step_inst_base (mk_inst iid SHR [Lit 1w; a] [x]) s =
  exec_pure2 (\n w. word_lsr w (w2n n))
    (mk_inst iid SHR [Lit 1w; a] [x]) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_shr_step:
  eval_operand a s = SOME w ==>
  step_inst_base (mk_inst iid SHR [Lit 1w; a] [x]) s =
    OK (update_var x (word_lsr w 1) s)
Proof
  simp[prefix_shr_dispatch, exec_pure2_def, mk_inst_def, eval_operand_def]
QED

Theorem prefix_shr_ptr_step:
  op_taint tn a = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid SHR [Lit 1w; a] [x]) s
Proof
  rpt strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
       step_inst_non_invoke, prefix_shr_dispatch, mk_inst_def,
       taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, op_taint_def, eval_operand_def] >>
  Cases_on `eval_operand a s` >> simp[exec_pure2_def, mk_inst_def,
    eval_operand_def, update_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem prefix_shr_ghost_step:
  eval_operand a s = SOME w ==>
  let inst = mk_inst iid SHR [Lit 1w; a] [x];
      t = update_var x (word_lsr w 1) s
  in ghost_step fuel ctx PG G tn inst s =
    (DRESTRICT G (COMPL {x}), step_taint inst s t tn)
Proof
  rpt strip_tac >> simp[] >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_shr_step,
       mk_inst_def, step_prov_def, set_prov_def, out_prov_def,
       prefix_shr_dispatch, exec_pure2_def, eval_operand_def]
QED

Theorem prefix_bool_shr_guard:
  !w:bytes32. (word_lsr w 1 = 0w) <=> w2n w < 2
Proof
  once_rewrite_tac[GSYM w2n_11] >>
  pure_rewrite_tac[w2n_lsr, w2n_n2w] >>
  simp[arithmeticTheory.DIV_EQ_0]
QED

Theorem prefix_shr_output_clean:
  op_taint tn a = {} ==>
  op_taint (step_taint (mk_inst iid SHR [Lit 1w; a] [x]) s t tn) (Var x) = {}
Proof
  simp[op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, eval_operand_def, FLOOKUP_UPDATE, shift_taint_def,
       pred_setTheory.EXTENSION]
QED

Theorem prefix_boolword_compile:
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      id = st.cs_next_id;
      insts = [mk_inst id DLOAD [src] [x 0];
        mk_inst (id+1) SHR [Lit 1w; Var(x 0)] [x 1];
        mk_inst (id+2) ISZERO [Var(x 1)] [x 2];
        mk_inst (id+3) ASSERT [Var(x 2)] [];
        mk_inst (id+4) MSTORE [dst; Var(x 0)] []]
  in
  compile_abi_decode_static src dst DLOAD
    (\v. compile_abi_clamp_basetype v BoolClamp) st =
  ((),st with <|cs_next_id := id+5; cs_next_var := st.cs_next_var+3;
               cs_current_insts := st.cs_current_insts ++ insts|>)
Proof
  simp[compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> REFL_TAC
QED

Theorem prefix_boolword_iszero_step:
  eval_operand a s = SOME w ==>
  step_inst_base (mk_inst iid ISZERO [a] [x]) s =
    OK (update_var x (bool_to_word (w = 0w)) s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure1_def]
QED

Theorem prefix_boolword_clamp_execution:
  eval_operand (Var v) s = SOME w /\ y <> z ==>
  let s1 = update_var y (word_lsr w 1) s;
      s2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) s1
  in
    run_inst_seq
      [mk_inst iid SHR [Lit 1w; Var v] [y];
       mk_inst (iid+1) ISZERO [Var y] [z];
       mk_inst (iid+2) ASSERT [Var z] []] s =
    if w2n w < 2 then OK s2
    else Abort Revert_abort (revert_state (set_returndata [] s2))
Proof
  rpt strip_tac >> drule prefix_shr_step >>
  disch_then (qspecl_then [`y`,`iid`] assume_tac) >>
  simp[run_inst_seq_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_pure1_def,
       eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, prefix_bool_shr_guard] >>
  Cases_on `word_lsr w 1 = 0w` >>
  gvs[prefix_bool_shr_guard, bool_to_word_def]
QED

Theorem prefix_boolword_clamp_steps:
  eval_operand (Var v) s = SOME w /\ op_taint tn (Var v) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid SHR [Lit 1w; Var v] [y];
      j = mk_inst (iid+1) ISZERO [Var y] [z];
      k = mk_inst (iid+2) ASSERT [Var z] [];
      s1 = update_var y (word_lsr w 1) s;
      s2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) s1;
      G1 = DRESTRICT G (COMPL {y});
      G2 = DRESTRICT G1 (COMPL {z});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j s1 s2 tn1
  in
    step_inst_base i s = OK s1 /\
    step_inst_base j s1 = OK s2 /\
    step_inst_base k s2 =
      (if w2n w < 2 then OK s2
       else Abort Revert_abort (revert_state (set_returndata [] s2))) /\
    ghost_step fuel ctx PG G tn i s = (G1,tn1) /\
    ghost_step fuel ctx PG G1 tn1 j s1 = (G2,tn2) /\
    ghost_step fuel ctx PG G2 tn2 k s2 = (G2,tn2) /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    ptr_safe_step D lo fuel ctx fn PG G1 tn1 j s1 /\
    ptr_safe_step D lo fuel ctx fn PG G2 tn2 k s2 /\
    op_taint tn2 (Var z) = {} /\ allocas_from lo s2
Proof
  rpt strip_tac >> simp[] >>
  `eval_operand (Var y) (update_var y (word_lsr w 1) s) =
     SOME (word_lsr w 1)` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand (Var z)
     (update_var z (bool_to_word (word_lsr w 1 = 0w))
       (update_var y (word_lsr w 1) s)) =
     SOME (bool_to_word (word_lsr w 1 = 0w))` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `allocas_from lo (update_var y (word_lsr w 1) s) /\
   allocas_from lo (update_var z (bool_to_word (word_lsr w 1 = 0w))
     (update_var y (word_lsr w 1) s))` by
    (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  simp[prefix_shr_step, prefix_boolword_iszero_step,
       prefix_assert_step,
       SRULE [] prefix_shr_ghost_step, prefix_iszero_ghost_step,
       prefix_assert_ghost_step, prefix_shr_ptr_step,
       prefix_iszero_ptr_step, prefix_assert_ptr_step,
       prefix_shr_output_clean, prefix_guard_output_taint] >>
  conj_tac
  >- (drule prefix_assert_step >>
      disch_then (qspec_then `iid+2` mp_tac) >>
      simp[bool_to_word_def, prefix_bool_shr_guard] >>
      Cases_on `w2n w < 2` >> simp[bool_to_word_def]) >>
  conj_tac
  >- (qpat_assum `eval_operand (Var v) s = SOME w`
        (mp_then Any mp_tac prefix_shr_ghost_step) >> simp[]) >>
  once_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
  irule prefix_iszero_ghost_step >> simp[prefix_boolword_iszero_step]
QED

Theorem prefix_boolword_clamp_continuation:
  eval_operand (Var v) s = SOME w /\ op_taint tn (Var v) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid SHR [Lit 1w; Var v] [y]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (iid+1) ISZERO [Var y] [z]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst (iid+2) ASSERT [Var z] []) ==>
  let i = mk_inst iid SHR [Lit 1w; Var v] [y];
      j = mk_inst (iid+1) ISZERO [Var y] [z];
      s1 = update_var y (word_lsr w 1) s;
      t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx;
      s2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) t1;
      t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx);
      G1 = DRESTRICT G (COMPL {y});
      G2 = DRESTRICT G1 (COMPL {z});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j t1 s2 tn1
  in
    ((w2n w < 2 ==>
       ptr_safe_block D lo fuel ctx fn PG G2 tn2 bb
         (t2 with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx)))) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `step_taint i s s1 tn` >>
  qabbrev_tac `t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qmatch_goalsub_abbrev_tac `step_taint j t1 s2 tn1` >>
  qabbrev_tac `t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `eval_operand (Var y) t1 = SOME (word_lsr w 1)` by
    simp[Abbr `t1`, Abbr `s1`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand (Var z) t2 = SOME (bool_to_word (word_lsr w 1 = 0w))` by
    simp[Abbr `t2`, Abbr `s2`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `allocas_from lo t1 /\ allocas_from lo t2` by
    (gvs[Abbr `t1`, Abbr `s1`, Abbr `t2`, Abbr `s2`,
         allocas_from_def, update_var_def] >> metis_tac[]) >>
  `op_taint tn1 (Var y) = {}` by
    simp[Abbr `tn1`, Abbr `i`, prefix_shr_output_clean] >>
  `op_taint (step_taint j t1 s2 tn1) (Var z) = {}` by
    simp[Abbr `j`, prefix_guard_output_taint] >>
  `i.inst_opcode = SHR /\ j.inst_opcode = ISZERO` by
    simp[Abbr `i`, Abbr `j`, mk_inst_def] >>
  `step_inst fuel ctx i s = OK s1` by
    (simp[step_inst_non_invoke] >> simp[Abbr `i`, Abbr `s1`, prefix_shr_step]) >>
  `step_inst fuel ctx j t1 = OK s2` by
    (simp[step_inst_non_invoke] >>
     simp[Abbr `j`, Abbr `s2`, prefix_boolword_iszero_step]) >>
  `ghost_step fuel ctx PG G tn i s = (DRESTRICT G (COMPL {y}),tn1)` by
    (qpat_assum `eval_operand (Var v) s = SOME w`
       (mp_then Any mp_tac prefix_shr_ghost_step) >>
     simp[Abbr `i`, Abbr `s1`, Abbr `tn1`]) >>
  `ghost_step fuel ctx PG (DRESTRICT G (COMPL {y})) tn1 j t1 =
     (DRESTRICT G (COMPL {y} INTER COMPL {z}),step_taint j t1 s2 tn1)` by
    (simp[Abbr `j`] >> once_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
     irule prefix_iszero_ghost_step >>
     simp[Abbr `s2`, prefix_boolword_iszero_step]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s /\
   ptr_safe_step D lo fuel ctx fn PG (DRESTRICT G (COMPL {y})) tn1 j t1 /\
   ptr_safe_step D lo fuel ctx fn PG (DRESTRICT G (COMPL {y} INTER COMPL {z}))
     (step_taint j t1 s2 tn1) (mk_inst (iid+2) ASSERT [Var z] []) t2` by
    simp[Abbr `i`, Abbr `j`, prefix_shr_ptr_step, prefix_iszero_ptr_step,
         prefix_assert_ptr_step] >>
  strip_tac >> once_rewrite_tac[ptr_safe_block_def] >>
  simp[is_terminator_def] >>
  qpat_x_assum `Abbrev (t1 = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[] >>
  `t1.vs_inst_idx = SUC s.vs_inst_idx /\
   t2.vs_inst_idx = SUC (SUC s.vs_inst_idx)` by
    (qpat_assum `_ with vs_inst_idx := _ = t1` (SUBST1_TAC o SYM) >>
     simp[Abbr `t2`]) >>
  once_rewrite_tac[ptr_safe_block_def] >> simp[is_terminator_def] >>
  qpat_assum `eval_operand (Var z) t2 = SOME _`
    (mp_then Any (qspec_then `iid+2` assume_tac) prefix_assert_step) >>
  qpat_assum `eval_operand (Var z) t2 = SOME _`
    (mp_then Any mp_tac prefix_assert_ghost_step) >>
  disch_then (qspec_then `iid+2` assume_tac) >>
  once_rewrite_tac[ptr_safe_block_def] >> simp[] >>
  simp[step_inst_non_invoke, mk_inst_def, is_terminator_def] >>
  Cases_on `w2n w < 2` >>
  gvs[prefix_bool_shr_guard, bool_to_word_def, Abbr `t2`]
QED

Theorem prefix_boolword_execution:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z ==>
  let w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      l = update_var x w s;
      s1 = update_var y (word_lsr w 1) l;
      s2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) s1;
      xs = [mk_inst iid DLOAD [src] [x];
        mk_inst (iid+1) SHR [Lit 1w; Var x] [y];
        mk_inst (iid+2) ISZERO [Var y] [z];
        mk_inst (iid+3) ASSERT [Var z] [];
        mk_inst (iid+4) MSTORE [Var dst;Var x] []]
  in
    run_inst_seq xs s =
      (if w2n w < 2 then OK (mstore (w2n p) w s2)
       else Abort Revert_abort (revert_state (set_returndata [] s2)))
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `update_var x w s` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `s1 = update_var y (word_lsr w 1) l` >>
  qabbrev_tac `s2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) s1` >>
  `eval_operand (Var x) l = SOME w /\
   eval_operand (Var x) s2 = SOME w /\ eval_operand (Var dst) s2 = SOME p` by
    gvs[Abbr `l`, Abbr `s1`, Abbr `s2`, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst iid DLOAD [src] [x]) s = OK l` by
    simp[prefix_dload_step, Abbr `l`, Abbr `w`] >>
  once_rewrite_tac[run_inst_seq_def] >> simp[] >>
  qabbrev_tac `clamp = [mk_inst (iid+1) SHR [Lit 1w; Var x] [y];
    mk_inst (iid+2) ISZERO [Var y] [z]; mk_inst (iid+3) ASSERT [Var z] []]` >>
  `run_inst_seq clamp l =
     if w2n w < 2 then OK s2
     else Abort Revert_abort (revert_state (set_returndata [] s2))` by
    (simp[Abbr `clamp`, Abbr `s2`, Abbr `s1`] >>
     qpat_assum `eval_operand (Var x) l = SOME w`
       (mp_then Any mp_tac prefix_boolword_clamp_execution) >>
     disch_then (qspecl_then [`z`,`y`,`iid+1`] mp_tac) >> simp[]) >>
  `run_inst_seq (clamp ++ [mk_inst (iid+4) MSTORE [Var dst;Var x] []]) l =
     if w2n w < 2 then OK (mstore (w2n p) w s2)
     else Abort Revert_abort (revert_state (set_returndata [] s2))` suffices_by
    simp[Abbr `clamp`] >>
  `step_inst_base (mk_inst (iid+4) MSTORE [Var dst;Var x] []) s2 =
     OK (mstore (w2n p) w s2)` by (irule prefix_mstore_step >> simp[]) >>
  Cases_on `w2n w < 2`
  >- (gvs[] >> drule run_inst_seq_append >> disch_then (qspec_then
        `[mk_inst (iid+4) MSTORE [Var dst;Var x] []]` mp_tac) >>
      simp[run_inst_seq_def, prefix_mstore_step]) >>
  `!t. run_inst_seq clamp l <> OK t` by simp[] >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `[mk_inst (iid+4) MSTORE [Var dst;Var x] []]` mp_tac) >>
  simp[]
QED

Theorem prefix_boolword_dload_continuation:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid DLOAD [src] [x]) ==>
  let i = mk_inst iid DLOAD [src] [x];
      w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      l = update_var x w s;
      tn1 = step_taint i s l tn
  in
    (ptr_safe_block D lo fuel ctx fn PG (DRESTRICT G (COMPL {x})) tn1 bb
       (l with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `step_taint i s l tn` >>
  `i.inst_opcode = DLOAD` by simp[Abbr `i`, mk_inst_def] >>
  `step_inst_base i s = OK l` by simp[Abbr `i`, Abbr `l`, prefix_dload_step] >>
  `step_inst fuel ctx i s = OK l` by simp[step_inst_non_invoke] >>
  `ghost_step fuel ctx PG G tn i s =
     (DRESTRICT G (COMPL {x}), step_taint i s l tn)` by
    (drule prefix_dload_ghost_step >> simp[Abbr `i`, Abbr `l`]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s` by
    simp[Abbr `i`, prefix_dload_ptr_step] >>
  strip_tac >> once_rewrite_tac[ptr_safe_block_def] >> simp[is_terminator_def]
QED

Theorem prefix_boolword_mstore_continuation:
  eval_operand (Var dst) s = SOME a /\ eval_operand value s = SOME w /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n a /\ w2n a + 32 <= b+sz /\
  op_taint tn (Var dst) = {} /\ op_taint tn value = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid MSTORE [Var dst;value] []) ==>
  let i = mk_inst iid MSTORE [Var dst;value] [];
      t = mstore (w2n a) w s
  in
    (ptr_safe_block D lo fuel ctx fn PG G (step_taint i s t tn) bb
       (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `step_taint i s t tn` >>
  `i.inst_opcode = MSTORE` by simp[Abbr `i`, mk_inst_def] >>
  `step_inst_base i s = OK t` by
    (simp[Abbr `i`, Abbr `t`] >> irule prefix_mstore_step >> simp[]) >>
  `step_inst fuel ctx i s = OK t` by simp[step_inst_non_invoke] >>
  `ghost_step fuel ctx PG G tn i s = (G,step_taint i s t tn)` by
    (simp[Abbr `i`] >> irule prefix_mstore_ghost_step >>
     simp[Abbr `t`, prefix_mstore_endpoint]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s` by
    (simp[Abbr `i`] >> irule prefix_mstore_ptr_step >> metis_tac[]) >>
  strip_tac >> once_rewrite_tac[ptr_safe_block_def] >> simp[is_terminator_def]
QED

Theorem prefix_boolword_code:
  compile_abi_decode_static src dst DLOAD
    (\v. compile_abi_clamp_basetype v BoolClamp) st = ((),st') ==>
  emitted_insts st st' =
    let x = (\k. "%" ++ toString (st.cs_next_var+k)); id = st.cs_next_id
    in [mk_inst id DLOAD [src] [x 0];
        mk_inst (id+1) SHR [Lit 1w;Var (x 0)] [x 1];
        mk_inst (id+2) ISZERO [Var (x 1)] [x 2];
        mk_inst (id+3) ASSERT [Var (x 2)] [];
        mk_inst (id+4) MSTORE [dst;Var (x 0)] []]
Proof
  rpt strip_tac >> mp_tac prefix_boolword_compile >>
  simp[emitted_insts_def, listTheory.DROP_APPEND]
QED

Theorem prefix_boolword_clamp_frames:
  let s1 = update_var y (word_lsr w 1) s;
      s2 = update_var z (bool_to_word (word_lsr w 1 = 0w)) s1;
      i = mk_inst iid SHR [Lit 1w;Var v] [y];
      j = mk_inst (iid+1) ISZERO [Var y] [z];
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j s1 s2 tn1;
      G2 = DRESTRICT (DRESTRICT G (COMPL {y})) (COMPL {z})
  in
    s2.vs_memory = s.vs_memory /\ s2.vs_data_section = s.vs_data_section /\
    s2.vs_allocas = s.vs_allocas /\ s2.vs_alloca_next = s.vs_alloca_next /\
    (!a. a <> y /\ a <> z ==>
      eval_operand (Var a) s2 = eval_operand (Var a) s /\
      op_taint tn2 (Var a) = op_taint tn (Var a) /\
      FLOOKUP G2 a = FLOOKUP G a)
Proof
  simp[] >> conj_tac
  >- simp[update_var_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       prefix_guard_taint_other, FLOOKUP_DRESTRICT]
QED

Theorem prefix_boolword_pure_taint_frame:
  opc IN {MLOAD; DLOAD; LT; SHR; ISZERO} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  let q = step_taint (mk_inst iid opc ops [x]) s t tn in
    q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
    q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
    (!v. v <> x ==> op_taint q (Var v) = op_taint tn (Var v))
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, mem_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       FLOOKUP_UPDATE, DRESTRICT_UNIV, new_site_bytes_def,
       step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, FLOOKUP_DEF,
       op_taint_def] >>
  simp[pred_setTheory.EXTENSION, SF CONJ_ss, FAPPLY_FUPDATE_THM] >>
  namedCases_on `ops` ["", "a tail"] >> simp[] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "c tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[]
QED

Theorem prefix_boolword_store_taint_frame:
  eval_operand (Var dst) s = SOME p /\ eval_operand (Var x) s <> NONE /\
  op_taint tn (Var x) = {} /\ t.vs_allocas = s.vs_allocas /\
  t.vs_fmp = s.vs_fmp ==>
  let q = step_taint (mk_inst iid MSTORE [Var dst;Var x] []) s t tn in
    q.t_mem = tn.t_mem DIFF range_bytes [(w2n p,32)] /\
    q.t_stor = tn.t_stor /\ q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
    (!v. op_taint q (Var v) = op_taint tn (Var v))
Proof
  rpt strip_tac >> Cases_on `eval_operand (Var x) s` >> gvs[] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def,
    mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    new_site_bytes_def, mstore_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def,
    FLOOKUP_DRESTRICT, DRESTRICT_UNIV, fixed_source_write_range_def] >>
  gvs[op_taint_def, FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem prefix_boolword_frames:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n p /\ w2n p + 32 <= b+sz /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let k = s.vs_inst_idx;
      w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) SHR [Lit 1w;Var x] [y];
      h = mk_inst (iid+2) ISZERO [Var y] [z];
      m = mk_inst (iid+4) MSTORE [Var dst;Var x] [];
      l = update_var x w s;
      r = update_var y (word_lsr w 1) l;
      t = update_var z (bool_to_word (word_lsr w 1 = 0w)) r;
      u = mstore (w2n p) w t;
      q0 = step_taint i s l tn;
      q1 = step_taint j (l with vs_inst_idx := k+1)
                         (r with vs_inst_idx := k+1) q0;
      q2 = step_taint h (r with vs_inst_idx := k+2)
                         (t with vs_inst_idx := k+2) q1;
      q3 = step_taint m (t with vs_inst_idx := k+4)
                         (u with vs_inst_idx := k+4) q2;
      H = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})) (COMPL {z})
  in
    t.vs_memory = s.vs_memory /\ q2.t_mem = tn.t_mem /\
    q3.t_mem = tn.t_mem DIFF range_bytes [(w2n p,32)] /\
    t.vs_data_section = s.vs_data_section /\ u.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ u.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = s.vs_inst_idx /\
    q2.t_stor = tn.t_stor /\ q3.t_stor = tn.t_stor /\
    q2.t_trans = tn.t_trans /\ q3.t_trans = tn.t_trans /\
    q2.t_imm = tn.t_imm /\ q3.t_imm = tn.t_imm /\
    op_taint q2 (Var x) = {} /\ op_taint q3 (Var x) = {} /\
    (!v. v <> x /\ v <> y /\ v <> z ==>
      eval_operand (Var v) t = eval_operand (Var v) s /\
      eval_operand (Var v) u = eval_operand (Var v) s /\
      op_taint q2 (Var v) = op_taint tn (Var v) /\
      op_taint q3 (Var v) = op_taint tn (Var v) /\
      FLOOKUP H v = FLOOKUP G v)
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `update_var x w s` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `r = update_var y (word_lsr w 1) l` >>
  qabbrev_tac `t = update_var z (bool_to_word (word_lsr w 1 = 0w)) r` >>
  qabbrev_tac `u = mstore (w2n p) w t` >>
  qabbrev_tac `q0 = step_taint (mk_inst iid DLOAD [src] [x]) s l tn` >>
  qabbrev_tac `q1 = step_taint (mk_inst (iid+1) SHR [Lit 1w;Var x] [y])
    (l with vs_inst_idx := s.vs_inst_idx+1)
    (r with vs_inst_idx := s.vs_inst_idx+1) q0` >>
  qabbrev_tac `q2 = step_taint (mk_inst (iid+2) ISZERO [Var y] [z])
    (r with vs_inst_idx := s.vs_inst_idx+2)
    (t with vs_inst_idx := s.vs_inst_idx+2) q1` >>
  qabbrev_tac `q3 = step_taint (mk_inst (iid+4) MSTORE [Var dst;Var x] [])
    (t with vs_inst_idx := s.vs_inst_idx+4)
    (u with vs_inst_idx := s.vs_inst_idx+4) q2` >>
  `op_taint q2 (Var x) = {}` by
    simp[Abbr `q2`, Abbr `q1`, Abbr `q0`, prefix_guard_taint_other,
         prefix_dload_output_taint] >>
  `eval_operand (Var dst) (t with vs_inst_idx := s.vs_inst_idx+4) = SOME p /\
   eval_operand (Var x) (t with vs_inst_idx := s.vs_inst_idx+4) = SOME w` by
    gvs[Abbr `t`, Abbr `r`, Abbr `l`, update_var_def,
        eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `q3.t_mem = q2.t_mem DIFF range_bytes [(w2n p,32)]` by
    (simp[Abbr `q3`] >>
     irule (cj 1 (SRULE [LET_THM] prefix_boolword_store_taint_frame)) >>
     simp[Abbr `u`, mstore_def]) >>
  simp[Abbr `q3`, SRULE [LET_THM] prefix_boolword_store_taint_frame,
       Abbr `u`, mstore_def] >>
  simp[Abbr `q2`, Abbr `q1`, Abbr `q0`,
       SRULE [LET_THM] prefix_boolword_pure_taint_frame,
       Abbr `t`, Abbr `r`, Abbr `l`, update_var_def,
       prefix_guard_taint_other, prefix_dload_output_taint,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem prefix_boolword_instruction[local]:
  isPREFIX xs (DROP k bb.bb_instructions) /\ n < LENGTH xs ==>
  get_instruction bb (k+n) = SOME (EL n xs)
Proof
  rpt strip_tac >> gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  `LENGTH (DROP k bb.bb_instructions) = LENGTH xs + LENGTH l` by
    metis_tac[listTheory.LENGTH_APPEND] >>
  `n < LENGTH (DROP k bb.bb_instructions)` by decide_tac >>
  `k+n < LENGTH bb.bb_instructions` by gvs[listTheory.LENGTH_DROP] >>
  simp[get_instruction_def] >>
  qspecl_then [`n`,`k`,`bb.bb_instructions`] mp_tac listTheory.EL_DROP >>
  simp[rich_listTheory.EL_APPEND1, arithmeticTheory.ADD_COMM]
QED

Theorem prefix_boolword_index_updates[local]:
  update_var v w (s with vs_inst_idx := k) =
    (update_var v w s) with vs_inst_idx := k /\
  mstore off w (s with vs_inst_idx := k) =
    (mstore off w s) with vs_inst_idx := k
Proof
  simp[update_var_def, mstore_def]
QED

Theorem prefix_boolword_ptr:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n p /\ w2n p + 32 <= b+sz /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let k = s.vs_inst_idx;
      w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) SHR [Lit 1w;Var x] [y];
      h = mk_inst (iid+2) ISZERO [Var y] [z];
      c = mk_inst (iid+3) ASSERT [Var z] [];
      m = mk_inst (iid+4) MSTORE [Var dst;Var x] [];
      l = update_var x w s;
      r = update_var y (word_lsr w 1) l;
      t = update_var z (bool_to_word (word_lsr w 1 = 0w)) r;
      u = mstore (w2n p) w t;
      q0 = step_taint i s l tn;
      q1 = step_taint j (l with vs_inst_idx := k+1)
                         (r with vs_inst_idx := k+1) q0;
      q2 = step_taint h (r with vs_inst_idx := k+2)
                         (t with vs_inst_idx := k+2) q1;
      q3 = step_taint m (t with vs_inst_idx := k+4)
                         (u with vs_inst_idx := k+4) q2;
      H = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})) (COMPL {z})
  in
    isPREFIX [i;j;h;c;m] (DROP k bb.bb_instructions) ==>
    (run_inst_seq [i;j;h;c;m] s =
      (if w2n w < 2 then OK u
       else Abort Revert_abort (revert_state (set_returndata [] t)))) /\
    ((w2n w < 2 ==> ptr_safe_block D lo fuel ctx fn PG H q3 bb
       (u with vs_inst_idx := k+5)) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  rpt strip_tac >> simp[] >> strip_tac >>
  conj_tac
  >- (irule (SRULE [LET_THM] prefix_boolword_execution) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `update_var x w s` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `r = update_var y (word_lsr w 1) l` >>
  qabbrev_tac `t = update_var z (bool_to_word (word_lsr w 1 = 0w)) r` >>
  qabbrev_tac `u = mstore (w2n p) w t` >>
  `!n. n < 5 ==> get_instruction bb (s.vs_inst_idx+n) =
    SOME (EL n [mk_inst iid DLOAD [src] [x];
      mk_inst (iid+1) SHR [Lit 1w;Var x] [y];
      mk_inst (iid+2) ISZERO [Var y] [z];
      mk_inst (iid+3) ASSERT [Var z] [];
      mk_inst (iid+4) MSTORE [Var dst;Var x] []])` by
    (rpt strip_tac >> irule prefix_boolword_instruction >> simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst iid DLOAD [src] [x])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_assum `Abbrev (w = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (l = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  strip_tac >> drule_all prefix_boolword_dload_continuation >>
  simp[LET_THM, arithmeticTheory.ADD1] >> disch_then irule >>
  qabbrev_tac `q0 = step_taint (mk_inst iid DLOAD [src] [x]) s l tn` >>
  qabbrev_tac `l1 = l with vs_inst_idx := s.vs_inst_idx+1` >>
  `eval_operand (Var x) l1 = SOME w /\ op_taint q0 (Var x) = {} /\
   allocas_from lo l1` by
    (simp[Abbr `l1`, Abbr `q0`, prefix_dload_output_taint] >>
     gvs[Abbr `l`, update_var_def, eval_operand_def, lookup_var_def,
         FLOOKUP_UPDATE, allocas_from_def] >> metis_tac[]) >>
  `get_instruction bb l1.vs_inst_idx =
      SOME (mk_inst (iid+1) SHR [Lit 1w;Var x] [y]) /\
   get_instruction bb (SUC l1.vs_inst_idx) =
      SOME (mk_inst (iid+2) ISZERO [Var y] [z]) /\
   get_instruction bb (SUC (SUC l1.vs_inst_idx)) =
      SOME (mk_inst (iid+3) ASSERT [Var z] [])` by
    simp[Abbr `l1`, arithmeticTheory.ADD1] >>
  qpat_assum `eval_operand (Var x) l1 = SOME w`
    (mp_then Any mp_tac prefix_boolword_clamp_continuation) >>
  simp[LET_THM, arithmeticTheory.ADD1] >> disch_then irule >> simp[] >>
  qexistsl [`iid+1`,`y`,`z`] >>
  simp[GSYM arithmeticTheory.ADD1] >>
  qpat_assum `Abbrev (r = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (t = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  simp[Abbr `l1`, prefix_boolword_index_updates, arithmeticTheory.ADD1] >>
  strip_tac >>
  qabbrev_tac `q1 = step_taint (mk_inst (iid+1) SHR [Lit 1w;Var x] [y])
    (l with vs_inst_idx := s.vs_inst_idx+1)
    (r with vs_inst_idx := s.vs_inst_idx+1) q0` >>
  qabbrev_tac `q2 = step_taint (mk_inst (iid+2) ISZERO [Var y] [z])
    (r with vs_inst_idx := s.vs_inst_idx+2)
    (t with vs_inst_idx := s.vs_inst_idx+2) q1` >>
  qabbrev_tac `H = DRESTRICT G (COMPL {x} INTER (COMPL {y} INTER COMPL {z}))` >>
  qabbrev_tac `t4 = t with vs_inst_idx := s.vs_inst_idx+4` >>
  `eval_operand (Var dst) t4 = SOME p /\ eval_operand (Var x) t4 = SOME w /\
   op_taint q2 (Var dst) = {} /\ op_taint q2 (Var x) = {} /\
   FLOOKUP H dst = SOME (b,sz) /\ allocas_from lo t4 /\
   get_instruction bb t4.vs_inst_idx =
     SOME (mk_inst (iid+4) MSTORE [Var dst;Var x] [])` by
    (simp[Abbr `t4`, Abbr `H`, FLOOKUP_DRESTRICT,
          Abbr `q2`, Abbr `q1`, Abbr `q0`, prefix_guard_taint_other,
          prefix_dload_output_taint] >>
     gvs[Abbr `t`, Abbr `r`, Abbr `l`, update_var_def,
         eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, allocas_from_def] >>
     metis_tac[]) >>
  drule_all prefix_boolword_mstore_continuation >>
  simp[LET_THM] >> disch_then irule >>
  simp[Abbr `t4`, prefix_boolword_index_updates, Abbr `u`, arithmeticTheory.ADD1]
QED

Theorem prefix_decoder_boolword_ptr:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) hi (DecPrimWord BoolClamp) st = ((),st') /\
  x = "%" ++ toString st.cs_next_var /\
  y = "%" ++ toString (st.cs_next_var+1) /\
  z = "%" ++ toString (st.cs_next_var+2) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n p /\ w2n p + 32 <= b+sz /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let k = s.vs_inst_idx;
      iid = st.cs_next_id;
      w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) SHR [Lit 1w;Var x] [y];
      h = mk_inst (iid+2) ISZERO [Var y] [z];
      m = mk_inst (iid+4) MSTORE [Var dst;Var x] [];
      l = update_var x w s;
      r = update_var y (word_lsr w 1) l;
      t = update_var z (bool_to_word (word_lsr w 1 = 0w)) r;
      u = mstore (w2n p) w t;
      q0 = step_taint i s l tn;
      q1 = step_taint j (l with vs_inst_idx := k+1)
                         (r with vs_inst_idx := k+1) q0;
      q2 = step_taint h (r with vs_inst_idx := k+2)
                         (t with vs_inst_idx := k+2) q1;
      q3 = step_taint m (t with vs_inst_idx := k+4)
                         (u with vs_inst_idx := k+4) q2;
      H = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})) (COMPL {z})
  in
    (run_inst_seq (emitted_insts st st') s =
      (if w2n w < 2 then OK u
       else Abort Revert_abort (revert_state (set_returndata [] t)))) /\
    (t.vs_memory = s.vs_memory /\ q2.t_mem = tn.t_mem /\
     q3.t_mem = tn.t_mem DIFF range_bytes [(w2n p,32)] /\
     t.vs_data_section = s.vs_data_section /\ u.vs_data_section = s.vs_data_section /\
     t.vs_allocas = s.vs_allocas /\ u.vs_allocas = s.vs_allocas /\
     t.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = s.vs_alloca_next /\
     t.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = s.vs_current_bb /\
     t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = s.vs_inst_idx /\
     q2.t_stor = tn.t_stor /\ q3.t_stor = tn.t_stor /\
     q2.t_trans = tn.t_trans /\ q3.t_trans = tn.t_trans /\
     q2.t_imm = tn.t_imm /\ q3.t_imm = tn.t_imm /\
     op_taint q2 (Var x) = {} /\ op_taint q3 (Var x) = {} /\
     (!v. v <> x /\ v <> y /\ v <> z ==>
       eval_operand (Var v) t = eval_operand (Var v) s /\
       eval_operand (Var v) u = eval_operand (Var v) s /\
       op_taint q2 (Var v) = op_taint tn (Var v) /\
       op_taint q3 (Var v) = op_taint tn (Var v) /\
       FLOOKUP H v = FLOOKUP G v)) /\
    ((w2n w < 2 ==> !fuel. ptr_safe_run D lo fuel ctx fn PG H q3
        (u with vs_inst_idx := k+5)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  rpt gen_tac >> strip_tac >>
  `emitted_insts st st' =
    [mk_inst st.cs_next_id DLOAD [src] [x];
     mk_inst (st.cs_next_id+1) SHR [Lit 1w;Var x] [y];
     mk_inst (st.cs_next_id+2) ISZERO [Var y] [z];
     mk_inst (st.cs_next_id+3) ASSERT [Var z] [];
     mk_inst (st.cs_next_id+4) MSTORE [Var dst;Var x] []]` by
    (gvs[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def] >> drule prefix_boolword_code >> simp[]) >>
  qpat_x_assum `x = _` kall_tac >>
  qpat_x_assum `y = _` kall_tac >>
  qpat_x_assum `z = _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` kall_tac >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule (SRULE [LET_THM] prefix_boolword_execution) >> simp[]) >>
  conj_tac
  >- (simp[] >> match_mp_tac (SRULE [LET_THM] prefix_boolword_frames) >> metis_tac[]) >>
  strip_tac >> gen_tac >>
  qmatch_asmsub_abbrev_tac `mstore (w2n p) w t` >>
  qabbrev_tac `u = mstore (w2n p) w t` >>
  `u.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `u`, Abbr `t`, update_var_def, mstore_def] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  pure_asm_rewrite_tac[] >> strip_tac >>
  qpat_assum `isPREFIX _ _`
    (mp_then Any mp_tac (SRULE [LET_THM, Excl "isPREFIX"] prefix_boolword_ptr)) >>
  disch_then (mp_tac o cj 2) >>
  simp[ptr_safe_run_def] >> disch_then irule >>
  simp[] >> strip_tac >>
  qpat_x_assum `w2n w < 2 ==> _` mp_tac >>
  simp[ptr_safe_run_def]
QED

val _ = export_theory();
