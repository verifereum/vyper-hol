(* Finite pure clamp instruction interfaces. *)
Theory ctorDeployMemoryRunPtrPrefixScalarClamps
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunPtrPrefixScalarPackage ctorDeployMemoryRunPtrPrefixScalarBool
  ctorDeployMemoryRunPtrPrefixBoolWord ctorDeployMemoryRunPtrPrefixSteps
  abiEncoder emitHelper compileEnv exprLoweringProps
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  finite_map words list pred_set memLocDefs codegenRel contextCodegenRel fragExec

Theorem prefix_scalar_shift_step:
  eval_operand a s = SOME w ==>
  step_inst_base (mk_inst iid SHR [Lit k; a] [x]) s =
    OK (update_var x (word_lsr w (w2n k)) s) /\
  step_inst_base (mk_inst iid SHL [Lit k; a] [x]) s =
    OK (update_var x (word_lsl w (w2n k)) s) /\
  step_inst_base (mk_inst iid SIGNEXTEND [Lit k; a] [x]) s =
    OK (update_var x (sign_extend k w) s)
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[] >>
  simp[exec_pure2_def, eval_operand_def]
QED

Theorem prefix_scalar_eq_step:
  eval_operand a s = SOME w /\ eval_operand b s = SOME v ==>
  step_inst_base (mk_inst iid EQ [a;b] [x]) s =
    OK (update_var x (bool_to_word (w = v)) s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def]
QED

Theorem prefix_scalar_shift_clean:
  op_taint tn a = {} ==>
  op_taint (step_taint (mk_inst iid SHR [Lit k;a] [x]) s t tn) (Var x) = {} /\
  op_taint (step_taint (mk_inst iid SHL [Lit k;a] [x]) s t tn) (Var x) = {} /\
  op_taint (step_taint (mk_inst iid SIGNEXTEND [Lit k;a] [x]) s t tn) (Var x) = {}
Proof
  simp[op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, eval_operand_def, FLOOKUP_UPDATE, shift_taint_def, EXTENSION]
QED

Theorem prefix_scalar_eq_clean:
  op_taint tn a = {} /\ op_taint tn b = {} ==>
  op_taint (step_taint (mk_inst iid EQ [a;b] [x]) s t tn) (Var x) = {}
Proof
  simp[op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, eval_operand_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem prefix_scalar_pure_dispatch[local]:
  step_inst_base (mk_inst iid SHR ops outs) s =
    exec_pure2 (\n w. word_lsr w (w2n n)) (mk_inst iid SHR ops outs) s /\
  step_inst_base (mk_inst iid SHL ops outs) s =
    exec_pure2 (\n w. word_lsl w (w2n n)) (mk_inst iid SHL ops outs) s /\
  step_inst_base (mk_inst iid SIGNEXTEND ops outs) s =
    exec_pure2 sign_extend (mk_inst iid SIGNEXTEND ops outs) s /\
  step_inst_base (mk_inst iid EQ ops outs) s =
    exec_pure2 (\a b. bool_to_word (a = b)) (mk_inst iid EQ ops outs) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_scalar_shift_ptr:
  (opc = SHR \/ opc = SHL \/ opc = SIGNEXTEND) /\
  op_taint tn a = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid opc [Lit k;a] [x]) s
Proof
  strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
       step_inst_non_invoke, mk_inst_def,
       taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, op_taint_def, eval_operand_def] >>
  gvs[] >>
  Cases_on `eval_operand a s` >>
  pure_rewrite_tac[SRULE [mk_inst_def] prefix_scalar_pure_dispatch] >>
  simp[exec_pure2_def, eval_operand_def, update_var_def] >>
  rpt strip_tac >> gvs[op_taint_def] >>
  Cases_on `op = Lit k` >> gvs[] >> Cases_on `op = a` >> gvs[]
QED

Theorem prefix_scalar_eq_ptr:
  op_taint tn a = {} /\ op_taint tn b = {} /\
  (!u. a = Var u \/ b = Var u ==> FLOOKUP G u = NONE) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid EQ [a;b] [x]) s
Proof
  strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
       step_inst_non_invoke, mk_inst_def,
       taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand b s` >>
  pure_rewrite_tac[SRULE [mk_inst_def] prefix_scalar_pure_dispatch] >>
  simp[exec_pure2_def, update_var_def] >>
  (conj_tac
   >- (rpt strip_tac >>
       `FLOOKUP G u = NONE /\ FLOOKUP G w = NONE` by metis_tac[] >>
       gvs[FLOOKUP_DEF]) >>
   metis_tac[])
QED

Theorem prefix_scalar_int_compile:
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      id = st.cs_next_id;
      insts = [mk_inst id DLOAD [src] [x 0];
        mk_inst (id+1) (if signed then SIGNEXTEND else SHR)
          [Lit (n2w (if signed then bits DIV 8-1 else bits)); Var(x 0)] [x 1];
        (if signed then mk_inst (id+2) EQ [Var(x 0); Var(x 1)] [x 2]
         else mk_inst (id+2) ISZERO [Var(x 1)] [x 2]);
        mk_inst (id+3) ASSERT [Var(x 2)] [];
        mk_inst (id+4) MSTORE [dst; Var(x 0)] []]
  in
  compile_abi_decode_static src dst DLOAD
    (\v. compile_abi_clamp_basetype v (IntClamp bits signed)) st =
  ((),st with <|cs_next_id := id+5; cs_next_var := st.cs_next_var+3;
               cs_current_insts := st.cs_current_insts ++ insts|>)
Proof
  Cases_on `signed` >>
  simp[compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
       compile_abi_int_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC
QED

Theorem prefix_scalar_bytes_compile:
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      id = st.cs_next_id;
      insts = [mk_inst id DLOAD [src] [x 0];
        mk_inst (id+1) SHL [Lit (n2w (m*8)); Var(x 0)] [x 1];
        mk_inst (id+2) ISZERO [Var(x 1)] [x 2];
        mk_inst (id+3) ASSERT [Var(x 2)] [];
        mk_inst (id+4) MSTORE [dst; Var(x 0)] []]
  in
  compile_abi_decode_static src dst DLOAD
    (\v. compile_abi_clamp_basetype v (BytesMClamp m)) st =
  ((),st with <|cs_next_id := id+5; cs_next_var := st.cs_next_var+3;
               cs_current_insts := st.cs_current_insts ++ insts|>)
Proof
  simp[compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
       compile_abi_bytes_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC
QED

Theorem prefix_scalar_pure_taint_frame:
  opc IN {SHR;SHL;SIGNEXTEND;EQ;ISZERO} /\
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
  simp[EXTENSION, SF CONJ_ss, FAPPLY_FUPDATE_THM] >>
  namedCases_on `ops` ["", "a tail"] >> simp[] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "c tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[]
QED

Theorem prefix_scalar_shift_ghost:
  eval_operand a s = SOME w ==>
  ghost_step fuel ctx PG G tn (mk_inst iid SHR [Lit k;a] [x]) s =
    (DRESTRICT G (COMPL {x}), step_taint (mk_inst iid SHR [Lit k;a] [x])
       s (update_var x (word_lsr w (w2n k)) s) tn) /\
  ghost_step fuel ctx PG G tn (mk_inst iid SHL [Lit k;a] [x]) s =
    (DRESTRICT G (COMPL {x}), step_taint (mk_inst iid SHL [Lit k;a] [x])
       s (update_var x (word_lsl w (w2n k)) s) tn) /\
  ghost_step fuel ctx PG G tn (mk_inst iid SIGNEXTEND [Lit k;a] [x]) s =
    (DRESTRICT G (COMPL {x}), step_taint (mk_inst iid SIGNEXTEND [Lit k;a] [x])
       s (update_var x (sign_extend k w) s) tn)
Proof
  strip_tac >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_scalar_shift_step,
       mk_inst_def, step_prov_def, set_prov_def, out_prov_def,
       SRULE [mk_inst_def] prefix_scalar_pure_dispatch, exec_pure2_def,
       eval_operand_def]
QED

Theorem prefix_scalar_eq_ghost:
  eval_operand a s = SOME w /\ eval_operand b s = SOME v ==>
  ghost_step fuel ctx PG G tn (mk_inst iid EQ [a;b] [x]) s =
    (DRESTRICT G (COMPL {x}), step_taint (mk_inst iid EQ [a;b] [x])
       s (update_var x (bool_to_word (w = v)) s) tn)
Proof
  strip_tac >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_scalar_eq_step,
       mk_inst_def, step_prov_def, set_prov_def, out_prov_def,
       SRULE [mk_inst_def] prefix_scalar_pure_dispatch, exec_pure2_def]
QED

Theorem prefix_scalar_shift_clamp_execution:
  eval_operand (Var v) s = SOME w ==>
  let shifted = (if left then word_lsl w (w2n k) else word_lsr w (w2n k));
      s1 = update_var y shifted s;
      s2 = update_var z (bool_to_word (shifted = 0w)) s1
  in
    run_inst_seq
      [mk_inst iid (if left then SHL else SHR) [Lit k; Var v] [y];
       mk_inst (iid+1) ISZERO [Var y] [z];
       mk_inst (iid+2) ASSERT [Var z] []] s =
    if shifted = 0w then OK s2
    else Abort Revert_abort (revert_state (set_returndata [] s2))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `a = if left then word_lsl w (w2n k) else word_lsr w (w2n k)` >>
  qabbrev_tac `s1 = update_var y a s` >>
  qabbrev_tac `s2 = update_var z (bool_to_word (a = 0w)) s1` >>
  `eval_operand (Var y) s1 = SOME a /\
   eval_operand (Var z) s2 = SOME (bool_to_word (a = 0w))` by
    simp[Abbr `s1`, Abbr `s2`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst iid (if left then SHL else SHR) [Lit k;Var v] [y]) s = OK s1` by
    (Cases_on `left` >> simp[Abbr `s1`, Abbr `a`] >>
     metis_tac[prefix_scalar_shift_step]) >>
  `step_inst_base (mk_inst (iid+1) ISZERO [Var y] [z]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule prefix_boolword_iszero_step >> simp[]) >>
  `step_inst_base (mk_inst (iid+2) ASSERT [Var z] []) s2 =
    if a = 0w then OK s2
    else Abort Revert_abort (revert_state (set_returndata [] s2))` by
    (drule prefix_assert_step >>
     disch_then (qspec_then `iid+2` mp_tac) >>
     Cases_on `a = 0w` >> simp[bool_to_word_def]) >>
  asm_rewrite_tac[run_inst_seq_def] >> Cases_on `a = 0w` >> simp[]
QED

Theorem prefix_scalar_signed_clamp_execution:
  eval_operand (Var v) s = SOME w /\ v <> y ==>
  let s1 = update_var y (sign_extend k w) s;
      s2 = update_var z (bool_to_word (w = sign_extend k w)) s1
  in
    run_inst_seq
      [mk_inst iid SIGNEXTEND [Lit k; Var v] [y];
       mk_inst (iid+1) EQ [Var v;Var y] [z];
       mk_inst (iid+2) ASSERT [Var z] []] s =
    if w = sign_extend k w then OK s2
    else Abort Revert_abort (revert_state (set_returndata [] s2))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `s1 = update_var y (sign_extend k w) s` >>
  qabbrev_tac `s2 = update_var z (bool_to_word (w = sign_extend k w)) s1` >>
  `eval_operand (Var v) s1 = SOME w /\
   eval_operand (Var y) s1 = SOME (sign_extend k w) /\
   eval_operand (Var z) s2 = SOME (bool_to_word (w = sign_extend k w))` by
    (gvs[Abbr `s1`, Abbr `s2`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iid SIGNEXTEND [Lit k;Var v] [y]) s = OK s1` by
    (simp[Abbr `s1`] >> metis_tac[prefix_scalar_shift_step]) >>
  `step_inst_base (mk_inst (iid+1) EQ [Var v;Var y] [z]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule prefix_scalar_eq_step >> simp[]) >>
  `step_inst_base (mk_inst (iid+2) ASSERT [Var z] []) s2 =
    if w = sign_extend k w then OK s2
    else Abort Revert_abort (revert_state (set_returndata [] s2))` by
    (drule prefix_assert_step >>
     disch_then (qspec_then `iid+2` mp_tac) >>
     Cases_on `w = sign_extend k w` >> simp[bool_to_word_def]) >>
  asm_rewrite_tac[run_inst_seq_def] >>
  Cases_on `w = sign_extend k w` >> simp[]
QED

Theorem prefix_scalar_shift_clamp_steps:
  eval_operand (Var v) s = SOME w /\ op_taint tn (Var v) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let a = (if left then word_lsl w (w2n n) else word_lsr w (w2n n));
      i = mk_inst iid (if left then SHL else SHR) [Lit n; Var v] [y];
      j = mk_inst (iid+1) ISZERO [Var y] [z];
      k = mk_inst (iid+2) ASSERT [Var z] [];
      s1 = update_var y a s;
      s2 = update_var z (bool_to_word (a = 0w)) s1;
      G1 = DRESTRICT G (COMPL {y});
      G2 = DRESTRICT G1 (COMPL {z});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j s1 s2 tn1
  in
    step_inst_base i s = OK s1 /\
    step_inst_base j s1 = OK s2 /\
    step_inst_base k s2 =
      (if a = 0w then OK s2
       else Abort Revert_abort (revert_state (set_returndata [] s2))) /\
    ghost_step fuel ctx PG G tn i s = (G1,tn1) /\
    ghost_step fuel ctx PG G1 tn1 j s1 = (G2,tn2) /\
    ghost_step fuel ctx PG G2 tn2 k s2 = (G2,tn2) /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    ptr_safe_step D lo fuel ctx fn PG G1 tn1 j s1 /\
    ptr_safe_step D lo fuel ctx fn PG G2 tn2 k s2 /\
    op_taint tn2 (Var z) = {} /\ allocas_from lo s2
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `a = if left then word_lsl w (w2n n) else word_lsr w (w2n n)` >>
  qabbrev_tac `s1 = update_var y a s` >>
  qabbrev_tac `s2 = update_var z (bool_to_word (a = 0w)) s1` >>
  `eval_operand (Var y) s1 = SOME a /\
   eval_operand (Var z) s2 = SOME (bool_to_word (a = 0w))` by
    simp[Abbr `s1`, Abbr `s2`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `allocas_from lo s1 /\ allocas_from lo s2` by
    (gvs[Abbr `s1`, Abbr `s2`, allocas_from_def, update_var_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst iid (if left then SHL else SHR) [Lit n;Var v] [y]) s = OK s1` by
    (Cases_on `left` >> simp[Abbr `s1`, Abbr `a`] >>
     metis_tac[prefix_scalar_shift_step]) >>
  `step_inst_base (mk_inst (iid+1) ISZERO [Var y] [z]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule prefix_boolword_iszero_step >> simp[]) >>
  `step_inst_base (mk_inst (iid+2) ASSERT [Var z] []) s2 =
    if a = 0w then OK s2
    else Abort Revert_abort (revert_state (set_returndata [] s2))` by
    (drule prefix_assert_step >>
     disch_then (qspec_then `iid+2` mp_tac) >>
     Cases_on `a = 0w` >> simp[bool_to_word_def]) >>
  `op_taint (step_taint (mk_inst iid (if left then SHL else SHR)
      [Lit n;Var v] [y]) s s1 tn) (Var y) = {}` by
    (Cases_on `left` >> simp[prefix_scalar_shift_clean]) >>
  simp[prefix_guard_output_taint, prefix_iszero_ptr_step, prefix_assert_ptr_step,
       prefix_scalar_shift_ptr, prefix_assert_ghost_step] >>
  conj_tac
  >- (Cases_on `left` >>
      qpat_assum `eval_operand (Var v) s = SOME w`
        (mp_then Any mp_tac prefix_scalar_shift_ghost) >>
      simp[Abbr `s1`, Abbr `a`]) >>
  conj_tac
  >- (once_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
      irule prefix_iszero_ghost_step >> simp[]) >>
  irule prefix_scalar_shift_ptr >> simp[] >> Cases_on `left` >> simp[]
QED

Theorem prefix_scalar_signed_clamp_steps:
  eval_operand (Var v) s = SOME w /\ op_taint tn (Var v) = {} /\
  v <> y /\ FLOOKUP G v = NONE /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid SIGNEXTEND [Lit n; Var v] [y];
      j = mk_inst (iid+1) EQ [Var v;Var y] [z];
      k = mk_inst (iid+2) ASSERT [Var z] [];
      s1 = update_var y (sign_extend n w) s;
      s2 = update_var z (bool_to_word (w = sign_extend n w)) s1;
      G1 = DRESTRICT G (COMPL {y});
      G2 = DRESTRICT G1 (COMPL {z});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j s1 s2 tn1
  in
    step_inst_base i s = OK s1 /\
    step_inst_base j s1 = OK s2 /\
    step_inst_base k s2 =
      (if w = sign_extend n w then OK s2
       else Abort Revert_abort (revert_state (set_returndata [] s2))) /\
    ghost_step fuel ctx PG G tn i s = (G1,tn1) /\
    ghost_step fuel ctx PG G1 tn1 j s1 = (G2,tn2) /\
    ghost_step fuel ctx PG G2 tn2 k s2 = (G2,tn2) /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    ptr_safe_step D lo fuel ctx fn PG G1 tn1 j s1 /\
    ptr_safe_step D lo fuel ctx fn PG G2 tn2 k s2 /\
    op_taint tn2 (Var z) = {} /\ allocas_from lo s2
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `s1 = update_var y (sign_extend n w) s` >>
  qabbrev_tac `s2 = update_var z (bool_to_word (w = sign_extend n w)) s1` >>
  `eval_operand (Var v) s1 = SOME w /\
   eval_operand (Var y) s1 = SOME (sign_extend n w) /\
   eval_operand (Var z) s2 = SOME (bool_to_word (w = sign_extend n w))` by
    (gvs[Abbr `s1`, Abbr `s2`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE]) >>
  `allocas_from lo s1 /\ allocas_from lo s2` by
    (gvs[Abbr `s1`, Abbr `s2`, allocas_from_def, update_var_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst iid SIGNEXTEND [Lit n;Var v] [y]) s = OK s1` by
    (simp[Abbr `s1`] >> metis_tac[prefix_scalar_shift_step]) >>
  `step_inst_base (mk_inst (iid+1) EQ [Var v;Var y] [z]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule prefix_scalar_eq_step >> simp[]) >>
  `step_inst_base (mk_inst (iid+2) ASSERT [Var z] []) s2 =
    if w = sign_extend n w then OK s2
    else Abort Revert_abort (revert_state (set_returndata [] s2))` by
    (drule prefix_assert_step >>
     disch_then (qspec_then `iid+2` mp_tac) >>
     Cases_on `w = sign_extend n w` >> simp[bool_to_word_def]) >>
  qabbrev_tac `tn1 = step_taint (mk_inst iid SIGNEXTEND [Lit n;Var v] [y]) s s1 tn` >>
  `op_taint tn1 (Var y) = {}` by simp[Abbr `tn1`, prefix_scalar_shift_clean] >>
  `op_taint tn1 (Var v) = {}` by
    (fs[op_taint_def] >>
     simp[Abbr `tn1`, op_taint_def, step_taint_def, set_var_taint_def,
          mk_inst_def, FLOOKUP_UPDATE]) >>
  simp[prefix_scalar_eq_clean, prefix_assert_ghost_step,
       prefix_assert_ptr_step, prefix_scalar_shift_ptr] >>
  conj_tac
  >- (qpat_assum `eval_operand (Var v) s = SOME w`
        (mp_then Any mp_tac prefix_scalar_shift_ghost) >>
      simp[Abbr `tn1`, Abbr `s1`]) >>
  conj_tac
  >- (simp[Abbr `s2`] >>
      once_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
      irule prefix_scalar_eq_ghost >> simp[]) >>
  irule prefix_scalar_eq_ptr >>
  simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem prefix_scalar_shift_clamp_continuation:
  eval_operand (Var v) s = SOME w /\ op_taint tn (Var v) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid (if left then SHL else SHR) [Lit n;Var v] [y]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (iid+1) ISZERO [Var y] [z]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst (iid+2) ASSERT [Var z] []) ==>
  let a = (if left then word_lsl w (w2n n) else word_lsr w (w2n n));
      i = mk_inst iid (if left then SHL else SHR) [Lit n;Var v] [y];
      j = mk_inst (iid+1) ISZERO [Var y] [z];
      s1 = update_var y a s;
      t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx;
      s2 = update_var z (bool_to_word (a = 0w)) t1;
      t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx);
      G1 = DRESTRICT G (COMPL {y});
      G2 = DRESTRICT G1 (COMPL {z});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j t1 s2 tn1
  in
    ((a = 0w ==>
       ptr_safe_block D lo fuel ctx fn PG G2 tn2 bb
         (t2 with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx)))) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `a = if left then word_lsl w (w2n n) else word_lsr w (w2n n)` >>
  qmatch_goalsub_abbrev_tac `step_taint i s s1 tn` >>
  qabbrev_tac `t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qmatch_goalsub_abbrev_tac `step_taint j t1 s2 tn1` >>
  qabbrev_tac `t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `eval_operand (Var y) t1 = SOME a` by
    simp[Abbr `t1`, Abbr `s1`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand (Var z) t2 = SOME (bool_to_word (a = 0w))` by
    simp[Abbr `t2`, Abbr `s2`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `allocas_from lo t1 /\ allocas_from lo t2` by
    (gvs[Abbr `t1`, Abbr `s1`, Abbr `t2`, Abbr `s2`,
         allocas_from_def, update_var_def] >> metis_tac[]) >>
  `op_taint tn1 (Var y) = {}` by
    (Cases_on `left` >> simp[Abbr `tn1`, Abbr `i`, prefix_scalar_shift_clean]) >>
  `op_taint (step_taint j t1 s2 tn1) (Var z) = {}` by
    simp[Abbr `j`, prefix_guard_output_taint] >>
  `i.inst_opcode <> INVOKE /\ j.inst_opcode <> INVOKE /\
   ~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode` by
    (Cases_on `left` >> simp[Abbr `i`, Abbr `j`, mk_inst_def, is_terminator_def]) >>
  `step_inst fuel ctx i s = OK s1` by
    (simp[step_inst_non_invoke] >>
     Cases_on `left` >> simp[Abbr `i`, Abbr `s1`, Abbr `a`] >>
     metis_tac[prefix_scalar_shift_step]) >>
  `step_inst fuel ctx j t1 = OK s2` by
    (simp[step_inst_non_invoke] >>
     simp[Abbr `j`, Abbr `s2`, prefix_boolword_iszero_step]) >>
  `ghost_step fuel ctx PG G tn i s = (DRESTRICT G (COMPL {y}),tn1)` by
    (Cases_on `left` >>
     qpat_assum `eval_operand (Var v) s = SOME w`
       (mp_then Any mp_tac prefix_scalar_shift_ghost) >>
     simp[Abbr `i`, Abbr `s1`, Abbr `tn1`, Abbr `a`]) >>
  `ghost_step fuel ctx PG (DRESTRICT G (COMPL {y})) tn1 j t1 =
     (DRESTRICT G (COMPL {y} INTER COMPL {z}),step_taint j t1 s2 tn1)` by
    (simp[Abbr `j`] >> once_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
     irule prefix_iszero_ghost_step >>
     simp[Abbr `s2`, prefix_boolword_iszero_step]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s` by
    (simp[Abbr `i`] >> irule prefix_scalar_shift_ptr >>
     simp[] >> Cases_on `left` >> simp[]) >>
  `ptr_safe_step D lo fuel ctx fn PG (DRESTRICT G (COMPL {y})) tn1 j t1 /\
   ptr_safe_step D lo fuel ctx fn PG (DRESTRICT G (COMPL {y} INTER COMPL {z}))
     (step_taint j t1 s2 tn1) (mk_inst (iid+2) ASSERT [Var z] []) t2` by
    simp[Abbr `j`, prefix_iszero_ptr_step, prefix_assert_ptr_step] >>
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
  Cases_on `a = 0w` >> gvs[bool_to_word_def, Abbr `t2`]
QED


Theorem prefix_scalar_signed_clamp_continuation:
  eval_operand (Var v) s = SOME w /\ op_taint tn (Var v) = {} /\
  v <> y /\ FLOOKUP G v = NONE /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid SIGNEXTEND [Lit n;Var v] [y]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (iid+1) EQ [Var v;Var y] [z]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst (iid+2) ASSERT [Var z] []) ==>
  let i = mk_inst iid SIGNEXTEND [Lit n;Var v] [y];
      j = mk_inst (iid+1) EQ [Var v;Var y] [z];
      s1 = update_var y (sign_extend n w) s;
      t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx;
      s2 = update_var z (bool_to_word (w = sign_extend n w)) t1;
      t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx);
      G1 = DRESTRICT G (COMPL {y});
      G2 = DRESTRICT G1 (COMPL {z});
      tn1 = step_taint i s s1 tn;
      tn2 = step_taint j t1 s2 tn1
  in
    ((w = sign_extend n w ==>
       ptr_safe_block D lo fuel ctx fn PG G2 tn2 bb
         (t2 with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx)))) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `step_taint i s s1 tn` >>
  qabbrev_tac `t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qmatch_goalsub_abbrev_tac `step_taint j t1 s2 tn1` >>
  qabbrev_tac `t2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `eval_operand (Var v) t1 = SOME w /\
   eval_operand (Var y) t1 = SOME (sign_extend n w)` by
    (gvs[Abbr `t1`, Abbr `s1`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE]) >>
  `eval_operand (Var z) t2 = SOME (bool_to_word (w = sign_extend n w))` by
    simp[Abbr `t2`, Abbr `s2`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `allocas_from lo t1 /\ allocas_from lo t2` by
    (gvs[Abbr `t1`, Abbr `s1`, Abbr `t2`, Abbr `s2`,
         allocas_from_def, update_var_def] >> metis_tac[]) >>
  `op_taint tn1 (Var y) = {}` by
    simp[Abbr `tn1`, Abbr `i`, prefix_scalar_shift_clean] >>
  `op_taint tn1 (Var v) = {}` by
    (fs[op_taint_def] >>
     simp[Abbr `tn1`, Abbr `i`, op_taint_def, step_taint_def,
          set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
  `op_taint (step_taint j t1 s2 tn1) (Var z) = {}` by
    simp[Abbr `j`, prefix_scalar_eq_clean] >>
  `i.inst_opcode <> INVOKE /\ j.inst_opcode <> INVOKE /\
   ~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode` by
    simp[Abbr `i`, Abbr `j`, mk_inst_def, is_terminator_def] >>
  `step_inst fuel ctx i s = OK s1` by
    (simp[step_inst_non_invoke, Abbr `i`, Abbr `s1`] >>
     metis_tac[prefix_scalar_shift_step]) >>
  `step_inst fuel ctx j t1 = OK s2` by
    (simp[step_inst_non_invoke, Abbr `j`, Abbr `s2`] >>
     irule prefix_scalar_eq_step >> simp[]) >>
  `ghost_step fuel ctx PG G tn i s = (DRESTRICT G (COMPL {y}),tn1)` by
    (qpat_assum `eval_operand (Var v) s = SOME w`
       (mp_then Any mp_tac prefix_scalar_shift_ghost) >>
     simp[Abbr `i`, Abbr `s1`, Abbr `tn1`]) >>
  `ghost_step fuel ctx PG (DRESTRICT G (COMPL {y})) tn1 j t1 =
     (DRESTRICT G (COMPL {y} INTER COMPL {z}),step_taint j t1 s2 tn1)` by
    (simp[Abbr `j`, Abbr `s2`] >>
     once_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
     irule prefix_scalar_eq_ghost >> simp[]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn i s` by
    simp[Abbr `i`, prefix_scalar_shift_ptr] >>
  `ptr_safe_step D lo fuel ctx fn PG (DRESTRICT G (COMPL {y})) tn1 j t1` by
    (simp[Abbr `j`] >> irule prefix_scalar_eq_ptr >>
     simp[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  `ptr_safe_step D lo fuel ctx fn PG (DRESTRICT G (COMPL {y} INTER COMPL {z}))
     (step_taint j t1 s2 tn1) (mk_inst (iid+2) ASSERT [Var z] []) t2` by
    simp[prefix_assert_ptr_step] >>
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
  Cases_on `w = sign_extend n w` >> gvs[bool_to_word_def, Abbr `t2`]
QED


Theorem prefix_scalar_clamp_frames:
  (opc = SHR \/ opc = SHL \/ opc = SIGNEXTEND) /\
  (chk = EQ \/ chk = ISZERO) /\
  s1 = update_var y a s /\ s2 = update_var z c s1 /\
  tn1 = step_taint (mk_inst iid opc ops [y]) s s1 tn /\
  tn2 = step_taint (mk_inst (iid+1) chk args [z])
    (s1 with vs_inst_idx := k+1) (s2 with vs_inst_idx := k+1) tn1 ==>
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
    (!v. v <> y /\ v <> z ==> op_taint tn2 (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `opc IN {SHR;SHL;SIGNEXTEND;EQ;ISZERO} /\
   chk IN {SHR;SHL;SIGNEXTEND;EQ;ISZERO}` by simp[] >>
  `s1.vs_allocas = s.vs_allocas /\ s1.vs_fmp = s.vs_fmp /\
   (s2 with vs_inst_idx := k+1).vs_allocas =
     (s1 with vs_inst_idx := k+1).vs_allocas /\
   (s2 with vs_inst_idx := k+1).vs_fmp =
     (s1 with vs_inst_idx := k+1).vs_fmp` by simp[update_var_def] >>
  qpat_assum `opc IN _` (mp_then Any mp_tac prefix_scalar_pure_taint_frame) >>
  disch_then (qspecl_then [`y`,`tn`,`s1`,`s`,`ops`] mp_tac) >>
  simp[] >> disch_then (qspec_then `iid` strip_assume_tac) >>
  qpat_assum `chk IN _` (mp_then Any mp_tac prefix_scalar_pure_taint_frame) >>
  disch_then (qspecl_then [`z`,`tn1`,`s2 with vs_inst_idx := k+1`,
    `s1 with vs_inst_idx := k+1`,`args`] mp_tac) >>
  simp[] >> disch_then (qspec_then `iid+1` strip_assume_tac) >>
  gvs[]
QED

Theorem prefix_scalar_word_execution:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z ==>
  let w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      shifted = (if signed then sign_extend n w
                 else if left then word_lsl w (w2n n) else word_lsr w (w2n n));
      valid = (if signed then w = shifted else shifted = 0w);
      l = update_var x w s;
      s1 = update_var y shifted l;
      s2 = update_var z (bool_to_word valid) s1;
      xs = [mk_inst iid DLOAD [src] [x];
        mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
          [Lit n;Var x] [y];
        (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
         else mk_inst (iid+2) ISZERO [Var y] [z]);
        mk_inst (iid+3) ASSERT [Var z] [];
        mk_inst (iid+4) MSTORE [Var dst;Var x] []]
  in
    run_inst_seq xs s =
      (if valid then OK (mstore (w2n p) w s2)
       else Abort Revert_abort (revert_state (set_returndata [] s2)))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `update_var x w s` >>
  qabbrev_tac `shifted = if signed then sign_extend n w
    else if left then word_lsl w (w2n n) else word_lsr w (w2n n)` >>
  qabbrev_tac `valid = if signed then w = shifted else shifted = 0w` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `s1 = update_var y shifted l` >>
  qabbrev_tac `s2 = update_var z (bool_to_word valid) s1` >>
  `eval_operand (Var x) l = SOME w /\
   eval_operand (Var x) s2 = SOME w /\ eval_operand (Var dst) s2 = SOME p` by
    gvs[Abbr `l`, Abbr `s1`, Abbr `s2`, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst iid DLOAD [src] [x]) s = OK l` by
    simp[prefix_dload_step, Abbr `l`, Abbr `w`] >>
  once_rewrite_tac[run_inst_seq_def] >> asm_rewrite_tac[] >> simp[] >>
  qabbrev_tac `clamp =
    [mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
       [Lit n;Var x] [y];
     (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
      else mk_inst (iid+2) ISZERO [Var y] [z]);
     mk_inst (iid+3) ASSERT [Var z] []]` >>
  `run_inst_seq clamp l =
     if valid then OK s2
     else Abort Revert_abort (revert_state (set_returndata [] s2))` by
    (Cases_on `signed`
     >- (qpat_assum `eval_operand (Var x) l = SOME w`
           (mp_then Any mp_tac prefix_scalar_signed_clamp_execution) >>
         disch_then (qspecl_then [`z`,`y`,`n`,`iid+1`] mp_tac) >>
         simp[Abbr `clamp`, Abbr `s2`, Abbr `s1`, Abbr `valid`, Abbr `shifted`]) >>
     qpat_assum `eval_operand (Var x) l = SOME w`
       (mp_then Any mp_tac prefix_scalar_shift_clamp_execution) >>
     disch_then (qspecl_then [`z`,`y`,`left`,`n`,`iid+1`] mp_tac) >>
     simp[Abbr `clamp`, Abbr `s2`, Abbr `s1`, Abbr `valid`, Abbr `shifted`]) >>
  `run_inst_seq (clamp ++ [mk_inst (iid+4) MSTORE [Var dst;Var x] []]) l =
     if valid then OK (mstore (w2n p) w s2)
     else Abort Revert_abort (revert_state (set_returndata [] s2))` suffices_by
    simp[Abbr `clamp`] >>
  `step_inst_base (mk_inst (iid+4) MSTORE [Var dst;Var x] []) s2 =
     OK (mstore (w2n p) w s2)` by (irule prefix_mstore_step >> simp[]) >>
  Cases_on `valid`
  >- (gvs[] >> drule run_inst_seq_append >> disch_then (qspec_then
        `[mk_inst (iid+4) MSTORE [Var dst;Var x] []]` mp_tac) >>
      simp[run_inst_seq_def, prefix_mstore_step]) >>
  `!t. run_inst_seq clamp l <> OK t` by simp[] >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `[mk_inst (iid+4) MSTORE [Var dst;Var x] []]` mp_tac) >>
  simp[]
QED

Theorem prefix_scalar_instruction[local]:
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

Theorem prefix_scalar_index_updates[local]:
  update_var v w (s with vs_inst_idx := k) =
    (update_var v w s) with vs_inst_idx := k /\
  mstore off w (s with vs_inst_idx := k) =
    (mstore off w s) with vs_inst_idx := k
Proof
  simp[update_var_def, mstore_def]
QED

Theorem prefix_scalar_word_ptr:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n p /\ w2n p + 32 <= b+sz /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let k = s.vs_inst_idx;
      w = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w));
      shifted = (if signed then sign_extend n w
                 else if left then word_lsl w (w2n n) else word_lsr w (w2n n));
      valid = (if signed then w = shifted else shifted = 0w);
      i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
        [Lit n;Var x] [y];
      h = (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
           else mk_inst (iid+2) ISZERO [Var y] [z]);
      c = mk_inst (iid+3) ASSERT [Var z] [];
      m = mk_inst (iid+4) MSTORE [Var dst;Var x] [];
      l = update_var x w s;
      r = update_var y shifted l;
      t = update_var z (bool_to_word valid) r;
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
    ((valid ==> ptr_safe_block D lo fuel ctx fn PG H q3 bb
       (u with vs_inst_idx := k+5)) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_goalsub_abbrev_tac `update_var x w s` >>
  qabbrev_tac `shifted = if signed then sign_extend n w
    else if left then word_lsl w (w2n n) else word_lsr w (w2n n)` >>
  qabbrev_tac `valid = if signed then w = shifted else shifted = 0w` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `r = update_var y shifted l` >>
  qabbrev_tac `t = update_var z (bool_to_word valid) r` >>
  qabbrev_tac `u = mstore (w2n p) w t` >>
  `!i. i < 5 ==> get_instruction bb (s.vs_inst_idx+i) =
    SOME (EL i [mk_inst iid DLOAD [src] [x];
      mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
        [Lit n;Var x] [y];
      (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
       else mk_inst (iid+2) ISZERO [Var y] [z]);
      mk_inst (iid+3) ASSERT [Var z] [];
      mk_inst (iid+4) MSTORE [Var dst;Var x] []])` by
    (rpt strip_tac >> irule prefix_scalar_instruction >> simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst iid DLOAD [src] [x])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_assum `Abbrev (w = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (l = _)` (assume_tac o GSYM o SRULE [markerTheory.Abbrev_def]) >>
  strip_tac >> drule_all prefix_boolword_dload_continuation >>
  simp[LET_THM, arithmeticTheory.ADD1] >> disch_then irule >>
  qabbrev_tac `q0 = step_taint (mk_inst iid DLOAD [src] [x]) s l tn` >>
  qabbrev_tac `l1 = l with vs_inst_idx := s.vs_inst_idx+1` >>
  `eval_operand (Var x) l1 = SOME w /\ op_taint q0 (Var x) = {} /\
   allocas_from lo l1 /\ FLOOKUP (DRESTRICT G (COMPL {x})) x = NONE` by
    (simp[Abbr `l1`, Abbr `q0`, prefix_dload_output_taint, FLOOKUP_DRESTRICT] >>
     gvs[Abbr `l`, update_var_def, eval_operand_def, lookup_var_def,
         FLOOKUP_UPDATE, allocas_from_def] >> metis_tac[]) >>
  `get_instruction bb l1.vs_inst_idx =
      SOME (mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
        [Lit n;Var x] [y]) /\
   get_instruction bb (SUC l1.vs_inst_idx) =
      SOME (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
            else mk_inst (iid+2) ISZERO [Var y] [z]) /\
   get_instruction bb (SUC (SUC l1.vs_inst_idx)) =
      SOME (mk_inst (iid+3) ASSERT [Var z] [])` by
    simp[Abbr `l1`, arithmeticTheory.ADD1] >>
  `((valid ==> ptr_safe_block D lo fuel ctx fn PG
      (DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})) (COMPL {z}))
      (step_taint
        (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
         else mk_inst (iid+2) ISZERO [Var y] [z])
        (r with vs_inst_idx := s.vs_inst_idx+2)
        (t with vs_inst_idx := s.vs_inst_idx+2)
        (step_taint
          (mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
            [Lit n;Var x] [y]) l1 (r with vs_inst_idx := s.vs_inst_idx+1) q0))
      bb (t with vs_inst_idx := s.vs_inst_idx+4)) ==>
     ptr_safe_block D lo fuel ctx fn PG (DRESTRICT G (COMPL {x})) q0 bb l1)` by
    (strip_tac >> Cases_on `signed`
     >- (qpat_assum `eval_operand (Var x) l1 = SOME w`
           (mp_then Any mp_tac prefix_scalar_signed_clamp_continuation) >>
         simp[LET_THM, arithmeticTheory.ADD1] >> disch_then irule >> simp[] >>
         qexistsl [`iid+1`,`n`,`y`,`z`] >>
         gvs[Abbr `l1`, Abbr `r`, Abbr `t`, Abbr `valid`, Abbr `shifted`,
             prefix_scalar_index_updates, arithmeticTheory.ADD1]) >>
     qpat_assum `eval_operand (Var x) l1 = SOME w`
       (mp_then Any mp_tac prefix_scalar_shift_clamp_continuation) >>
     simp[LET_THM, arithmeticTheory.ADD1] >> disch_then irule >> simp[] >>
     qexistsl [`iid+1`,`left`,`n`,`y`,`z`] >>
     gvs[Abbr `l1`, Abbr `r`, Abbr `t`, Abbr `valid`, Abbr `shifted`,
         prefix_scalar_index_updates, arithmeticTheory.ADD1]) >>
  first_x_assum irule >> strip_tac >>
  qabbrev_tac `q1 = step_taint
    (mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
      [Lit n;Var x] [y]) l1 (r with vs_inst_idx := s.vs_inst_idx+1) q0` >>
  qabbrev_tac `q2 = step_taint
    (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
     else mk_inst (iid+2) ISZERO [Var y] [z])
    (r with vs_inst_idx := s.vs_inst_idx+2)
    (t with vs_inst_idx := s.vs_inst_idx+2) q1` >>
  qabbrev_tac `H = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x}))
    (COMPL {y})) (COMPL {z})` >>
  qabbrev_tac `t4 = t with vs_inst_idx := s.vs_inst_idx+4` >>
  `eval_operand (Var dst) t4 = SOME p /\ eval_operand (Var x) t4 = SOME w /\
   FLOOKUP H dst = SOME (b,sz) /\ allocas_from lo t4 /\
   get_instruction bb t4.vs_inst_idx =
     SOME (mk_inst (iid+4) MSTORE [Var dst;Var x] [])` by
    (simp[Abbr `t4`, Abbr `H`, FLOOKUP_DRESTRICT] >>
     gvs[Abbr `t`, Abbr `r`, Abbr `l`, update_var_def,
         eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, allocas_from_def] >>
     metis_tac[]) >>
  `op_taint q2 (Var dst) = {} /\ op_taint q2 (Var x) = {}` by
    (Cases_on `signed` >> Cases_on `left` >>
     simp[Abbr `q2`, Abbr `q1`, Abbr `l1`, Abbr `t`, Abbr `r`,
          prefix_guard_taint_other, prefix_scalar_pure_taint_frame,
          update_var_def] >>
     simp[Abbr `q0`, prefix_dload_output_taint, prefix_guard_taint_other]) >>
  drule_all prefix_boolword_mstore_continuation >>
  simp[LET_THM] >> disch_then irule >>
  simp[Abbr `t4`, prefix_scalar_index_updates, Abbr `u`, arithmeticTheory.ADD1]
QED

Theorem prefix_scalar_word_frames:
  eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\
  op_taint tn src = {} ==>
  let l = update_var x w s;
      r = update_var y shifted l;
      t = update_var z c r;
      u = mstore (w2n p) w t;
      q0 = step_taint (mk_inst iid DLOAD [src] [x]) s l tn;
      q1 = step_taint
        (mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
          [Lit n;Var x] [y]) (l with vs_inst_idx := s.vs_inst_idx+1)
          (r with vs_inst_idx := s.vs_inst_idx+1) q0;
      q2 = step_taint
        (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
         else mk_inst (iid+2) ISZERO [Var y] [z])
        (r with vs_inst_idx := s.vs_inst_idx+2)
        (t with vs_inst_idx := s.vs_inst_idx+2) q1;
      q3 = step_taint (mk_inst (iid+4) MSTORE [Var dst;Var x] [])
        (t with vs_inst_idx := s.vs_inst_idx+4)
        (u with vs_inst_idx := s.vs_inst_idx+4) q2
  in
    q3.t_mem = tn.t_mem DIFF range_bytes [(w2n p,32)] /\
    q3.t_stor = tn.t_stor /\ q3.t_trans = tn.t_trans /\ q3.t_imm = tn.t_imm /\
    (!v. v <> x /\ v <> y /\ v <> z ==>
      op_taint q3 (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `r = update_var y shifted l` >>
  qabbrev_tac `t = update_var z c r` >>
  qabbrev_tac `u = mstore (w2n p) w t` >>
  qabbrev_tac `q0 = step_taint (mk_inst iid DLOAD [src] [x]) s l tn` >>
  qabbrev_tac `q1 = step_taint
    (mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
      [Lit n;Var x] [y]) (l with vs_inst_idx := s.vs_inst_idx+1)
      (r with vs_inst_idx := s.vs_inst_idx+1) q0` >>
  qabbrev_tac `q2 = step_taint
    (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
     else mk_inst (iid+2) ISZERO [Var y] [z])
    (r with vs_inst_idx := s.vs_inst_idx+2)
    (t with vs_inst_idx := s.vs_inst_idx+2) q1` >>
  `op_taint q2 (Var x) = {}` by
    (Cases_on `signed` >> Cases_on `left` >>
     simp[Abbr `q2`, Abbr `q1`, Abbr `q0`, prefix_guard_taint_other,
          prefix_dload_output_taint]) >>
  `eval_operand (Var dst) (t with vs_inst_idx := s.vs_inst_idx+4) = SOME p /\
   eval_operand (Var x) (t with vs_inst_idx := s.vs_inst_idx+4) = SOME w` by
    gvs[Abbr `t`, Abbr `r`, Abbr `l`, update_var_def,
        eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `let q3 = step_taint (mk_inst (iid+4) MSTORE [Var dst;Var x] [])
      (t with vs_inst_idx := s.vs_inst_idx+4)
      (u with vs_inst_idx := s.vs_inst_idx+4) q2
   in q3.t_mem = q2.t_mem DIFF range_bytes [(w2n p,32)] /\
      q3.t_stor = q2.t_stor /\ q3.t_trans = q2.t_trans /\ q3.t_imm = q2.t_imm /\
      (!v. op_taint q3 (Var v) = op_taint q2 (Var v))` by
    (irule prefix_boolword_store_taint_frame >> simp[Abbr `u`, mstore_def]) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  pop_assum (mp_tac o SRULE [LET_THM]) >> strip_tac >> asm_rewrite_tac[] >>
  Cases_on `signed` >> Cases_on `left` >>
  simp[Abbr `q2`, Abbr `q1`, Abbr `q0`,
       SRULE [LET_THM] prefix_scalar_pure_taint_frame,
       SRULE [LET_THM] prefix_boolword_pure_taint_frame,
       Abbr `t`, Abbr `r`, Abbr `l`, update_var_def,
       prefix_guard_taint_other, prefix_dload_output_taint]
QED

Theorem prefix_scalar_word_success:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME p /\
  x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n p /\ w2n p+32 <= b+sz /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  xs = [mk_inst iid DLOAD [src] [x];
    mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
      [Lit n;Var x] [y];
    (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
     else mk_inst (iid+2) ISZERO [Var y] [z]);
    mk_inst (iid+3) ASSERT [Var z] [];
    mk_inst (iid+4) MSTORE [Var dst;Var x] []] /\
  isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq xs s = OK end ==>
  ?H qt.
    qt.t_mem = tn.t_mem DIFF range_bytes [(w2n p,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x /\ v <> y /\ v <> z ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
      (end with vs_inst_idx := s.vs_inst_idx+5)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  qabbrev_tac `w = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))` >>
  qabbrev_tac `shifted = if signed then sign_extend n w
    else if left then word_lsl w (w2n n) else word_lsr w (w2n n)` >>
  qabbrev_tac `valid = if signed then w = shifted else shifted = 0w` >>
  qabbrev_tac `l = update_var x w s` >>
  qabbrev_tac `r = update_var y shifted l` >>
  qabbrev_tac `t = update_var z (bool_to_word valid) r` >>
  qabbrev_tac `u = mstore (w2n p) w t` >>
  qabbrev_tac `q0 = step_taint (mk_inst iid DLOAD [src] [x]) s l tn` >>
  qabbrev_tac `q1 = step_taint
    (mk_inst (iid+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
      [Lit n;Var x] [y]) (l with vs_inst_idx := s.vs_inst_idx+1)
      (r with vs_inst_idx := s.vs_inst_idx+1) q0` >>
  qabbrev_tac `q2 = step_taint
    (if signed then mk_inst (iid+2) EQ [Var x;Var y] [z]
     else mk_inst (iid+2) ISZERO [Var y] [z])
    (r with vs_inst_idx := s.vs_inst_idx+2)
    (t with vs_inst_idx := s.vs_inst_idx+2) q1` >>
  qabbrev_tac `qt = step_taint (mk_inst (iid+4) MSTORE [Var dst;Var x] [])
    (t with vs_inst_idx := s.vs_inst_idx+4)
    (u with vs_inst_idx := s.vs_inst_idx+4) q2` >>
  qabbrev_tac `H = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x}))
    (COMPL {y})) (COMPL {z})` >>
  `run_inst_seq xs s =
    if valid then OK u else Abort Revert_abort (revert_state (set_returndata [] t))` by
    (qpat_x_assum `run_inst_seq _ _ = OK end` kall_tac >>
     simp[Abbr `u`, Abbr `t`, Abbr `r`, Abbr `l`, Abbr `valid`,
          Abbr `shifted`, Abbr `w`] >>
     irule (SRULE [LET_THM] prefix_scalar_word_execution) >> simp[]) >>
  `valid /\ end = u` by (Cases_on `valid` >> gvs[]) >>
  `qt.t_mem = tn.t_mem DIFF range_bytes [(w2n p,32)] /\
   qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
   (!v. v <> x /\ v <> y /\ v <> z ==>
     op_taint qt (Var v) = op_taint tn (Var v))` by
    (simp[Abbr `qt`, Abbr `q2`, Abbr `q1`, Abbr `q0`, Abbr `u`,
          Abbr `t`, Abbr `r`, Abbr `l`] >>
     irule (SRULE [LET_THM] prefix_scalar_word_frames) >> simp[]) >>
  qexistsl [`H`,`qt`] >> asm_rewrite_tac[] >>
  conj_tac >- simp[Abbr `H`, FLOOKUP_DRESTRICT] >>
  strip_tac >> gen_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `u`, Abbr `t`, Abbr `r`, Abbr `l`, update_var_def, mstore_def] >>
  qpat_x_assum `xs = _` SUBST_ALL_TAC >>
  qpat_assum `isPREFIX _ _`
    (mp_then Any mp_tac (SRULE [LET_THM, Excl "isPREFIX"] prefix_scalar_word_ptr)) >>
  simp[ptr_safe_run_def] >> disch_then irule >>
  gvs[Abbr `H`, Abbr `qt`, Abbr `q2`, Abbr `q1`, Abbr `t`, Abbr `u`,
      Abbr `valid`, Abbr `shifted`, ptr_safe_run_def]
QED

Theorem prefix_scalar_checked_layout:
  ((clamp = IntClamp bits signed /\ ~left /\
      n = n2w (if signed then bits DIV 8-1 else bits)) \/
   (clamp = BytesMClamp m /\ ~signed /\ left /\ n = n2w (m*8))) /\
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') ==>
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      id = st.cs_next_id;
      insts = [mk_inst id DLOAD [src] [x 0];
        mk_inst (id+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
          [Lit n;Var(x 0)] [x 1];
        (if signed then mk_inst (id+2) EQ [Var(x 0);Var(x 1)] [x 2]
         else mk_inst (id+2) ISZERO [Var(x 1)] [x 2]);
        mk_inst (id+3) ASSERT [Var(x 2)] [];
        mk_inst (id+4) MSTORE [dst;Var(x 0)] []]
  in emitted_insts st st' = insts /\
     st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
     st'.cs_next_var = st.cs_next_var+3 /\
     isPREFIX st.cs_current_insts st'.cs_current_insts /\
     LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts+5
Proof
  strip_tac >>
  gvs[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def, SRULE [LET_THM] prefix_scalar_int_compile,
      SRULE [LET_THM] prefix_scalar_bytes_compile, emitted_insts_def,
      rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND, APPEND] >> simp[]
QED

Theorem prefix_scalar_checked_ghost:
  ((clamp = IntClamp bits signed /\ ~left /\
      (n:bytes32) = n2w (if signed then bits DIV 8-1 else bits)) \/
   (clamp = BytesMClamp m /\ ~signed /\ left /\ n = n2w (m*8))) /\
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w d) /\ d < dimword (:256) /\
  (!v. src = Var v \/ Var dst = Var v \/ Lit 0w = Var v ==> not_fresh_at st v) /\
  fn_has_code st st' fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?H qt.
    qt.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
      (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
    prefix_scalar_checked_layout >>
  disch_then (qspecl_then [`signed`,`n`,`m`,`left`,`bits`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `emitted_insts st st' = _` kall_tac >>
     gvs[emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND, APPEND] >>
     metis_tac[]) >>
  qabbrev_tac `x = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `y = "%" ++ toString (st.cs_next_var+1)` >>
  qabbrev_tac `z = "%" ++ toString (st.cs_next_var+2)` >>
  `x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z` by
    gvs[Abbr `x`, Abbr `y`, Abbr `z`, not_fresh_at_def] >>
  `b <= w2n (n2w d:bytes32) /\ w2n (n2w d:bytes32)+32 <= b+sz` by simp[w2n_n2w] >>
  `emitted_insts st st' =
    [mk_inst st.cs_next_id DLOAD [src] [x];
     mk_inst (st.cs_next_id+1) (if signed then SIGNEXTEND else if left then SHL else SHR)
       [Lit n;Var x] [y];
     (if signed then mk_inst (st.cs_next_id+2) EQ [Var x;Var y] [z]
      else mk_inst (st.cs_next_id+2) ISZERO [Var y] [z]);
     mk_inst (st.cs_next_id+3) ASSERT [Var z] [];
     mk_inst (st.cs_next_id+4) MSTORE [Var dst;Var x] []]` by
    simp[Abbr `x`, Abbr `y`, Abbr `z`] >>
  drule_all prefix_scalar_word_success >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  `w2n (n2w d:bytes32) = d` by simp[w2n_n2w] >>
  pure_asm_rewrite_tac[] >> strip_tac >>
  qexistsl [`H`,`qt`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[not_fresh_at_def] >>
  `v <> STRING #"%" (toString st.cs_next_var) /\
   v <> STRING #"%" (toString (st.cs_next_var+1)) /\
   v <> STRING #"%" (toString (st.cs_next_var+2))` by
    (qpat_x_assum `not_fresh_at st v` mp_tac >>
     pure_rewrite_tac[not_fresh_at_def] >> strip_tac >>
     rpt conj_tac >> first_x_assum irule >> decide_tac) >>
  simp[Abbr `x`, Abbr `y`, Abbr `z`]
QED

val _ = export_theory();
