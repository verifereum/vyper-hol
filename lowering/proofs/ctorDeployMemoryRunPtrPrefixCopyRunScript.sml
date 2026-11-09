(* Successful zero-hi copy decoders, with the supplied execution endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixCopyRun
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunPtrPrefixCopyStep ctorDeployMemoryRunPtrPrefixBoolPreheader
  ctorDeployMemoryRunPtrPrefixBoolWord ctorDeployMemoryRunPtrPrefixSequence
  abiDecoderBytes abiDecoderGuards abiDecoderContract abiDecoderComposition
  abiDecoderBulk abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader
  ctorDeployMemoryRunPtrPrefixSteps ctorDeployMemoryRunPtrPrefixBoolBody arithmetic
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  codegenRel contextCodegenRel memLocDefs finite_map words pred_set
  abiEncoder emitHelper compileEnv exprLoweringProps fragExec list

Theorem prefix_copy_cnt_success_steps:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  abi_decode_load DLOAD a s = n2w cnt /\
  cnt <= limit /\ limit < dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) GT [Var x; Lit (n2w limit)] [y];
      k = mk_inst (iid+2) ISZERO [Var y] [z];
      l = mk_inst (iid+3) ASSERT [Var z] [];
      s1 = update_var x (n2w cnt) s;
      s2 = update_var y 0w s1;
      s3 = update_var z 1w s2;
      G1 = DRESTRICT G (COMPL {x});
      G2 = DRESTRICT G1 (COMPL {y});
      G3 = DRESTRICT G2 (COMPL {z});
      q1 = step_taint i s s1 tn;
      q2 = step_taint j s1 s2 q1;
      q3 = step_taint k s2 s3 q2
  in
    step_inst_base i s = OK s1 /\
    step_inst_base j s1 = OK s2 /\
    step_inst_base k s2 = OK s3 /\
    step_inst_base l s3 = OK s3 /\
    ghost_step fuel ctx PG G tn i s = (G1,q1) /\
    ghost_step fuel ctx PG G1 q1 j s1 = (G2,q2) /\
    ghost_step fuel ctx PG G2 q2 k s2 = (G3,q3) /\
    ghost_step fuel ctx PG G3 q3 l s3 = (G3,q3) /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    ptr_safe_step D lo fuel ctx fn PG G1 q1 j s1 /\
    ptr_safe_step D lo fuel ctx fn PG G2 q2 k s2 /\
    ptr_safe_step D lo fuel ctx fn PG G3 q3 l s3
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `cnt < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst iid DLOAD [src] [x]) s =
     OK (update_var x (n2w cnt) s)` by
    (drule prefix_dload_step >>
     disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     gvs[abi_decode_load_def, abi_decode_source_def]) >>
  `step_inst_base (mk_inst (iid+1) GT [Var x;Lit (n2w limit)] [y])
     (update_var x (n2w cnt) s) =
     OK (update_var y 0w (update_var x (n2w cnt) s))` by
    simp[step_inst_base_def, exec_pure2_def, mk_inst_def, eval_operand_def,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE, w2n_n2w,
         GREATER_DEF, bool_to_word_def] >>
  `step_inst_base (mk_inst (iid+2) ISZERO [Var y] [z])
     (update_var y 0w (update_var x (n2w cnt) s)) =
     OK (update_var z 1w (update_var y 0w (update_var x (n2w cnt) s)))` by
    simp[step_inst_base_def, exec_pure1_def, mk_inst_def, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
  `eval_operand (Var z)
     (update_var z 1w (update_var y 0w (update_var x (n2w cnt) s))) = SOME 1w` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (drule prefix_assert_step >> disch_then (qspec_then `iid+3` mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_assum `eval_operand src s = SOME a`
        (mp_then Any mp_tac prefix_dload_ghost_step) >>
      disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
      gvs[abi_decode_load_def, abi_decode_source_def]) >>
  conj_tac
  >- (once_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
      irule prefix_compare_ghost_step >> simp[]) >>
  conj_tac
  >- (pure_rewrite_tac[GSYM DRESTRICT_DRESTRICT] >>
      irule prefix_iszero_ghost_step >> simp[]) >>
  conj_tac
  >- (irule prefix_assert_ghost_step >> goal_assum (drule_at Any)) >>
  `allocas_from lo (update_var x (n2w cnt) s) /\
   allocas_from lo (update_var y 0w (update_var x (n2w cnt) s)) /\
   allocas_from lo (update_var z 1w (update_var y 0w (update_var x (n2w cnt) s)))` by
    (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  simp[prefix_dload_ptr_step, prefix_iszero_ptr_step, prefix_assert_ptr_step,
       prefix_dload_output_taint, prefix_guard_output_taint] >>
  irule prefix_compare_ptr_step >>
  simp[prefix_dload_output_taint, op_taint_def, op_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem prefix_bytestring_sentinel_code:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) (DecBytestring n) st = ((),st') ==>
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      iid = st.cs_next_id;
      xs = [mk_inst iid DLOAD [src] [x 0];
            mk_inst (iid+1) GT [Var (x 0);Lit (n2w n)] [x 1];
            mk_inst (iid+2) ISZERO [Var (x 1)] [x 2];
            mk_inst (iid+3) ASSERT [Var (x 2)] [];
            mk_inst (iid+4) DLOADBYTES
              [dst;src;Lit (n2w (abi_decode_bytes_copy_size n))] []]
  in emitted_insts st st' = xs /\
     st'.cs_next_var = st.cs_next_var+3 /\
     st'.cs_current_insts = st.cs_current_insts ++ xs /\
     st'.cs_current_bb = st.cs_current_bb
Proof
  simp[abi_decode_bytes_sentinel, abi_decode_source_opcode_def,
       abi_decode_count_guard_def, abi_decode_copy_opcode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  simp[GSYM listTheory.APPEND_ASSOC, listTheory.DROP_APPEND]
QED

Theorem prefix_copy_pure_taint:
  opc IN {DLOAD;GT;ISZERO} ==>
  step_taint (mk_inst iid opc ops [x]) s (update_var x w s) tn =
    tn with t_var := tn.t_var |+ (x,{})
Proof
  strip_tac >> gvs[] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, mem_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, update_var_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, FLOOKUP_DEF,
       taint_component_equality, EXTENSION, SF CONJ_ss] >>
  namedCases_on `ops` ["", "a tail"] >> simp[out_taint_def] >>
  Cases_on `eval_operand a s` >> simp[] >>
  namedCases_on `tail` ["", "b tail2"] >> simp[out_taint_def] >>
  namedCases_on `tail2` ["", "c tail3"] >> simp[out_taint_def] >>
  Cases_on `tail3` >> simp[out_taint_def]
QED

Theorem prefix_copy_eval_index[local]:
  eval_operand op (s with vs_inst_idx := k) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem prefix_copy_update_index[local]:
  update_var x w (s with vs_inst_idx := m) =
    (update_var x w s) with vs_inst_idx := m
Proof
  simp[update_var_def]
QED

Theorem prefix_copy_taint_index[local]:
  i.inst_opcode IN {DLOAD;GT;ISZERO;DLOADBYTES} ==>
  step_taint i (s with vs_inst_idx := k) (t with vs_inst_idx := j) tn =
    step_taint i s t tn
Proof
  strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, written_taint_def, out_taint_def,
       adopt_reset_def, store_taint_def, imm_taint_def,
       prefix_copy_eval_index]
QED

Theorem prefix_copy_count_success_block:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  abi_decode_load DLOAD a s = n2w cnt /\
  cnt <= limit /\ limit < dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) GT [Var x;Lit (n2w limit)] [y];
      k = mk_inst (iid+2) ISZERO [Var y] [z];
      l = mk_inst (iid+3) ASSERT [Var z] [];
      s1 = update_var x (n2w cnt) s;
      s2 = update_var y 0w s1;
      s3 = update_var z 1w s2;
      G1 = DRESTRICT G (COMPL {x});
      G2 = DRESTRICT G1 (COMPL {y});
      G3 = DRESTRICT G2 (COMPL {z});
      q1 = tn with t_var := tn.t_var |+ (x,{});
      q2 = q1 with t_var := q1.t_var |+ (y,{});
      q3 = q2 with t_var := q2.t_var |+ (z,{})
  in isPREFIX [i;j;k;l] (DROP s.vs_inst_idx bb.bb_instructions) ==>
    run_inst_seq [i;j;k;l] s = OK s3 /\
    (ptr_safe_block D lo fuel ctx fn PG G3 q3 bb
       (s3 with vs_inst_idx := s.vs_inst_idx+4) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `s1 = update_var x (n2w cnt) s` >>
  qabbrev_tac `s2 = update_var y 0w s1` >>
  qabbrev_tac `s3 = update_var z 1w s2` >>
  qabbrev_tac `u = (\j. EL j [s;s1;s2;s3;s3])` >>
  qabbrev_tac `g = (\j. EL j [G;DRESTRICT G (COMPL {x});
    DRESTRICT G (COMPL {x} INTER COMPL {y});
    DRESTRICT G (COMPL {x} INTER COMPL {y} INTER COMPL {z});
    DRESTRICT G (COMPL {x} INTER COMPL {y} INTER COMPL {z})])` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  qabbrev_tac `q2 = q1 with t_var := q1.t_var |+ (y,{})` >>
  qabbrev_tac `q3 = q2 with t_var := q2.t_var |+ (z,{})` >>
  qabbrev_tac `q = (\j. EL j [tn;q1;q2;q3;q3])` >>
  qabbrev_tac `xs = [mk_inst iid DLOAD [src] [x];
    mk_inst (iid+1) GT [Var x;Lit (n2w limit)] [y];
    mk_inst (iid+2) ISZERO [Var y] [z];
    mk_inst (iid+3) ASSERT [Var z] []]` >>
  `!m. eval_operand src (s with vs_inst_idx := m) = SOME a /\
       abi_decode_load DLOAD a (s with vs_inst_idx := m) = n2w cnt /\
       allocas_from lo (s with vs_inst_idx := m)` by
    (gvs[prefix_copy_eval_index, abi_decode_load_def, abi_decode_source_def,
         allocas_from_def] >> metis_tac[]) >>
  `!j. j < LENGTH xs ==>
    step_inst_base (EL j xs) (u j) = OK (u (SUC j)) /\
    step_inst fuel ctx (EL j xs) ((u j) with vs_inst_idx := s.vs_inst_idx+j) =
      OK ((u (SUC j)) with vs_inst_idx := s.vs_inst_idx+j) /\
    ptr_safe_step D lo fuel ctx fn PG (g j) (q j) (EL j xs)
      ((u j) with vs_inst_idx := s.vs_inst_idx+j) /\
    ghost_step fuel ctx PG (g j) (q j) (EL j xs)
      ((u j) with vs_inst_idx := s.vs_inst_idx+j) = (g (SUC j),q (SUC j))` by
    (gen_tac >> simp[Abbr `xs`] >> strip_tac >>
     `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` by decide_tac >>
     mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := s.vs_inst_idx+j`]
       prefix_copy_cnt_success_steps) >>
     asm_simp_tac bool_ss [LET_THM] >>
     simp[Abbr `u`, Abbr `g`, Abbr `q`,
          Abbr `q1`, Abbr `q2`, Abbr `q3`,
          Abbr `s1`, Abbr `s2`, Abbr `s3`, prefix_copy_pure_taint] >>
     rpt strip_tac >> gvs[] >>
     mp_tac prefix_copy_cnt_success_steps >>
     asm_simp_tac bool_ss [LET_THM] >>
     simp[prefix_copy_pure_taint] >>
     rpt strip_tac >>
     gvs[step_inst_non_invoke, mk_inst_def, update_var_def, INTER_ASSOC]) >>
  `u 0 = s /\ g 0 = G /\ q 0 = tn` by
    simp[Abbr `u`, Abbr `g`, Abbr `q`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs` by
    simp[Abbr `xs`, mk_inst_def, is_terminator_def] >>
  drule_all prefix_trace_ptr_safe_block >>
  simp[Abbr `u`, Abbr `g`, Abbr `q`, Abbr `xs`, DRESTRICT_DRESTRICT,
       INTER_ASSOC]
QED

Theorem prefix_copy_success_block:
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) /\
  eval_operand (Var dst) s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME k /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n d /\ w2n d+w2n k <= b+sz /\
  op_taint tn (Var dst) = {} /\ op_taint tn src = {} /\ op_taint tn lenop = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  step_inst fuel ctx (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) s = OK t ==>
  let qt = step_taint (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) s t tn in
    qt.t_mem SUBSET tn.t_mem /\
    DISJOINT (range_bytes [(w2n d,w2n k)]) qt.t_mem /\
    qt.t_var = tn.t_var /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (ptr_safe_block D lo fuel ctx fn PG G qt bb
       (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `ptr_safe_step D lo fuel ctx fn PG G tn
      (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) s` by
    (irule prefix_dloadbytes_ptr_step >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ghost_step fuel ctx PG G tn
      (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) s =
      (G,step_taint (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) s t tn)` by
    (irule prefix_dloadbytes_ghost_step >> goal_assum (drule_at Any)) >>
  `((step_taint (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) s t tn).t_mem
       SUBSET tn.t_mem) /\
    DISJOINT (range_bytes [(w2n d,w2n k)])
      (step_taint (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) s t tn).t_mem` by
    (irule (SRULE [LET_THM] prefix_dloadbytes_clean) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[SRULE [LET_THM] prefix_dloadbytes_taint_frame] >>
  `~is_terminator (mk_inst iid DLOADBYTES [Var dst;src;lenop] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >> simp[]
QED

Theorem prefix_bytestring_success_ghost:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (DecBytestring n) st = ((),st') /\
  fn_has_code st st' fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!v. src = Var v \/ dst = v ==> not_fresh_at st v) /\
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME d /\
  abi_decode_load DLOAD a s = n2w cnt /\ cnt <= n /\ n < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n d /\
  w2n d + abi_decode_bytes_copy_size n <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    qt.t_mem SUBSET tn.t_mem /\
    DISJOINT (range_bytes [(w2n d,abi_decode_bytes_copy_size n)]) qt.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
       FLOOKUP qt.t_var v = FLOOKUP tn.t_var v) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
       (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule prefix_bytestring_sentinel_code >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `x = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `y = "%" ++ toString (st.cs_next_var+1)` >>
  qabbrev_tac `z = "%" ++ toString (st.cs_next_var+2)` >>
  `!v. not_fresh_at st v ==> v <> x /\ v <> y /\ v <> z` by
    (simp[Abbr `x`, Abbr `y`, Abbr `z`, not_fresh_at_def] >> metis_tac[LESS_EQ_ADD]) >>
  `dst <> x /\ dst <> y /\ dst <> z /\
   (!v. src = Var v ==> v <> x /\ v <> y /\ v <> z)` by metis_tac[] >>
  qabbrev_tac `s3 = update_var z 1w (update_var y 0w (update_var x (n2w cnt) s))` >>
  qabbrev_tac `H = DRESTRICT G (COMPL {x} INTER COMPL {y} INTER COMPL {z})` >>
  qabbrev_tac `q3 = tn with t_var := tn.t_var |+ (x,{}) |+ (y,{}) |+ (z,{})` >>
  qabbrev_tac `i = mk_inst (st.cs_next_id+4) DLOADBYTES
    [Var dst;src;Lit (n2w (abi_decode_bytes_copy_size n))] []` >>
  qabbrev_tac `qt = step_taint i s3 t q3` >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> asm_rewrite_tac[GSYM APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >> metis_tac[]) >>
  suspend "certificate"
QED

Resume prefix_bytestring_success_ghost[certificate]:
  qabbrev_tac `xs = [mk_inst st.cs_next_id DLOAD [src] [x];
    mk_inst (st.cs_next_id+1) GT [Var x;Lit (n2w n)] [y];
    mk_inst (st.cs_next_id+2) ISZERO [Var y] [z];
    mk_inst (st.cs_next_id+3) ASSERT [Var z] []]` >>
  `emitted_insts st st' = xs ++ [i]` by
    simp[Abbr `xs`, Abbr `x`, Abbr `y`, Abbr `z`] >>
  `isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (emitted_insts st st') _` mp_tac >>
     asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `[i] ++ l` >> simp[APPEND_ASSOC]) >>
  `!fuel. run_inst_seq xs s = OK s3 /\
    (ptr_safe_block D lo fuel ctx fn PG H q3 bb
       (s3 with vs_inst_idx := s.vs_inst_idx+4) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)` by
    (gen_tac >>
     mp_tac (Q.INST [`iid` |-> `st.cs_next_id`, `limit` |-> `n`]
       prefix_copy_count_success_block) >>
     asm_simp_tac (srw_ss()) [LET_THM, Abbr `s3`, Abbr `H`, Abbr `q3`,
       Abbr `xs`, DRESTRICT_DRESTRICT, INTER_ASSOC]) >>
  `eval_operand (Var dst) s3 = SOME d /\ eval_operand src s3 = SOME a /\
   op_taint q3 (Var dst) = {} /\ op_taint q3 src = {} /\
   FLOOKUP H dst = SOME (b,sz) /\ allocas_from lo s3` by
    (simp[Abbr `s3`, Abbr `q3`, Abbr `H`, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def, allocas_from_def] >>
     Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, op_taint_def,
       FLOOKUP_UPDATE, allocas_from_def] >> metis_tac[]) >>
  `step_inst_base i s3 = OK t` by
    (`run_inst_seq xs s = OK s3` by metis_tac[] >>
     drule run_inst_seq_append >>
     disch_then (qspec_then `[i]` assume_tac) >>
     qpat_x_assum `run_inst_seq (emitted_insts st st') s = OK t` mp_tac >>
     qpat_x_assum `emitted_insts st st' = xs ++ [i]` SUBST1_TAC >>
     asm_rewrite_tac[] >>
     simp[run_inst_seq_def, comp_bind_def, comp_return_def] >>
     Cases_on `step_inst_base i s3` >> simp[]) >>
  suspend "copy"
QED

Resume prefix_bytestring_success_ghost[copy]:
  `!fuel. step_inst fuel ctx i s3 = OK t` by
    simp[step_inst_non_invoke, Abbr `i`, mk_inst_def] >>
  `t = write_memory_with_expansion (w2n d)
      (TAKE (abi_decode_bytes_copy_size n)
        (DROP (w2n a) s3.vs_data_section ++
         REPLICATE (abi_decode_bytes_copy_size n) 0w)) s3` by
    (qpat_assum `eval_operand (Var dst) s3 = SOME d`
       (mp_then (Pos hd) mp_tac prefix_dloadbytes_step) >>
     disch_then (qspecl_then [`src`,`a`,
       `Lit (n2w (abi_decode_bytes_copy_size n))`,
       `n2w (abi_decode_bytes_copy_size n)`] mp_tac) >>
     simp[eval_operand_def] >>
     disch_then (qspecl_then [`st.cs_next_id+4`,`0`,`ctx`] mp_tac) >>
     simp[w2n_n2w] >> gvs[Abbr `i`]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `s3`, update_var_def, write_memory_with_expansion_def] >>
  `!fuel m. step_inst fuel ctx i (s3 with vs_inst_idx := m) =
     OK (t with vs_inst_idx := m)` by
    (rpt gen_tac >>
     `eval_operand (Var dst) (s3 with vs_inst_idx := m) = SOME d` by
       simp[prefix_copy_eval_index] >>
     qpat_assum `eval_operand (Var dst) (s3 with vs_inst_idx := m) = SOME d`
       (mp_then (Pos hd) mp_tac prefix_dloadbytes_step) >>
     disch_then (qspecl_then [`src`,`a`,
       `Lit (n2w (abi_decode_bytes_copy_size n))`,
       `n2w (abi_decode_bytes_copy_size n)`] mp_tac) >>
     simp[prefix_copy_eval_index, eval_operand_def] >>
     disch_then (qspecl_then [`st.cs_next_id+4`,`fuel`,`ctx`] mp_tac) >>
     simp[Abbr `i`, w2n_n2w, write_memory_with_expansion_def]) >>
  `get_instruction bb (s.vs_inst_idx+4) = SOME i` by
    (qpat_assum `isPREFIX (emitted_insts st st') _` mp_tac >>
     qpat_assum `emitted_insts st st' = xs ++ [i]` SUBST1_TAC >>
     rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     `s.vs_inst_idx+4 < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
        simp[Abbr `xs`, LENGTH_DROP] >> decide_tac) >>
     qspecl_then [`4`,`s.vs_inst_idx`,`bb.bb_instructions`] mp_tac rich_listTheory.EL_DROP >>
     simp[get_instruction_def, Abbr `xs`]) >>
  suspend "finish"
QED

Resume prefix_bytestring_success_ghost[finish]:
  qabbrev_tac `u = s3 with vs_inst_idx := s.vs_inst_idx+4` >>
  `get_instruction bb u.vs_inst_idx = SOME
      (mk_inst (st.cs_next_id+4) DLOADBYTES
        [Var dst;src;Lit (n2w (abi_decode_bytes_copy_size n))] []) /\
   eval_operand (Var dst) u = SOME d /\ eval_operand src u = SOME a /\
   eval_operand (Lit (n2w (abi_decode_bytes_copy_size n))) u =
      SOME (n2w (abi_decode_bytes_copy_size n)) /\
   op_taint q3 (Lit (n2w (abi_decode_bytes_copy_size n))) = {} /\
   allocas_from lo u` by
    (simp[Abbr `u`, Abbr `i`, prefix_copy_eval_index,
       eval_operand_def, op_taint_def, allocas_from_def] >>
     gvs[eval_operand_def, lookup_var_def, allocas_from_def] >> metis_tac[]) >>
  `!fuel. qt.t_mem SUBSET q3.t_mem /\
    DISJOINT (range_bytes [(w2n d,abi_decode_bytes_copy_size n)]) qt.t_mem /\
    qt.t_var = q3.t_var /\ qt.t_stor = q3.t_stor /\
    qt.t_trans = q3.t_trans /\ qt.t_imm = q3.t_imm /\
    (ptr_safe_block D lo fuel ctx fn PG H qt bb
       (t with vs_inst_idx := s.vs_inst_idx+5) ==>
     ptr_safe_block D lo fuel ctx fn PG H q3 bb u)` by
    (gen_tac >>
     `step_inst fuel ctx (mk_inst (st.cs_next_id+4) DLOADBYTES
       [Var dst;src;Lit (n2w (abi_decode_bytes_copy_size n))] []) u =
       OK (t with vs_inst_idx := s.vs_inst_idx+4)` by simp[Abbr `i`, Abbr `u`] >>
     `w2n d + w2n (n2w (abi_decode_bytes_copy_size n) : bytes32) <= b+sz` by
       simp[w2n_n2w] >>
     drule_all prefix_copy_success_block >>
     simp[LET_THM, w2n_n2w, Abbr `u`, Abbr `qt`, Abbr `i`,
       prefix_copy_taint_index, mk_inst_def, ADD1]) >>
  qpat_assum `!fuel. qt.t_mem SUBSET _ /\ _` (qspec_then `0` strip_assume_tac) >>
  qexistsl_tac [`H`,`qt`] >>
  `q3.t_mem = tn.t_mem /\ q3.t_stor = tn.t_stor /\
   q3.t_trans = tn.t_trans /\ q3.t_imm = tn.t_imm` by simp[Abbr `q3`] >>
  `qt.t_mem SUBSET tn.t_mem /\ qt.t_stor = tn.t_stor /\
   qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm` by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `v <> x /\ v <> y /\ v <> z` by metis_tac[] >>
      simp[Abbr `H`, FLOOKUP_DRESTRICT, Abbr `q3`, FLOOKUP_UPDATE]) >>
  strip_tac >> gen_tac >>
  `ptr_safe_block D lo fuel ctx fn PG H qt bb
      (t with vs_inst_idx := s.vs_inst_idx+5)` by
    (`LENGTH st'.cs_current_insts = s.vs_inst_idx+5` by simp[] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _`
      (qspec_then `fuel` mp_tac) >>
     simp_tac (srw_ss()) [ptr_safe_run_def] >>
     qpat_assum `t.vs_current_bb = s.vs_current_bb`
       (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `LENGTH st'.cs_current_insts = s.vs_inst_idx+5`
       (fn th => rewrite_tac[th]) >> simp_tac (srw_ss()) []) >>
  `ptr_safe_block D lo fuel ctx fn PG H q3 bb u` by metis_tac[] >>
  `ptr_safe_block D lo fuel ctx fn PG G tn bb s` by metis_tac[] >>
  simp[ptr_safe_run_def]
QED

Finalise prefix_bytestring_success_ghost

Theorem prefix_bulk_sentinel_code:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei ==>
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      xs = [mk_inst st.cs_next_id DLOAD [src] [x 0];
        mk_inst (st.cs_next_id+1) GT [Var (x 0);Lit (n2w maxn)] [x 1];
        mk_inst (st.cs_next_id+2) ISZERO [Var (x 1)] [x 2];
        mk_inst (st.cs_next_id+3) ASSERT [Var (x 2)] [];
        mk_inst (st.cs_next_id+4) DLOAD [src] [x 3];
        mk_inst (st.cs_next_id+5) MSTORE [dst;Var (x 3)] [];
        mk_inst (st.cs_next_id+6) MUL [Var (x 3);Lit (n2w mem_sz)] [x 4];
        mk_inst (st.cs_next_id+7) ADD [src;Lit 32w] [x 5];
        mk_inst (st.cs_next_id+8) ADD [dst;Lit 32w] [x 6];
        mk_inst (st.cs_next_id+9) DLOADBYTES [Var (x 6);Var (x 5);Var (x 4)] []]
  in emitted_insts st st' = xs /\ st'.cs_next_var = st.cs_next_var+7 /\
     st'.cs_current_insts = st.cs_current_insts ++ xs /\
     st'.cs_current_bb = st.cs_current_bb
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_bulk_phases, abi_decode_source_opcode_def,
    abi_decode_dynarray_prefix_def, abi_decode_count_guard_def,
    abi_decode_dynarray_end_guard_def, abi_decode_bulk_body_def,
    abi_decode_array_header_def, abi_decode_bulk_payload_def,
    abi_decode_copy_opcode_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def, LET_THM] >>
  disch_then (SUBST1_TAC o SYM) >>
  simp_tac (srw_ss()) [emitted_insts_def, GSYM APPEND_ASSOC, ADD_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem prefix_bulk_arith_success_block:
  (opc = ADD \/ opc = MUL) /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid opc [a;b] [x]) /\
  eval_operand a s = SOME u /\ eval_operand b s = SOME v /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let t = update_var x (if opc = ADD then u+v else u*v) s;
      H = if opc = ADD then set_prov G [x] (first_prov G [a;b])
          else DRESTRICT G (COMPL {x});
      qt = step_taint (mk_inst iid opc [a;b] [x]) s t tn
  in step_inst_base (mk_inst iid opc [a;b] [x]) s = OK t /\
     qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
     qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
     op_taint qt (Var x) = {} /\
     (!y. y <> x ==> op_taint qt (Var y) = op_taint tn (Var y)) /\
     (ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid opc [a;b] [x]) s` by
    (irule prefix_bool_body_arith_ptr_step >> simp[]) >>
  `!w. (update_var x w s).vs_allocas = s.vs_allocas /\
        (update_var x w s).vs_fmp = s.vs_fmp` by simp[update_var_def] >>
  mp_tac (Q.INST [`t` |-> `update_var x (if opc = ADD then u+v else u*v) s`]
    prefix_bool_body_arith_taint_frame) >>
  simp[] >> strip_tac >>
  `step_inst_base (mk_inst iid opc [a;b] [x]) s =
     OK (update_var x (if opc = ADD then u+v else u*v) s)` by
    (Cases_on `opc = ADD` >> gvs[] >>
     simp[prefix_bool_body_add_step, prefix_bool_body_mul_step]) >>
  asm_rewrite_tac[] >>
  `ghost_step fuel ctx PG G tn (mk_inst iid opc [a;b] [x]) s =
     (if opc = ADD then set_prov G [x] (first_prov G [a;b]) else DRESTRICT G (COMPL {x}),
      step_taint (mk_inst iid opc [a;b] [x]) s
        (update_var x (if opc = ADD then u+v else u*v) s) tn)` by
    (Cases_on `opc = ADD` >> gvs[] >>
     metis_tac[SRULE [LET_THM] prefix_bool_body_add_ghost,
       SRULE [LET_THM] prefix_bool_body_mul_ghost]) >>
  `step_inst fuel ctx (mk_inst iid opc [a;b] [x]) s =
     OK (update_var x (if opc = ADD then u+v else u*v) s)` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~is_terminator (mk_inst iid opc [a;b] [x]).inst_opcode` by
    (gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all ptr_safe_block_step >> gvs[] >> metis_tac[]
QED

Theorem prefix_bulk_header_success_block:
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid MSTORE [Var dst;value] []) /\
  eval_operand (Var dst) s = SOME a /\ eval_operand value s = SOME w /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n a /\ w2n a+32 <= b+sz /\
  op_taint tn (Var dst) = {} /\ op_taint tn value = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let t = mstore (w2n a) w s;
      qt = step_taint (mk_inst iid MSTORE [Var dst;value] []) s t tn
  in step_inst fuel ctx (mk_inst iid MSTORE [Var dst;value] []) s = OK t /\
     qt.t_mem SUBSET tn.t_mem /\
     DISJOINT (range_bytes [(w2n a,32)]) qt.t_mem /\
     qt.t_var = tn.t_var /\ qt.t_stor = tn.t_stor /\
     qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
     (ptr_safe_block D lo fuel ctx fn PG G qt bb
       (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `step_inst fuel ctx (mk_inst iid MSTORE [Var dst;value] []) s =
     OK (mstore (w2n a) w s)` by simp[prefix_mstore_endpoint] >>
  `ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid MSTORE [Var dst;value] []) s` by
    (irule prefix_mstore_ptr_step >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ghost_step fuel ctx PG G tn (mk_inst iid MSTORE [Var dst;value] []) s =
     (G,step_taint (mk_inst iid MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)` by
    (irule prefix_mstore_ghost_step >> goal_assum (drule_at Any)) >>
  `~is_terminator (mk_inst iid MSTORE [Var dst;value] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[SRULE [LET_THM] prefix_mstore_taint_frame, prefix_mstore_mem_taint] >>
  conj_tac >- (simp[range_bytes_def, DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  drule_all ptr_safe_block_step >> simp[]
QED

Theorem prefix_bulk_reload_success_block:
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid DLOAD [src] [x]) /\
  eval_operand src s = SOME a /\ abi_decode_load DLOAD a s = w /\
  op_taint tn src = {} /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let t = update_var x w s;
      H = DRESTRICT G (COMPL {x});
      qt = tn with t_var := tn.t_var |+ (x,{})
  in step_inst_base (mk_inst iid DLOAD [src] [x]) s = OK t /\
     (ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `step_inst_base (mk_inst iid DLOAD [src] [x]) s = OK (update_var x w s)` by
    (drule prefix_dload_step >> disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     gvs[abi_decode_load_def, abi_decode_source_def]) >>
  `step_inst fuel ctx (mk_inst iid DLOAD [src] [x]) s = OK (update_var x w s)` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `ghost_step fuel ctx PG G tn (mk_inst iid DLOAD [src] [x]) s =
     (DRESTRICT G (COMPL {x}),tn with t_var := tn.t_var |+ (x,{}))` by
    (qpat_assum `eval_operand src s = SOME a`
       (mp_then Any mp_tac prefix_dload_ghost_step) >>
     disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     gvs[abi_decode_load_def, abi_decode_source_def, prefix_copy_pure_taint]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid DLOAD [src] [x]) s` by
    (irule prefix_dload_ptr_step >> simp[]) >>
  `~is_terminator (mk_inst iid DLOAD [src] [x]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  asm_rewrite_tac[] >> drule_all ptr_safe_block_step >> simp[]
QED

Theorem prefix_bulk_body_raw:
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME d /\
  abi_decode_load DLOAD a s = n2w cnt /\
  ALL_DISTINCT [r;p;q;z] /\
  (!v. src = Var v \/ dst = v ==> ~MEM v [r;p;q;z]) ==>
  let s1 = update_var r (n2w cnt) s;
      s2 = mstore (w2n d) (n2w cnt) s1;
      s3 = update_var p (n2w (cnt*mem_sz)) s2;
      s4 = update_var q (a+32w) s3;
      s5 = update_var z (d+32w) s4;
      t = write_memory_with_expansion (w2n (d+32w))
        (TAKE (w2n (n2w (cnt*mem_sz):bytes32))
          (DROP (w2n (a+32w)) s.vs_data_section ++
           REPLICATE (w2n (n2w (cnt*mem_sz):bytes32)) 0w)) s5
  in run_inst_seq
    [mk_inst iid DLOAD [src] [r];
     mk_inst (iid+1) MSTORE [Var dst;Var r] [];
     mk_inst (iid+2) MUL [Var r;Lit (n2w mem_sz)] [p];
     mk_inst (iid+3) ADD [src;Lit 32w] [q];
     mk_inst (iid+4) ADD [Var dst;Lit 32w] [z];
     mk_inst (iid+5) DLOADBYTES [Var z;Var q;Var p] []] s = OK t
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `step_inst_base (mk_inst iid DLOAD [src] [r]) s = OK (update_var r (n2w cnt) s)` by
    (qpat_assum `eval_operand src s = SOME a` (mp_then Any mp_tac prefix_dload_step) >>
     disch_then (qspecl_then [`iid`,`r`] mp_tac) >>
     gvs[abi_decode_load_def, abi_decode_source_def]) >>
  simp[run_inst_seq_def, comp_bind_def, comp_return_def] >>
  `dst <> r /\ dst <> p /\ dst <> q /\ dst <> z` by metis_tac[MEM] >>
  `eval_operand (Var dst) (update_var r (n2w cnt) s) = SOME d /\
   eval_operand (Var r) (update_var r (n2w cnt) s) = SOME (n2w cnt)` by
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (iid+1) MSTORE [Var dst;Var r] [])
     (update_var r (n2w cnt) s) =
     OK (mstore (w2n d) (n2w cnt) (update_var r (n2w cnt) s))` by
    (irule prefix_mstore_step >> simp[]) >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `mstore (w2n d) (n2w cnt) s1` >>
  qabbrev_tac `s2 = mstore (w2n d) (n2w cnt) s1` >>
  `eval_operand (Var r) s2 = SOME (n2w cnt)` by
    simp[Abbr `s2`, Abbr `s1`, mstore_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (iid+2) MUL [Var r;Lit (n2w mem_sz)] [p]) s2 =
    OK (update_var p (n2w (cnt*mem_sz)) s2)` by
    (rewrite_tac[GSYM word_mul_n2w] >> irule prefix_bool_body_mul_step >>
     simp[eval_operand_def]) >>
  simp[] >>
  qabbrev_tac `s3 = update_var p (n2w (cnt*mem_sz)) s2` >>
  `eval_operand src s3 = SOME a` by
    (Cases_on `src` >>
     gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`, mstore_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[MEM]) >>
  `step_inst_base (mk_inst (iid+3) ADD [src;Lit 32w] [q]) s3 =
     OK (update_var q (a+32w) s3)` by
    (irule prefix_bool_body_add_step >> simp[eval_operand_def]) >>
  simp[] >>
  qabbrev_tac `s4 = update_var q (a+32w) s3` >>
  `eval_operand (Var dst) s4 = SOME d` by
    gvs[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, mstore_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (iid+4) ADD [Var dst;Lit 32w] [z]) s4 =
     OK (update_var z (d+32w) s4)` by
    (irule prefix_bool_body_add_step >> simp[eval_operand_def]) >>
  simp[] >>
  qabbrev_tac `s5 = update_var z (d+32w) s4` >>
  `eval_operand (Var z) s5 = SOME (d+32w) /\
   eval_operand (Var q) s5 = SOME (a+32w) /\
   eval_operand (Var p) s5 = SOME (n2w (cnt*mem_sz)) /\
   s5.vs_data_section = s.vs_data_section` by
    gvs[Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
      mstore_def, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst 0 ctx (mk_inst (iid+5) DLOADBYTES [Var z;Var q;Var p] []) s5 =
    OK (write_memory_with_expansion (w2n (d+32w))
      (TAKE (w2n (n2w (cnt*mem_sz):bytes32))
        (DROP (w2n (a+32w)) s5.vs_data_section ++
          REPLICATE (w2n (n2w (cnt*mem_sz):bytes32)) 0w)) s5)` by
    (irule prefix_dloadbytes_step >> simp[]) >>
  fs[step_inst_non_invoke, mk_inst_def] >> simp[]
QED

Theorem prefix_bulk_mstore_index[local]:
  mstore a w (s with vs_inst_idx := k) = mstore a w s with vs_inst_idx := k
Proof
  simp[mstore_def]
QED

Theorem prefix_bulk_write_index[local]:
  write_memory_with_expansion a bs (s with vs_inst_idx := k) =
    write_memory_with_expansion a bs s with vs_inst_idx := k
Proof
  simp[write_memory_with_expansion_def]
QED

Theorem prefix_bulk_body_success_block:
  let ys =
    [mk_inst iid DLOAD [src] [x];
     mk_inst (iid+1) MSTORE [Var dst;Var x] [];
     mk_inst (iid+2) MUL [Var x;Lit (n2w mem_sz)] [p];
     mk_inst (iid+3) ADD [src;Lit 32w] [q];
     mk_inst (iid+4) ADD [Var dst;Lit 32w] [z];
     mk_inst (iid+5) DLOADBYTES [Var z;Var q;Var p] []]
  in ALL_DISTINCT [x;p;q;z] /\
     (!v. src = Var v \/ dst = v ==> ~MEM v [x;p;q;z]) /\
     eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME d /\
     abi_decode_load DLOAD a s = n2w cnt /\
     cnt*mem_sz < dimword (:256) /\
     w2n d+32+cnt*mem_sz < dimword (:256) /\
     FLOOKUP G dst = SOME (b,sz) /\ b <= w2n d /\
     w2n d+32+cnt*mem_sz <= b+sz /\
     op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
     allocas_from lo s /\ ~ctx_has_dalloca ctx /\
     isPREFIX ys (DROP s.vs_inst_idx bb.bb_instructions) /\
     run_inst_seq ys s = OK t ==>
     ?H qt.
       qt.t_mem SUBSET tn.t_mem /\
       DISJOINT (range_bytes [(w2n d,32+cnt*mem_sz)]) qt.t_mem /\
       qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
       (!v. ~MEM v [x;p;q;z] ==>
         FLOOKUP H v = FLOOKUP G v /\ FLOOKUP qt.t_var v = FLOOKUP tn.t_var v) /\
       (!fuel. ptr_safe_block D lo fuel ctx fn PG H qt bb
         (t with vs_inst_idx := s.vs_inst_idx+6) ==>
         ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `isPREFIX ys _` >> strip_tac >>
  `!j. j < 6 ==> get_instruction bb (s.vs_inst_idx+j) = SOME (EL j ys)` by
    (rpt strip_tac >>
     qpat_x_assum `isPREFIX _ _` mp_tac >>
     rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     `LENGTH ys = 6` by simp[Abbr `ys`] >>
     `s.vs_inst_idx+j < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
        simp[LENGTH_DROP] >> decide_tac) >>
     qspecl_then [`j`,`s.vs_inst_idx`,`bb.bb_instructions`] mp_tac rich_listTheory.EL_DROP >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  qabbrev_tac `s1 = update_var x (n2w cnt) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {x})` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  `!fuel. ptr_safe_block D lo fuel ctx fn PG G1 q1 bb s1 ==>
    ptr_safe_block D lo fuel ctx fn PG G tn bb s` by
    (gen_tac >>
     `get_instruction bb s.vs_inst_idx = SOME (mk_inst iid DLOAD [src] [x])` by
       (qpat_x_assum `!j. j < 6 ==> _` (qspec_then `0` mp_tac) >> simp[Abbr `ys`]) >>
     drule_all prefix_bulk_reload_success_block >>
     disch_then (qspecl_then [`fuel`,`fn`,`PG`,`G`,`D`] mp_tac) >>
     simp[LET_THM, Abbr `s1`, Abbr `G1`, Abbr `q1`]) >>
  `get_instruction bb s1.vs_inst_idx = SOME
    (mk_inst (iid+1) MSTORE [Var dst;Var x] [])` by
    (simp[Abbr `s1`, ADD1] >>
     qpat_x_assum `!j. j < 6 ==> _` (qspec_then `1` mp_tac) >> simp[Abbr `ys`]) >>
  `eval_operand (Var dst) s1 = SOME d /\
   eval_operand (Var x) s1 = SOME (n2w cnt) /\
   FLOOKUP G1 dst = SOME (b,sz) /\
   op_taint q1 (Var dst) = {} /\ op_taint q1 (Var x) = {} /\
   allocas_from lo s1 /\ w2n d+32 <= b+sz` by
    (simp[Abbr `s1`, Abbr `G1`, Abbr `q1`,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, allocas_from_def] >>
     fs[MEM, eval_operand_def, lookup_var_def, op_taint_def, allocas_from_def] >>
     metis_tac[DECIDE ``n+32+k <= m ==> n+32 <= m``]) >>
  drule_all prefix_bulk_header_success_block >>
  disch_then (mp_tac o SRULE [LET_THM, FORALL_AND_THM]) >>
  qabbrev_tac `h = mk_inst (iid+1) MSTORE [Var dst;Var x] []` >>
  qabbrev_tac `r2 = mstore (w2n d) (n2w cnt) s1` >>
  qabbrev_tac `s2 = r2 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `q2 = step_taint h s1 r2 q1` >> strip_tac >>
  `get_instruction bb s2.vs_inst_idx = SOME
    (mk_inst (iid+2) MUL [Var x;Lit (n2w mem_sz)] [p])` by
    (simp[Abbr `s2`, Abbr `s1`, ADD1] >>
     qpat_x_assum `!j. j < 6 ==> _` (qspec_then `2` mp_tac) >> simp[Abbr `ys`]) >>
  `eval_operand (Var x) s2 = SOME (n2w cnt) /\
   eval_operand (Lit (n2w mem_sz)) s2 = SOME (n2w mem_sz) /\
   op_taint q2 (Var x) = {} /\ op_taint q2 (Lit (n2w mem_sz)) = {} /\
   allocas_from lo s2` by
    (simp[Abbr `s2`, Abbr `r2`, Abbr `s1`, mstore_def, update_var_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def,
       Abbr `q1`, allocas_from_def] >>
     fs[allocas_from_def, op_taint_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`] prefix_bulk_arith_success_block)) >>
  disch_then (mp_tac o SRULE [LET_THM, FORALL_AND_THM]) >>
  qabbrev_tac `i2 = mk_inst (iid+2) MUL [Var x;Lit (n2w mem_sz)] [p]` >>
  qabbrev_tac `r3 = update_var p ((n2w cnt:bytes32)*n2w mem_sz) s2` >>
  qabbrev_tac `s3 = r3 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  qabbrev_tac `G3 = DRESTRICT G1 (COMPL {p})` >>
  qabbrev_tac `q3 = step_taint i2 s2 r3 q2` >> strip_tac >>
  `get_instruction bb s3.vs_inst_idx = SOME
    (mk_inst (iid+3) ADD [src;Lit 32w] [q])` by
    (simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, ADD1] >>
     qpat_x_assum `!j. j < 6 ==> _` (qspec_then `3` mp_tac) >> simp[Abbr `ys`]) >>
  `eval_operand src s3 = SOME a /\ eval_operand (Lit 32w) s3 = SOME 32w /\
   op_taint q3 src = {} /\ op_taint q3 (Lit 32w) = {} /\ allocas_from lo s3` by
    (simp[Abbr `s3`, Abbr `r3`, Abbr `s2`, Abbr `r2`, Abbr `s1`,
       update_var_def, mstore_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
     Cases_on `src` >>
     fs[MEM, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       op_taint_def, Abbr `q1`, allocas_from_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] prefix_bulk_arith_success_block)) >>
  disch_then (mp_tac o SRULE [LET_THM, FORALL_AND_THM]) >>
  qabbrev_tac `i3 = mk_inst (iid+3) ADD [src;Lit 32w] [q]` >>
  qabbrev_tac `r4 = update_var q (a+32w) s3` >>
  qabbrev_tac `s4 = r4 with vs_inst_idx := SUC s3.vs_inst_idx` >>
  qabbrev_tac `G4 = set_prov G3 [q] (first_prov G3 [src;Lit 32w])` >>
  qabbrev_tac `q4 = step_taint i3 s3 r4 q3` >> strip_tac >>
  `get_instruction bb s4.vs_inst_idx = SOME
    (mk_inst (iid+4) ADD [Var dst;Lit 32w] [z])` by
    (simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, ADD1] >>
     qpat_x_assum `!j. j < 6 ==> _` (qspec_then `4` mp_tac) >> simp[Abbr `ys`]) >>
  `eval_operand (Var dst) s4 = SOME d /\ eval_operand (Lit 32w) s4 = SOME 32w /\
   op_taint q4 (Var dst) = {} /\ op_taint q4 (Lit 32w) = {} /\ allocas_from lo s4` by
    (simp[Abbr `s4`, Abbr `r4`, Abbr `s3`, Abbr `r3`, Abbr `s2`,
       Abbr `r2`, Abbr `s1`, update_var_def, mstore_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def,
       allocas_from_def] >>
     fs[MEM, eval_operand_def, lookup_var_def, op_taint_def,
       Abbr `q1`, allocas_from_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] prefix_bulk_arith_success_block)) >>
  disch_then (mp_tac o SRULE [LET_THM, FORALL_AND_THM]) >>
  qabbrev_tac `i4 = mk_inst (iid+4) ADD [Var dst;Lit 32w] [z]` >>
  qabbrev_tac `r5 = update_var z (d+32w) s4` >>
  qabbrev_tac `s5 = r5 with vs_inst_idx := SUC s4.vs_inst_idx` >>
  qabbrev_tac `G5 = set_prov G4 [z] (first_prov G4 [Var dst;Lit 32w])` >>
  qabbrev_tac `q5 = step_taint i4 s4 r5 q4` >> strip_tac >>
  `get_instruction bb s5.vs_inst_idx = SOME
    (mk_inst (iid+5) DLOADBYTES [Var z;Var q;Var p] [])` by
    (simp[Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, ADD1] >>
     qpat_x_assum `!j. j < 6 ==> _` (qspec_then `5` mp_tac) >> simp[Abbr `ys`]) >>
  `eval_operand (Var z) s5 = SOME (d+32w) /\
   eval_operand (Var q) s5 = SOME (a+32w) /\
   eval_operand (Var p) s5 = SOME (n2w (cnt*mem_sz)) /\
   op_taint q5 (Var z) = {} /\ op_taint q5 (Var q) = {} /\
   op_taint q5 (Var p) = {} /\ allocas_from lo s5` by
    (simp[Abbr `s5`, Abbr `r5`, Abbr `s4`, Abbr `r4`, Abbr `s3`,
       Abbr `r3`, update_var_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, GSYM word_mul_n2w, op_taint_def, allocas_from_def] >>
     fs[ALL_DISTINCT, op_taint_def, allocas_from_def] >> metis_tac[]) >>
  `dst <> x /\ dst <> p /\ dst <> q /\ dst <> z` by metis_tac[MEM] >>
  `FLOOKUP G4 dst = SOME (b,sz)` by
    (Cases_on `first_prov G3 [src;Lit 32w]` >>
     simp[Abbr `G4`, set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
          Abbr `G3`, Abbr `G1`]) >>
  `FLOOKUP G5 z = SOME (b,sz)` by
    simp[Abbr `G5`, set_prov_def, first_prov_def, op_prov_def, FLOOKUP_UPDATE] >>
  `w2n (d+32w) = w2n d+32 /\ w2n (n2w (cnt*mem_sz):bytes32) = cnt*mem_sz` by
    (`w2n d+32 < dimword (:256)` by decide_tac >>
     simp[w2n_add_2, w2n_n2w, LESS_MOD]) >>
  `b <= w2n (d+32w) /\
   w2n (d+32w)+w2n (n2w (cnt*mem_sz):bytes32) <= b+sz` by decide_tac >>
  `!fuel. step_inst fuel ctx (mk_inst (iid+5) DLOADBYTES [Var z;Var q;Var p] []) s5 =
    OK (write_memory_with_expansion (w2n (d+32w))
      (TAKE (w2n (n2w (cnt*mem_sz):bytes32)) (DROP (w2n (a+32w)) s5.vs_data_section ++
         REPLICATE (w2n (n2w (cnt*mem_sz):bytes32)) 0w)) s5)` by
    (gen_tac >> irule prefix_dloadbytes_step >> simp[]) >>
  qpat_x_assum `!fuel. step_inst _ _ (mk_inst (iid+5) _ _ _) _ = _`
    (assume_tac o SRULE [step_inst_non_invoke, mk_inst_def]) >>
  qpat_assum `get_instruction bb s5.vs_inst_idx = _`
    (assume_tac o SRULE [mk_inst_def]) >>
  drule_all (SRULE [step_inst_non_invoke, mk_inst_def] prefix_copy_success_block) >>
  disch_then (mp_tac o SRULE [LET_THM, FORALL_AND_THM, GSYM mk_inst_def]) >>
  simp[LESS_MOD] >>
  qabbrev_tac `i5 = mk_inst (iid+5) DLOADBYTES [Var z;Var q;Var p] []` >>
  qabbrev_tac `r6 = write_memory_with_expansion (w2n d+32)
      (TAKE (cnt*mem_sz) (DROP (w2n (a+32w)) s5.vs_data_section ++
         REPLICATE (cnt*mem_sz) 0w)) s5` >>
  qabbrev_tac `q6 = step_taint i5 s5 r6 q5` >> strip_tac >>
  qexistsl [`G5`,`q6`] >>
  rpt conj_tac
  >- (fs[Abbr `q1`] >> metis_tac[SUBSET_TRANS])
  >- (`range_bytes [(w2n d,32+cnt*mem_sz)] =
         range_bytes [(w2n d,32)] UNION range_bytes [(w2n d+32,cnt*mem_sz)]` by
        (simp[range_bytes_def, EXTENSION] >> decide_tac) >>
      fs[DISJOINT_UNION] >> metis_tac[DISJOINT_SUBSET])
  >- simp[Abbr `q1`]
  >- simp[Abbr `q1`]
  >- simp[Abbr `q1`]
  >- (gen_tac >> disch_tac >> conj_tac
      >- (Cases_on `first_prov G3 [src;Lit 32w]` >>
          simp[Abbr `G5`, Abbr `G4`, Abbr `G3`, Abbr `G1`,
            first_prov_def, op_prov_def, set_prov_def,
            FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
      simp[] >>
      simp[Abbr `q5`, Abbr `q4`, Abbr `q3`, Abbr `q1`,
        Abbr `i4`, Abbr `i3`, Abbr `i2`, Abbr `r5`, Abbr `r4`, Abbr `r3`,
        step_taint_def, mk_inst_def, set_var_taint_def, adopt_reset_def,
        update_var_def, FLOOKUP_UPDATE]) >>
  `run_inst_seq
    [mk_inst iid DLOAD [src] [x];
     mk_inst (iid+1) MSTORE [Var dst;Var x] [];
     mk_inst (iid+2) MUL [Var x;Lit (n2w mem_sz)] [p];
     mk_inst (iid+3) ADD [src;Lit 32w] [q];
     mk_inst (iid+4) ADD [Var dst;Lit 32w] [z];
     mk_inst (iid+5) DLOADBYTES [Var z;Var q;Var p] []] s = OK t` by
    fs[Abbr `ys`, Abbr `h`, Abbr `i2`, Abbr `i3`, Abbr `i4`, Abbr `i5`] >>
  `r6 with vs_inst_idx := SUC s5.vs_inst_idx =
    t with vs_inst_idx := s.vs_inst_idx+6` by
    (drule_all prefix_bulk_body_raw >>
     disch_then (qspecl_then [`mem_sz`,`iid`] mp_tac) >>
     simp[LET_THM] >> strip_tac >>
     `s5.vs_data_section = s.vs_data_section` by
       simp[Abbr `s5`, Abbr `r5`, Abbr `s4`, Abbr `r4`,
         Abbr `s3`, Abbr `r3`, Abbr `s2`, Abbr `r2`, Abbr `s1`,
         update_var_def, mstore_def] >>
     simp[Abbr `r6`, Abbr `s5`, Abbr `r5`, Abbr `s4`, Abbr `r4`,
       Abbr `s3`, Abbr `r3`, Abbr `s2`, Abbr `r2`, Abbr `s1`,
       prefix_copy_update_index, prefix_bulk_mstore_index, prefix_bulk_write_index,
       GSYM word_mul_n2w, LESS_MOD, ADD1]) >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!fuel. _ ==> ptr_safe_block D lo fuel ctx fn PG G tn bb s` irule >>
  qpat_x_assum `!fuel fn PG D. _ ==> ptr_safe_block D lo fuel ctx fn PG G1 q1 bb s1` irule >>
  qpat_x_assum `!fuel fn PG G D. _ ==> ptr_safe_block D lo fuel ctx fn PG G q2 bb s2` irule >>
  qpat_x_assum `!fuel fn PG G D. _ ==> ptr_safe_block D lo fuel ctx fn PG G q3 bb s3` irule >>
  qpat_x_assum `!fuel fn PG G D. _ ==> ptr_safe_block D lo fuel ctx fn PG G q4 bb s4` irule >>
  fs[Abbr `G5`, Abbr `G4`, Abbr `G3`] >>
  first_x_assum irule >> simp[]
QED

Theorem prefix_bulk_success_ghost:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  fn_has_code st st' fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!v. src = Var v \/ dst = v ==> not_fresh_at st v) /\
  eval_operand src s = SOME a /\ eval_operand (Var dst) s = SOME d /\
  abi_decode_load DLOAD a s = n2w cnt /\ cnt <= maxn /\ maxn < dimword (:256) /\
  cnt*mem_sz < dimword (:256) /\ w2n d+32+cnt*mem_sz < dimword (:256) /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n d /\
  w2n d+32+cnt*mem_sz <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    qt.t_mem SUBSET tn.t_mem /\
    DISJOINT (range_bytes [(w2n d,32+cnt*mem_sz)]) qt.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
       FLOOKUP qt.t_var v = FLOOKUP tn.t_var v) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
       (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all prefix_bulk_sentinel_code >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `x = (\k. "%" ++ toString (st.cs_next_var+k))` >>
  `!v k. not_fresh_at st v ==> v <> x k` by
    (simp[Abbr `x`, not_fresh_at_def] >> metis_tac[LESS_EQ_ADD]) >>
  `!k. dst <> x k /\ (!v. src = Var v ==> v <> x k)` by metis_tac[] >>
  qabbrev_tac `s3 = update_var (x 2) 1w
    (update_var (x 1) 0w (update_var (x 0) (n2w cnt) s))` >>
  qabbrev_tac `G3 = DRESTRICT G (COMPL {x 0} INTER COMPL {x 1} INTER COMPL {x 2})` >>
  qabbrev_tac `q3 = tn with t_var := tn.t_var |+ (x 0,{}) |+ (x 1,{}) |+ (x 2,{})` >>
  qabbrev_tac `xs = [mk_inst st.cs_next_id DLOAD [src] [x 0];
    mk_inst (st.cs_next_id+1) GT [Var (x 0);Lit (n2w maxn)] [x 1];
    mk_inst (st.cs_next_id+2) ISZERO [Var (x 1)] [x 2];
    mk_inst (st.cs_next_id+3) ASSERT [Var (x 2)] []]` >>
  qabbrev_tac `ys = [mk_inst (st.cs_next_id+4) DLOAD [src] [x 3];
    mk_inst (st.cs_next_id+5) MSTORE [Var dst;Var (x 3)] [];
    mk_inst (st.cs_next_id+6) MUL [Var (x 3);Lit (n2w mem_sz)] [x 4];
    mk_inst (st.cs_next_id+7) ADD [src;Lit 32w] [x 5];
    mk_inst (st.cs_next_id+8) ADD [Var dst;Lit 32w] [x 6];
    mk_inst (st.cs_next_id+9) DLOADBYTES [Var (x 6);Var (x 5);Var (x 4)] []]` >>
  `emitted_insts st st' = xs ++ ys` by simp[Abbr `xs`, Abbr `ys`] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (qpat_x_assum `fn_has_code st st' fn` mp_tac >>
     simp_tac (srw_ss()) [fn_has_code_def] >> strip_tac >> metis_tac[]) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> asm_rewrite_tac[GSYM APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> simp[Abbr `xs`]) >>
  suspend "count"
QED

Resume prefix_bulk_success_ghost[count]:
  `isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (emitted_insts st st') _` mp_tac >>
     asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `ys ++ l` >> simp[APPEND_ASSOC]) >>
  `!fuel. run_inst_seq xs s = OK s3 /\
    (ptr_safe_block D lo fuel ctx fn PG G3 q3 bb
       (s3 with vs_inst_idx := s.vs_inst_idx+4) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)` by
    (gen_tac >>
     simp_tac (srw_ss()) [Abbr `s3`, Abbr `G3`, Abbr `q3`, Abbr `xs`] >>
     irule (SRULE [LET_THM, DRESTRICT_DRESTRICT, INTER_ASSOC]
       prefix_copy_count_success_block) >> simp[] >>
     qpat_x_assum `s.vs_inst_idx = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     fs[]) >>
  `eval_operand src s3 = SOME a /\ eval_operand (Var dst) s3 = SOME d /\
   abi_decode_load DLOAD a s3 = n2w cnt` by
    (simp[Abbr `s3`, abi_decode_load_def, abi_decode_source_def,
       update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
     Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       abi_decode_load_def, abi_decode_source_def] >> metis_tac[]) >>
  `ALL_DISTINCT [x 3;x 4;x 5;x 6]` by simp[Abbr `x`] >>
  qabbrev_tac `s4 = update_var (x 3) (n2w cnt) s3` >>
  qabbrev_tac `s5 = mstore (w2n d) (n2w cnt) s4` >>
  qabbrev_tac `s6 = update_var (x 4) (n2w (cnt*mem_sz)) s5` >>
  qabbrev_tac `s7 = update_var (x 5) (a+32w) s6` >>
  qabbrev_tac `s8 = update_var (x 6) (d+32w) s7` >>
  `run_inst_seq ys s3 = OK
     (write_memory_with_expansion (w2n (d+32w))
       (TAKE (w2n (n2w (cnt*mem_sz):bytes32))
         (DROP (w2n (a+32w)) s3.vs_data_section ++
           REPLICATE (w2n (n2w (cnt*mem_sz):bytes32)) 0w)) s8)` by
    (simp_tac (srw_ss()) [Abbr `ys`, Abbr `s8`, Abbr `s7`, Abbr `s6`,
       Abbr `s5`, Abbr `s4`] >>
     irule (SRULE [LET_THM, GSYM ADD_ASSOC]
       (Q.INST [`iid` |-> `st.cs_next_id+4`] prefix_bulk_body_raw)) >>
     fs[ALL_DISTINCT] >> metis_tac[]) >>
  `t = write_memory_with_expansion (w2n (d+32w))
       (TAKE (w2n (n2w (cnt*mem_sz):bytes32))
         (DROP (w2n (a+32w)) s3.vs_data_section ++
           REPLICATE (w2n (n2w (cnt*mem_sz):bytes32)) 0w)) s8` by
    (qpat_x_assum `run_inst_seq (emitted_insts st st') s = OK t` mp_tac >>
     qpat_assum `emitted_insts st st' = xs ++ ys` SUBST1_TAC >>
     `run_inst_seq xs s = OK s3` by metis_tac[] >>
     drule run_inst_seq_append >> disch_then (qspec_then `ys` assume_tac) >>
     asm_rewrite_tac[] >> simp[]) >>
  suspend "body"
QED

Resume prefix_bulk_success_ghost[body]:
  `op_taint q3 src = {} /\ op_taint q3 (Var dst) = {} /\
   FLOOKUP G3 dst = SOME (b,sz) /\ allocas_from lo s3` by
    (simp[Abbr `s3`, Abbr `q3`, Abbr `G3`, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def, allocas_from_def] >>
     Cases_on `src` >> gvs[op_taint_def, FLOOKUP_UPDATE, allocas_from_def] >> metis_tac[]) >>
  qabbrev_tac `u3 = s3 with vs_inst_idx := s.vs_inst_idx+4` >>
  `isPREFIX ys (DROP u3.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (emitted_insts st st') _` mp_tac >>
     asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     `LENGTH xs = 4` by simp[Abbr `xs`] >>
     `DROP (s.vs_inst_idx+4) bb.bb_instructions = ys ++ l` by
       (qpat_x_assum `DROP _ _ = xs ++ ys ++ l`
          (mp_tac o AP_TERM ``DROP 4 : instruction list -> instruction list``) >>
        simp[rich_listTheory.DROP_DROP_T, ADD_COMM, Abbr `xs`]) >>
     fs[Abbr `u3`, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `run_inst_seq ys s3 = OK t` by metis_tac[] >>
  `run_inst_seq ys u3 = OK (t with vs_inst_idx := s.vs_inst_idx+4)` by
    (simp[Abbr `u3`, run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def,
       Abbr `ys`, mk_inst_def, is_terminator_def]) >>
  `eval_operand src u3 = SOME a /\ eval_operand (Var dst) u3 = SOME d /\
   abi_decode_load DLOAD a u3 = n2w cnt /\ allocas_from lo u3` by
    (fs[Abbr `u3`, prefix_copy_eval_index, abi_decode_load_def,
      abi_decode_source_def, allocas_from_def] >> metis_tac[]) >>
  qpat_assum `isPREFIX ys (DROP u3.vs_inst_idx _)` mp_tac >>
  simp_tac (srw_ss()) [Abbr `ys`, GSYM ADD_ASSOC] >> strip_tac >>
  qpat_assum `run_inst_seq _ u3 = _` mp_tac >>
  simp_tac (srw_ss()) [GSYM ADD_ASSOC] >> strip_tac >>
  `!v. src = Var v \/ dst = v ==> ~MEM v [x 3;x 4;x 5;x 6]` by
    (simp[MEM] >> metis_tac[]) >>
  qpat_assum `ALL_DISTINCT [x 3;x 4;x 5;x 6]`
    (mp_then (Pat `ALL_DISTINCT _`)
      (fn th => mp_tac (REWRITE_RULE [GSYM ADD_ASSOC]
        (Q.INST [`t` |-> `t with vs_inst_idx := s.vs_inst_idx+4`]
          (SPEC_ALL th))))
      (BETA_RULE (REWRITE_RULE [LET_THM]
        (Q.INST [`iid` |-> `st.cs_next_id+4`, `s` |-> `u3`,
          `G` |-> `G3`, `tn` |-> `q3`] prefix_bulk_body_success_block)))) >>
  (impl_tac >- (simp[] >> metis_tac[MEM])) >>
  strip_tac >>
  `LENGTH st'.cs_current_insts = s.vs_inst_idx+10` by simp[] >>
  `!fuel. ptr_safe_block D lo fuel ctx fn PG H qt bb
      (t with vs_inst_idx := LENGTH st'.cs_current_insts) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s` by
    (gen_tac >> strip_tac >>
     `ptr_safe_block D lo fuel ctx fn PG G3 q3 bb u3` by
       (qpat_x_assum `!fuel. _ ==> ptr_safe_block D lo fuel ctx fn PG G3 q3 bb u3`
          irule >>
        qpat_x_assum `ptr_safe_block D lo fuel ctx fn PG H qt bb _` mp_tac >>
        simp[Abbr `u3`, ADD_ASSOC]) >> metis_tac[]) >>
  `qt.t_mem SUBSET tn.t_mem /\ qt.t_stor = tn.t_stor /\
   qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm` by
    (qpat_x_assum `qt.t_mem SUBSET _` mp_tac >>
     qpat_x_assum `qt.t_stor = _` mp_tac >>
     qpat_x_assum `qt.t_trans = _` mp_tac >>
     qpat_x_assum `qt.t_imm = _` mp_tac >> simp[Abbr `q3`]) >>
  qexistsl_tac [`H`,`qt`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (rpt strip_tac >>
     `~MEM v [x 3;x 4;x 5;x 6]` by (simp[MEM] >> metis_tac[]) >>
     first_x_assum drule >> simp[Abbr `G3`, Abbr `q3`, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE] >> metis_tac[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `t = write_memory_with_expansion _ _ _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [Abbr `s8`, Abbr `s7`, Abbr `s6`, Abbr `s5`,
       Abbr `s4`, Abbr `s3`, update_var_def, mstore_def,
       write_memory_with_expansion_def, LET_THM]) >>
  strip_tac >> gen_tac >>
  `ptr_safe_block D lo fuel ctx fn PG H qt bb
      (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _`
       (qspec_then `fuel` mp_tac) >>
     qpat_assum `t = write_memory_with_expansion _ _ _`
       (fn th => rewrite_tac[GSYM th]) >>
     simp_tac (srw_ss()) [ptr_safe_run_def] >>
     qpat_assum `t.vs_current_bb = s.vs_current_bb`
       (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb`
       (fn th => rewrite_tac[th]) >> simp_tac (srw_ss()) []) >>
  `ptr_safe_block D lo fuel ctx fn PG G tn bb s` by metis_tac[] >>
  simp[ptr_safe_run_def]
QED

Finalise prefix_bulk_success_ghost

val _ = export_theory();
