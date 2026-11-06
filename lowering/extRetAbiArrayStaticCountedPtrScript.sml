(* Actual dynamic-length/static-element array compiler integration. *)
Theory extRetAbiArrayStaticCountedPtr
Ancestors
  extRetAbiArrayStaticLoopPtr extRetAbiArrayInitPtr extRetCopyCountedPtr
  extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr abiEncoderArrayCode
  abiEncoderArrayContext abiEncoderArrayPhaseAppend abiEncoderArrayPhases
  abiEncoderArrayHeader abiDecoderIndexInit abiEncoderCounters abiDecoderLoopEmit
  robustCopyTransportPtr abiEncoderInputFrame valueEncodingProofs bodyPtrDefs fragGasPathPtr fragExec
  emitHelperProps exprLoweringProps compileEnv emitHelper context
  bodyPtrCtrlCases venomInst abiEncoderInput representationCleanPtr valueEncodingProps
  venomState venomExecSemantics ptrDiscipline words finite_map list pred_set arithmetic

(* Retain all producer frames while transporting the robust source and the
   already encoded destination header through scratch allocation/reset. *)
Theorem abi_array_static_index_init_counted_ptr[local]:
  abi_decode_index_init sa = (Var ip,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s scap /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s dcap /\
  32 <= dcap /\
  (w2n a+scap <= addr \/ addr+32 <= w2n a) /\
  (w2n b+dcap <= addr \/ addr+32 <= w2n b) /\
  mem_bytes_at (w2n b) 32 s.vs_memory = header /\
  (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input info ty v (w2n a) scap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    mload addr sf = 0w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
    lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap /\
    mem_bytes_at (w2n b) 32 sf.vs_memory = header /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input info ty v (w2n a) scap mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_decode_index_init_counted_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
   lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `!off len. (off+len <= addr \/ addr+32 <= off) ==>
    mem_bytes_at off len sf.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >> irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     `mem_bytes_at (off+x) 1 sf.vs_memory = mem_bytes_at (off+x) 1 s.vs_memory` by
       (qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
        simp[mem_agree_outside_def] >> strip_tac >> first_x_assum irule >>
        simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  `mem_bytes_at (w2n a) scap sf.vs_memory = mem_bytes_at (w2n a) scap s.vs_memory` by metis_tac[] >>
  `mem_bytes_at (w2n b) 32 sf.vs_memory = header` by
    (qpat_x_assum `w2n b+dcap <= addr \/ _` strip_assume_tac >>
     `w2n b+32 <= addr \/ addr+32 <= w2n b` by decide_tac >> metis_tac[]) >>
  `!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem` by
    (rpt strip_tac >> `i < addr \/ addr+32 <= i` by decide_tac >> metis_tac[]) >>
  `!i. i < scap ==> (w2n a+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[] >>
  rpt strip_tac >> drule_all copied_window_agree_witness >> strip_tac >>
  `abi_encoder_input info ty v (w2n a) scap mix` by metis_tac[] >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED

Theorem abi_array_static_exit_counted_ptr[local]:
  abi_encode_array_static_exit (Var src) asz sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  mload (w2n a) s = n2w n /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+n*asz)) /\ op_taint tnf out = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_array_static_exit _ _ _ = _` mp_tac >>
  simp[abi_encode_array_static_exit_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (len,sc)` >>
  rename1 `emit_op MUL [len;_] sc = (payload,sd)` >>
  `?lv pv ov. len = Var lv /\ payload = Var pv /\ out = Var ov` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    (imp_res_tac emit_op_extends >> gvs[cs_extends_def, inst_extends_def, same_blocks_def]) >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x /\ not_fresh_at sd x` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op MUL _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> decide_tac) >>
  drule_all emit_mload_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Var lv) sf = SOME (n2w n) /\
   eval_operand (Lit (n2w asz)) sf = SOME (n2w asz) /\
   op_taint tnf (Lit (n2w asz)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_bulk_binop_counted_ptr |>
    Q.INST [`opc` |-> `MUL`,`f` |-> `word_mul`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] strip_assume_tac) >>
  `eval_operand (Lit 32w) sf' = SOME 32w /\
   eval_operand (Var pv) sf' = SOME (n2w (n*asz)) /\
   op_taint tnf' (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def, GSYM word_mul_n2w] >>
  drule_all (emit_copy_len_binop_counted_ptr |>
    Q.INST [`opc` |-> `ADD`,`f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`Gf'`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`,`tnf''`,`sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  simp[eval_operand_def, GSYM word_add_n2w, WORD_ADD_COMM] >> metis_tac[]
QED

Theorem abi_array_header_entry_counted_ptr[local]:
  abi_encode_array_header ip count_op sa = ((hdr,body_lbl,exit_lbl),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to hdr s))
Proof
  strip_tac >>
  qabbrev_tac `cut = sa with cs_current_insts := sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label hdr] []]` >>
  `fn_has_code sa cut fn` by
    (gvs[abi_encode_array_header_shape, fn_has_code_def, emitted_blocks_def, Abbr `cut`] >>
     first_x_assum (qspec_then `<|bb_label := sa.cs_current_bb;
       bb_instructions := sa.cs_current_insts ++ [mk_inst sa.cs_next_id JMP
         [Label (fresh_label_output "enc_dyn_hdr" sa.cs_next_label)] []]|>` mp_tac) >>
     simp[] >> strip_tac >> goal_assum drule >> simp[]) >>
  irule emit_jump_zero_path_ptr >>
  simp[] >> qexistsl_tac [`sa`,`cut`] >> simp[Abbr `cut`]
QED

Theorem abi_array_static_loop_inv_jump[local]:
  abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j G tn (jump_to lbl s) <=>
  abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j G tn s
Proof
  simp[abi_array_static_loop_inv_def, ptr_covers_def, lookup_var_def, mload_def, jump_to_def]
QED

Theorem abi_array_robust_header[local]:
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs) (w2n a) scap mem') ==>
  32 <= scap /\ mload (w2n a) s = n2w (LENGTH avs) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    32 <= scap /\ mem_word_at (w2n a) mem' = n2w (LENGTH avs)` by
    (rpt strip_tac >> first_x_assum drule >> simp[abi_encoder_array_input_iff] >>
     rpt strip_tac >> decide_tac) >>
  `mem_agree_outside tn.t_mem s.vs_memory s.vs_memory` by simp[mem_agree_outside_def] >>
  `32 <= scap /\ mem_word_at (w2n a) s.vs_memory = n2w (LENGTH avs)` by metis_tac[] >>
  simp[GSYM mem_word_at_eq_mload] >> qx_gen_tac `i` >> disch_tac >>
  irule robust_mem_word_at_clean >> metis_tac[]
QED

Theorem compile_abi_encode_dyn_static_loop_counted_ptr:
  compile_abi_encode_dyn_static_loop (Var dst) (Var src) ei asz msz (Var cv) sa = (out,se) /\
  fn_has_code sa se fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa cv /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s scap /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s dcap /\
  lookup_var cv s = SOME (n2w (LENGTH avs)) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs) (w2n a) scap mem') /\
  mem_bytes_at (w2n b) 32 s.vs_memory = header /\ LENGTH header = 32 /\
  (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tn.t_mem) /\
  ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= dcap /\
  32+LENGTH avs*asz <= dcap /\ LENGTH avs < dimword(:256) /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id = SOME (addr,32) /\
  addr+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n a+scap <= addr \/ addr+32 <= w2n a) /\
  (w2n b+dcap <= addr \/ addr+32 <= w2n b) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\ sf.vs_inst_idx = LENGTH se.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+LENGTH avs*asz)) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b) (32+LENGTH avs*asz) sf.vs_memory = header ++ FLAT (MAP (enc ty) avs) /\
    (!i. w2n b <= i /\ i < w2n b+32+LENGTH avs*asz ==> i NOTIN tnf.t_mem) /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
    lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs) (w2n a) scap mem') /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule abi_encode_array_static_loop_trace >> strip_tac >>
  PairCases_on `labels` >>
  `cs_extends sa owner_st /\ cs_extends owner_st body_st /\
   cs_extends body_st body_end /\ cs_extends body_end exit_st /\ cs_extends exit_st se` by
    metis_tac[abi_encoder_appends_result, abi_encode_array_phase_append] >>
  `cs_extends owner_st exit_st /\ cs_extends owner_st se /\ cs_extends body_st se` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa owner_st fn /\ fn_has_code owner_st exit_st fn /\
   fn_has_code owner_st body_st fn /\ fn_has_code exit_st se fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  rename1 `abi_decode_index_init sa = (index_op,owner_st)` >>
  drule abi_decode_index_init_shape >> strip_tac >>
  qpat_x_assum `index_op = _` SUBST_ALL_TAC >>
  qabbrev_tac `ip = STRING #"%" (toString sa.cs_next_var)` >>
  `32 <= dcap` by decide_tac >>
  drule_all abi_array_static_index_init_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "run"
QED

Resume compile_abi_encode_dyn_static_loop_counted_ptr[run]:
  `addr < dimword(:256)` by decide_tac >>
  `w2n (n2w addr : bytes32) = addr` by simp[w2n_n2w] >>
  `not_fresh_at owner_st ip /\
   (!x. not_fresh_at sa x ==> not_fresh_at owner_st x)` by
    (simp[not_fresh_at_def, Abbr `ip`] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `lookup_var cv sf = SOME (n2w (LENGTH avs)) /\
   op_taint tnf (Var cv) = {} /\ op_prov Gf (Var cv) = NONE` by
    (qpat_x_assum `op_prov G (Var cv) = NONE` mp_tac >>
     simp[op_prov_def] >> metis_tac[]) >>
  drule_all abi_array_header_entry_counted_ptr >>
  disch_then (qspecl_then [`tnf`,`PG`,`Gf`,`D`] assume_tac) >>
  `abi_array_static_loop_inv ip src dst cv (n2w addr) a b scap dcap ei ty avs asz msz header 0
     Gf tnf (jump_to labels0 sf)` by
    simp[abi_array_static_loop_inv_jump, abi_array_static_loop_inv_def] >>
  `not_fresh_at owner_st src /\ not_fresh_at owner_st dst /\ not_fresh_at owner_st cv` by metis_tac[] >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [] >> disch_tac >>
  `?G2 tn2 s2.
    gas_path_ptr D 0 ctx fn PG Gf tnf (jump_to labels0 sf) 0 G2 tn2 (OK s2) /\
    s2.vs_current_bb = labels2 /\ s2.vs_inst_idx = 0 /\
    abi_array_static_loop_inv ip src dst cv (n2w addr) a b scap dcap ei ty avs asz msz header
      (LENGTH avs) G2 tn2 s2 /\
    mem_bytes_at (w2n b) (32+LENGTH avs*asz) s2.vs_memory = header ++ FLAT (MAP (enc ty) avs) /\
    tn2.t_stor = tnf.t_stor /\ tn2.t_trans = tnf.t_trans /\
    (!v. not_fresh_at owner_st v ==>
      lookup_var v s2 = lookup_var v (jump_to labels0 sf) /\ FLOOKUP G2 v = FLOOKUP Gf v /\
      op_taint tn2 (Var v) = op_taint tnf (Var v))` by
    (irule (abi_array_static_loop_counted_ptr |> Q.SPECL [`LENGTH (avs : value list)`, `0`]) >>
     simp[jump_to_def] >> qexists_tac `REPLICATE (LENGTH avs) ARB` >> simp[]) >>
  suspend "exit"
QED

Resume compile_abi_encode_dyn_static_loop_counted_ptr[exit]:
  qpat_x_assum `abi_array_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_array_static_loop_inv_def] >> strip_tac >>
  drule abi_array_robust_header >> strip_tac >>
  `ptr_covers G2 tn2 src s2 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `exit_st.cs_current_bb = labels2 /\ exit_st.cs_current_insts = []` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     simp_tac (srw_ss() ++ boolSimps.LET_ss) [abi_decode_loop_suffix_def, comp_bind_def, comp_ignore_bind_def,
         emit_op_def, fresh_var_def, fresh_id_def, emit_def, emit_void_def,
         emit_inst_def, new_block_def, comp_return_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `s2.vs_current_bb = exit_st.cs_current_bb /\
   s2.vs_inst_idx = LENGTH exit_st.cs_current_insts` by simp[] >>
  drule_all abi_array_static_exit_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all abi_array_static_loop_phase_code >> strip_tac >>
  `body_end.cs_next_var <= exit_st.cs_next_var` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     simp_tac (srw_ss() ++ boolSimps.LET_ss) [abi_decode_loop_suffix_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, fresh_var_def,
       fresh_id_def, emit_def, emit_void_def, emit_inst_def, new_block_def,
       comp_return_def] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `!x. not_fresh_at owner_st x ==> not_fresh_at exit_st x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`Gf'`,`tnf'`,`sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`jump_to labels0 sf`,`tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`G2`,`s2`,`tn2`] >> simp[]) >>
  `mem_bytes_at (w2n b) (asz*LENGTH avs+32) sf'.vs_memory =
    header ++ FLAT (MAP (enc ty) avs)` by
    metis_tac[ADD_COMM, MULT_COMM] >>
  simp[] >>
  `lookup_var src sf' = SOME a /\ lookup_var dst sf' = SOME b` by metis_tac[] >>
  simp[] >>
  conj_tac >- metis_tac[ADD_COMM, MULT_COMM] >>
  conj_tac >-
    (qpat_x_assum `ptr_covers G2 tn2 src s2 scap` mp_tac >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >-
    (qpat_x_assum `ptr_covers G2 tn2 dst s2 dcap` mp_tac >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  rpt strip_tac >> simp[jump_to_def, lookup_var_def] >>
  metis_tac[lookup_var_def]
QED

Finalise compile_abi_encode_dyn_static_loop_counted_ptr
