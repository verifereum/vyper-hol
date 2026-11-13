(* Dynamic typed-copy execution: live length and recursive loop resources. *)
Theory assignTupleTypedCopyDynamicArrayPtr
Ancestors
  assignBasePtrBytesPrefix assignTupleTypedCopyArrayPtr typedCopyLayoutPtr
  normalizationPrefixPtr typedCopyRobustTransportPtr
  bodyPtrPopMemoryHeader bodyPtrMakeArrayWordStore bodyPtrMakeArrayCopyStep
  wordLoadStorePtr valueEncodingProps representationCleanPtr
  liveArrayTransportPtr robustCopyTransportPtr abiStaticAggregateProps assignBasePtrMcopyTransport
  augAssignPtrScalarCertificate typedCopyLoopHeaderPtr typedCopyLoopBackedgePtr
  augAssignPtrScalarSafety augAssignPtrScalarRun
  typedNormalizeDynarray typedNormalizeDynarrayLoop typedCopyAmbientFramePtr typedCopyPtr compileEnv
  bodyPtrDefs ptrDiscipline ptrSafeRun fragGasSeqPtr fragExecPtr
  venomState venomInst venomExecSemantics venomInstProofs codegenRel contextCodegenRel
  exprSimBufferStore valueEncodingDefs exprLoweringProps fragExec finite_map words arithmetic list pred_set

Triviality typed_dynarray_live_copy_post:
  !tv vs cap a b dirty dirty' mem mem'.
    EVERY (\v. val_wf tv v /\ val_footprint tv v <= type_memory_size tv) vs /\
    mem_bytes_at (b+32) (LENGTH vs * type_memory_size tv) mem' =
      mem_bytes_at a (LENGTH vs * type_memory_size tv) mem /\
    (!i. i < LENGTH vs * type_memory_size tv ==>
      (b+32+i IN dirty' <=> a+i IN dirty)) /\
    mem_bytes_at b 32 mem' = mem_bytes_at b 32 mem /\
    (!i. i < 32 ==> (b+i IN dirty' <=> b+i IN dirty)) /\
    (!m. mem_agree_outside dirty mem m ==> mem_word_at b m = n2w (LENGTH vs)) /\
    (!m. mem_agree_outside dirty mem m ==> elems_in_memory vs a tv m) ==>
    !m. mem_agree_outside dirty' mem' m ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) b m
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[NoAsms, val_in_memory_def] >> conj_tac
  >- (`?mix. mem_agree_outside dirty mem mix /\
              mem_bytes_at b 32 mix = mem_bytes_at b 32 m` by
        (irule copied_window_agree_witness >>
         qexistsl_tac [`mem'`, `dirty'`] >> simp[]) >>
      `mem_word_at b mix = n2w (LENGTH vs)` by metis_tac[] >>
      gvs[mem_word_at_bytes] >> metis_tac[]) >>
  irule robust_elems_in_memory_copy_transport >> simp[] >>
  qexistsl_tac [`mem`, `mem'`, `LENGTH vs * type_memory_size tv`, `a`, `dirty`, `dirty'`] >>
  gvs[]
QED

Theorem typed_dynarray_empty_mcopy_ok[local]:
  eval_operand (Var dst) s = SOME b /\
  eval_operand (Var src) s = SOME a /\
  eval_operand count_op s = SOME (0w:256 word) /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var src) = {} /\
  op_taint tn count_op = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
Proof
  rpt strip_tac >>
  `step_inst fuel ctx (mk_inst id MCOPY [Var dst; Var src; count_op] []) s =
    OK (mcopy (w2n b) (w2n a) 0 s)` by
    (simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `op` >>
  Cases_on `count_op` >> gvs[op_taint_def] >> metis_tac[]
QED

Theorem typed_dynarray_mcopy_frag_ptr[local]:
  !cx ctx PG sa sb id dst src count_op P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MCOPY [Var dst; Var src; count_op] []] /\
    (!G tn s. P G tn s ==>
       ?a b n. lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
         eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
         ((w2n n = 0 /\ op_taint tn (Var dst) = {} /\ op_taint tn (Var src) = {}) \/
          (ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n))) /\
         Q (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] [])
              (mcopy (w2n b) (w2n a) (w2n n) s))
           (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
              (mcopy (w2n b) (w2n a) (w2n n) s) tn)
           ((mcopy (w2n b) (w2n a) (w2n n) s) with
              vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt strip_tac >> irule ptr_fragment_step >> simp[is_terminator_def] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (qx_choose_then `a` (qx_choose_then `b`
    (qx_choose_then `n` (map_every assume_tac o CONJUNCTS)))) >>
  qexists_tac `mcopy (w2n b) (w2n a) (w2n n) s` >>
  conj_tac >- simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  simp[mcopy_def, write_memory_with_expansion_def] >> rpt strip_tac >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (irule typed_dynarray_empty_mcopy_ok >>
      gvs[wordsTheory.w2n_eq_0, eval_operand_def] >> metis_tac[])
  >> irule ptr_inst_ok_mcopy_operand >> simp[] >> metis_tac[]
QED

Theorem typed_dynarray_load_length_ptr:
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tm u.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [len]] (s with vs_inst_idx := k) H tm) /\
    run_inst_seq [mk_inst id MLOAD [Var src] [len]] s = OK u /\
    u = update_var len (n2w (LENGTH vs)) s /\
    lookup_var len u = SOME (n2w (LENGTH vs)) /\
    op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> len ==> lookup_var p u = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mload_def, mem_word_at_def, mem_bytes_at_def]) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[pop_robust_dynarray_header_clean] >>
  drule_all assign_base_bytes_mload_seq >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `id`, `len`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `u`] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* The bound check keeps the loaded scalar live and provenance-free. *)
Theorem typed_dynarray_check_length_ptr:
  lookup_var len s = SOME (n2w n) /\ n <= cap /\ cap < dimword(:256) /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  len <> long /\ len <> ok /\ ~ctx_has_dalloca ctx ==>
  ?H tm.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id GT [Var len; Lit (n2w cap)] [long];
       mk_inst (id+1) ISZERO [Var long] [ok];
       mk_inst (id+2) ASSERT [Var ok] []] s H tm /\
    run_inst_seq
      [mk_inst id GT [Var len; Lit (n2w cap)] [long];
       mk_inst (id+1) ISZERO [Var long] [ok];
       mk_inst (id+2) ASSERT [Var ok] []] s =
      OK (update_var ok 1w (update_var long 0w s)) /\
    op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> long /\ p <> ok ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `code =
    [mk_inst id GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+1) ISZERO [Var long] [ok];
     mk_inst (id+2) ASSERT [Var ok] []]` >>
  `scalar_code {len} code` by
    simp[Abbr `code`, scalar_code_def, scalar_shape_def, scalar_binary_def,
         scalar_unary_def, scalar_available_def, mk_inst_def] >>
  `!v. v IN {len} ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}` by simp[] >>
  `run_inst_seq code s = OK (update_var ok 1w (update_var long 0w s))` by
    (simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure2_def, exec_pure1_def, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
     `n < dimword(:256)` by decide_tac >>
     gvs[lookup_var_def]) >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`, `s`] strip_assume_tac) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qexistsl_tac [`H`, `tm`] >>
  gvs[Abbr `code`, mk_inst_def, op_prov_def] >> metis_tac[]
QED

(* The checked prefix chooses a single semantic/ghost endpoint. *)
Triviality typed_dynarray_load_check_ptr:
  code =
    [mk_inst id MLOAD [Var src] [len];
     mk_inst (id+1) GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+2) ISZERO [Var long] [ok];
     mk_inst (id+3) ASSERT [Var ok] []] /\
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ LENGTH vs <= cap /\ cap < dimword(:256) /\
  len <> long /\ len <> ok /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic source_cap))
      (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tm u.
    inst_seq_ptr D 0 ctx fn PG G tn code s H tm /\
    run_inst_seq code s = OK u /\
    u = update_var ok 1w (update_var long 0w
      (update_var len (n2w (LENGTH vs)) s)) /\
    lookup_var len u = SOME (n2w (LENGTH vs)) /\
    op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> len /\ p <> long /\ p <> ok ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all typed_dynarray_load_length_ptr >>
  disch_then (qspecl_then [`len`, `id`, `fn`, `PG`, `D`]
    (qx_choose_then `g1` (qx_choose_then `t1`
      (qx_choose_then `s1` strip_assume_tac)))) >>
  qabbrev_tac `s2 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var len s2 = SOME (n2w (LENGTH vs))` by simp[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  mp_tac (Q.INST [`s` |-> `s2`, `G` |-> `g1`, `tn` |-> `t1`,
    `n` |-> `LENGTH (vs:value list)`, `id` |-> `id+1`] typed_dynarray_check_length_ptr) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `g2` (qx_choose_then `t2` strip_assume_tac)) >>
  qexistsl_tac [`g2`, `t2`,
    `update_var ok 1w (update_var long 0w s1)`] >>
  conj_tac >- suspend "checked_prefix" >>
  conj_tac >- suspend "checked_run" >>
  gvs[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED
Resume typed_dynarray_load_check_ptr[checked_prefix]:
  qpat_x_assum `code = _` SUBST1_TAC >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` mp_tac) >>
  qpat_x_assum `run_inst_seq [_] s = OK s1` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  gvs[Abbr `s2`, ADD_ASSOC, inst_seq_ptr_def]
QED
Resume typed_dynarray_load_check_ptr[checked_run]:
  `LENGTH vs < dimword(:256)` by decide_tac >>
  qpat_x_assum `run_inst_seq [_] s = OK s1` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, exec_pure1_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def]
QED
Finalise typed_dynarray_load_check_ptr

(* Pointwise bind keeps endpoint choices inside the runtime continuation. *)
Triviality typed_dynarray_frag_bind_ptr:
  frag_exec_ptr cx ctx PG a b P Q R /\
  (!G tn s. Q G tn s ==>
    frag_exec_ptr cx ctx PG b c (\g t u. g = G /\ t = tn /\ u = s) Post R) /\
  cs_extends a b /\ cs_extends b c ==>
  frag_exec_ptr cx ctx PG a c P Post R
Proof
  strip_tac >> irule fragExecPtrTheory.frag_exec_ptr_seq >>
  qexistsl_tac [`Q`, `b`] >> simp[] >>
  rewrite_tac[frag_exec_ptr_def] >> rpt strip_tac >>
  first_x_assum drule >> rewrite_tac[frag_exec_ptr_def] >>
  disch_then drule >> simp[]
QED

(* Lift a checked straight-line prefix at its single concrete endpoint. *)
Triviality typed_dynarray_checked_seq_frag_ptr:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  (!fn. ~ctx_has_dalloca ctx ==>
    ?H tm u. inst_seq_ptr (cx_dead cx) 0 ctx fn PG G tn code s H tm /\
      run_inst_seq code s = OK u /\
      u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
      Q H tm (u with vs_inst_idx := s.vs_inst_idx + LENGTH code)) ==>
  frag_exec_ptr cx ctx PG sa sb (\g t v. g = G /\ t = tn /\ v = s) Q R
Proof
  strip_tac >> rewrite_tac[frag_exec_ptr_def] >> rpt gen_tac >> strip_tac >>
  gvs[GSYM CONJ_ASSOC] >>
  first_x_assum (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[rich_listTheory.DROP_APPEND]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) code)) H tm
    (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (irule run_inst_seq_gas_path_ptr >> metis_tac[]) >>
  drule gasPathPtrExecTheory.gas_path_ptr_exec >>
  simp[exit_result_def] >> strip_tac >> disj1_tac >>
  qexistsl_tac [`H`, `tm`, `u with vs_inst_idx := s.vs_inst_idx + LENGTH code`] >>
  simp[]
QED

Triviality typed_dynarray_load_check_frag_ptr:
  code =
    [mk_inst id MLOAD [Var src] [len];
     mk_inst (id+1) GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+2) ISZERO [Var long] [ok];
     mk_inst (id+3) ASSERT [Var ok] []] /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  LENGTH vs <= cap /\ cap < dimword(:256) /\ len <> long /\ len <> ok /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic source_cap))
      (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  frag_exec_ptr cx ctx PG sa sb (\g t v. g = G /\ t = tn /\ v = s)
    (\H tm u.
      u = (update_var ok 1w (update_var long 0w
        (update_var len (n2w (LENGTH vs)) s)) with vs_inst_idx := s.vs_inst_idx+4) /\
      lookup_var len u = SOME (n2w (LENGTH vs)) /\
      op_prov H (Var len) = NONE /\ op_taint tm (Var len) = {} /\
      tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
      tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> len /\ x <> long /\ x <> ok ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))) R
Proof
  strip_tac >> irule typed_dynarray_checked_seq_frag_ptr >>
  conj_tac >- simp[] >> qexists_tac `code` >> simp[] >>
  reverse conj_tac >- simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> drule_all typed_dynarray_load_check_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `cx_dead cx`] strip_assume_tac) >>
  qexistsl_tac [`H`, `tm`, `u`] >>
  gvs[update_var_def, lookup_var_def]
QED

(* A clean header store exposes the actual singleton endpoint and its complete
   exterior frame; all variables (not only older compiler variables) survive. *)
Triviality typed_dynarray_store_length_frag_ptr:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id MSTORE [Var dst; value] []] /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  ?tm u.
    frag_exec_ptr cx ctx PG sa sb (\g t v. g = G /\ t = tn /\ v = s)
      (\g t v. g = G /\ t = tm /\ v = u) R /\
    (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
      mem_word_at (w2n a) m = w) /\
    (u with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p n. p+n <= w2n a \/ w2n a+32 <= p ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!p. p < w2n a \/ w2n a+32 <= p ==>
      (p IN tm.t_mem <=> p IN tn.t_mem)) /\
    (!x. lookup_var x u = lookup_var x s /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `u = mstore (w2n a) w s` >>
  qabbrev_tac `tm = step_taint (mk_inst id MSTORE [Var dst; value] []) s u tn` >>
  `step_prov PG G (mk_inst id MSTORE [Var dst; value] []) u = G /\
   tm.t_var = tn.t_var /\ tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
   tm.t_imm = tn.t_imm /\
   tm.t_mem = tn.t_mem DIFF {p | w2n a <= p /\ p < w2n a+32}` by
    simp[Abbr `tm`, Abbr `u`, mstore_raw_ghost_frame] >>
  qexistsl_tac [`tm`, `u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (irule mstore_frag_ptr >> simp[] >>
      qexistsl_tac [`dst`, `id`, `value`] >>
      simp[Abbr `tm`, Abbr `u`]) >>
  conj_tac
  >- (rpt strip_tac >> irule mstore_raw_robust_word >>
      qexistsl_tac [`dst`, `id`, `s`, `tn`, `tm`, `value`] >>
      gvs[Abbr `tm`, Abbr `u`]) >>
  conj_tac >- simp[Abbr `u`, mstore_def] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[Abbr `u`] >>
      irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[Abbr `u`, mstore_def, lookup_var_def, op_taint_def]
QED

(* Pointer arithmetic retains a complete concrete endpoint, including the
   empty data window at the end of the address space. *)
Triviality typed_dynarray_data_address_frag_ptr:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id ADD [Var root; Lit (n2w off)] [out]] /\
  ptr_covers G tn root s span /\ lookup_var root s = SOME a /\
  off + n <= span /\ (n = 0 \/ w2n a + off < dimword(:256)) ==>
  ?H tm u.
    frag_exec_ptr cx ctx PG sa sb (\g t v. g = G /\ t = tn /\ v = s)
      (\g t v. g = H /\ t = tm /\ v = u) R /\
    u = (update_var out (a + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    lookup_var out u = SOME (a + n2w off) /\
    op_taint tm (Var out) = {} /\
    (n = 0 \/ ptr_covers H tm out u n) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x <> out ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `v = update_var out (a + n2w off) s` >>
  qabbrev_tac `H = step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out]) v` >>
  qabbrev_tac `tm = step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s v tn` >>
  qexistsl_tac [`H`, `tm`, `v with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (irule copy_len_binop_frag_ptr >> simp[] >>
      qexistsl_tac [`word_add`, `id`, `Var root`, `ADD`, `Lit (n2w off)`, `out`] >>
      gvs[ptr_covers_def, eval_operand_def, op_taint_def, Abbr `H`, Abbr `tm`, Abbr `v`]) >>
  conj_tac >- simp[Abbr `v`] >>
  conj_tac >- simp[Abbr `v`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `tm`, Abbr `v`, copy_len_binop_ghost_frame] >>
  conj_tac >- suspend "data_coverage" >>
  conj_tac >- simp[Abbr `v`, update_var_def] >>
  suspend "data_frame"
QED
Resume typed_dynarray_data_address_frag_ptr[data_coverage]:
  Cases_on `n = 0` >> simp[] >>
  `op_taint tm (Var out) = {}` by
    simp[Abbr `tm`, Abbr `v`, copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  `w2n (a + n2w off) = w2n a + off` by
    simp[typedMemoryCopyTheory.typed_copy_offset_nonwrap] >>
  simp[Abbr `H`, Abbr `v`, ptr_covers_def,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
       mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  decide_tac
QED
Resume typed_dynarray_data_address_frag_ptr[data_frame]:
  simp[Abbr `H`, Abbr `tm`, Abbr `v`, copy_len_binop_ghost_frame] >>
  simp[step_taint_def, mk_inst_def, out_taint_def, store_taint_def,
       imm_taint_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
Finalise typed_dynarray_data_address_frag_ptr

(* The child premise ranges over actual compiler slices and arbitrary runtime
   states. Capacity windows are geometric, not taint-cleanliness assumptions. *)
(* Zero-sized elements still execute the child; only coverage is conditional. *)
Triviality typed_dynarray_loop_address_ptr:
  !cx ctx PG R sb si ctr so doff sp dp sr dr id i ss ds a b S T G tn s.
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
    op_taint tn (Var sr) = {} /\ op_taint tn (Var dr) = {} /\
    (ss <> 0 ==> ptr_covers G tn sr s S /\ i*ss < S /\
      i*ss+ss <= S /\ w2n a+i*ss < dimword(:256)) /\
    (ds <> 0 ==> ptr_covers G tn dr s T /\ i*ds < T /\
      i*ds+ds <= T /\ w2n b+i*ds < dimword(:256)) /\
    ALL_DISTINCT [so;doff;sp;dp] /\
    (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
    si.cs_blocks = sb.cs_blocks /\ si.cs_current_bb = sb.cs_current_bb /\
    si.cs_current_insts = sb.cs_current_insts ++
      [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
       mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
       mk_inst (id+2) ADD [Var sr;Var so] [sp];
       mk_inst (id+3) ADD [Var dr;Var doff] [dp]] ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sb si
        (\g t v. g=G /\ t=tn /\ v=s)
        (\g t v. g=Gf /\ t=tnf /\ v=sf) R /\
      lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
      lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
      (ss = 0 \/ ptr_covers Gf tnf sp sf ss) /\
      (ds = 0 \/ ptr_covers Gf tnf dp sf ds) /\
      sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
      tnf.t_mem=tn.t_mem /\ tnf.t_stor=tn.t_stor /\
      tnf.t_trans=tn.t_trans /\ tnf.t_imm=tn.t_imm /\
      (!p. ~MEM p [so;doff;sp;dp] ==>
        lookup_var p sf=lookup_var p s /\ FLOOKUP Gf p=FLOOKUP G p /\
        op_taint tnf (Var p)=op_taint tn (Var p))
Proof
  typedCopyLoopAmbientLib.address_witnesses >>
  conj_tac >- (typedCopyLoopAmbientLib.address_fragment typed_copy_loop_mul_frag_ptr) >>
  `lookup_var sp s4 = SOME (n2w (w2n a+i*ss)) /\
   lookup_var dp s4 = SOME (n2w (w2n b+i*ds))` by
    simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  simp[] >>
  conj_tac >- suspend "source_cover" >>
  conj_tac >- suspend "destination_cover" >>
  suspend "address_frame"
QED

Resume typed_dynarray_loop_address_ptr[source_cover]:
  Cases_on `ss = 0` >- simp[] >>
  simp[] >>
  `ptr_covers g3 tn3 sp t3 ss` by
    (simp[Abbr `g3`, Abbr `tn3`, Abbr `t3`] >>
     irule typed_copy_loop_dynamic_offset_covers >>
     simp[Abbr `s2`, Abbr `s1`, Abbr `g2`, Abbr `g1`,
          Abbr `tn2`, Abbr `tn1`, eval_operand_def,
          ptr_covers_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
     conj_tac >- gvs[lookup_var_def] >>
     qexists_tac `S'` >> gvs[ptr_covers_def, lookup_var_def, op_taint_def]) >>
  gvs[Abbr `s4`, Abbr `s3`, Abbr `g4`, Abbr `tn4`, Abbr `t4`,
      ptr_covers_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE, copy_len_binop_ghost_frame]
QED

Resume typed_dynarray_loop_address_ptr[destination_cover]:
  Cases_on `ds = 0` >- simp[] >>
  simp[] >>
  `ptr_covers g3 tn3 dr s3 T'` by
    gvs[Abbr `g3`, Abbr `tn3`, Abbr `s3`, Abbr `t3`,
        ptr_covers_def, lookup_var_def, update_var_def,
        copy_len_binop_ghost_frame, Abbr `g2`, Abbr `g1`,
        Abbr `tn2`, Abbr `tn1`, Abbr `s2`, Abbr `s1`,
        FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  `ptr_covers g4 tn4 dp t4 ds` by
    (simp[Abbr `g4`, Abbr `tn4`, Abbr `t4`] >>
     irule typed_copy_loop_dynamic_offset_covers >> simp[] >>
     conj_tac >- simp[Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     conj_tac >- gvs[Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     qexists_tac `T'` >> simp[]) >>
  gvs[Abbr `s4`, ptr_covers_def, lookup_var_def]
QED

Resume typed_dynarray_loop_address_ptr[address_frame]:
  conj_tac >-
    simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
         update_var_def] >>
  simp[Abbr `g4`, Abbr `tn4`, Abbr `t4`, copy_len_binop_ghost_frame] >>
  simp[Abbr `g3`, Abbr `tn3`, Abbr `t3`, copy_len_binop_ghost_frame] >>
  simp[Abbr `tn2`, Abbr `tn1`] >> rpt strip_tac >>
  simp[copy_len_binop_ghost_frame,
       Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def, FLOOKUP_UPDATE,
       Abbr `g2`, Abbr `g1`, FLOOKUP_DRESTRICT, op_taint_def] >>
  simp[Abbr `s4`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_taint_def, imm_taint_def, mk_inst_def]
QED

Finalise typed_dynarray_loop_address_ptr

Triviality typed_dynarray_loop_entry_run:
  !ctx fn s bb pre id ctr cond sf.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = pre ++
      [mk_inst id ASSIGN [Lit 0w] [ctr];
       mk_inst (id+1) JMP [Label cond] []] /\
    s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
    sf = jump_to cond (update_var ctr 0w s) ==>
    !fuel. run_from (SUC fuel) ctx fn s = run_blocks (SUC fuel) ctx fn sf
Proof
  rpt strip_tac >>
  simp[run_from_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, EL_APPEND_EQN, ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, Once exec_block_def, get_instruction_def,
       update_var_def, step_inst_non_invoke, is_terminator_def, EL_APPEND_EQN, ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, jump_to_def]
QED

Triviality typed_dynarray_loop_entry_assign_ghost:
  !PG G tn s id ctr.
    step_prov PG G (mk_inst id ASSIGN [Lit 0w] [ctr]) (update_var ctr 0w s) =
      DRESTRICT G (COMPL {ctr}) /\
    step_taint (mk_inst id ASSIGN [Lit 0w] [ctr]) s (update_var ctr 0w s) tn =
      (tn with t_var := tn.t_var |+ (ctr,{}))
Proof
  rpt gen_tac >>
  `new_site_bytes s (update_var ctr 0w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, out_taint_def, op_taint_def, imm_taint_def, range_bytes_def,
       taint_component_equality, eval_operand_def]
QED

Triviality typed_dynarray_loop_entry_ghost_run:
  !ctx fn PG G tn s bb pre id ctr cond sf target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = pre ++
      [mk_inst id ASSIGN [Lit 0w] [ctr];
       mk_inst (id+1) JMP [Label cond] []] /\
    s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
    sf = jump_to cond (update_var ctr 0w s) /\
    lookup_block cond fn.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0 ==>
    !fuel. ghost_run (SUC fuel) ctx fn PG G tn s =
      ghost_run fuel ctx fn PG (DRESTRICT G (COMPL {ctr}))
        (tn with t_var := tn.t_var |+ (ctr,{})) sf
Proof
  rpt strip_tac >>
  simp[ghost_run_def, Once ghost_block_def, get_instruction_def,
       step_inst_non_invoke, EL_APPEND_EQN, ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, is_terminator_def, ghost_step_def, step_inst_non_invoke,
       mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, GSYM mk_inst_def, eval_operand_def] >>
  simp[typed_dynarray_loop_entry_assign_ghost] >>
  simp[Once ghost_block_def, get_instruction_def, step_inst_non_invoke,
       update_var_def, EL_APPEND_EQN, ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, is_terminator_def, jump_to_def] >>
  qmatch_goalsub_abbrev_tac `entry_prov fn sj gg` >>
  qmatch_goalsub_abbrev_tac `entry_taint_vars fn sj tt` >>
  `entry_prov fn sj gg = gg /\ entry_taint_vars fn sj tt = tt` by
    (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     simp[Abbr `sj`] >> metis_tac[]) >>
  simp[Once ghost_blocks_def, Abbr `sj`, GSYM ADD1] >>
  Cases_on `target.bb_instructions` >- simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def, eval_phis_def]
QED

Triviality typed_dynarray_loop_entry_ptr_safe:
  !D ctx fn PG G tn s bb pre id ctr cond sf target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = pre ++
      [mk_inst id ASSIGN [Lit 0w] [ctr];
       mk_inst (id+1) JMP [Label cond] []] /\
    s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
    sf = jump_to cond (update_var ctr 0w s) /\
    lookup_block cond fn.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0 /\ ~ctx_has_dalloca ctx ==>
    !fuel. ptr_safe_run D 0 fuel ctx fn PG (DRESTRICT G (COMPL {ctr}))
      (tn with t_var := tn.t_var |+ (ctr,{})) sf ==>
      ptr_safe_run D 0 (SUC fuel) ctx fn PG G tn s
Proof
  rpt strip_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, get_instruction_def,
       ptr_safe_step_def, step_inst_non_invoke, EL_APPEND_EQN, ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, is_terminator_def] >>
  conj_tac >- suspend "assign_safe" >>
  simp[ghost_step_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       GSYM mk_inst_def, eval_operand_def, typed_dynarray_loop_entry_assign_ghost] >>
  simp[Once ptr_safe_block_def, get_instruction_def, ptr_safe_step_def,
       step_inst_non_invoke, update_var_def, EL_APPEND_EQN, ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, is_terminator_def, jump_to_def] >>
  conj_tac >- suspend "jump_safe" >>
  qmatch_goalsub_abbrev_tac `entry_prov fn sj gg` >>
  qmatch_goalsub_abbrev_tac `entry_taint_vars fn sj tt` >>
  `entry_prov fn sj gg = gg /\ entry_taint_vars fn sj tt = tt` by
    (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     simp[Abbr `sj`] >> metis_tac[]) >>
  simp[Once ptr_safe_blocks_def, Abbr `sj`, GSYM ADD1] >>
  qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_safe_run_def, GSYM ADD1, update_var_def, jump_to_def] >>
  Cases_on `target.bb_instructions` >- simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def, eval_phis_def]
QED

Resume typed_dynarray_loop_entry_ptr_safe[assign_safe]:
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, update_var_def,
       eval_operand_def, op_taint_def]
QED

Resume typed_dynarray_loop_entry_ptr_safe[jump_safe]:
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, update_var_def,
       jump_to_def, eval_operand_def, op_taint_def]
QED

Finalise typed_dynarray_loop_entry_ptr_safe

(* A normal child preserves the live source and length, and extends exactly
   one destination element.  This is independent of all prefix runtime states. *)
Triviality typed_dynarray_child_memory_frame:
  !stv dtv vs source_cap cap a b i dirty dirty' mem mem'.
    i < LENGTH vs /\ LENGTH vs <= source_cap /\ LENGTH vs <= cap /\
    EVERY (\v. val_wf stv v /\ val_wf dtv v) vs /\
    (a + source_cap * type_memory_size stv <= b \/
     b + (cap * type_memory_size dtv + 32) <= a) /\
    (!m. mem_agree_outside dirty mem m ==>
      elems_in_memory vs a stv m) /\
    (!m. mem_agree_outside dirty mem m ==>
      mem_word_at b m = n2w (LENGTH vs)) /\
    (!j. j < i ==> !m. mem_agree_outside dirty mem m ==>
      val_in_memory dtv (EL j vs) (b+32+j*type_memory_size dtv) m) /\
    (!m. mem_agree_outside dirty' mem' m ==>
      val_in_memory dtv (EL i vs) (b+32+i*type_memory_size dtv) m) /\
    (!p n. p+n <= b+32+i*type_memory_size dtv \/
      b+32+i*type_memory_size dtv+type_memory_size dtv <= p ==>
      mem_bytes_at p n mem' = mem_bytes_at p n mem) /\
    (!p. p < b+32+i*type_memory_size dtv \/
      b+32+i*type_memory_size dtv+type_memory_size dtv <= p ==>
      (p IN dirty' <=> p IN dirty)) ==>
    (!m. mem_agree_outside dirty' mem' m ==>
      elems_in_memory vs a stv m) /\
    (!m. mem_agree_outside dirty' mem' m ==>
      mem_word_at b m = n2w (LENGTH vs)) /\
    (!j. j < SUC i ==> !m. mem_agree_outside dirty' mem' m ==>
      val_in_memory dtv (EL j vs) (b+32+j*type_memory_size dtv) m)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- suspend "source" >>
  conj_tac >- suspend "header" >>
  match_mp_tac robust_array_prefix_extend >>
  qexistsl_tac [`dirty`, `mem`] >> simp[] >>
  conj_tac >-
    (rpt strip_tac >>
     `j < LENGTH vs` by decide_tac >>
     gvs[EVERY_EL] >> metis_tac[exprSimPropsTheory.val_footprint_le, LESS_TRANS]) >>
  qx_gen_tac `x` >> disch_tac >>
  `x < b+32+i*type_memory_size dtv \/
   b+32+i*type_memory_size dtv+type_memory_size dtv <= x` by
    (gvs[LEFT_ADD_DISTRIB] >> decide_tac) >>
  conj_tac >- (first_x_assum irule >> decide_tac) >> metis_tac[]
QED

Resume typed_dynarray_child_memory_frame[source]:
  match_mp_tac robust_elems_in_memory_copy_transport >>
  qexistsl_tac [`a`, `LENGTH vs * type_memory_size stv`, `dirty`, `mem`] >>
  simp[] >>
  `LENGTH vs * type_memory_size stv <= source_cap * type_memory_size stv /\
   (i+1) * type_memory_size dtv <= cap * type_memory_size dtv` by
    (conj_tac >> irule LESS_MONO_MULT >> decide_tac) >>
  rpt conj_tac
  >- (gvs[EVERY_EL] >> metis_tac[exprSimPropsTheory.val_footprint_le, LESS_TRANS])
  >- (first_x_assum irule >>
      rule_assum_tac (REWRITE_RULE [LEFT_ADD_DISTRIB, MULT_CLAUSES]) >>
      pure_rewrite_tac[LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >>
  rule_assum_tac (REWRITE_RULE [LEFT_ADD_DISTRIB, MULT_CLAUSES]) >>
  pure_rewrite_tac[LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac
QED

Resume typed_dynarray_child_memory_frame[header]:
  rpt strip_tac >>
  `?mix. mem_agree_outside dirty mem mix /\
    mem_bytes_at b 32 mix = mem_bytes_at b 32 m` by
    (irule copied_window_agree_witness >>
     qexistsl_tac [`mem'`, `dirty'`] >> simp[]) >>
  `mem_word_at b mix = n2w (LENGTH vs)` by metis_tac[] >>
  gvs[mem_word_at_def, GSYM mem_bytes_at_def]
QED
Finalise typed_dynarray_child_memory_frame

(* Size-zero child endpoints may wrap, but their empty windows still fit. *)
Triviality typed_dynarray_child_word_window:
  !a k n i frontier.
    i < n /\ a+n*k <= frontier /\ a+n*k <= dimword(:256) ==>
    w2n (n2w (a+i*k):bytes32)+k <= frontier /\
    w2n (n2w (a+i*k):bytes32)+k <= dimword(:256) /\
    (k <> 0 ==> w2n (n2w (a+i*k):bytes32) = a+i*k)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(i+1)*k <= n*k` by (irule LESS_MONO_MULT >> decide_tac) >>
  Cases_on `k=0`
  >- (gvs[] >>
      `a MOD dimword(:256) <= a` by simp[MOD_LESS_EQ] >>
      simp[w2n_n2w] >> decide_tac) >>
  `a+i*k < dimword(:256)` by
    (qpat_x_assum `(i+1)*k <= n*k` mp_tac >>
     pure_rewrite_tac[LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  simp[w2n_n2w, LESS_MOD] >>
  qpat_x_assum `(i+1)*k <= n*k` mp_tac >>
  pure_rewrite_tac[LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac
QED

(* One real loop iteration: operand-count header, the address/child slice,
   and the backedge at the child's actual final block.  Q carries the memory
   invariant; neither child termination nor a single-block child is assumed. *)
Triviality typed_dynarray_iteration_continuation:
  !cx ctx fn PG G tn s ctr bound lt done hid i n body exit hb bb
    sc ec eb bid tmp Gh th sh Q R.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME hb /\
    hb.bb_instructions =
      [mk_inst hid LT [Var ctr;bound] [lt];
       mk_inst (hid+1) ISZERO [Var lt] [done];
       mk_inst (hid+2) JNZ [Var done;Label exit;Label body] []] /\
    lookup_block body fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0 /\
    phi_prefix_length hb.bb_instructions = 0 /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\
    eval_operand bound s = SOME (n2w n) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn bound = {} /\
    op_prov G (Var ctr) = NONE /\ op_prov G bound = NONE /\
    ~ctx_has_dalloca ctx /\ i < n /\ n < dimword(:256) /\
    ctr <> lt /\ ctr <> done /\ ctr <> tmp /\
    Gh = DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}) /\
    th = (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})) /\
    sh = jump_to body (update_var done 0w (update_var lt 1w s)) /\
    sc.cs_current_bb = body /\ sc.cs_current_insts = [] /\
    fn_has_code sc ec fn /\
    lookup_block ec.cs_current_bb fn.fn_blocks = SOME eb /\
    eb.bb_instructions = ec.cs_current_insts ++
      [mk_inst bid ADD [Var ctr;Lit 1w] [tmp];
       mk_inst (bid+1) ASSIGN [Var tmp] [ctr];
       mk_inst (bid+2) JMP [Label s.vs_current_bb] []] /\
    frag_exec_ptr cx ctx PG sc ec (\g t u. g=Gh /\ t=th /\ u=sh)
      (\g t u. Q g t u /\ lookup_var ctr u = SOME (n2w i) /\
        FLOOKUP g ctr = NONE /\ op_taint t (Var ctr) = {}) R ==>
    ((?Gc tc uc Gf tf uf.
       Q Gc tc uc /\
       uf = jump_to s.vs_current_bb
         (update_var ctr (n2w (i+1)) (update_var tmp (n2w (i+1)) uc)) /\
       Gf = DRESTRICT (DRESTRICT Gc (COMPL {tmp})) (COMPL {ctr}) /\
       tf = (tc with t_var := (tc.t_var |+ (tmp,{})) |+ (ctr,{})) /\
       (!fuel r. run_from fuel ctx fn uf = r /\ (!e. r <> Error e) ==>
         ?fuel'. run_from fuel' ctx fn s = r /\
           ghost_run fuel' ctx fn PG G tn s =
             ghost_run fuel ctx fn PG Gf tf uf /\
           (ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG Gf tf uf ==>
            ptr_safe_run (cx_dead cx) 0 fuel' ctx fn PG G tn s))) \/
     (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
       (!e. r <> Error e) /\ R (ghost_run fuel ctx fn PG G tn s) r /\
       ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!fuel r. run_from fuel ctx fn sh = r /\ (!e. r <> Error e) ==>
    run_from (SUC fuel) ctx fn s = r /\
    ghost_run (SUC fuel) ctx fn PG G tn s = ghost_run fuel ctx fn PG Gh th sh /\
    (ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG Gh th sh ==>
     ptr_safe_run (cx_dead cx) 0 (SUC fuel) ctx fn PG G tn s)` by
    (match_mp_tac typed_copy_operand_loop_test_continuation >>
     simp[mk_inst_def, instruction_component_equality, bool_to_word_def] >>
     qexistsl_tac [`i`,`n`,`bb`] >> simp[bool_to_word_def] >> decide_tac) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[frag_exec_ptr_def] >>
  disch_then (qspecl_then [`fn`,`Gh`,`th`,`sh`] mp_tac) >>
  (impl_tac >- simp[jump_to_def, update_var_def]) >>
  disch_then strip_assume_tac
  >- (qpat_x_assum `(\g t u. _) _ _ _` mp_tac >> BETA_TAC >> strip_tac >>
      rename1 `Q Gc tc uc` >>
      qabbrev_tac `uf = jump_to s.vs_current_bb
        (update_var ctr (n2w (i+1)) (update_var tmp (n2w (i+1)) uc))` >>
      qabbrev_tac `Gf = DRESTRICT (DRESTRICT Gc (COMPL {tmp})) (COMPL {ctr})` >>
      qabbrev_tac `tf = tc with t_var := (tc.t_var |+ (tmp,{})) |+ (ctr,{})` >>
      `!fuel r. run_from fuel ctx fn uf = r /\ (!e. r <> Error e) ==>
        run_from (SUC fuel) ctx fn uc = r /\
        ghost_run (SUC fuel) ctx fn PG Gc tc uc = ghost_run fuel ctx fn PG Gf tf uf /\
        (ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG Gf tf uf ==>
         ptr_safe_run (cx_dead cx) 0 (SUC fuel) ctx fn PG Gc tc uc)` by
        suspend "backedge" >>
      disj1_tac >> qexistsl_tac [`Gc`,`tc`,`uc`,`Gf`,`tf`,`uf`] >>
      simp[] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn uf = r /\ _ ==> _`
        (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn uc = r /\ _ ==> _` drule_all >>
      strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn sh = r /\ _ ==> _` drule_all >>
      strip_tac >> qexists_tac `SUC fuel'` >> simp[]) >>
  disj2_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> gvs[exit_result_def]) >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn sh = r /\ _ ==> _` drule_all >>
  strip_tac >> qexistsl_tac [`SUC fuel`,`r`] >> gvs[]
QED

Resume typed_dynarray_iteration_continuation[backedge]:
  `!fuel. run_from (SUC fuel) ctx fn uc = run_blocks (SUC fuel) ctx fn uf` by
    (match_mp_tac typed_copy_loop_backedge_run >>
     simp[Abbr `uf`] >> metis_tac[]) >>
  `!fuel. run_blocks (SUC fuel) ctx fn uf = run_from fuel ctx fn uf` by
    (gen_tac >>
     `lookup_block uf.vs_current_bb fn.fn_blocks = SOME hb` by
       simp[Abbr `uf`, jump_to_def] >>
     drule run_blocks_run_from_no_phi >>
     disch_then (qspec_then `fuel` mp_tac) >>
     simp[Abbr `uf`, jump_to_def, phi_prefix_length_def, mk_inst_def]) >>
  `!fuel. ghost_run (SUC fuel) ctx fn PG Gc tc uc =
    ghost_run fuel ctx fn PG Gf tf uf` by
    (match_mp_tac typed_copy_loop_backedge_ghost_run >>
     simp[Abbr `uf`, Abbr `Gf`, Abbr `tf`] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  match_mp_tac typed_copy_loop_backedge_ptr_safe >>
  simp[Abbr `uf`, Abbr `Gf`, Abbr `tf`] >> metis_tac[]
QED
Finalise typed_dynarray_iteration_continuation

Theorem compile_copy_dynarray_typed_child_frag_ptr:
  !ce st dt stv dtv vs source_cap cap dst src sa sb cx ctx PG R.
  type_memory_size stv = type_memory_bytes ce st /\
  type_memory_size dtv = type_memory_bytes ce dt /\
  LENGTH vs <= source_cap /\ LENGTH vs <= cap /\ cap < dimword(:256) /\
  EVERY (\v. value_has_type stv v /\ value_has_type dtv v) vs /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (dt = st ==> dtv = stv) /\
  (!sc ec sop dop v.
    compile_store_memory_typed ce dop dt sop st sc = ((),ec) /\
    (!x. sop = Var x \/ dop = Var x ==> not_fresh_at sc x) /\
    value_has_type stv v /\ value_has_type dtv v ==>
    !G tn s p q.
    eval_operand sop s = SOME p /\ eval_operand dop s = SOME q /\
    (type_memory_bytes ce st = 0 \/
      ?x. sop = Var x /\ ptr_covers G tn x s (type_memory_bytes ce st)) /\
    (type_memory_bytes ce dt = 0 \/
      ?x. dop = Var x /\ ptr_covers G tn x s (type_memory_bytes ce dt)) /\
    w2n p + type_memory_bytes ce st <= s.vs_alloca_next /\
    w2n q + type_memory_bytes ce dt <= s.vs_alloca_next /\
    w2n p + type_memory_bytes ce st <= dimword(:256) /\
    w2n q + type_memory_bytes ce dt <= dimword(:256) /\
    (w2n p + type_memory_bytes ce st <= w2n q \/
      w2n q + type_memory_bytes ce dt <= w2n p) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n p) m) ==>
    frag_exec_ptr cx ctx PG sc ec (\g t u. g = G /\ t = tn /\ u = s)
      (\H tm u.
        (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
          val_in_memory dtv v (w2n q) m) /\
        (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
          vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
          vs_prev_bb := s.vs_prev_bb|>) = s /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!a n. a+n <= w2n q \/ w2n q + type_memory_bytes ce dt <= a ==>
          mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory) /\
        (!a. a < w2n q \/ w2n q + type_memory_bytes ce dt <= a ==>
          (a IN tm.t_mem <=> a IN tn.t_mem)) /\
        (!x. not_fresh_at sc x ==>
          lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x))) R) ==>
  !G tn s p q.
  eval_operand src s = SOME p /\ eval_operand dst s = SOME q /\
  (32 + source_cap * type_memory_bytes ce st = 0 \/
    ?x. src = Var x /\ ptr_covers G tn x s
      (32 + source_cap * type_memory_bytes ce st)) /\
  (32 + cap * type_memory_bytes ce dt = 0 \/
    ?x. dst = Var x /\ ptr_covers G tn x s
      (32 + cap * type_memory_bytes ce dt)) /\
  w2n p + (32 + source_cap * type_memory_bytes ce st) <= s.vs_alloca_next /\
  w2n q + (32 + cap * type_memory_bytes ce dt) <= s.vs_alloca_next /\
  w2n p + (32 + source_cap * type_memory_bytes ce st) <= dimword(:256) /\
  w2n q + (32 + cap * type_memory_bytes ce dt) <= dimword(:256) /\
  (w2n p + (32 + source_cap * type_memory_bytes ce st) <= w2n q \/
    w2n q + (32 + cap * type_memory_bytes ce dt) <= w2n p) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV stv (Dynamic source_cap))
      (ArrayV (DynArrayV vs)) (w2n p) m) ==>
  frag_exec_ptr cx ctx PG sa sb (\g t u. g = G /\ t = tn /\ u = s)
    (\H tm u.
      (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
        val_in_memory (ArrayTV dtv (Dynamic cap))
          (ArrayV (DynArrayV vs)) (w2n q) m) /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
        vs_prev_bb := s.vs_prev_bb|>) = s /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!a n. a+n <= w2n q \/ w2n q + (32 + cap * type_memory_bytes ce dt) <= a ==>
        mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory) /\
      (!a. a < w2n q \/ w2n q + (32 + cap * type_memory_bytes ce dt) <= a ==>
        (a IN tm.t_mem <=> a IN tn.t_mem)) /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))) R
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[] >>
  qpat_x_assum `?x. src = Var x /\ _` strip_assume_tac >>
  qpat_x_assum `?x. dst = Var x /\ _` strip_assume_tac >>
  qmatch_goalsub_abbrev_tac `frag_exec_ptr cx ctx PG sa sb _ Post R` >>
  rewrite_tac[frag_exec_ptr_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[] >>
  drule_all typed_dynarray_compiler_prefix >> simp[LET_THM] >>
  disch_then (qx_choose_then `sm` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `sm.cs_current_insts = sa.cs_current_insts ++ code7` >>
  qabbrev_tac `cut4 = sm with cs_current_insts := sa.cs_current_insts ++ TAKE 4 code7` >>
  `cs_extends sa cut4 /\ cs_extends cut4 sm /\ cs_extends sm sb` by
    (gvs[ci_mono_def, Abbr `cut4`, cs_extends_def,
         rich_listTheory.IS_PREFIX_APPEND, Abbr `code7`] >>
     metis_tac[]) >>
  `frag_exec_ptr cx ctx PG sa sb (\g t u. g = G /\ t = tn /\ u = s) Post R`
    suffices_by
      (rewrite_tac[frag_exec_ptr_def] >> disch_then drule >> simp[]) >>
  `ptr_covers G tn x s 32` by
    (qpat_assum `ptr_covers G tn x s _` mp_tac >>
     simp_tac std_ss [ptr_covers_def] >> strip_tac >>
     qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  `lookup_var x s = SOME p` by
    metis_tac[eval_operand_def] >>
  `cs_extends cut4 sb` by
    (irule cs_extends_trans >> qexists_tac `sm` >> simp[]) >>
  irule typed_dynarray_frag_bind_ptr >>
  qrefinel [`_`, `cut4`] >>
  irule_at Any typed_dynarray_load_check_frag_ptr >>
  qexistsl_tac [`vs`, `stv`, `x`, `source_cap`,
    `STRING #"%" (toString (sa.cs_next_var + 2))`,
    `STRING #"%" (toString (sa.cs_next_var + 1))`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `sa.cs_next_id`, `TAKE 4 code7`, `cap`, `p`] >>
  simp[Abbr `cut4`, Abbr `code7`, listTheory.TAKE_def] >>
  map_every qx_gen_tac [`H4`, `t4`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_abbrev_tac `s4 = update_var _ _ _ with vs_inst_idx := _` >>
  qmatch_goalsub_abbrev_tac `frag_exec_ptr cx ctx PG c4 sb _ _ _` >>
  qabbrev_tac `c5 = sm with cs_current_insts := TAKE (LENGTH sa.cs_current_insts + 5) sm.cs_current_insts` >>
  `!k. not_fresh_at sa k ==> k <> STRING #"%" (toString sa.cs_next_var) /\
      k <> STRING #"%" (toString (sa.cs_next_var+1)) /\
      k <> STRING #"%" (toString (sa.cs_next_var+2))` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  `!k. not_fresh_at sa k ==>
    lookup_var k s4 = lookup_var k s /\ FLOOKUP H4 k = FLOOKUP G k /\
    op_taint t4 (Var k) = op_taint tn (Var k)` by metis_tac[] >>
  `lookup_var x' s4 = SOME q` by metis_tac[eval_operand_def] >>
  `ptr_covers H4 t4 x' s4 32` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[] >>
     conj_tac >- metis_tac[] >>
     qpat_assum `ptr_covers G tn x' s (cap * _ + 32)` mp_tac >>
     simp_tac std_ss [ptr_covers_def] >> strip_tac >>
     simp[] >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  `c5.cs_current_bb = c4.cs_current_bb /\
   c5.cs_current_insts = c4.cs_current_insts ++
     [mk_inst (sa.cs_next_id+4) MSTORE
       [Var x'; Var (STRING #"%" (toString sa.cs_next_var))] []]` by
    (simp[Abbr `c5`, Abbr `c4`,
          listTheory.TAKE_def, rich_listTheory.TAKE_APPEND]) >>
  `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) s4 =
     SOME (n2w (LENGTH vs))` by simp[eval_operand_def] >>
  drule_all typed_dynarray_store_length_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `R`, `PG`]
    (qx_choose_then `t5` (qx_choose_then `s5` strip_assume_tac))) >>
  `cs_extends c4 c5 /\ cs_extends c5 sm` by
    (simp[Abbr `c4`, Abbr `c5`, cs_extends_def,
          rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.TAKE_APPEND,
          listTheory.TAKE_def]) >>
  `cs_extends c5 sb` by
    (irule cs_extends_trans >> qexists_tac `sm` >> simp[]) >>
  irule typed_dynarray_frag_bind_ptr >>
  qexistsl_tac [`\g t u. g = H4 /\ t = t5 /\ u = s5`, `c5`] >>
  simp[] >>
  `EVERY (\v. val_wf stv v /\ val_footprint stv v <= type_memory_size stv) vs` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     `value_has_type stv v` by metis_tac[] >>
     drule valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
     metis_tac[exprSimPropsTheory.val_footprint_le, LESS_TRANS]) >>
  `LENGTH vs * type_memory_size stv <= source_cap * type_memory_bytes ce st` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `!m. mem_agree_outside t5.t_mem s5.vs_memory m ==>
       elems_in_memory vs (w2n p+32) stv m` by
    (rpt strip_tac >> irule robust_elems_in_memory_copy_transport >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s4.vs_memory`, `s5.vs_memory`,
       `LENGTH vs * type_memory_size stv`, `w2n p+32`, `t4.t_mem`, `t5.t_mem`] >>
     simp[] >>
     conj_tac >-
       (qx_gen_tac `mm` >> strip_tac >>
        `mem_agree_outside tn.t_mem s.vs_memory mm` by
          fs[Abbr `s4`, update_var_def] >>
        `val_in_memory (ArrayTV stv (Dynamic source_cap))
           (ArrayV (DynArrayV vs)) (w2n p) mm` by metis_tac[] >>
        pop_assum mp_tac >> simp[NoAsms, Once val_in_memory_def]) >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_assum `!z. z < w2n q \/ _ ==> _`
          (qspec_then `i+(w2n p+32)` mp_tac) >>
        impl_tac >-
          (qpat_assum `type_memory_size stv = _` SUBST_ALL_TAC >>
           qpat_x_assum `_ \/ _` strip_assume_tac >> decide_tac) >> simp[]) >>
     first_x_assum irule >>
     qpat_assum `type_memory_size stv = _` SUBST_ALL_TAC >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> decide_tac) >>
  qabbrev_tac `c6 = sm with cs_current_insts := TAKE (LENGTH sa.cs_current_insts + 6) sm.cs_current_insts` >>
  `lookup_var x s5 = SOME p` by metis_tac[eval_operand_def] >>
  `ptr_covers H4 t5 x s5 (source_cap * type_memory_bytes ce st + 32)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
  `c6.cs_current_bb = c5.cs_current_bb /\
   c6.cs_current_insts = c5.cs_current_insts ++
     [mk_inst (sa.cs_next_id+5) ADD [Var x; Lit (n2w 32)]
       [STRING #"%" (toString (sa.cs_next_var+3))]]` by
    (simp[NoAsms, Abbr `c5`, Abbr `c6`] >>
     qpat_x_assum `sm.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, rich_listTheory.TAKE_APPEND, listTheory.TAKE_def,
          listTheory.TAKE_LENGTH_TOO_LONG]) >>
  drule_at (Pat `sb.cs_current_insts = _`) typed_dynarray_data_address_frag_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspec_then `source_cap * type_memory_bytes ce st` mp_tac) >>
  disch_then (qspecl_then [`cx`, `ctx`, `p`, `R`, `PG`] mp_tac) >>
  impl_tac >-
    (conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- decide_tac >>
     Cases_on `source_cap * type_memory_bytes ce st = 0` >- (disj1_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >> decide_tac) >>
  disch_then (qx_choose_then `H6` (qx_choose_then `t6` (qx_choose_then `s6`
      (map_every assume_tac o CONJUNCTS)))) >>
  `cs_extends c5 c6 /\ cs_extends c6 sm` by
    (simp[NoAsms, Abbr `c5`, Abbr `c6`, cs_extends_def] >>
     qpat_assum `sm.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, rich_listTheory.TAKE_APPEND, listTheory.TAKE_def,
          listTheory.TAKE_LENGTH_TOO_LONG, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends c6 sb` by
    (irule cs_extends_trans >> qexists_tac `sm` >> simp[]) >>
  irule typed_dynarray_frag_bind_ptr >>
  qexistsl_tac [`\g t u. g = H6 /\ t = t6 /\ u = s6`, `c6`] >> simp[] >>
  `x' <> STRING #"%" (toString (sa.cs_next_var+3))` by
    (qpat_assum `!k. _ ==> not_fresh_at sa k` (qspec_then `x'` mp_tac) >>
     simp_tac std_ss [loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  `lookup_var x' s6 = SOME q` by metis_tac[eval_operand_def] >>
  `ptr_covers H6 t6 x' s6 (cap * type_memory_bytes ce dt + 32)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`H4`, `s5`, `t5`] >> simp[] >>
     irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
  `sm.cs_current_bb = c6.cs_current_bb /\
   sm.cs_current_insts = c6.cs_current_insts ++
     [mk_inst (sa.cs_next_id+6) ADD [Var x'; Lit (n2w 32)]
       [STRING #"%" (toString (sa.cs_next_var+4))]]` by
    (simp[NoAsms, Abbr `c6`] >>
     qpat_assum `sm.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, rich_listTheory.TAKE_APPEND, listTheory.TAKE_def,
          listTheory.TAKE_LENGTH_TOO_LONG]) >>
  drule_at (Pat `sb.cs_current_insts = _`) typed_dynarray_data_address_frag_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspec_then `cap * type_memory_bytes ce dt` mp_tac) >>
  disch_then (qspecl_then [`cx`, `ctx`, `q`, `R`, `PG`] mp_tac) >>
  impl_tac >-
    (conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- decide_tac >>
     Cases_on `cap * type_memory_bytes ce dt = 0` >- (disj1_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >> decide_tac) >>
  disch_then (qx_choose_then `H7` (qx_choose_then `t7` (qx_choose_then `s7`
      (map_every assume_tac o CONJUNCTS)))) >>
  irule typed_dynarray_frag_bind_ptr >>
  qexistsl_tac [`\g t u. g = H7 /\ t = t7 /\ u = s7`, `sm`] >> simp[] >>
  reverse conj_tac >-
    (qpat_assum `frag_exec_ptr cx ctx PG c6 sm _ _ R` mp_tac >>
     qpat_assum `s7 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `s6 = _` (fn th => rewrite_tac[th]) >> simp[NoAsms]) >>
  Cases_on `dt = st`
  >- suspend "equal_layout"
  >> suspend "element_loop"
QED

Resume compile_copy_dynarray_typed_child_frag_ptr[equal_layout]:
  `dtv = stv` by metis_tac[] >>
  qpat_x_assum `dt = st` SUBST_ALL_TAC >>
  drule typed_dynarray_equal_shape >> strip_tac >>
  qabbrev_tac `c8 = sb with cs_current_insts := TAKE (LENGTH sa.cs_current_insts+8) sb.cs_current_insts` >>
  `c8.cs_current_bb = sm.cs_current_bb /\
   c8.cs_current_insts = sm.cs_current_insts ++
     [mk_inst (sa.cs_next_id+7) MUL
       [Var (STRING #"%" (toString sa.cs_next_var)); Lit (n2w (type_memory_bytes ce st))]
       [STRING #"%" (toString (sa.cs_next_var+5))]]` by
    (simp[NoAsms, Abbr `c8`] >>
     qpat_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sm.cs_current_insts = sa.cs_current_insts ++ _` (fn th => rewrite_tac[th]) >>
     simp_tac std_ss [rich_listTheory.TAKE_APPEND, listTheory.TAKE_def,
       listTheory.TAKE_LENGTH_TOO_LONG, stringTheory.STRCAT_EQNS,
       listTheory.APPEND_ASSOC] >>
     conj_tac >- (qpat_assum `sb.cs_current_bb = sa.cs_current_bb` (fn th => rewrite_tac[th]) >> sym_tac >> first_assum ACCEPT_TAC) >>
     simp_tac arith_ss [stringTheory.STRCAT_EQNS, GSYM listTheory.APPEND_ASSOC,
       listTheory.APPEND]) >>
  qabbrev_tac `nvar = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `bvar = STRING #"%" (toString (sa.cs_next_var+5))` >>
  qabbrev_tac `H8 = DRESTRICT H7 (COMPL {bvar})` >>
  qabbrev_tac `t8 = t7 with t_var := t7.t_var |+ (bvar,{})` >>
  qabbrev_tac `s8 = update_var bvar (n2w (LENGTH vs) * n2w (type_memory_bytes ce st)) s7
     with vs_inst_idx := SUC s7.vs_inst_idx` >>
  `lookup_var nvar s5 = SOME (n2w (LENGTH vs))` by
    (simp[Abbr `nvar`] >> metis_tac[]) >>
  `frag_exec_ptr cx ctx PG sm c8 (\g t u. g = H7 /\ t = t7 /\ u = s7)
     (\g t u. g = H8 /\ t = t8 /\ u = s8) R` by
    (irule typed_copy_loop_mul_frag_ptr >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`sa.cs_next_id+7`, `Var nvar`, `bvar`, `Lit (n2w (type_memory_bytes ce st))`] >>
     simp[Abbr `nvar`, Abbr `bvar`] >>
     simp[op_taint_def, eval_operand_def, Abbr `s8`,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_inj] >>
     qexists_tac `n2w (LENGTH vs)` >> simp[] >>
     qpat_assum `lookup_var (STRING #"%" (toString sa.cs_next_var)) s5 = _` mp_tac >>
     simp_tac std_ss [lookup_var_def]) >>
  `sb.cs_blocks = sm.cs_blocks` by
    (qpat_assum `ci_mono sm sb` mp_tac >> simp[ci_mono_def]) >>
  `cs_extends sm c8` by
    (simp[cs_extends_def, Abbr `c8`] >> qexists_tac `[]` >>
     simp[] >> metis_tac[rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends c8 sb` by
    (simp[NoAsms, Abbr `c8`, cs_extends_def,
       rich_listTheory.IS_PREFIX_EQ_TAKE'] >> metis_tac[]) >>
  irule typed_dynarray_frag_bind_ptr >>
  qexistsl_tac [`\g t u. g = H8 /\ t = t8 /\ u = s8`, `c8`] >> simp[] >>
  reverse conj_tac >-
    (qpat_assum `frag_exec_ptr cx ctx PG sm c8 _ _ R` mp_tac >>
     qpat_assum `s7 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `s6 = _` (fn th => rewrite_tac[th]) >> simp[NoAsms]) >>
  `s8.vs_memory = s5.vs_memory /\ t8.t_mem = t5.t_mem` by
    simp[Abbr `s8`, Abbr `t8`, update_var_def] >>
  `!m. mem_agree_outside t8.t_mem s8.vs_memory m ==>
       elems_in_memory vs (w2n p+32) stv m` by metis_tac[] >>
  `!m. mem_agree_outside t8.t_mem s8.vs_memory m ==>
       mem_word_at (w2n q) m = n2w (LENGTH vs)` by metis_tac[] >>
  irule typed_dynarray_mcopy_frag_ptr >>
  conj_tac >- simp[NoAsms, Abbr `c8`] >>
  qexistsl_tac [`Var bvar`,
    `STRING #"%" (toString (sa.cs_next_var+4))`, `sa.cs_next_id+8`,
    `STRING #"%" (toString (sa.cs_next_var+3))`] >>
  reverse conj_tac >-
    (qpat_assum `c8.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sm.cs_current_insts = sa.cs_current_insts ++ _` (fn th => rewrite_tac[th]) >>
     simp_tac arith_ss [Abbr `bvar`, Abbr `nvar`, stringTheory.STRCAT_EQNS,
       GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  simp_tac std_ss [] >>
  qexistsl_tac [`p + 32w`, `q + 32w`,
    `n2w (LENGTH vs) * n2w (type_memory_bytes ce st)`] >>
  conj_tac >-
    (simp[NoAsms, Abbr `s8`, Abbr `bvar`, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `!k. k <> STRING #"%" (toString (sa.cs_next_var+4)) ==> _` (qspec_then `STRING #"%" (toString (sa.cs_next_var+3))` mp_tac) >>
     simp[lookup_var_def, FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]) >>
  conj_tac >-
    (simp[NoAsms, Abbr `s8`, Abbr `bvar`, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `lookup_var (STRING #"%" (toString (sa.cs_next_var+4))) s7 = _` mp_tac >>
     simp_tac std_ss [lookup_var_def]) >>
  conj_tac >- simp[NoAsms, Abbr `s8`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[NoAsms, Abbr `t8`, op_taint_def, FLOOKUP_UPDATE] >>
  conj_tac >-
    (`LENGTH vs * type_memory_bytes ce st <= cap * type_memory_bytes ce st /\
      LENGTH vs * type_memory_bytes ce st <= source_cap * type_memory_bytes ce st` by
       simp[arithmeticTheory.LE_MULT_RCANCEL] >>
     `LENGTH vs * type_memory_bytes ce st < dimword(:256)` by decide_tac >>
     simp[NoAsms, wordsTheory.word_mul_n2w, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >>
     Cases_on `LENGTH vs * type_memory_bytes ce st = 0`
     >- (disj1_tac >> simp[Abbr `t8`, Abbr `bvar`, op_taint_def, FLOOKUP_UPDATE,
           ASCIInumbersTheory.toString_inj] >>
         qpat_assum `!k. k <> STRING #"%" (toString (sa.cs_next_var+4)) ==> _`
           (qspec_then `STRING #"%" (toString (sa.cs_next_var+3))` mp_tac) >>
         simp[wordsTheory.word_mul_n2w, ASCIInumbersTheory.toString_inj] >>
         qpat_assum `op_taint t7 (Var (STRING #"%" (toString (sa.cs_next_var+4)))) = {}`
           (fn th => rewrite_tac[SRULE[op_taint_def] th]) >>
         qpat_assum `!k. k <> STRING #"%" (toString (sa.cs_next_var+4)) ==> _`
           (qspec_then `STRING #"%" (toString (sa.cs_next_var+3))`
             (mp_tac o SRULE[op_taint_def])) >>
         qpat_assum `op_taint t6 (Var (STRING #"%" (toString (sa.cs_next_var+3)))) = {}`
           (fn th => rewrite_tac[SRULE[op_taint_def] th]) >>
         simp[NoAsms, ASCIInumbersTheory.toString_inj]) >>
     disj2_tac >>
     `ptr_covers H7 t7 (STRING #"%" (toString (sa.cs_next_var+4))) s7
       (cap * type_memory_bytes ce st)` by
       (qpat_assum `cap * _ = 0 \/ ptr_covers H7 _ _ _ _` strip_assume_tac >>
        simp[] >> decide_tac) >>
     `ptr_covers H6 t6 (STRING #"%" (toString (sa.cs_next_var+3))) s6
       (source_cap * type_memory_bytes ce st)` by
       (qpat_assum `source_cap * _ = 0 \/ ptr_covers H6 _ _ _ _` strip_assume_tac >>
        simp[] >> decide_tac) >>
     conj_tac >-
       (qpat_assum `ptr_covers H7 t7 _ _ _` mp_tac >>
        simp[NoAsms, ptr_covers_def, Abbr `H8`, Abbr `t8`, Abbr `s8`, Abbr `bvar`,
          op_taint_def, lookup_var_def, update_var_def, FLOOKUP_DRESTRICT,
          FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj] >>
        rpt strip_tac >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
     qpat_assum `!k. k <> STRING #"%" (toString (sa.cs_next_var+4)) ==> _`
       (qspec_then `STRING #"%" (toString (sa.cs_next_var+3))`
         (strip_assume_tac o SRULE[ASCIInumbersTheory.toString_inj])) >>
     qpat_assum `ptr_covers H6 t6 _ _ _` mp_tac >>
     simp[NoAsms, ptr_covers_def, Abbr `H8`, Abbr `t8`, Abbr `s8`, Abbr `bvar`,
       op_taint_def, lookup_var_def, update_var_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `op_taint t7 (Var (STRING #"%" (toString (sa.cs_next_var+3)))) = _`
       (fn th => rewrite_tac[SRULE[op_taint_def] th]) >>
     simp[] >> rpt strip_tac >> qexistsl_tac [`w`, `b`, `sz'`] >>
     simp[FLOOKUP_UPDATE] >>
     qpat_assum `FLOOKUP (s5.vs_vars |+ _) _ = SOME w` mp_tac >>
     simp[FLOOKUP_UPDATE]) >>
  qmatch_goalsub_abbrev_tac `Post H9 t9 s9` >>
  `LENGTH vs * type_memory_bytes ce st < dimword(:256)` by
    (`LENGTH vs * type_memory_bytes ce st <= cap * type_memory_bytes ce st` by
       simp[arithmeticTheory.LE_MULT_RCANCEL] >> decide_tac) >>
  `w2n (n2w (LENGTH vs) * n2w (type_memory_bytes ce st):256 word) =
     LENGTH vs * type_memory_size stv` by
    simp[wordsTheory.word_mul_n2w, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  simp[Abbr `Post`] >>
  conj_tac >- suspend "equal_value" >>
  suspend "equal_frames"
QED

Resume compile_copy_dynarray_typed_child_frag_ptr[equal_value]:
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+4)))) s8 = SOME (q+32w) /\
   eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+3)))) s8 = SOME (p+32w) /\
   eval_operand (Var bvar) s8 = SOME (n2w (LENGTH vs) * n2w (type_memory_bytes ce st))` by
    (simp[Abbr `s8`, Abbr `bvar`, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `!k. k <> STRING #"%" (toString (sa.cs_next_var+4)) ==> _`
       (qspec_then `STRING #"%" (toString (sa.cs_next_var+3))` mp_tac) >>
     simp[lookup_var_def, FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]) >>
  `(!i. i < LENGTH vs * type_memory_size stv ==>
      (w2n (q+32w)+i IN t9.t_mem <=> w2n (p+32w)+i IN t8.t_mem)) /\
   (!i. i < w2n (q+32w) \/ w2n (q+32w)+LENGTH vs * type_memory_size stv <= i ==>
      (i IN t9.t_mem <=> i IN t8.t_mem))` by
    (qpat_assum `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+4)))) s8 = _`
       (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] assign_base_mcopy_taint_window)) >>
     disch_then (qspecl_then [`Var (STRING #"%" (toString (sa.cs_next_var+3)))`,
       `Var bvar`, `p+32w`, `n2w (LENGTH vs) * n2w (type_memory_bytes ce st)`] mp_tac) >>
     simp[] >> disch_then (qspecl_then [`sa.cs_next_id+8`, `t8`] mp_tac) >>
     simp[Abbr `t9`] >> metis_tac[]) >>
  rpt strip_tac >> irule typed_dynarray_live_copy_post >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`w2n p+32`, `t8.t_mem`, `t9.t_mem`, `s8.vs_memory`, `s9.vs_memory`] >>
  simp[] >>
  Cases_on `LENGTH vs * type_memory_bytes ce st = 0`
  >- (simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!i. i < w2n (q+32w) \/ _ ==> _`
            (qspec_then `i+w2n q` mp_tac) >> simp[]) >>
      `w2n (q+32w) = 0 \/ w2n (q+32w) = w2n q+32` by
        (Cases_on `w2n q+32 = dimword(:256)`
         >- (disj1_tac >>
             `q+32w = n2w (w2n q+32)` by
               rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
             simp[wordsTheory.w2n_n2w]) >>
         disj2_tac >> simp[wordsTheory.w2n_add_2]) >>
      simp[Abbr `s9`] >>
      (conj_tac
       >- (qpat_assum `s8.vs_memory = s5.vs_memory` (fn th => rewrite_tac[GSYM th]) >>
           irule mcopy_mem_bytes_at_disjoint >> simp[] >> decide_tac)) >>
      simp[mem_bytes_at_def]) >>
  `LENGTH vs * type_memory_bytes ce st <= cap * type_memory_bytes ce st /\
   LENGTH vs * type_memory_bytes ce st <= source_cap * type_memory_bytes ce st` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `w2n (p+32w) = w2n p+32 /\ w2n (q+32w) = w2n q+32` by
    (`w2n p+32 < dimword(:256) /\ w2n q+32 < dimword(:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2]) >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_assum `!i. i < w2n (q+32w) \/ _ ==> _`
       (qspec_then `i+w2n q` mp_tac) >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH vs * type_memory_size stv ==> _`
       (qspec_then `i` mp_tac) >>
     `i + (w2n q+32) = (w2n q+32)+i /\
      i + (w2n p+32) = (w2n p+32)+i` by decide_tac >>
     qpat_assum `w2n (p+32w) = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `w2n (q+32w) = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `t8.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `type_memory_size stv = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `i + (w2n q+32) = _` (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `i + (w2n p+32) = _` (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `i < LENGTH vs * type_memory_bytes ce st`
       (fn th => rewrite_tac[th])) >>
  simp[Abbr `s9`] >> conj_tac
  >- (qpat_assum `s8.vs_memory = s5.vs_memory` (fn th => rewrite_tac[GSYM th]) >>
      irule mcopy_mem_bytes_at_disjoint >> simp[]) >>
  simp[mcopy_mem_bytes_at_same]
QED

Resume compile_copy_dynarray_typed_child_frag_ptr[equal_frames]:
  conj_tac
  >- (simp[Abbr `s9`, Abbr `s8`, mcopy_def, update_var_def,
           venom_state_component_equality] >>
      qpat_x_assum `s7 with <|vs_vars := _; vs_inst_idx := _|> = s6` mp_tac >>
      qpat_x_assum `s6 with <|vs_vars := _; vs_inst_idx := _|> = s5` mp_tac >>
      qpat_x_assum `s5 with <|vs_memory := _; vs_inst_idx := _|> = s4` mp_tac >>
      simp[Abbr `s4`, update_var_def, venom_state_component_equality] >>
      qpat_assum `s.vs_current_bb = _` mp_tac >>
      qpat_assum `s.vs_inst_idx = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      simp[write_memory_with_expansion_def]) >>
  conj_tac >- simp[Abbr `t9`, Abbr `t8`, step_taint_def, mcopy_def,
                      write_memory_with_expansion_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  conj_tac >- simp[Abbr `t9`, Abbr `t8`, step_taint_def, mcopy_def,
                      write_memory_with_expansion_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  conj_tac >- simp[Abbr `t9`, Abbr `t8`, step_taint_def, mcopy_def,
                      write_memory_with_expansion_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  `LENGTH vs * type_memory_bytes ce st <= cap * type_memory_bytes ce st` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `w2n (q+32w) = (if w2n q+32 = dimword(:256) then 0 else w2n q+32) /\
   (w2n q+32 = dimword(:256) ==> LENGTH vs * type_memory_bytes ce st = 0)` by
    (Cases_on `w2n q+32 = dimword(:256)`
     >- (`LENGTH vs * type_memory_bytes ce st = 0` by decide_tac >>
         `q+32w = n2w (w2n q+32)` by
           rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
         pure_asm_rewrite_tac[wordsTheory.w2n_n2w] >> simp[]) >>
     simp[wordsTheory.w2n_add_2]) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at a n s9.vs_memory = mem_bytes_at a n s8.vs_memory` by
        (simp[NoAsms, Abbr `s9`] >> irule mcopy_mem_bytes_at_disjoint >>
         Cases_on `w2n q+32 = dimword(:256)` >> simp[] >> decide_tac) >>
      `mem_bytes_at a n s5.vs_memory = mem_bytes_at a n s4.vs_memory` by
        (qpat_assum `!p n. p+n <= w2n q \/ _ ==> _` irule >> decide_tac) >>
      simp[Abbr `s4`, update_var_def]) >>
  conj_tac
  >- (`eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+4)))) s8 = SOME (q+32w) /\
       eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+3)))) s8 = SOME (p+32w) /\
       eval_operand (Var bvar) s8 = SOME (n2w (LENGTH vs) * n2w (type_memory_bytes ce st))` by
        (simp[Abbr `s8`, Abbr `bvar`, eval_operand_def, lookup_var_def, update_var_def,
           FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj] >>
         qpat_assum `!k. k <> STRING #"%" (toString (sa.cs_next_var+4)) ==> _`
           (qspec_then `STRING #"%" (toString (sa.cs_next_var+3))` mp_tac) >>
         simp[lookup_var_def, FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]) >>
      `!i. i < w2n (q+32w) \/ w2n (q+32w)+LENGTH vs * type_memory_size stv <= i ==>
           (i IN t9.t_mem <=> i IN t8.t_mem)` by
        (qpat_assum `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+4)))) s8 = _`
          (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] assign_base_mcopy_taint_window)) >>
         disch_then (qspecl_then [`Var (STRING #"%" (toString (sa.cs_next_var+3)))`,
           `Var bvar`, `p+32w`, `n2w (LENGTH vs) * n2w (type_memory_bytes ce st)`] mp_tac) >>
         simp[] >> disch_then (qspecl_then [`sa.cs_next_id+8`, `t8`] mp_tac) >>
         simp[Abbr `t9`] >> metis_tac[]) >>
      rpt strip_tac >>
      `a IN t9.t_mem <=> a IN t8.t_mem` by
        (qpat_assum `!i. i < w2n (q+32w) \/ _ ==> _` irule >>
         Cases_on `w2n q+32 = dimword(:256)` >> simp[] >> decide_tac) >>
      `a IN t5.t_mem <=> a IN t4.t_mem` by
        (qpat_assum `!p. p < w2n q \/ _ ==> _` irule >> decide_tac) >>
      simp[]) >>
  qx_gen_tac `k` >> strip_tac >>
  `k <> STRING #"%" (toString (sa.cs_next_var+3)) /\
   k <> STRING #"%" (toString (sa.cs_next_var+4)) /\ k <> bvar` by
    (qpat_assum `not_fresh_at sa k` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.not_fresh_at_def] >>
     simp[NoAsms, Abbr `bvar`] >> strip_tac >> rpt conj_tac >> first_x_assum irule >> simp[]) >>
  `lookup_var k s7 = lookup_var k s /\ FLOOKUP H7 k = FLOOKUP G k /\
   op_taint t7 (Var k) = op_taint tn (Var k)` by simp[] >>
  simp[Abbr `s9`, Abbr `H9`, Abbr `t9`, Abbr `s8`, Abbr `H8`, Abbr `t8`,
    step_prov_def, step_taint_def, mcopy_def, write_memory_with_expansion_def,
    lookup_var_def, update_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    op_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    set_prov_def, set_var_taint_def] >>
  conj_tac
  >- (qpat_assum `!x. lookup_var x s5 = _ /\ _` (qspec_then `k` mp_tac) >>
      qpat_assum `!k. not_fresh_at sa k ==> lookup_var k _ = lookup_var k s /\ _`
        (qspec_then `k` mp_tac) >>
      pure_rewrite_tac[lookup_var_def] >>
      qpat_assum `not_fresh_at sa k` (fn th => simp[NoAsms, th]) >>
      rpt strip_tac >> simp[]) >>
  qpat_assum `op_taint t7 (Var k) = _` mp_tac >>
  pure_rewrite_tac[op_taint_def] >> simp[]
QED

Resume compile_copy_dynarray_typed_child_frag_ptr[element_loop]:
  rewrite_tac[frag_exec_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\g t u. _) _ _ _` mp_tac >>
  BETA_TAC >> strip_tac >>
  qpat_x_assum `G'' = H7` SUBST_ALL_TAC >>
  qpat_x_assum `tn'' = t7` SUBST_ALL_TAC >>
  `fn_has_code sa sb fn'` by
    (qpat_assum `fn_has_code sm sb fn'` mp_tac >>
     qpat_assum `sm.cs_blocks = sa.cs_blocks` (fn th =>
       simp[NoAsms, fn_has_code_def, emitted_blocks_def, th])) >>
  `~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st)` by simp[] >>
  drule_at (Pat `fn_has_code _ _ fn'`) typed_dynarray_child_states >>
  disch_then drule_all >>
  disch_then (qx_choose_then `sc` (qx_choose_then `ec`
    (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `sr = STRING #"%" (toString (sa.cs_next_var+3))` >>
  qabbrev_tac `dr = STRING #"%" (toString (sa.cs_next_var+4))` >>
  qabbrev_tac `len = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `ctr = STRING #"%" (toString (sa.cs_next_var+5))` >>
  qabbrev_tac `so = STRING #"%" (toString (sa.cs_next_var+8))` >>
  qabbrev_tac `dof = STRING #"%" (toString (sa.cs_next_var+9))` >>
  qabbrev_tac `sp = STRING #"%" (toString (sa.cs_next_var+10))` >>
  qabbrev_tac `dp = STRING #"%" (toString (sa.cs_next_var+11))` >>
  qabbrev_tac `n = LENGTH vs` >>
  qabbrev_tac `ss = type_memory_bytes ce st` >>
  qabbrev_tac `ds = type_memory_bytes ce dt` >>
  qabbrev_tac `a = w2n p+32` >>
  qabbrev_tac `b = w2n q` >>
  qabbrev_tac `srcspan = source_cap*ss` >>
  qabbrev_tac `dstspan = cap*ds` >>
  qabbrev_tac `V = {z | not_fresh_at sa z \/ z=sr \/ z=dr \/ z=len}` >>
  qabbrev_tac `Frame = (\g t u.
    (u with <|vs_vars:=s7.vs_vars; vs_memory:=s7.vs_memory;
      vs_current_bb:=s7.vs_current_bb; vs_inst_idx:=s7.vs_inst_idx;
      vs_prev_bb:=s7.vs_prev_bb|>)=s7 /\
    t.t_stor=t7.t_stor /\ t.t_trans=t7.t_trans /\ t.t_imm=t7.t_imm /\
    (!z k. z+k<=b \/ b+32+dstspan<=z ==>
      mem_bytes_at z k u.vs_memory=mem_bytes_at z k s7.vs_memory) /\
    (!z. z<b \/ b+32+dstspan<=z ==> (z IN t.t_mem <=> z IN t7.t_mem)) /\
    (!z. z IN V ==> lookup_var z u=lookup_var z s7 /\
      FLOOKUP g z=FLOOKUP H7 z /\ op_taint t (Var z)=op_taint t7 (Var z)))` >>
  qabbrev_tac `Mem = (\i t u.
    (!m. mem_agree_outside t.t_mem u.vs_memory m ==> elems_in_memory vs a stv m) /\
    (!m. mem_agree_outside t.t_mem u.vs_memory m ==> mem_word_at b m=n2w n) /\
    (!j. j<i ==> !m. mem_agree_outside t.t_mem u.vs_memory m ==>
      val_in_memory dtv (EL j vs) (b+32+j*ds) m))` >>
  qabbrev_tac `Regs = (\g t u.
    lookup_var sr u=SOME(n2w a) /\ lookup_var dr u=SOME(n2w(b+32)) /\
    lookup_var len u=SOME(n2w n) /\ op_taint t (Var sr)={} /\
    op_taint t (Var dr)={} /\ op_taint t (Var len)={} /\ FLOOKUP g len=NONE /\
    (ss<>0 ==> ptr_covers g t sr u srcspan) /\
    (ds<>0 ==> ptr_covers g t dr u dstspan))` >>
  qabbrev_tac `sbod = sc with cs_current_insts := []` >>
  `ALL_DISTINCT [so;dof;sp;dp] /\
   (!z. MEM z [so;dof;sp;dp] ==> ctr<>z /\ sr<>z /\ dr<>z)` by
    (simp[Abbr `so`, Abbr `dof`, Abbr `sp`, Abbr `dp`, Abbr `ctr`,
      Abbr `sr`, Abbr `dr`, ASCIInumbersTheory.toString_inj] >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    gvs[ASCIInumbersTheory.toString_inj]) >>
  `sc.cs_blocks=sbod.cs_blocks /\ sc.cs_current_bb=sbod.cs_current_bb /\
   sc.cs_current_insts=sbod.cs_current_insts ++
     [mk_inst (sa.cs_next_id+12) MUL [Var ctr;Lit (n2w ss)] [so];
      mk_inst (sa.cs_next_id+13) MUL [Var ctr;Lit (n2w ds)] [dof];
      mk_inst (sa.cs_next_id+14) ADD [Var sr;Var so] [sp];
      mk_inst (sa.cs_next_id+15) ADD [Var dr;Var dof] [dp]]` by
    simp[Abbr `sbod`, Abbr `ctr`, Abbr `so`, Abbr `dof`, Abbr `sp`,
      Abbr `dp`, Abbr `sr`, Abbr `dr`] >>
  `s7.vs_alloca_next=s.vs_alloca_next` by
    (qpat_assum `_ = s6` (mp_tac o Q.AP_TERM `(\u:venom_state. u.vs_alloca_next)`) >>
     qpat_assum `_ = s5` (mp_tac o Q.AP_TERM `(\u:venom_state. u.vs_alloca_next)`) >>
     qpat_assum `_ = s4` (mp_tac o Q.AP_TERM `(\u:venom_state. u.vs_alloca_next)`) >>
     simp[Abbr `s4`, update_var_def]) >>
  `a+srcspan<=s7.vs_alloca_next /\ b+32+dstspan<=s7.vs_alloca_next /\
   a+srcspan<=dimword(:256) /\ b+32+dstspan<=dimword(:256)` by
    (simp[Abbr `a`] >> decide_tac) >>
  `!i g t u. i<n /\ Regs g t u /\ Mem i t u /\ Frame g t u /\
    lookup_var ctr u=SOME(n2w i) /\ FLOOKUP g ctr=NONE /\ op_taint t (Var ctr)={} ==>
    frag_exec_ptr cx ctx PG sbod ec (\h v w. h=g /\ v=t /\ w=u)
      (\h v w. Regs h v w /\ Mem (SUC i) v w /\ Frame h v w /\
        lookup_var ctr w=SOME(n2w i) /\ FLOOKUP h ctr=NONE /\
        op_taint v (Var ctr)={}) R` by suspend "body_step" >>
  suspend "element_loop_chain"
QED

Resume compile_copy_dynarray_typed_child_frag_ptr[body_step]:
  markerLib.RESUME_TAC >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`Abbrev (Post = _)`, `Abbrev (s4 = _)`, `Abbrev (c4 = _)`,
     `Abbrev (c5 = _)`, `Abbrev (c6 = _)`] >>
  rpt (qhdtm_x_assum `Abbrev` mp_tac) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`type_memory_size stv = ss`, `type_memory_size dtv = ds`,
     `n <= source_cap`, `n <= cap`, `cap < dimword(:256)`,
     `EVERY (\v. value_has_type stv v /\ value_has_type dtv v) vs`,
     `!sc ec sop dop v. _`,
     `compile_store_memory_typed _ _ _ _ _ sc = _`,
     `sc.cs_next_var = _`, `ci_mono sa sc`,
     `ALL_DISTINCT [so;dof;sp;dp]`,
     `!z. MEM z [so;dof;sp;dp] ==> _`,
     `sc.cs_blocks = sbod.cs_blocks`,
     `sc.cs_current_bb = sbod.cs_current_bb`,
     `sc.cs_current_insts = sbod.cs_current_insts ++ _`,
     `a+srcspan <= s7.vs_alloca_next`,
     `b+32+dstspan <= s7.vs_alloca_next`,
     `a+srcspan <= dimword(:256)`, `b+32+dstspan <= dimword(:256)`,
     `w2n p + (srcspan+32) <= b \/ _`] >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >>
  rpt gen_tac >> strip_tac >>
  `ss<>0 ==> i*ss<srcspan /\ i*ss+ss<=srcspan /\
      w2n (n2w a:bytes32)+i*ss<dimword(:256)` by
    (strip_tac >>
     `i<source_cap /\ SUC i<=source_cap` by decide_tac >>
     `SUC i*ss<=source_cap*ss` by
       (pure_rewrite_tac[arithmeticTheory.LE_MULT_RCANCEL] >> simp[]) >>
     `i*ss<srcspan /\ i*ss+ss<=srcspan` by
       (qpat_x_assum `SUC i*ss<=_` mp_tac >>
        pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >>
        disch_tac >> simp[Abbr `srcspan`] >> decide_tac) >>
     `a<dimword(:256)` by decide_tac >> simp[] >> decide_tac) >>
  `ds<>0 ==> i*ds<dstspan /\ i*ds+ds<=dstspan /\
      w2n (n2w (b+32):bytes32)+i*ds<dimword(:256)` by
    (strip_tac >>
     `i<cap /\ SUC i<=cap` by decide_tac >>
     `SUC i*ds<=cap*ds` by
       (pure_rewrite_tac[arithmeticTheory.LE_MULT_RCANCEL] >> simp[]) >>
     `i*ds<dstspan /\ i*ds+ds<=dstspan` by
       (qpat_x_assum `SUC i*ds<=_` mp_tac >>
        pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >>
        disch_tac >> simp[Abbr `dstspan`] >> decide_tac) >>
     `b+32<dimword(:256)` by decide_tac >> simp[] >> decide_tac) >>
  qpat_assum `Regs g t u` mp_tac >> simp[NoAsms, Abbr `Regs`] >> strip_tac >>
  Q.UNDISCH_THEN `lookup_var ctr u = SOME (n2w i)`
    (mp_then (Pat `lookup_var ctr s = SOME (n2w i)`) mp_tac
      typed_dynarray_loop_address_ptr) >>
  disch_then (fn th => Q.UNDISCH_THEN `op_taint t (Var ctr) = {}`
    (mp_then (Pat `op_taint tn (Var ctr) = {}`) mp_tac th)) >>
  disch_then (fn th => Q.UNDISCH_THEN `lookup_var sr u = SOME (n2w a)`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => Q.UNDISCH_THEN `lookup_var dr u = SOME (n2w (b+32))`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => Q.UNDISCH_THEN `op_taint t (Var sr) = {}`
    (mp_then (Pat `op_taint tn (Var sr) = {}`) mp_tac th)) >>
  disch_then (fn th => Q.UNDISCH_THEN `op_taint t (Var dr) = {}`
    (mp_then (Pat `op_taint tn (Var dr) = {}`) mp_tac th)) >>
  disch_then (fn th =>
    `ss<>0 ==> ptr_covers g t sr u srcspan /\ i*ss<srcspan /\
      i*ss+ss<=srcspan /\ w2n (n2w a:bytes32)+i*ss<dimword(:256)` by simp[] >>
    qpat_x_assum `ss<>0 ==> ptr_covers _ _ _ _ _ /\ _`
      (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th =>
    `ds<>0 ==> ptr_covers g t dr u dstspan /\ i*ds<dstspan /\
      i*ds+ds<=dstspan /\ w2n (n2w (b+32):bytes32)+i*ds<dimword(:256)` by simp[] >>
    qpat_x_assum `ds<>0 ==> ptr_covers _ _ _ _ _ /\ _`
      (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => qpat_assum `ALL_DISTINCT [so;dof;sp;dp]`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => qpat_assum `!z. MEM z [so;dof;sp;dp] ==> _`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => qpat_assum `sc.cs_blocks=sbod.cs_blocks`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => qpat_assum `sc.cs_current_bb=sbod.cs_current_bb`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`,`sa.cs_next_id+12`] mp_tac) >>
  (impl_tac >- simp[arithmeticTheory.ADD_ASSOC]) >>
  disch_then (qx_choose_then `ga` (qx_choose_then `ta`
    (qx_choose_then `ua` (map_every assume_tac o CONJUNCTS)))) >>
  `compile_store_memory_typed ce (Var dp) dt (Var sp) st sc = ((),ec)` by
    (qpat_assum `compile_store_memory_typed ce _ dt _ st sc = _` mp_tac >>
     simp[NoAsms, Abbr `dp`, Abbr `sp`, stringTheory.STRCAT_EQNS]) >>
  qpat_assum `compile_store_memory_typed ce (Var dp) dt (Var sp) st sc = _`
    (fn cth => qpat_assum `!sc ec sop dop v. _`
      (fn ith => mp_then (Pos hd) mp_tac ith cth)) >>
  disch_then (qspec_then `EL i vs` mp_tac) >>
  disch_then (qspecl_then [`ga`,`ta`,`ua`] mp_tac) >>
  disch_then (qspecl_then
    [`n2w (w2n (n2w a:bytes32)+i*ss):bytes32`,
     `n2w (w2n (n2w (b+32):bytes32)+i*ds):bytes32`] mp_tac) >>
  (impl_tac >- suspend "child_runtime") >>
  suspend "child_composition"
QED

Resume compile_copy_dynarray_typed_child_frag_ptr[child_runtime]:
  markerLib.RESUME_TAC >>
  `n2w (w2n (n2w a:bytes32)+i*ss):bytes32 = n2w (a+i*ss)` by
    simp[GSYM word_add_n2w] >>
  `n2w (w2n (n2w (b+32):bytes32)+i*ds):bytes32 = n2w (b+32+i*ds)` by
    simp[GSYM word_add_n2w] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (conj_tac
      >- (qpat_assum `sc.cs_next_var = _` mp_tac >>
          simp[NoAsms, Abbr `sp`, Abbr `dp`,
            loweringStateRelDefsTheory.not_fresh_at_def,
            ASCIInumbersTheory.toString_inj] >>
          rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >> decide_tac) >>
      qpat_assum `EVERY _ vs` mp_tac >> pure_rewrite_tac[EVERY_EL] >>
      disch_then (qspec_then `i` mp_tac) >>
      qpat_assum `i<n` mp_tac >> simp[NoAsms, Abbr `n`]) >>
  `ua.vs_alloca_next = s7.vs_alloca_next` by
    (qpat_assum `ua with <|vs_vars := _; vs_inst_idx := _|> = u`
       (mp_tac o Q.AP_TERM `(\v:venom_state. v.vs_alloca_next)`) >>
     qpat_assum `Frame g t u` mp_tac >>
     simp[NoAsms, Abbr `Frame`] >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (mp_tac o Q.AP_TERM `(\v:venom_state. v.vs_alloca_next)`) >>
     simp[]) >>
  `w2n (n2w (a+i*ss):bytes32)+ss<=ua.vs_alloca_next /\
   w2n (n2w (a+i*ss):bytes32)+ss<=dimword(:256) /\
   (ss<>0 ==> w2n (n2w (a+i*ss):bytes32)=a+i*ss)` by
    (irule typed_dynarray_child_word_window >> qexists_tac `source_cap` >>
     simp[Abbr `srcspan`] >> decide_tac) >>
  `w2n (n2w (b+32+i*ds):bytes32)+ds<=ua.vs_alloca_next /\
   w2n (n2w (b+32+i*ds):bytes32)+ds<=dimword(:256) /\
   (ds<>0 ==> w2n (n2w (b+32+i*ds):bytes32)=b+32+i*ds)` by
    (irule typed_dynarray_child_word_window >> qexists_tac `cap` >>
     simp[Abbr `dstspan`] >> decide_tac) >>
  simp[eval_operand_def] >>
  FAIL_TAC "runtime_separation"
QED
