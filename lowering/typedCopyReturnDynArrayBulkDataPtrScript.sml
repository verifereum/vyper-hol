(* Live-data dynamic array copying: zero payloads need clean roots, not provenance. *)
Theory typedCopyReturnDynArrayBulkDataPtr
Ancestors
  bodyPtrPopLocalRootFrame assignTuplePtrPrefix annAssignPtrCopy fragGasSeqPtr
  assignBasePtrMcopyTransport typedMemoryCopy forPtrBulk
  fragExecPtr ptrSafeRun ptrDiscipline codegenRel contextCodegenRel venomExecSemantics
  venomInst venomState context emitHelper compileEnv words finite_map pred_set

Theorem typed_copy_empty_operand_ok[local]:
  eval_operand count_op s = SOME 0w /\ op_taint tn count_op = {} /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
Proof
  strip_tac >>
  `step_inst fuel ctx (mk_inst id MCOPY [Var dst; Var src; count_op] []) s =
     OK (mcopy (w2n b) (w2n a) 0 s)` by
    (simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, eval_operand_def,
       mcopy_def, write_memory_with_expansion_def] >>
  gen_tac >> Cases_on `op = Var dst` >> gvs[] >>
  Cases_on `op = Var src` >> gvs[] >>
  Cases_on `op = count_op` >> gvs[op_taint_def]
QED

Theorem typed_copy_dynamic_operand_counted[local]:
  compile_copy_memory_dynamic (Var dst) (Var src) count_op sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  (n <> 0w ==> ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n)) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s))
    (step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (OK ((mcopy (w2n b) (w2n a) (w2n n) s) with
      vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `emit_inst MCOPY [Var dst;Var src;count_op] [] sa = ((),sb)` by
    gvs[compile_copy_memory_dynamic_def,emit_void_def,emit_inst_def] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by
    gvs[emit_inst_def,comp_bind_def,fresh_id_def,emit_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s` by
    (Cases_on `n = 0w`
     >- (irule typed_copy_empty_operand_ok >> gvs[] >> metis_tac[]) >>
     irule ptr_inst_ok_mcopy_operand >> simp[] >> metis_tac[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s =
    OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
    simp[step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def] >>
  drule (SRULE [is_terminator_def] (Q.INST [`opc` |-> `MCOPY`] emit_inst_zero_path_ptr)) >>
  disch_then (drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[]
QED

Theorem typed_copy_robust_elements_transport[local]:
  EVERY (val_wf tv) vs /\
  mem_bytes_at dst (LENGTH vs * type_memory_size tv) target =
    mem_bytes_at src (LENGTH vs * type_memory_size tv) original /\
  (!i. i < LENGTH vs * type_memory_size tv ==>
    (dst+i IN dirty' <=> src+i IN dirty)) /\
  (!m. mem_agree_outside dirty original m ==> elems_in_memory vs src tv m) ==>
  !m. mem_agree_outside dirty' target m ==> elems_in_memory vs dst tv m
Proof
  strip_tac >> simp[typed_copy_elems_indexed] >> rpt strip_tac >>
  `val_wf tv (EL i vs)` by metis_tac[listTheory.EVERY_EL] >>
  `val_footprint tv (EL i vs) <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  `i * type_memory_size tv + type_memory_size tv <=
    LENGTH vs * type_memory_size tv` by
    (`SUC i <= LENGTH (vs:value list)` by simp[] >>
     metis_tac[arithmeticTheory.MULT_CLAUSES, arithmeticTheory.ADD_COMM,
       arithmeticTheory.LESS_MONO_MULT]) >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
  simp[] >> qexistsl_tac [`original`,`target`,`type_memory_size tv`,
    `src+i*type_memory_size tv`,`dirty`,`dirty'`] >> simp[] >>
  conj_tac >- metis_tac[typed_copy_elems_indexed] >>
  irule valueEncodingPropsTheory.mem_bytes_at_translated_window >> metis_tac[]
QED

Theorem typed_copy_dynarray_memory_transport[local]:
  EVERY (val_wf tv) vs /\
  mem_bytes_at (dst+32) (LENGTH vs * type_memory_size tv) target =
    mem_bytes_at src (LENGTH vs * type_memory_size tv) original /\
  (!i. i < LENGTH vs * type_memory_size tv ==>
    (dst+32+i IN dirty' <=> src+i IN dirty)) /\
  (!i. dst <= i /\ i < dst+32 ==>
    mem_bytes_at i 1 target = mem_bytes_at i 1 original /\
    (i IN dirty' <=> i IN dirty)) /\
  (!m. mem_agree_outside dirty original m ==>
    mem_word_at dst m = n2w (LENGTH vs)) /\
  (!m. mem_agree_outside dirty original m ==> elems_in_memory vs src tv m) ==>
  !m. mem_agree_outside dirty' target m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) dst m
Proof
  strip_tac >>
  `!i. dst <= i /\ i < dst+32 ==> i NOTIN dirty` by
    metis_tac[representationCleanPtrTheory.robust_mem_word_at_clean] >>
  `!m. mem_agree_outside dirty' target m ==> elems_in_memory vs (dst+32) tv m` by
    (rpt strip_tac >> irule typed_copy_robust_elements_transport >>
     metis_tac[]) >>
  rpt strip_tac >> simp[valueEncodingTheory.val_in_memory_def] >>
  `mem_bytes_at dst 32 m = mem_bytes_at dst 32 original` by
    (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >> rpt strip_tac >>
     `i NOTIN dirty' /\ mem_bytes_at i 1 target = mem_bytes_at i 1 original` by
       metis_tac[] >>
     fs[bodyPtrDefsTheory.mem_agree_outside_def] >> metis_tac[]) >>
  `mem_word_at dst original = n2w (LENGTH vs)` by
    (first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  metis_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes]
QED

Theorem typed_copy_dynarray_mcopy_post[local]:
  eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a /\
  eval_operand count_op s = SOME (n2w n) /\
  n = LENGTH vs * type_memory_size tv /\ n < dimword(:256) /\
  w2n b = dbase+32 /\ EVERY (val_wf tv) vs /\
  u = mcopy (w2n b) (w2n a) n s /\
  tf = step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s u tn /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at dbase m = n2w (LENGTH vs)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    elems_in_memory vs (w2n a) tv m) ==>
  step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] []) u = G /\
  tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  tf.t_imm = tn.t_imm /\
  (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) dbase m) /\
  (!i. i < w2n b \/ w2n b+n <= i ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `w2n ((n2w n):256 word) = n` by simp[] >>
  mp_tac (Q.SPECL [`PG`,`G`,`tn`,`s`,`id`]
    typedCopyPtrTheory.mcopy_operand_ghost_frame) >>
  disch_then (qspecl_then [`Var dst`,`Var src`,`count_op`] mp_tac) >>
  disch_then (qspecl_then [`a`,`b`,`n2w n`] mp_tac) >>
  simp[] >> strip_tac >>
  `tf.t_imm = tn.t_imm` by
    gvs[step_taint_def,mk_inst_def,imm_taint_def,adopt_reset_def,set_var_taint_def] >>
  `!i. i < w2n b \/ w2n b+n <= i ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_tac >> conj_tac
     >- (gvs[] >> irule valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint >> decide_tac) >>
     gvs[] >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) dbase m` by
    (rpt strip_tac >> irule (GEN_ALL typed_copy_dynarray_memory_transport) >>
     simp[] >>
     qexistsl_tac [`tn.t_mem`,`tf.t_mem`,`s.vs_memory`,`w2n a`,`u.vs_memory`] >>
     simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_same]) >>
  gvs[] >> metis_tac[]
QED

Theorem typed_copy_dynarray_operand_endpoint[local]:
  compile_copy_memory_dynamic (Var dst) (Var src) count_op sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME (n2w (LENGTH vs * type_memory_size tv)) /\
  op_taint tn count_op = {} /\ op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  LENGTH vs * type_memory_size tv < dimword(:256) /\
  (LENGTH vs * type_memory_size tv <> 0 ==>
    ptr_covers G tn src s (LENGTH vs * type_memory_size tv) /\
    ptr_covers G tn dst s (LENGTH vs * type_memory_size tv)) /\
  w2n b = dbase+32 /\ EVERY (val_wf tv) vs /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at dbase m = n2w (LENGTH vs)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    elems_in_memory vs (w2n a) tv m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ typed_copy_state_frame sa (w2n b) (LENGTH vs * type_memory_size tv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) dbase m) /\
    (!i. i < w2n b \/ w2n b + LENGTH vs * type_memory_size tv <= i ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `n2w (LENGTH vs * type_memory_size tv) <> (0w:256 word) ==>
   ptr_covers G tn src s (w2n ((n2w (LENGTH vs * type_memory_size tv)):256 word)) /\
   ptr_covers G tn dst s (w2n ((n2w (LENGTH vs * type_memory_size tv)):256 word))` by simp[] >>
  drule_all (GEN_ALL typed_copy_dynamic_operand_counted) >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u)` >>
  qmatch_asmsub_abbrev_tac `tm = step_taint inst s copied tn` >>
  `eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a` by
    simp[eval_operand_def] >>
  mp_tac (Q.INST [`id` |-> `sa.cs_next_id`, `n` |-> `LENGTH vs * type_memory_size tv`,
    `u` |-> `copied`, `tf` |-> `tm`] typed_copy_dynarray_mcopy_post) >>
  simp[Abbr `copied`, Abbr `tm`, Abbr `inst`] >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[compile_copy_memory_dynamic_def,emit_void_def,emit_inst_def,comp_bind_def,
        fresh_id_def,emit_def] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u)` >>
  qexistsl_tac [`H`,`tm`,`u`] >>
  simp[Abbr `u`, typed_copy_mcopy_state_frame] >>
  conj_tac >- simp[mcopy_def,write_memory_with_expansion_def] >>
  conj_tac >- metis_tac[] >>
  simp[mcopy_def,write_memory_with_expansion_def,lookup_var_def,op_taint_def]
QED

Theorem typed_copy_dynarray_bulk_data_counted:
  emit_op MUL [lenop; Lit (n2w (type_memory_size tv))] sa = (count_op,sb) /\
  compile_copy_memory_dynamic (Var dst) (Var src) count_op sb = ((),sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand lenop s = SOME (n2w (LENGTH vs)) /\ op_taint tn lenop = {} /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  LENGTH vs * type_memory_size tv < dimword(:256) /\
  (LENGTH vs * type_memory_size tv <> 0 ==>
    ptr_covers G tn src s (LENGTH vs * type_memory_size tv) /\
    ptr_covers G tn dst s (LENGTH vs * type_memory_size tv)) /\
  w2n b = dbase+32 /\ EVERY (val_wf tv) vs /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at dbase m = n2w (LENGTH vs)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    elems_in_memory vs (w2n a) tv m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) (LENGTH vs * type_memory_size tv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) dbase m) /\
    (!i. i < w2n b \/ w2n b + LENGTH vs * type_memory_size tv <= i ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Lit (n2w (type_memory_size tv))) s =
     SOME (n2w (type_memory_size tv)) /\
   op_taint tn (Lit (n2w (type_memory_size tv))) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  drule_all pop_local_mul_exact >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `lookup_var src t = SOME a /\ lookup_var dst t = SOME b /\
   op_taint tn' (Var src) = {} /\ op_taint tn' (Var dst) = {}` by metis_tac[] >>
  `eval_operand count_op t = SOME (n2w (LENGTH vs * type_memory_size tv))` by
    gvs[wordsTheory.word_mul_n2w] >>
  `LENGTH vs * type_memory_size tv <> 0 ==>
   ptr_covers G' tn' src t (LENGTH vs * type_memory_size tv) /\
   ptr_covers G' tn' dst t (LENGTH vs * type_memory_size tv)` by
    (strip_tac >> fs[] >> metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame]) >>
  `(!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      mem_word_at dbase m = n2w (LENGTH vs)) /\
   (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      elems_in_memory vs (w2n a) tv m)` by gvs[] >>
  drule_all (GEN_ALL typed_copy_dynarray_operand_endpoint) >>
  disch_then (qspecl_then [`cap`,`PG`,`D`] strip_assume_tac) >>
  drule_all fragGasPathPtrTheory.gas_path_ptr_then >> strip_tac >>
  qexistsl_tac [`H`,`tm`,`t'`] >> simp[] >>
  `ci_mono sa sb` by metis_tac[typed_copy_emit_op_mono] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    metis_tac[exprLoweringPropsTheory.ci_mono_def,freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `t` >> conj_tac
      >- (rw[typed_copy_state_frame_def,typed_copy_frame_def]
          >- (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
                (fn th => once_rewrite_tac[th]) >>
              qpat_x_assum `s.vs_current_bb = _` (fn th => rewrite_tac[GSYM th]) >>
              qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
          metis_tac[]) >>
      metis_tac[typed_copy_state_frame_mono]) >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  metis_tac[]
QED
