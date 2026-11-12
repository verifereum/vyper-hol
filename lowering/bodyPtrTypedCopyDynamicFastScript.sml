(* Counted runtime payload copy for equal-element dynamic arrays. *)
Theory bodyPtrTypedCopyDynamicFast
Ancestors bodyPtrTypedCopyArrayControl annAssignPtrCopy
  assignTuplePtrLocalFixedCopy annAssignPtrScratch venomMemProofs
  venomExecSemantics venomInst venomState ptrDiscipline words
  finite_map arithmetic bodyPtrDefs fragGasPathPtr fragGasSeqPtr
  bodyPtrTypedCopyDynamicEntry bodyPtrTypedCopyArrayFrame bodyPtrTypedCopyBoundary
  typedDynStoreProps vyperTypeValues vyperTypeSystem typedCopyStateFrame
  typedCopyLayoutPtr bodyPtrPopMemoryHeader dynCopyCode abiBytestringCode
  externalReturnCopyArrays normalizationPrefixPtr valueEncodingProps
  rich_list fragExec loweringStateRelDefs typedArrayLoopValues externalEntryShape
  exprLoweringProps bodyPtrTypedCopyDynamicControl typedMemoryCopy
  typedCopyRobustTransportPtr robustCopyTransportPtr

Theorem typed_copy_dynamic_payload_counted:
  !s ctx fn bb id len cnt src dst a b n stride G tn PG D.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MUL [Var len;Lit (n2w stride)] [cnt]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) MCOPY [Var dst;Var src;Var cnt] []) /\
  lookup_var len s = SOME (n2w n) /\ op_taint tn (Var len) = {} /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (n*stride) /\ ptr_covers G tn dst s (n*stride) /\
  cnt <> src /\ cnt <> dst /\ cnt <> len /\
  n*stride < dimword(:256) /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?H tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\
    ~u.vs_halted /\
    u.vs_memory = (mcopy (w2n b) (w2n a) (n*stride) s).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. i < n*stride ==> (w2n b+i IN tf.t_mem <=> w2n a+i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+n*stride) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    mem_bytes_at (w2n b) (n*stride) u.vs_memory =
      mem_bytes_at (w2n a) (n*stride) s.vs_memory /\
    (!p. p <> cnt ==> lookup_var p u = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var cnt (n2w (n*stride)) s with
    vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {cnt})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (cnt,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     irule typed_copy_arith_counted >> simp[update_var_def] >>
     qexistsl_tac [`id`, `MUL`, `[Var len; Lit (n2w stride)]`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[op_taint_def]) >>
     simp[update_var_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, wordsTheory.word_mul_n2w]) >>
  qabbrev_tac `u = (mcopy (w2n b) (w2n a) (n*stride) s1) with
    vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `tf = step_taint (mk_inst (id+1) MCOPY
    [Var dst; Var src; Var cnt] []) s1
    (mcopy (w2n b) (w2n a) (n*stride) s1) t1` >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g1 tf (OK u)` by
    (simp[Abbr `u`, Abbr `tf`] >>
     irule annassign_mcopy_path_ptr >>
     simp[Abbr `s1`, Abbr `g1`, Abbr `t1`, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, eval_operand_def, op_taint_def,
       ptr_covers_def, FLOOKUP_DRESTRICT, LESS_MOD] >>
     gvs[ptr_covers_def, lookup_var_def, op_taint_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tf (OK u)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `tf.t_var = t1.t_var /\ tf.t_stor = t1.t_stor /\
   tf.t_trans = t1.t_trans /\ tf.t_imm = t1.t_imm /\
   (!i. i < n*stride ==> (w2n b+i IN tf.t_mem <=> w2n a+i IN t1.t_mem)) /\
   (!i. ~(w2n b <= i /\ i < w2n b+n*stride) ==>
     (i IN tf.t_mem <=> i IN t1.t_mem))` by
    (irule mcopy_operand_taint_frames_ptr >>
     qexistsl_tac [`Var cnt`, `Var dst`, `id+1`,
       `n2w (n*stride)`, `s1`, `Var src`] >>
     simp[Abbr `tf`, Abbr `s1`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, LESS_MOD] >>
     gvs[lookup_var_def]) >>
  `!p. p <> cnt ==> lookup_var p u = lookup_var p s /\
    FLOOKUP g1 p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >>
     simp[Abbr `u`, Abbr `s1`, Abbr `g1`, lookup_var_def,
       mcopy_def, write_memory_with_expansion_def,
       update_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       op_taint_def, Abbr `t1`]) >>
  qexistsl_tac [`g1`, `tf`, `u`] >>
  simp[Abbr `t1`] >>
  `u.vs_memory = (mcopy (w2n b) (w2n a) (n*stride) s).vs_memory` by
    simp[Abbr `u`, Abbr `s1`, mcopy_def, write_memory_with_expansion_def,
      update_var_def] >>
  simp[valueEncodingProofsTheory.mcopy_mem_bytes_at_same] >>
  `!i. ~(w2n b <= i) \/ ~(i < w2n b+n*stride) ==>
     mem_bytes_at i 1 (mcopy (w2n b) (w2n a) (n*stride) s).vs_memory =
     mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >>
     irule valueEncodingProofsTheory.mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[] >>
  gvs[Abbr `u`, Abbr `s1`, mcopy_def, write_memory_with_expansion_def,
    update_var_def] >> gvs[]
QED

Theorem typed_copy_dynamic_array_fast:
  !ce de se dc sc tenv dtv stv v dst src sa sb ctx fn D PG G tn s a b.
    de = se /\ type_memory_bytes ce de = type_memory_bytes ce se /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    type_widens_to tenv (ArrayT se (Dynamic sc)) (ArrayT de (Dynamic dc)) /\
    evaluate_type tenv (ArrayT se (Dynamic sc)) = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic dc)) = SOME dtv /\
    type_memory_bytes ce (ArrayT se (Dynamic sc)) = type_memory_size stv /\
    type_memory_bytes ce (ArrayT de (Dynamic dc)) = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    compile_store_memory_typed ce (Var dst) (ArrayT de (Dynamic dc))
      (Var src) (ArrayT se (Dynamic sc)) sa = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (type_memory_bytes ce (ArrayT se (Dynamic sc))) /\
    ptr_covers G tn dst s (type_memory_bytes ce (ArrayT de (Dynamic dc))) /\
    w2n a + type_memory_bytes ce (ArrayT se (Dynamic sc)) < dimword(:256) /\
    w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc)) < dimword(:256) /\
    (type_memory_bytes ce (ArrayT se (Dynamic sc)) <> 0 /\
     type_memory_bytes ce (ArrayT de (Dynamic dc)) <> 0 ==>
      w2n a + type_memory_bytes ce (ArrayT se (Dynamic sc)) <= w2n b \/
      w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc)) <= w2n a) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sb /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b) (type_memory_bytes ce (ArrayT de (Dynamic dc))) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc))) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_assum `evaluate_type _ (ArrayT se (Dynamic sc)) = _`
    (mp_then Any strip_assume_tac evaluate_type_ArrayT_cases) >>
  qpat_assum `evaluate_type _ (ArrayT se (Dynamic dc)) = _`
    (mp_then Any strip_assume_tac evaluate_type_ArrayT_cases) >>
  gvs[] >> rename1 `evaluate_type tenv se = SOME tv` >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `dc < dimword(:256) /\ sc < dimword(:256)` by
    metis_tac[evaluate_type_dynarray_count_bound] >>
  `LENGTH vs <= dc /\ LENGTH vs <= sc` by
    gvs[vyperTypingTheory.value_has_type_def] >>
  `compile_copy_dynarray_typed ce (Var dst) se dc (Var src) se sa = ((),sb)` by
    metis_tac[compile_typed_dynarray_dispatch] >>
  `cs_extends sa sb` by metis_tac[typed_memory_family_labels, pairTheory.SND] >>
  simp[] >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
    metis_tac[pop_robust_dynarray_header_clean] >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (qpat_assum `!m. mem_agree_outside tn.t_mem _ _ ==> _`
      (qspec_then `s.vs_memory` mp_tac) >>
     simp_tac std_ss [mem_agree_outside_def] >>
     disch_then (mp_then Any mp_tac placeDynLayoutTheory.place_dyn_memory_header) >>
     rewrite_tac[mem_word_at_eq_mload]) >>
  drule_all compile_copy_dynarray_code >> strip_tac >>
  `fn_has_code sa (dyn_copy_prefix_state sa (Var dst) (Var src) dc) fn` by
    (gvs[fn_has_code_def, typedDynLoopCodeTheory.dyn_copy_prefix_state_fields,
       emitted_blocks_def, same_blocks_def, IS_PREFIX_APPEND,
       dyn_copy_insts_def, dyn_copy_prefix_insts_def,
       compiler_var_names_six, bytesCopyCodeTheory.compiler_var_names_five] >>
     metis_tac[listTheory.APPEND_ASSOC]) >>
  `ptr_covers G tn src s (32+sc*type_memory_size tv) /\
   ptr_covers G tn dst s (32+dc*type_memory_size tv) /\
   w2n a+32+sc*type_memory_size tv < dimword(:256) /\
   w2n b+32+dc*type_memory_size tv < dimword(:256)` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  assume_tac typed_copy_dynamic_preamble_counted >>
  drule_all typed_copy_dynamic_entry_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `!s ctx fn bb prefix suffix id src dst len too ok sp dp a b S T n cap G tn PG D. _` kall_tac >>
  `type_memory_bytes ce se = type_memory_size tv` by
    (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==> _` drule >>
     simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME
      (mk_inst (sa.cs_next_id+7) MUL
        [Var (EL 0 (compiler_var_names sa.cs_next_var 5));
         Lit (n2w (type_memory_size tv))]
        [EL 5 (compiler_var_names sa.cs_next_var 6)]) /\
    get_instruction bb (SUC u.vs_inst_idx) = SOME
      (mk_inst (sa.cs_next_id+8) MCOPY
        [Var (EL 4 (compiler_var_names sa.cs_next_var 5));
         Var (EL 3 (compiler_var_names sa.cs_next_var 5));
         Var (EL 5 (compiler_var_names sa.cs_next_var 6))] [])` by
    (qpat_assum `fn_has_code sa sb fn`
       (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
     gvs[typedDynLoopCodeTheory.dyn_copy_prefix_state_fields,
       IS_PREFIX_APPEND, dyn_copy_insts_def, compiler_var_names_six,
       bytesCopyCodeTheory.compiler_var_names_five,
       dyn_copy_prefix_insts_def] >>
     qexists_tac `bb` >>
     gvs[same_blocks_def, get_instruction_def, listTheory.EL_APPEND_EQN, ADD1]) >>
  pop_assum strip_assume_tac >>
  `LENGTH vs * type_memory_size tv <= sc * type_memory_size tv /\
   LENGTH vs * type_memory_size tv <= dc * type_memory_size tv` by
    simp[] >>
  `LENGTH vs * type_memory_size tv < dimword(:256)` by decide_tac >>
  `ptr_covers H tf (EL 3 (compiler_var_names sa.cs_next_var 5)) u
      (LENGTH vs * type_memory_size tv) /\
   ptr_covers H tf (EL 4 (compiler_var_names sa.cs_next_var 5)) u
      (LENGTH vs * type_memory_size tv)` by
    (gvs[ptr_covers_def] >>
     `LENGTH vs * type_memory_size tv <= sc * type_memory_size tv /\
      LENGTH vs * type_memory_size tv <= dc * type_memory_size tv` by simp[] >>
     decide_tac) >>
  `EL 5 (compiler_var_names sa.cs_next_var 6) <>
      EL 3 (compiler_var_names sa.cs_next_var 5) /\
   EL 5 (compiler_var_names sa.cs_next_var 6) <>
      EL 4 (compiler_var_names sa.cs_next_var 5) /\
   EL 5 (compiler_var_names sa.cs_next_var 6) <>
      EL 0 (compiler_var_names sa.cs_next_var 5)` by
    simp[compiler_var_names_six, bytesCopyCodeTheory.compiler_var_names_five] >>
  `get_instruction bb (SUC u.vs_inst_idx) = SOME
      (mk_inst ((sa.cs_next_id+7)+1) MCOPY
        [Var (EL 4 (compiler_var_names sa.cs_next_var 5));
         Var (EL 3 (compiler_var_names sa.cs_next_var 5));
         Var (EL 5 (compiler_var_names sa.cs_next_var 6))] [])` by simp[] >>
  drule_all typed_copy_dynamic_payload_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' tf' (OK u')` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `!p. not_fresh_at sa p ==> p <> EL 5 (compiler_var_names sa.cs_next_var 6)` by
    (simp[compiler_var_names_six, not_fresh_at_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `!p. not_fresh_at sa p ==>
     lookup_var p u' = lookup_var p s /\ FLOOKUP H' p = FLOOKUP G p /\
     op_taint tf' (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  `w2n (a+32w) = w2n a+32 /\ w2n (b+32w) = w2n b+32` by
    (conj_tac >> simp[wordsTheory.w2n_add_2]) >>
  `!i. ~(w2n b <= i /\ i < w2n b+32+dc*type_memory_size tv) ==>
    (i IN tf'.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     qpat_x_assum `!i. ~(_ <= i /\ i < _) ==> _ /\ _`
       (qspec_then `i` mp_tac) >>
     impl_tac >- decide_tac >>
     simp[] >> strip_tac >>
     gvs[] >> decide_tac) >>
  `typed_copy_frame (w2n b) 32 s.vs_memory u.vs_memory` by
    (simp[typed_copy_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
     simp[mstore_def, write_memory_with_expansion_def, LET_THM,
       listTheory.LENGTH_TAKE, listTheory.LENGTH_DROP] >>
     Cases_on `w2n b + 32 > LENGTH s.vs_memory` >>
     simp[listTheory.LENGTH_TAKE] >> decide_tac) >>
  `typed_copy_frame (w2n b+32) (LENGTH vs*type_memory_size tv)
    u.vs_memory u'.vs_memory` by
    (simp[typed_copy_frame_def] >> conj_tac
     >- (rpt strip_tac >> simp[mcopy_mem_bytes_at_disjoint]) >>
     metis_tac[placeMemoryTypedPrimitiveTheory.mcopy_memory_length]) >>
  `typed_copy_frame (w2n b) (32+dc*type_memory_size tv) s.vs_memory u'.vs_memory` by
    (irule typed_copy_frame_trans >> qexists_tac `u.vs_memory` >> conj_tac >>
     irule typed_copy_frame_subinterval >> goal_assum (drule_at Any) >> simp[]) >>
  `u' with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_inst_idx := s.vs_inst_idx|> = s` by
    (qpat_x_assum `u' with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory; vs_inst_idx := u.vs_inst_idx|> = u`
      (mp_tac o Q.AP_TERM `(\z. z with <|vs_vars := s.vs_vars;
        vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>)`) >> simp[]) >>
  `typed_copy_state_frame sa (w2n b) (32+dc*type_memory_size tv) s u'` by
    (simp[typed_copy_state_frame_def] >>
     qpat_assum `u' with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|> = s`
       (mp_tac o Q.AP_TERM `(\z. z with <|vs_prev_bb := s.vs_prev_bb;
         vs_current_bb := s.vs_current_bb|>)`) >> simp[]) >>
  `w2n a + (32+sc*type_memory_size tv) <= w2n b \/
    w2n b + (32+dc*type_memory_size tv) <= w2n a` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic sc)) (ArrayV (DynArrayV vs)) (w2n a) m` by
    (rpt strip_tac >> irule robust_representation_exterior_frame >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`w2n b`, `s.vs_memory`, `u.vs_memory`, `32`, `tn.t_mem`, `tf.t_mem`] >>
     simp[valueEncodingTheory.type_memory_size_def] >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `mem_bytes_at (w2n b) 32 u'.vs_memory =
    mem_bytes_at (w2n a) 32 u.vs_memory` by
    (qpat_assum `!m. mem_agree_outside tf.t_mem _ _ ==> _`
       (strip_assume_tac o REWRITE_RULE [robust_dynarray_indexed]) >>
     `mem_word_at (w2n a) u.vs_memory = n2w (LENGTH vs)` by
       (first_x_assum (qspec_then `u.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
     `mem_bytes_at (w2n b) 32 u'.vs_memory = mem_bytes_at (w2n b) 32 u.vs_memory` by
       (qpat_x_assum `typed_copy_frame (w2n b+32) _ _ _` mp_tac >>
        simp[typed_copy_frame_def]) >>
     `mem_word_at (w2n b) u.vs_memory = n2w (LENGTH vs)` by
       (qpat_assum `u.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
        rewrite_tac[mem_word_at_eq_mload, venomMemProofsTheory.mload_mstore_same_proof]) >>
     metis_tac[valueEncodingProofsTheory.mem_bytes_at_word]) >>
  `mem_bytes_at (w2n b) (32+LENGTH vs*type_memory_size tv) u'.vs_memory =
    mem_bytes_at (w2n a) (32+LENGTH vs*type_memory_size tv) u.vs_memory` by
    (pure_rewrite_tac[valueEncodingProofsTheory.mem_bytes_at_split_padded] >>
     metis_tac[]) >>
  `!i. i < 32+LENGTH vs*type_memory_size tv ==>
    (w2n b+i IN tf'.t_mem <=> w2n a+i IN tf.t_mem)` by
    (rpt strip_tac >> Cases_on `i < 32`
     >- (qpat_assum `!i. ~(_ <= i /\ i < _) ==> _ /\ _`
           (qspec_then `w2n b+i` mp_tac) >>
         impl_tac >- decide_tac >>
         gvs[] >> simp[] >> decide_tac) >>
     qpat_assum `!i. i < LENGTH vs * type_memory_size tv ==> _`
       (qspec_then `i-32` mp_tac) >>
     impl_tac >- decide_tac >> simp[] >>
     `w2n b+32+(i-32) = w2n b+i /\ w2n a+32+(i-32) = w2n a+i` by decide_tac >>
     simp[]) >>
  `val_wf (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs))` by
    gvs[valueEncodingDefsTheory.val_wf_def] >>
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs)) (w2n a) m` by
    (rewrite_tac[robust_dynarray_indexed] >>
     qpat_assum `!m. mem_agree_outside tf.t_mem u.vs_memory m ==> _`
       (mp_tac o REWRITE_RULE [robust_dynarray_indexed]) >> simp[]) >>
  `!m. mem_agree_outside tf'.t_mem u'.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs)) (w2n b) m` by
    (rpt strip_tac >> irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`u.vs_memory`, `u'.vs_memory`, `32+LENGTH vs*type_memory_size tv`, `w2n a`, `tf.t_mem`, `tf'.t_mem`] >>
     simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def]) >>
  `!m. mem_agree_outside tf'.t_mem u'.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic dc)) (ArrayV (DynArrayV vs)) (w2n b) m` by
    (rewrite_tac[robust_dynarray_indexed] >>
     qpat_assum `!m. mem_agree_outside tf'.t_mem u'.vs_memory m ==> _`
       (mp_tac o REWRITE_RULE [robust_dynarray_indexed]) >> simp[]) >>
  qexistsl_tac [`H'`, `tf'`, `u'`] >>
  simp[valueEncodingTheory.type_memory_size_def] >>
  qpat_x_assum `same_blocks sa sb` mp_tac >>
  simp[same_blocks_def, dyn_copy_prefix_insts_def, dyn_copy_insts_def,
    arithmeticTheory.ADD_COMM] >>
  qpat_assum `typed_copy_state_frame sa _ _ s u'`
    (mp_tac o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]) >> simp[]
QED
