Theory abiEncTuplePtrRawSlot
Ancestors
  abiTupleEncodeSlot abiDecodePtrBytesTail bodyPtrAttributeAdd
  rawCallHeaderFramePtr assignBasePtrMcopyGhost assignBasePtrCopyPath
  exprLowering venomMemProofs abiDecoderContract context valueEncodingProps
  augAssignPtrStore wordLoadStorePtr abiTupleProps fragExec
  localPtrsProps exprSimCopy logGhostFramePtr fragGasPathPtr
  bodyPtrEnvBuiltinsSelectorBuffer bodyPtrStructLitFieldStore
  ghostPcTransportPtr ptrCoverage bodyPtrDefs compileEnv emitHelper emitHelperProps
  loweringStateRelDefs venomState venomInst venomExecSemantics
  typedCopyPtr ptrDiscipline finite_map words arithmetic ASCIInumbers

Theorem abi_tuple_slot_address_resources_ptr:
  emit_op ADD [Var bx;Lit (n2w off)] st = (dst,ready) /\
  fn_has_code st ready func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var bx s = SOME (n2w b) /\ ptr_covers G tn bx s N /\
  off+n <= N /\ b+N < dimword(:256) /\
  local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  ghost_inv rb cenv cx es G tn s ==>
  ?out H tf t.
    dst = Var out /\ gas_path_ptr D 0 ctx func PG G tn s 0 H tf (OK t) /\
    t = (update_var out (n2w (b+off)) s with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    H = step_prov PG G (mk_inst st.cs_next_id ADD [Var bx;Lit (n2w off)] [out])
      (update_var out (n2w (b+off)) s) /\
    tf = step_taint (mk_inst st.cs_next_id ADD [Var bx;Lit (n2w off)] [out]) s
      (update_var out (n2w (b+off)) s) tn /\
    lookup_var out t = SOME (n2w (b+off)) /\ ptr_covers H tf out t n /\
    ghost_inv rb cenv cx es H tf t /\ ghost_kept cenv es st G tn s H tf /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x) /\
      (!sz. ptr_covers G tn x s sz ==> ptr_covers H tf x t sz))
Proof
  strip_tac >>
  `b < dimword(:256)` by decide_tac >>
  `op_taint tn (Var bx) = {}` by gvs[ptr_covers_def] >>
  `eval_operand (Var bx) s = SOME (n2w b)` by simp[eval_operand_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (attribute_emit_binop_path_ptr |> SPEC_ALL
    |> Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[word_add_n2w] >>
  `ready.cs_current_bb = st.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  gvs[listTheory.LENGTH_APPEND, GSYM ADD1] >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
      irule (abi_decode_ptr_output_address_covers
        |> Q.INST [`b` |-> `basew`]
        |> Q.INST [`basew` |-> `n2w b:bytes32`]
        |> SRULE [ghostPcTransportPtrTheory.ptr_covers_inst_idx, word_add_n2w]) >>
      simp[] >> qexists_tac `N` >> simp[w2n_n2w]) >>
  conj_tac
  >- (simp[ghost_inv_inst_idx] >>
      irule (cj 1 raw_call_emit_add_ghost_frame
        |> Q.INST [`a` |-> `aw`, `b` |-> `bw`]
        |> Q.INST [`aw` |-> `n2w b:bytes32`, `bw` |-> `n2w off:bytes32`]
        |> SRULE [ghost_inv_inst_idx, word_add_n2w]) >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule (cj 2 raw_call_emit_add_ghost_frame
        |> Q.INST [`a` |-> `aw`, `b` |-> `bw`]
        |> Q.INST [`aw` |-> `n2w b:bytes32`, `bw` |-> `n2w off:bytes32`]
        |> SRULE [word_add_n2w]) >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  `x <> STRING #"%" (toString st.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[] >> rpt strip_tac >>
  irule (attribute_ptr_covers_update
    |> SRULE [ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >> simp[] >> metis_tac[]
QED

(* Physical MCOPY boundary; no logical-value or clean-padding premise. *)
Theorem abi_tuple_slot_copy_resources_ptr:
  0 < n /\ n < dimword(:256) /\
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  ptr_covers G tn dst s n /\ ptr_covers G tn src s n /\
  local_ptrs_rel func cenv es.scopes s /\ ghost_inv rb cenv cx es G tn s /\
  (!name base sz. local_region cenv es.scopes s name base sz ==>
    regions_disjoint (w2n b) n base sz) /\
  (!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) /\
    aid < fr.cs_next_id /\
    (!name p k. local_region cenv es.scopes s name p k ==>
      base+sz <= p \/ p+k <= base) ==>
    regions_disjoint (w2n b) n base sz) ==>
  ?tf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tf (OK t) /\
    t = (mcopy (w2n b) (w2n a) n s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_inv rb cenv cx es G tf t /\ ghost_kept cenv es fr G tn s G tf /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. lookup_var x t = lookup_var x s) /\
    (!x k. ptr_covers G tf x t k <=> ptr_covers G tn x s k) /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = (tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+n}) UNION
      {w2n b+j | j < n /\ w2n a+j IN tn.t_mem} /\
    mem_bytes_at (w2n b) n t.vs_memory = mem_bytes_at (w2n a) n s.vs_memory /\
    abi_decode_frame (w2n b) n s t
Proof
  strip_tac >>
  drule_all assign_base_copy_memory_path_ptr >>
  disch_then (qspecl_then [`D`,`PG`] assume_tac) >>
  drule_all assign_base_mcopy_nat_ghost_inv >>
  disch_then (qspecl_then [`PG`,`sa.cs_next_id`] assume_tac) >>
  drule_all assign_base_mcopy_nat_ghost_kept >>
  disch_then (qspecl_then [`PG`,`G`,`tn`,`sa.cs_next_id`] assume_tac) >>
  `eval_operand (Var dst) s = SOME b /\
   eval_operand (Var src) s = SOME a /\
   eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  mp_tac (mcopy_operand_ghost_frame |> SPEC_ALL
    |> Q.INST [`dst` |-> `dst_op`, `src` |-> `src_op`, `n` |-> `nw`]
    |> Q.INST [`dst_op` |-> `Var dst`, `src_op` |-> `Var src`,
      `count_op` |-> `Lit (n2w n)`, `nw` |-> `n2w n:bytes32`,
      `id` |-> `sa.cs_next_id`]) >>
  simp[eval_operand_def, w2n_n2w] >> strip_tac >>
  gvs[w2n_n2w] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 G tf (OK t)` >>
  qexists_tac `tf` >> simp[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (Cases_on `n` >> gvs[compile_copy_memory_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, fresh_id_def, emit_def, comp_return_def]) >>
  `abi_decode_frame (w2n b) n s t` by
    (simp[Abbr `t`, abi_decode_frame_def] >>
     metis_tac[mcopy_mem_bytes_at_disjoint, ADD_COMM]) >>
  `mem_bytes_at (w2n b) n (mcopy (w2n b) (w2n a) n s).vs_memory =
   mem_bytes_at (w2n a) n s.vs_memory` by simp[mcopy_mem_bytes_at_same] >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def,
    lookup_var_def, ptr_covers_def, op_taint_def] >>
  simp[Abbr `tf`, step_taint_def, mk_inst_def, imm_taint_def]
QED

Theorem abi_tuple_slot_word_resources_ptr:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var dst s = SOME b /\ eval_operand value s = SOME w /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  local_ptrs_rel func cenv es.scopes s /\ ghost_inv rb cenv cx es G tn s /\
  (!name base sz. local_region cenv es.scopes s name base sz ==>
    base+sz <= w2n b \/ w2n b+32 <= base) /\
  ghost_kept cenv es fr G0 tn0 s0 G tn ==>
  ?tf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tf (OK t) /\
    t = (mstore (w2n b) w s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_inv rb cenv cx es G tf t /\ ghost_kept cenv es fr G0 tn0 s0 G tf /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. lookup_var x t = lookup_var x s) /\
    (!x k. ptr_covers G tf x t k <=> ptr_covers G tn x s k) /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+32} /\
    abi_decode_frame (w2n b) 32 s t
Proof
  strip_tac >> drule_all emit_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >> gvs[] >>
  drule_all mstore_step_ghost_inv >>
  disch_then (qspecl_then [`PG`,`sa.cs_next_id`] assume_tac) >>
  drule_all mstore_ghost_kept >>
  disch_then (qspecl_then [`PG`,`sa.cs_next_id`] assume_tac) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`sa.cs_next_id`] strip_assume_tac) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 G tf (OK t)` >>
  qexists_tac `tf` >> simp[] >>
  `abi_decode_frame (w2n b) 32 s t` by
    (simp[Abbr `t`, abi_decode_frame_def] >>
     metis_tac[mstore_mem_bytes_at_disjoint, ADD_COMM]) >>
  simp[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def] >>
  simp[Abbr `tf`, step_taint_def, mk_inst_def, imm_taint_def]
QED

Theorem compile_abi_tuple_slot_resources_ptr:
  compile_abi_tuple_slot ce (Var bx) off op ty st = ((),final) /\
  n = type_memory_bytes ce ty /\ (is_word_type ty ==> n = 32) /\
  fn_has_code st final func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_var bx s = SOME (n2w b) /\ ptr_covers G tn bx s N /\
  not_fresh_at st bx /\ off+n <= N /\ b+N < dimword(:256) /\
  eval_operand op s = SOME v /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  (is_word_type ty ==> op_taint tn op = {}) /\
  (~is_word_type ty /\ 0 < n ==> ?x. op = Var x /\ ptr_covers G tn x s n) /\
  local_ptrs_reserved cenv st /\ local_ptrs_rel func cenv es.scopes s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  ghost_inv rb cenv cx es G tn s /\
  fr.cs_next_id <= st.cs_next_id /\
  (!x. not_fresh_at fr x ==> not_fresh_at st x) /\
  (!name base sz. local_region cenv es.scopes s name base sz ==>
    regions_disjoint (b+off) n base sz) /\
  (!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base,sz) /\
    aid < fr.cs_next_id /\
    (!name p k. local_region cenv es.scopes s name p k ==>
      base+sz <= p \/ p+k <= base) ==>
    regions_disjoint (b+off) n base sz) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t) /\
    ghost_inv rb cenv cx es H tm t /\ ghost_kept cenv es fr G tn s H tm /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers H tm bx t N /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x) /\
      (!k. ptr_covers G tn x s k ==> ptr_covers H tm x t k)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    t.vs_memory = (if is_word_type ty then mstore (b+off) v s
      else if n = 0 then s else mcopy (b+off) (w2n v) n s).vs_memory /\
    tm.t_mem = (if is_word_type ty then tn.t_mem DIFF {j | b+off <= j /\ j < b+off+n}
      else (tn.t_mem DIFF {j | b+off <= j /\ j < b+off+n}) UNION
        {b+off+j | j < n /\ w2n v+j IN tn.t_mem}) /\
    abi_decode_frame (b+off) n s t
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_abi_tuple_slot_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `emit_op ADD _ st = (dst,sa)` >>
  gvs[] >>
  `cs_extends st sa /\ cs_extends sa final` by
    (Cases_on `is_word_type ty` >>
     Cases_on `type_memory_bytes ce ty` >>
     gvs[emit_op_def, emit_void_def, compile_copy_memory_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def, cs_extends_def] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code st sa func /\ fn_has_code sa final func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  mp_tac (abi_tuple_slot_address_resources_ptr |> SPEC_ALL
    |> Q.INST [`ready` |-> `sa`, `n` |-> `type_memory_bytes ce ty`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `ghost_inv rb cenv cx es H tf u` >>
  qpat_x_assum `H = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tf = step_taint _ _ _ _` kall_tac >>
  `u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_data_section = s.vs_data_section` by simp[update_var_def] >>
  qpat_x_assum `u = _` kall_tac >>
  `(!name base sz. local_region cenv es.scopes u name base sz <=>
      local_region cenv es.scopes s name base sz)` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `st` >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes u` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand op u = SOME v /\ op_taint tf op = op_taint tn op` by
    (Cases_on `op` >> gvs[eval_operand_def, op_taint_def]) >>
  `ghost_kept cenv es fr G tn s H tf` by
    (gvs[ghost_kept_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  Cases_on `is_word_type ty`
  >- suspend "word"
  >> Cases_on `type_memory_bytes ce ty = 0`
  >- suspend "zero"
  >> suspend "copy"
QED

Resume compile_abi_tuple_slot_resources_ptr[word]:
  gvs[] >>
  `b+off < dimword(:256)` by decide_tac >>
  `!name base sz. local_region cenv es.scopes u name base sz ==>
     base+sz <= w2n (n2w (b+off):bytes32) \/
     w2n (n2w (b+off):bytes32)+32 <= base` by
    (simp[w2n_n2w] >> rpt strip_tac >>
     qpat_x_assum `!name base sz. local_region cenv es.scopes s name base sz ==> regions_disjoint _ _ base sz` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  drule_all abi_tuple_slot_word_resources_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`tf'`,`t`] >>
  simp[w2n_n2w] >>
  conj_tac >- (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >> goal_assum (drule_at Any) >>
    gvs[w2n_n2w]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!x. not_fresh_at st x ==> _` drule >>
    simp[op_taint_def]) >>
  conj_tac >- simp[mstore_def, write_memory_with_expansion_def] >>
  gvs[w2n_n2w, abi_decode_frame_def] >> metis_tac[]
QED
Resume compile_abi_tuple_slot_resources_ptr[zero]:
  gvs[compile_copy_memory_def, comp_return_def] >>
  qexistsl_tac [`H`,`tf`,`u`] >>
  simp[mcopy_def, abi_decode_frame_def] >>
  metis_tac[]
QED
Resume compile_abi_tuple_slot_resources_ptr[copy]:
  gvs[] >>
  `0 < type_memory_bytes ce ty /\ type_memory_bytes ce ty < dimword(:256) /\
   b+off < dimword(:256)` by decide_tac >>
  `ptr_covers H tf x u (type_memory_bytes ce ty)` by metis_tac[] >>
  `!name base sz. local_region cenv es.scopes u name base sz ==>
     regions_disjoint (w2n (n2w (b+off):bytes32)) (type_memory_bytes ce ty) base sz` by
    (simp[w2n_n2w] >> metis_tac[]) >>
  `!aid base sz. FLOOKUP u.vs_allocas aid = SOME (base,sz) /\
    aid < fr.cs_next_id /\
    (!name p k. local_region cenv es.scopes u name p k ==>
      base+sz <= p \/ p+k <= base) ==>
    regions_disjoint (w2n (n2w (b+off):bytes32)) (type_memory_bytes ce ty) base sz` by
    (simp[w2n_n2w] >> metis_tac[]) >>
  mp_tac (abi_tuple_slot_copy_resources_ptr |> SPEC_ALL
    |> Q.INST [`b` |-> `bw`]
    |> Q.INST [`s` |-> `u`, `sb` |-> `final`, `n` |-> `type_memory_bytes ce ty`,
      `bw` |-> `n2w (b+off):bytes32`, `a` |-> `v`,
      `G` |-> `H`, `tn` |-> `tf`, `dst` |-> `out`, `src` |-> `x`]) >>
  (impl_tac >- (gvs[eval_operand_def] >> metis_tac[])) >>
  strip_tac >>
  qexistsl_tac [`H`,`tf'`,`t`] >>
  simp[w2n_n2w] >>
  conj_tac >- (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
    goal_assum (drule_at Any) >> gvs[w2n_n2w]) >>
  conj_tac >- (irule wordArgsPtrTheory.ghost_kept_trans >>
    goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!x. not_fresh_at st x ==> _` drule >> simp[op_taint_def]) >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  gvs[w2n_n2w, abi_decode_frame_def] >> metis_tac[]
QED
Finalise compile_abi_tuple_slot_resources_ptr
