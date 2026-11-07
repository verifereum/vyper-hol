(* Runtime code unwrap: allocation, checked copy, and semantic resources. *)
Theory reasonCodeNormalizationPtr
Ancestors
  normalizationAllocationPathPtr
  reasonCodeResourcesPtr reasonCodeCopyPtr exprSimCopy
  storageNormalizationOwnershipPtr reasonPrefixPtr reasonAllocationFramePtr
  venomInst allocationPtr exprSimAlloc exprLoweringProps context compileEnv
  emitHelper emitHelperProps loweringPosts bodyPtrDefs venomState
  exprLowering loweringHalt immutableCopyExecution immutableMemoryFrame
  valueEncodingProps list
  ptrDiscipline words arithmetic fragExec fragGasPathPtr

Theorem code_unwrap_compile_parts:
  ~is_word_type ann /\ p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  type_memory_bytes cenv ann = 32*n /\
  (type_memory_bytes cenv ann+31) DIV 32 = n /\
  unwrap_value cenv (LocatedValue ann p) cc = (op,cb) ==>
  ?buf ca root.
    compile_alloc_buffer (32*n) cc = (buf,ca) /\
    buf.buf_operand = Var root /\ op = Var root /\
    compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand
      (Var root) n 0 ca = ((),cb)
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = (op,cb)` mp_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Exact copy memory yields the two semantic-frame premises without replaying
   DLOAD/MSTORE instructions.  The zero-word copy is included. *)
Theorem code_copy_memory_frame:
  w2n a + 32*n < dimword(:256) /\
  w2n b + 32*n < dimword(:256) /\
  t.vs_memory = (immutable_transfers F F a b n 0 s).vs_memory ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!off len. off + len <= w2n b \/ w2n b + 32*n <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> Cases_on `n = 0`
  >- gvs[immutable_transfers_def] >>
  `immutable_transfers F F a b n 0 s =
   write_memory_with_expansion (w2n b)
     (TAKE (32*n) (DROP (w2n a) s.vs_data_section ++ REPLICATE (32*n) 0w)) s` by
    (mp_tac immutableCopyExecutionTheory.immutable_runtime_transfers_snapshot >>
     disch_then (qspecl_then [`n`, `w2n a`, `w2n b`, `0`, `s`] mp_tac) >>
     simp[]) >>
  gvs[] >> conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
  rpt strip_tac >> irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  simp[listTheory.LENGTH_TAKE_EQ]
QED

Theorem code_copy_state_rel_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  w2n a + 32*n < dimword(:256) /\ w2n b + 32*n < dimword(:256) /\
  t.vs_memory = (immutable_transfers F F a b n 0 s).vs_memory /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,32*n) /\
  (!name lb len. local_region cenv es.scopes s name lb len ==>
     regions_disjoint (w2n b) (32*n) lb len) ==>
  stmt_state_rel ctx func cenv cx es t /\
  (!aid off len. aid <> inst.inst_id /\
    FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> drule_all code_copy_memory_frame >> strip_tac >>
  `copy_static t = copy_static s` by
    gvs[exprSimStorageCopyTheory.copy_static_def, venom_state_component_equality] >>
  drule_at (Pat `FLOOKUP _ _ = SOME _`)
    normalization_copy_ownership_frame >>
  disch_then (drule_all_then strip_assume_tac) >> metis_tac[]
QED

Theorem code_reason_copy_resources_ptr:
  compile_imm_copy_to_memory F imm src (Var root) n 0 ca = ((),cb) /\
  fn_has_code ca cb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\ ~s.vs_halted /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var root s = SOME b /\ ptr_covers G tn root s (32*n) /\
  (!p. src = Var p ==> not_fresh_at ca p) /\ not_fresh_at ca root /\
  w2n b + 32*n < dimword(:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv ca /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,32*n) /\
  (!name lb len. local_region cenv es.scopes s name lb len ==>
     regions_disjoint (w2n b) (32*n) lb len) /\
  ~cenv.ce_is_ctor /\ immutable_holds cenv cx ty tv a es u /\
  read_result cx tv es = (INL (StringV str),es) /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  type_slot_size (BaseTV (StringT max)) = n /\
  type_memory_size (BaseTV (StringT max)) = 32*n ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = cb.cs_current_bb /\
    t.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx es t /\
    lookup_var root t = SOME b /\ ptr_covers Gf tnf root t (32*n) /\
    ptr_mem_ok cx ty (StringV str) (Var root) Gf tnf t /\
    32 + 32 * word_size (LENGTH str) <= 32*n /\
    t.vs_allocas = s.vs_allocas /\
    (!aid off len. aid <> inst.inst_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!p k. not_fresh_at ca p /\ ptr_covers G tn p s k ==>
      ptr_covers Gf tnf p t k) /\
    (!p. not_fresh_at ca p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all immutable_source_resources >> strip_tac >>
  `32*n <= 32*n /\ 32*n + w2n b < dimword(:256) /\
   32*n + w2n a < dimword(:256)` by gvs[] >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    code_copy_path_ptr >> simp[] >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var root sf = SOME b /\ ptr_covers Gf tnf root sf (32*n)` by
    metis_tac[] >>
  `stmt_state_rel ctx func cenv cx es sf /\
   (!aid off len. aid <> inst.inst_id /\
     FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
     mem_bytes_at off len sf.vs_memory = mem_bytes_at off len s.vs_memory)` by
    (irule code_copy_state_rel_frame >> goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- (qexists_tac `a` >> asm_rewrite_tac[]) >>
     qexists_tac `ca` >> asm_rewrite_tac[] >> metis_tac[]) >>
  `ptr_mem_ok cx ty (StringV str) (Var root) Gf tnf sf /\
   32 + 32 * word_size (LENGTH str) <= 32*n` by
    (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)
       code_reason_normalization_resources >>
     disch_then (drule_at_then (Pat `lookup_var _ _ = SOME _`) mp_tac) >>
     simp[] >> disch_then irule >>
     goal_assum (drule_at Any) >> simp[pred_setTheory.IN_DIFF] >>
     (qexistsl_tac [`ctx`, `func`, `s`, `s`] >> simp[])) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >> decide_tac
QED

Theorem code_reason_alloc_copy_path_ptr:
  compile_alloc_buffer (32*n) cc = (buf,ca) /\
  buf.buf_operand = Var root /\
  compile_imm_copy_to_memory F imm src (Var root) n 0 ca = ((),cb) /\
  fn_has_code cc ca func /\ fn_has_code ca cb func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv cc /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  32*n < dimword(:256) /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ (!p. src = Var p ==> not_fresh_at cc p) /\
  ~cenv.ce_is_ctor /\ immutable_holds cenv cx ty tv a es s /\
  read_result cx tv es = (INL (StringV str),es) /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  type_slot_size (BaseTV (StringT max)) = n /\
  type_memory_size (BaseTV (StringT max)) = 32*n ==>
  ?Gf tnf t b.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = cb.cs_current_bb /\
    t.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx es t /\
    lookup_var root t = SOME (n2w b) /\ ptr_covers Gf tnf root t (32*n) /\
    ptr_mem_ok cx ty (StringV str) (Var root) Gf tnf t /\
    32 + 32*word_size (LENGTH str) <= 32*n /\ b+32*n < dimword(:256) /\
    FLOOKUP t.vs_allocas cc.cs_next_id = SOME (b,32*n) /\
    (!aid off len. aid < cc.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!p k. not_fresh_at cc p /\ ptr_covers G tn p s k ==>
      ptr_covers Gf tnf p t k) /\
    (!p. not_fresh_at cc p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all normalization_alloc_buffer_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `root' = root` by metis_tac[operand_11] >> gvs[] >>
  `eval_operand src u = SOME a /\ op_taint tn1 src = {}` by
    (Cases_on `src` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    code_reason_copy_resources_ptr >>
  disch_then (drule_at_then (Pat `lookup_var _ _ = SOME _`) mp_tac) >>
  `b < dimword(:256)` by decide_tac >>
  disch_then (drule_at_then (Pat `MEM _ (fn_insts _)`) mp_tac) >>
  simp[mk_inst_def] >>
  disch_then (drule_at_then (Pat `ptr_covers _ _ _ _ _`) mp_tac) >>
  disch_then (drule_at_then (Pat `immutable_holds _ _ _ _ _ _ _`) mp_tac) >>
  disch_then (qspecl_then [`str`, `max`, `ctx`, `PG`, `D`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[])) >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `t`, `b`] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (drule_all gas_path_ptr_then >> simp[])
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `aid` >>
      conj_tac >- decide_tac >> metis_tac[])
  >- metis_tac[]
  >> metis_tac[]
QED

Theorem code_reason_unwrap_path_ptr:
  unwrap_value cenv (LocatedValue ann p) cc = (op,cb) /\
  ~is_word_type ann /\ p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  type_memory_bytes cenv ann = 32*n /\
  (type_memory_bytes cenv ann+31) DIV 32 = n /\
  fn_has_code cc cb func /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv cc /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  32*n < dimword(:256) /\ eval_operand p.ptr_operand s = SOME a /\
  op_taint tn p.ptr_operand = {} /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at cc x) /\
  immutable_holds cenv cx ty tv a es s /\
  read_result cx tv es = (INL (StringV str),es) /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  type_slot_size (BaseTV (StringT max)) = n /\
  type_memory_size (BaseTV (StringT max)) = 32*n ==>
  ?root Gf tnf t b.
    op = Var root /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = cb.cs_current_bb /\
    t.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx es t /\
    lookup_var root t = SOME (n2w b) /\ ptr_covers Gf tnf root t (32*n) /\
    ptr_mem_ok cx ty (StringV str) (Var root) Gf tnf t /\
    32 + 32*word_size (LENGTH str) <= 32*n /\ b+32*n < dimword(:256) /\
    FLOOKUP t.vs_allocas cc.cs_next_id = SOME (b,32*n) /\
    (!aid off len. aid < cc.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!x k. not_fresh_at cc x /\ ptr_covers G tn x s k ==>
      ptr_covers Gf tnf x t k) /\
    (!x. not_fresh_at cc x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all code_unwrap_compile_parts >> strip_tac >>
  `ci_mono cc ca /\ ci_mono ca cb` by
    (conj_tac
     >- (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
         rpt (pop_assum kall_tac) >> strip_tac >>
         metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND]) >>
     qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `fn_has_code cc ca func /\ fn_has_code ca cb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) code_reason_alloc_copy_path_ptr >>
  disch_then (drule_at_then (Pat `immutable_holds _ _ _ _ _ _ _`) mp_tac) >>
  disch_then (drule_at_then (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`) mp_tac) >>
  disch_then (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _`) mp_tac) >>
  disch_then (drule_at_then (Pat `read_result _ _ _ = _`) mp_tac) >>
  disch_then (drule_at_then (Pat `op_taint _ _ = {}`) mp_tac) >>
  disch_then (qspec_then `max` mp_tac) >>
  asm_rewrite_tac[] >> disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`root`, `Gf`, `tnf`, `t`, `b`] >> asm_rewrite_tac[]
QED
