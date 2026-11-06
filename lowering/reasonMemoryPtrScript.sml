(* Memory-source boundaries shared by reason-bearing raise and assert. *)
Theory reasonMemoryPtr
Ancestors bodyPtrDefs ptrDiscipline venomState exprLowering compileEnv
  reasonNormalizedSuffixPtr reasonResourcesPtr reasonPrefixPtr
  exprLoweringProps emitHelperProps context emitHelper

Theorem reason_ptr_mem_ok_transport:
  ptr_mem_ok cx ty v op G tn s /\
  eval_operand op s = SOME w /\ eval_operand op t = SOME w /\
  op_prov G' op = op_prov G op /\
  (!tv mem. evaluate_type (get_tenv cx) ty = SOME tv /\
    mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_mem_ok cx ty v op G' tn' t
Proof
  strip_tac >> simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >>
  strip_tac >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem reason_memory_unwrap_identity:
  ~is_word_type ty /\ p.ptr_location = LocMemory ==>
  unwrap_value cenv (LocatedValue ty p) sa = (p.ptr_operand,sa)
Proof
  simp[unwrap_value_def, comp_return_def]
QED

(* Code slices are supplied by the compile_raise_reason split: its c5 is sa
   here, c6..c10 are c1..sm, c11=sc and c12=sb. Identity unwrap
   identifies c5 with the checked prefix endpoint. The remaining premises are
   endpoint projections of reason_encoder_prefix_path_ptr, not a new invariant. *)
Theorem reason_memory_suffix_path_ptr:
  compile_alloc_buffer (64+m) cc = (outerbuf,p1) /\
  emit_void MSTORE [outerbuf.buf_operand;Lit 0x08c379a0w] p1 = ((),p2) /\
  emit_op ADD [outerbuf.buf_operand;Lit 32w] p2 = (Var payload,p3) /\
  compile_alloc_buffer m p3 = (tuplebuf,sa) /\
  outerbuf.buf_operand = Var outer /\ tuplebuf.buf_operand = Var tuple /\
  emit_op MLOAD [Var src] sa = (Var v1,c1) /\
  emit_op ADD [Var v1;Lit 31w] c1 = (Var v2,c2) /\
  emit_op AND [Var v2;Lit (i2w (-32))] c2 = (Var v3,c3) /\
  emit_op ADD [Lit 32w;Var v3] c3 = (Var v4,c4) /\
  emit_void MCOPY [Var tuple;Var src;Var v4] c4 = ((),sm) /\
  compile_alloc_buffer 32 sm = (buf,sc) /\ buf.buf_operand = Var slot /\
  emit_void MSTORE [Var slot;Lit 32w] sc = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\ fn_has_code c4 sm func /\
  fn_has_code sm sc func /\ fn_has_code sc sb func /\ ~ctx_has_dalloca ctx /\
  t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~t.vs_halted /\
  eval_operand (Var src) s = SOME a /\ eval_operand (Var src) t = SOME a /\
  eval_operand (Var tuple) t = SOME (n2w b2) /\
  eval_operand (Var payload) t = SOME (n2w b+32w) /\
  eval_operand (Var outer) t = SOME (n2w b) /\
  ptr_mem_ok cx ty (StringV str) (Var src) G tn s /\
  op_prov G4 (Var src) = op_prov G (Var src) /\
  op_taint tn4 (Var src) = op_taint tn (Var src) /\ op_taint tn (Var src) = {} /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT cap)) /\
  val_wf (BaseTV (StringT cap)) (StringV str) /\
  (!mem. mem_agree_outside tn4.t_mem t.vs_memory mem ==>
    val_in_memory (BaseTV (StringT cap)) (StringV str) (w2n a) mem) /\
  ptr_covers G4 tn4 tuple t m /\ ptr_covers G4 tn4 outer t (64+m) /\
  ptr_covers G4 tn4 payload t ((64+m)-32) /\
  m = type_memory_bytes cenv (BaseT (StringT cap)) /\
  type_alloc_ok cenv (BaseT (StringT cap)) /\
  b+64+m < dimword (:256) /\ b2+m < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es t /\ fn_inst_ids_distinct func /\
  MEM (mk_inst p3.cs_next_id ALLOCA [Lit (n2w m)] [tuple]) (fn_insts func) /\
  not_local_ptr cenv es.scopes tuple /\
  FLOOKUP t.vs_allocas p3.cs_next_id = SOME (b2,m) /\
  fresh_vars_wrt sa t /\ local_ptrs_reserved cenv sa /\ not_fresh_at cc src /\
  reason_encode_finish (Var outer) (Var payload) (Var tuple) (Var slot) sb = ((),se) /\
  fn_has_code sb se func ==>
  ?Gf tnf sf. gas_path_ptr D 0 ctx func PG G4 tn4 t 0 Gf tnf (Abort Revert_abort sf)
Proof
  strip_tac >>
  `ptr_mem_ok cx ty (StringV str) (Var src) G4 tn4 t` by
    (irule reason_ptr_mem_ok_transport >> qexistsl_tac [`G`, `s`, `tn`, `a`] >> simp[]) >>
  `op_taint tn4 (Var src) = {}` by metis_tac[] >>
  `ptr_covers G4 tn4 src t (32+32*word_size (LENGTH str))` by
    (drule_all reason_string_source_covers >> simp[]) >>
  `32+32*word_size (LENGTH str) <= type_memory_bytes cenv (BaseT (StringT cap))` by
    (irule reason_string_type_capacity >> simp[]) >>
  `64+type_memory_bytes cenv (BaseT (StringT cap)) < dimword (:256)` by
    (irule reason_encoder_allocation_limit >> simp[]) >>
  `p3.cs_next_id < sm.cs_next_id /\
   (!p. MEM p [src;tuple;payload;outer] ==> not_fresh_at sa p)` by
    suspend "compiler" >>
  `w2n (n2w b : bytes32) = b /\ w2n (n2w b+32w : bytes32) = b+32` by
    (simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w] >> decide_tac) >>
  `32+32*word_size (LENGTH str) <= m /\
   32+32*word_size (LENGTH str) < dimword (:256) /\
   64+m < dimword (:256) /\ b2 < dimword (:256) /\
   w2n (n2w b : bytes32)+(64+m) < dimword (:256) /\
   w2n (n2w b+32w : bytes32)+(32+m) < dimword (:256)` by
    (simp[] >> decide_tac) >>
  fs[eval_operand_def] >>
  drule_at (Pat `reason_encode_finish _ _ _ _ _ = _`)
    (REWRITE_RULE [GSYM AND_IMP_INTRO] reason_normalized_suffix_path_ptr) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  rpt (disch_then drule) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[venomInstTheory.mk_inst_def, exprSimPropsTheory.val_store_size_def] >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then drule >> simp[]
QED

Resume reason_memory_suffix_path_ptr[compiler]:
  qpat_x_assum `not_fresh_at cc src` mp_tac >>
  qpat_x_assum `outerbuf.buf_operand = _` mp_tac >>
  qpat_x_assum `tuplebuf.buf_operand = _` mp_tac >>
  rpt (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` mp_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_inst_def, emit_def,
       not_fresh_at_def] >> rpt strip_tac >> gvs[]
QED

Finalise reason_memory_suffix_path_ptr
