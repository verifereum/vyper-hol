(* Resource audit boundaries between tuple copying and the checked finish.
   Tuple MCOPY frames operands/coverage but not expr_post.  Slot allocation
   still needs the source-state allocation invariant and separation from the
   tuple head before its initializing MSTORE can preserve that head. *)
Theory reasonNormalizedSuffixPtr
Ancestors reasonFinishPtr reasonTupleCopyPtr reasonResourcesPtr
  representationCleanPtr valueEncoding venomMemProps bodyPtrDefs
  exprSimProps words list pred_set reasonTupleCompilerPtr reasonSlotResourcesPtr
  emitHelperProps exprLoweringProps compileEnv finite_map reasonCompilerFramePtr
  loweringHalt contextProps freshWrites reasonFinishBoundsPtr reasonFinishCode

Theorem reason_tuple_copy_string_head:
  ptr_mem_ok cx ty (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME a /\ val_wf tv (StringV str) /\
  val_store_size tv (StringV str) <= n /\
  sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
  tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
    {w2n b + i | i < n /\ w2n a + i IN tn.t_mem} ==>
  (!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory tv (StringV str) (w2n b) mem) /\
  (!i. w2n b <= i /\ i < w2n b + 32 ==> i NOTIN tnf.t_mem) /\
  mload (w2n b) sf = n2w (LENGTH str)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory tv (StringV str) (w2n b) mem` by
    (rpt strip_tac >> irule reason_tuple_copy_resources_ptr >>
     conj_tac >- simp[] >>
     qexistsl [`G`, `a`, `cx`, `n`, `op`, `s`, `sf`, `tn`, `tnf`, `ty`] >> simp[]) >>
  conj_tac >- simp[] >> conj_tac
  >- (drule robust_val_in_memory_string_clean >> simp[]) >>
  `val_in_memory tv (StringV str) (w2n b) sf.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  gvs[val_in_memory_def, venomStateTheory.mload_def, mem_word_at_def]
QED

(* The normalized copy and size-slot prefix exports only the resources used
   by reason_encode_finish_path_ptr; source expression posts do not escape. *)
Theorem reason_normalized_finish_resources_ptr:
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
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ lookup_var tuple s = SOME (n2w b) /\
  lookup_var payload s = SOME payload_addr /\ lookup_var outer s = SOME outer_addr /\
  ptr_mem_ok cx ty (StringV str) (Var src) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv (StringV str) /\
  ptr_covers G tn src s n /\ ptr_covers G tn tuple s m /\
  ptr_covers G tn payload s (32+m) /\ ptr_covers G tn outer s (64+m) /\
  n = 32 + 32 * word_size (LENGTH str) /\ n <= m /\ n < dimword (:256) /\
  val_store_size tv (StringV str) <= n /\ b < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [tuple] /\ not_local_ptr cenv es.scopes tuple /\
  inst.inst_id < sm.cs_next_id /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,m) /\
  fresh_vars_wrt sa s /\ local_ptrs_reserved cenv sa /\
  (!p. MEM p [src;tuple;payload;outer] ==> not_fresh_at sa p) ==>
  ?Gf tnf sf slot_addr.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    (!p. MEM p [outer;payload;tuple;slot] ==> not_fresh_at sb p) /\
    lookup_var tuple sf = SOME (n2w b) /\ ptr_covers Gf tnf tuple sf m /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tnf.t_mem) /\
    mload b sf = n2w (LENGTH str) /\
    lookup_var slot sf = SOME slot_addr /\ ptr_covers Gf tnf slot sf 32 /\
    (!i. w2n slot_addr <= i /\ i < w2n slot_addr+32 ==> i NOTIN tnf.t_mem) /\
    mload (w2n slot_addr) sf = 32w /\
    lookup_var payload sf = SOME payload_addr /\ ptr_covers Gf tnf payload sf (32+m) /\
    lookup_var outer sf = SOME outer_addr /\ ptr_covers Gf tnf outer sf (64+m)
Proof
  strip_tac >>
  `eval_operand (Var src) s = SOME a` by simp[venomStateTheory.eval_operand_def] >>
  `mload (w2n a) s = n2w (LENGTH str) /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)` by
    (conj_tac
     >- (drule_all reason_string_length_word >>
         simp[venomStateTheory.mload_def, mem_word_at_def]) >>
     imp_res_tac reason_string_head_clean >> simp[]) >>
  `32 <= n /\ ptr_covers G tn tuple s n` by
    (conj_tac >- simp[] >> fs[ptr_covers_def] >>
     qexists_tac `n2w b` >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `not_fresh_at sa src /\ not_fresh_at sa tuple /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n (n2w b : bytes32),m)` by
    simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  drule_all reason_tuple_copy_compiler_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "resources"
QED

Resume reason_normalized_finish_resources_ptr[resources]:
  drule_all reason_tuple_copy_fresh_names >> strip_tac >>
  `!p. MEM p [src;tuple;payload;outer] ==>
     p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4` by
    (qpat_x_assum `!p. MEM p [v1;v2;v3;v4] ==> lookup_var p s = NONE` mp_tac >>
     map_every (fn pat => qpat_x_assum pat mp_tac)
       [`lookup_var src s = _`, `lookup_var tuple s = _`,
        `lookup_var payload s = _`, `lookup_var outer s = _`] >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `!p. MEM p [src;tuple;payload;outer] ==> not_fresh_at sm p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `lookup_var tuple sf = SOME (n2w b) /\
   lookup_var payload sf = SOME payload_addr /\ lookup_var outer sf = SOME outer_addr /\
   ptr_covers Gf tnf tuple sf m /\ ptr_covers Gf tnf payload sf (32+m) /\
   ptr_covers Gf tnf outer sf (64+m)` by (simp[] >> metis_tac[]) >>
  `(!i. b <= i /\ i < b+32 ==> i NOTIN tnf.t_mem) /\
   mload b sf = n2w (LENGTH str)` by
    (drule_all reason_tuple_copy_string_head >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `tuple <> slot /\ payload <> slot /\ outer <> slot` by
    (gvs[] >> metis_tac[]) >>
  `32 <= m /\ not_fresh_at sm tuple /\
   FLOOKUP sf.vs_allocas inst.inst_id = SOME (b,m)` by (simp[] >> decide_tac) >>
  drule_all reason_slot_tuple_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "finish"
QED

Resume reason_normalized_finish_resources_ptr[finish]:
  `sb.cs_next_var = sc.cs_next_var` by
    (qpat_x_assum `emit_void MSTORE _ sc = _` mp_tac >>
     simp[emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def,
          fresh_id_def, emit_def, comp_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  `!p. MEM p [outer;payload;tuple;slot] ==> not_fresh_at sb p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sc` >>
     simp[] >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`, `a'`] >> simp[] >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf)` mp_tac >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG Gf tnf sf 0 Gf' tnf' (OK sf')` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Finalise reason_normalized_finish_resources_ptr

Theorem reason_normalized_suffix_path_ptr:
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
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ lookup_var tuple s = SOME (n2w b) /\
  lookup_var payload s = SOME payload_addr /\ lookup_var outer s = SOME outer_addr /\
  ptr_mem_ok cx ty (StringV str) (Var src) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv (StringV str) /\
  ptr_covers G tn src s n /\ ptr_covers G tn tuple s m /\
  ptr_covers G tn payload s (32+m) /\ ptr_covers G tn outer s (64+m) /\
  n = 32 + 32 * word_size (LENGTH str) /\ n <= m /\ n < dimword (:256) /\
  val_store_size tv (StringV str) <= n /\ b < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [tuple] /\ not_local_ptr cenv es.scopes tuple /\
  inst.inst_id < sm.cs_next_id /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,m) /\
  fresh_vars_wrt sa s /\ local_ptrs_reserved cenv sa /\
  (!p. MEM p [src;tuple;payload;outer] ==> not_fresh_at sa p) /\
  reason_encode_finish (Var outer) (Var payload) (Var tuple) (Var slot) sb = ((),se) /\
  fn_has_code sb se func /\ 64+m < dimword (:256) /\
  w2n payload_addr+(32+m) < dimword (:256) /\
  w2n outer_addr+(64+m) < dimword (:256) ==>
  ?Gf tnf sf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort sf)
Proof
  strip_tac >> drule_all reason_normalized_finish_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `32 + 32 * word_size (LENGTH str) <= m` by gvs[] >>
  drule_all reason_finish_capacity_bounds >> strip_tac >>
  `mload (w2n (n2w b : bytes32)) sf = n2w (LENGTH str) /\
   (!i. w2n (n2w b : bytes32) <= i /\ i < w2n (n2w b : bytes32)+32 ==>
     i NOTIN tnf.t_mem)` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  drule_all reason_encode_finish_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf)` mp_tac >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG Gf tnf sf 0 Gf' tnf' (Abort Revert_abort sf')` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED
