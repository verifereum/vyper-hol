Theory typedCopyAggregateCounted
Ancestors
  typedCopyLoopCounted typedNormalizeDynarray typedNormalizeStaticRigidity
  placeMemoryTypedPrimitive bodyCopyMemory exprSimBufferStore
  bodyDeclMemoryCounted bodyDeclMemoryCore fragGasPathMem
  valueCopy valueCopyBytes valueEncoding valueEncodingProps
  exprLoweringProps venomState venomInst venomMemDefs venomExecSemantics context compileEnv list words arithmetic

Theorem copy_memory_window_path:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  n < dimword (:256) /\
  w2n p + n <= s.vs_alloca_next /\ w2n d + n <= s.vs_alloca_next /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ alloca_history fn t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      (!a k. a + k <= w2n d \/ w2n d + n <= a ==>
        mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (t with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all compile_copy_memory_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_copy_memory_body_mem_ok >> metis_tac[]) >>
  qabbrev_tac `q = if n = 0 then s else mcopy (w2n d) (w2n p) n s` >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx fn s 0
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists `sa` >> simp[]) >>
  `alloca_history fn (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl [`s`, `sa`] >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all buffer_copy_memory_encoding >> strip_tac >> gvs[] >>
  qexists `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[same_blocks_def] >>
  qpat_x_assum `(_ with vs_memory := _) = _` mp_tac >>
  simp[venom_state_component_equality, lookup_var_def] >> metis_tac[]
QED

Theorem typed_dynarray_equal_path:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) /\
  l * type_memory_bytes ce ty < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  w2n (p+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
  w2n (d+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ alloca_history fn u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory =
      (mcopy (w2n (d+32w)) (w2n (p+32w)) (l * type_memory_bytes ce ty)
        (mstore (w2n d) (n2w l) s)).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_dynarray_equal_compiler_run >> strip_tac >>
  drule typed_dynarray_equal_shape >> strip_tac >>
  `same_blocks sa sb` by simp[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx fn s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists `sa` >> simp[]) >>
  `alloca_history fn (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl [`s`, `sa`] >> simp[mk_inst_def, is_terminator_def]) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[lookup_var_def] >>
  qpat_x_assum `(_ with <|vs_memory := _; vs_vars := _|>) = _` mp_tac >>
  simp[venom_state_component_equality, lookup_var_def] >> metis_tac[]
QED

Theorem typed_dynarray_equal_window_path:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) /\
  l * type_memory_bytes ce ty < dimword(:256) /\
  w2n p + 32 < dimword(:256) /\ w2n d + 32 < dimword(:256) /\
  32 + l * type_memory_bytes ce ty <= src_size /\
  w2n p + src_size <= s.vs_alloca_next /\
  w2n d + 32 + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
  (w2n p + src_size <= w2n d \/
   w2n d + 32 + l * type_memory_bytes ce ty <= w2n p) /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + l * type_memory_bytes ce ty /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ alloca_history fn u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n d) u.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+32+l*type_memory_bytes ce ty <= a ==>
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (p+32w) = w2n p+32 /\ w2n (d+32w) = w2n d+32` by
    simp[w2n_add_2] >>
  `w2n p + 32 <= s.vs_alloca_next /\
   w2n d + 32 <= s.vs_alloca_next /\
   w2n (p+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
   w2n (d+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next` by decide_tac >>
  drule_all typed_dynarray_equal_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> qexists `u` >> simp[] >>
  conj_tac
  >- (irule valueCopyTheory.val_in_memory_relocate >> conj_tac >- simp[] >>
      qexistsl [`w2n p`, `32+l*type_memory_bytes ce ty`, `s.vs_memory`] >>
      simp[] >>
      pure_rewrite_tac [Q.SPECL [`l*type_memory_bytes ce ty`, `32`] ADD_COMM] >>
      irule typed_dynarray_equal_window >> metis_tac[]) >>
  rpt strip_tac >> irule typed_dynarray_equal_exterior >> simp[]
QED

Theorem typed_sarray_fast_window_path:
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  type_memory_bytes ce dt = type_memory_bytes ce st /\
  ~is_abi_dynamic ce.ce_struct_fields dt /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  ncount * type_memory_bytes ce dt < dimword (:256) /\
  w2n p + ncount * type_memory_bytes ce dt <= s.vs_alloca_next /\
  w2n d + ncount * type_memory_bytes ce dt <= s.vs_alloca_next /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= ncount * type_memory_bytes ce dt /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ alloca_history fn t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      (!a k. a+k <= w2n d \/ w2n d+ncount*type_memory_bytes ce dt <= a ==>
        mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (t with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `compile_copy_memory dst src (ncount * type_memory_bytes ce dt) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def]) >>
  irule copy_memory_window_path >> metis_tac[]
QED
