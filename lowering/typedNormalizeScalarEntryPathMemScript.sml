(* Same-endpoint finite entries for nonrecursive typed normalization. *)
Theory typedNormalizeScalarEntryPathMem
Ancestors
  typedNormalizePrimitivePath typedNormalizeDynarray typedNormalizeFastRepresentation
  fragGasPathMem typedCopyAgreement typedNormalizeFrame venomState exprSimDefs exprLoweringProps
  exprSimProps valueEncoding typedMemoryCopy stmtSimReturn arithmetic
  valueCopyBytes exprSimBufferStore emitHelperProps exprSimAggregateChildren words
  vyperTypeSystem vyperTypeArgFits vyperTyping valueCopy compileEnv exprLowering emitHelper
  context vyperValue allocaFootprint fragGasSeqMem list rich_list venomExecSemantics venomInst
  stmtReasonLitFragMemory loweringPosts venomMemProps

Theorem typed_store_word_path_mem:
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  `sty = dty` by metis_tac[typed_copy_word_widening] >> gvs[] >>
  `type_memory_size dtv = 32` by metis_tac[word_type_sizes] >>
  drule_all normalize_word_straight >> strip_tac >>
  fs[ADD_COMM] >>
  drule_all normalize_word_window_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`q with vs_inst_idx := LENGTH sb.cs_current_insts`, `0`] >>
  gvs[venom_state_component_equality, lookup_var_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem typed_store_bytestring_path_mem:
  is_bytestring_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  `is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_store_size stv v = val_store_size dtv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  `val_store_size stv v <= type_memory_size stv /\
   val_store_size dtv v <= type_memory_size dtv /\
   val_footprint dtv v <= val_store_size dtv v` by
    metis_tac[val_store_size_le,val_footprint_le_store_size] >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  `32 + 32 * word_size len < dimword(:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   val_footprint dtv v <= 32 + 32 * word_size len` by decide_tac >>
  `compile_store_bytestring src dst sa = ((),sb)` by
    gvs[compile_store_memory_typed_bytes] >>
  drule buffer_store_bytestring_shape >> simp[same_blocks_def] >> strip_tac >>
  drule_all normalize_bytestring_window_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`q with vs_inst_idx := LENGTH sb.cs_current_insts`, `0`] >>
  gvs[venom_state_component_equality,lookup_var_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem typed_store_empty_path_mem:
  acyclic_struct_metadata ce.ce_struct_fields /\ value_has_type dtv v /\
  type_widens_to tenv sty NoneT /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv NoneT = SOME dtv /\
  compile_store_memory_typed ce dst NoneT src sty sa = ((),sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
    comp_return_def, evaluate_type_def, value_has_type_def] >>
  qexistsl_tac [`s`, `0`] >> simp[val_in_memory_def,
    venom_state_component_equality] >> irule (cj 1 gas_path_mem_rules) >> simp[]
QED

Theorem emit_mcopy_path_mem:
  emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  n < dimword(:256) /\ w2n p + n <= s.vs_alloca_next /\
  w2n d + n <= s.vs_alloca_next /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx fn s 0
    (OK ((mcopy (w2n d) (w2n p) n s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all emit_mcopy_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule emit_mcopy_mem_ok >>
     disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
     disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
     disch_then irule >> simp[eval_operand_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, fresh_id_def, emit_inst_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]) >>
  fs[same_blocks_def] >> drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

Theorem typed_store_bulk_path_mem:
  compile_copy_memory dst src (type_memory_size tv) sa = ((),sb) /\
  0 < type_memory_size tv /\ type_memory_size tv < dimword(:256) /\
  val_wf tv v /\ val_in_memory tv v (w2n sw) s.vs_memory /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size tv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> Cases_on `type_memory_size tv` >- fs[] >>
  gvs[compile_copy_memory_def] >> fs[ADD_COMM] >>
  drule emit_mcopy_path_mem >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (qspec_then `fn` mp_tac) >>
  (impl_tac >- simp[ADD_COMM]) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all emit_mcopy_run >> strip_tac >>
  qexistsl_tac [`mcopy (w2n dw) (w2n sw) (SUC n) s with
    vs_inst_idx := LENGTH sb.cs_current_insts`, `0`] >>
  `typed_copy_state_frame sa (w2n dw) (SUC n) s
    (mcopy (w2n dw) (w2n sw) (SUC n) s with
      vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[typed_copy_mcopy_state_frame] >>
  `val_in_memory tv v (w2n dw)
    (mcopy (w2n dw) (w2n sw) (SUC n) s).vs_memory` by
    (irule mcopy_val_in_memory >> simp[] >> metis_tac[val_footprint_le]) >>
  `~(mcopy (w2n dw) (w2n sw) (SUC n) s).vs_halted /\
   (mcopy (w2n dw) (w2n sw) (SUC n) s).vs_current_bb = s.vs_current_bb` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  fs[typed_copy_state_frame_def, typed_copy_frame_def, same_blocks_def] >>
  simp[ADD_COMM] >> rpt strip_tac >> simp[] >>
  qpat_x_assum `mcopy _ _ _ _ with <|vs_memory := _; vs_vars := _;
    vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[]
QED

Theorem normalize_dynarray_equal_window_path_mem:
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
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx fn s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    val_in_memory tv v (w2n d) u.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+32+l*type_memory_bytes ce ty <= a ==>
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  strip_tac >> (
  `w2n (p+32w) = w2n p+32 /\ w2n (d+32w) = w2n d+32` by simp[w2n_add_2] >>
  `w2n p + 32 <= s.vs_alloca_next /\
   w2n d + 32 <= s.vs_alloca_next /\
   w2n (p+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
   w2n (d+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next` by decide_tac >>
  drule_all typed_dynarray_equal_compiler_run >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by
    (irule LESS_EQ_TRANS >>
     qexists `LENGTH (mstore (w2n d) (n2w l) s).vs_memory` >>
     simp[mstore_memory_nondecreasing, mcopy_def,
       write_memory_with_expansion_nondecreasing]) >>
  drule typed_dynarray_equal_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[mk_inst_def, is_terminator_def] >>
  qpat_x_assum `emitted_insts sa sb = _` kall_tac >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  `gas_path_mem ctx fn s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >> simp[]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule val_in_memory_relocate >> conj_tac >- simp[] >>
      qexistsl_tac [`w2n p`, `32+l*type_memory_bytes ce ty`, `s.vs_memory`] >>
      simp[] >>
      pure_rewrite_tac [Q.SPECL [`l*type_memory_bytes ce ty`, `32`] ADD_COMM] >>
      irule typed_dynarray_equal_window >> metis_tac[]) >>
  rpt strip_tac >> simp[typed_dynarray_equal_exterior])
QED

Theorem typed_store_dynarray_equal_path_mem:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w (LENGTH vs) /\ LENGTH vs <= cap /\
  type_memory_bytes ce ty = type_memory_size tv /\
  cap < dimword(:256) /\ LENGTH vs * type_memory_size tv < dimword(:256) /\
  w2n sw + 32 < dimword(:256) /\ w2n dw + 32 < dimword(:256) /\
  32 + LENGTH vs * type_memory_size tv <= type_memory_size (ArrayTV tv (Dynamic scap)) /\
  w2n sw + type_memory_size (ArrayTV tv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  (w2n sw + type_memory_size (ArrayTV tv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= w2n sw) /\
  val_in_memory (ArrayTV tv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n sw) s.vs_memory /\
  val_wf (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs)) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size (ArrayTV tv (Dynamic cap)) <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH vs * type_memory_size tv <= cap * type_memory_size tv` by simp[] >>
  `val_in_memory (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs))
     (w2n sw) s.vs_memory` by metis_tac[dynarray_in_memory_capacity_irrelevant] >>
  qpat_x_assum `val_in_memory (ArrayTV tv (Dynamic scap)) _ _ _` kall_tac >>
  drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)
    normalize_dynarray_equal_window_path_mem >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (qspecl_then [`type_memory_size (ArrayTV tv (Dynamic scap))`, `LENGTH vs`, `fn`, `ctx`] mp_tac) >>
  (impl_tac >- (fs[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >>
    simp[val_footprint_def, type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> gvs[])) >>
  strip_tac >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by metis_tac[typed_dynarray_equal_shape] >>
  `!p k. p+k <= w2n dw \/ w2n dw+type_memory_size (ArrayTV tv (Dynamic cap)) <= p ==>
     mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ _ = _`
       (qspecl_then [`p`, `k`] mp_tac) >>
     fs[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> simp[] >> decide_tac) >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `0`] >>
  gvs[venom_state_component_equality,lookup_var_def] >>
  metis_tac[dynarray_in_memory_capacity_irrelevant]
QED
