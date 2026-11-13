(* Same-endpoint counted paths for straight typed normalization windows. *)
Theory typedNormalizeStraightPathMem
Ancestors
  typedNormalizeFrame typedNormalizeFields placeMemoryFieldsForward placeMemoryTypedBase typedBytesArrayMem valueEncodingProps exprSimProps
  typedNormalizeDynarray bodyIfExpBytesCopy fragGasSeqMem fragGasMode fragExec
  externalReturnNormalizeMem exprLoweringProps compileEnv venomInst venomState
  list rich_list

Theorem typed_normalize_straight_mem_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  EVERY (\i. i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rw[fn_has_code_def] >>
  `isPREFIX code (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[EVERY_MEM]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >>
  simp[gas_marked_path_def, arithmeticTheory.ADD_COMM]
QED

Theorem normalize_byte_offset_mem_path:
  compile_with_byte_offset op off sa = (out,sb) /\
  eval_operand op s = SOME a /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. out = Var x ==> not_fresh_at sb x) /\
  ?t. mem_cont_sim ctx fn s t /\
      eval_operand out t = SOME (a + n2w off) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      gas_marked_path T ctx fn s 0 (OK t)
Proof
  strip_tac >> drule_all normalize_byte_offset_run >> strip_tac >>
  drule_all compile_with_byte_offset_sequence >> strip_tac >>
  `u = q` by fs[] >> fs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule normalize_byte_offset_mem_ok >> simp[]) >>
  `gas_marked_path T ctx fn s 0
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule typed_normalize_straight_mem_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[same_blocks_def]) >>
  `mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule typed_bytes_child_seq_cont >> simp[] >> qexists_tac `sa` >>
     gvs[same_blocks_def]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def,
      same_blocks_def]
QED

Theorem normalize_word_window_mem_path:
  is_word_type dst_ty /\ evaluate_type tenv dst_ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
  compile_store_memory_typed ce dst dst_ty src src_ty sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (!a k. a + k <= w2n d \/ w2n d + 32 <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      gas_marked_path T ctx fn s 0
        (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_word_copy_run >> strip_tac >>
  drule_all typed_memory_word_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all typed_copy_word_mem_ok >> simp[]) >>
  `gas_marked_path T ctx fn s 0
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule typed_normalize_straight_mem_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> fs[same_blocks_def]) >>
  `mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule typed_bytes_child_seq_cont >> simp[] >> qexists_tac `sa` >>
     fs[same_blocks_def]) >>
  qexists_tac `q` >> simp[] >> conj_tac
  >- (drule_all val_in_memory_word_type >>
      simp[mem_word_at_eq_mload] >> strip_tac >>
      drule_all val_in_memory_word >>
      disch_then (qspecl_then [`w2n d`,
        `(mstore (w2n d) (mload (w2n p) s) s).vs_memory`] mp_tac) >>
      simp[mstore_mem_word_at_same]) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem typed_dynarray_equal_mem_path:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) /\
  l * type_memory_bytes ce ty < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  w2n (p+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
  w2n (d+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. mem_cont_sim ctx fn s (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    u.vs_memory =
      (mcopy (w2n (d+32w)) (w2n (p+32w)) (l * type_memory_bytes ce ty)
        (mstore (w2n d) (n2w l) s)).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    gas_marked_path T ctx fn s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all typed_dynarray_equal_compiler_run >> strip_tac >>
  drule typed_dynarray_equal_shape >> strip_tac >>
  `gas_marked_path T ctx fn s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule typed_normalize_straight_mem_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
     simp[mk_inst_def, is_terminator_def]) >>
  `mem_cont_sim ctx fn s (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule typed_bytes_child_seq_cont >> simp[] >> qexists_tac `sa` >>
     simp[IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]) >>
  qexists_tac `u` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem normalize_bytestring_window_mem_path:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size len /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (!a k. a + k <= w2n d \/
          w2n d + (32 + 32 * word_size len) <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      gas_marked_path T ctx fn s 0
        (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all normalize_bytestring_window_run >> strip_tac >>
  drule exprSimBufferStoreTheory.buffer_store_bytestring_shape >> strip_tac >>
  drule ifexp_bytes_copy_no_gas >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `gas_marked_path T ctx fn s 0
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule typed_normalize_straight_mem_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> fs[same_blocks_def]) >>
  `mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule typed_bytes_child_seq_cont >> simp[] >> qexists_tac `sa` >>
     fs[same_blocks_def, IS_PREFIX_APPEND]) >>
  qexists_tac `q` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem typed_store_empty_mem_path:
  acyclic_struct_metadata ce.ce_struct_fields /\ value_has_type dtv v /\
  type_widens_to tenv sty NoneT /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv NoneT = SOME dtv /\
  compile_store_memory_typed ce dst NoneT src sty sa = ((),sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    gas_marked_path T ctx fn s 0 (OK t)
Proof
  strip_tac >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[vyperTypeSystemTheory.type_widens_to_def,
      vyperTypeSystemTheory.arg_type_fits_def]) >>
  gvs[Once contextTheory.compile_store_memory_typed_def,
    is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
    contextTheory.compile_copy_memory_def, comp_return_def,
    vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def] >>
  qexists_tac `s` >>
  simp[memContinuationTheory.mem_cont_sim_refl, valueEncodingDefsTheory.val_in_memory_def,
    venom_state_component_equality, gas_marked_path_def,
    fragGasPathMemTheory.gas_path_mem_rules]
QED
