Theory typedCopyCounted
Ancestors
  typedNormalizeFrame bodyDeclMemoryCounted bodyMemAggregateStore
  externalReturnNormalizeMem bodyDeclMemoryCore
  exprLoweringProps context typedCopyAgreement venomState valueEncodingProps
  valueEncodingProofs valueCopy valueCopyBytes exprSimProps emitHelper venomInst compileEnv
  exprSimBufferStore list fragGasPathMem valueEncoding vyperTyping
  vyperTypeSystem vyperValue vyperTypeInvariants

Theorem normalize_word_window_path:
  is_word_type dst_ty /\ evaluate_type tenv dst_ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
  compile_store_memory_typed ce dst dst_ty src src_ty sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ alloca_history fn t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      (!a k. a + k <= w2n d \/ w2n d + 32 <= a ==>
        mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_word_copy_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all typed_copy_word_mem_ok >> simp[]) >>
  drule_all normalize_word_straight >> strip_tac >>
  `same_blocks sa sb` by simp[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_store_memory_typed_word, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1, mk_inst_def,
       is_terminator_def]) >>
  `gas_path_mem ctx fn s 0
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists `sa` >> simp[]) >>
  `alloca_history fn (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl [`s`, `sa`] >> simp[]) >>
  qexists `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, lookup_var_def] >>
  conj_tac
  >- (drule_all val_in_memory_word_type >>
      simp[mem_word_at_eq_mload] >> strip_tac >>
      drule_all val_in_memory_word >>
      disch_then (qspecl_then [`w2n d`,
        `(mstore (w2n d) (mload (w2n p) s) s).vs_memory`] mp_tac) >>
      simp[mstore_mem_word_at_same]) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem normalize_bytestring_window_path:
  is_bytestring_type dst_ty /\ is_bytestring_type src_ty /\
  compile_store_memory_typed ce dst dst_ty src src_ty sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size len /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ alloca_history fn t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      (!a k. a + k <= w2n d \/
          w2n d + (32 + 32 * word_size len) <= a ==>
        mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `compile_store_bytestring src dst sa = ((),sb)` by
    gvs[compile_store_memory_typed_bytes] >>
  drule_all normalize_bytestring_window_run >> strip_tac >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  `compile_store_memory ce src dst dst_ty dst_ty sa = ((),sb)` by
    simp[compile_store_memory_def, is_bytestring_word_type] >>
  drule aggregate_store_memory_no_gas >> strip_tac >>
  `gas_path_mem ctx fn s 0
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists `sa` >> simp[]) >>
  `alloca_history fn (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl [`s`, `sa`] >>
     fs[EVERY_MEM]) >>
  qexists `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, lookup_var_def, same_blocks_def] >> gvs[]
QED

Theorem typed_store_empty_path:
  acyclic_struct_metadata ce.ce_struct_fields /\ value_has_type dtv v /\
  type_widens_to tenv sty NoneT /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv NoneT = SOME dtv /\
  compile_store_memory_typed ce dst NoneT src sty sa = ((),sb) /\
  alloca_history fn s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ alloca_history fn t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    t = s
Proof
  strip_tac >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
    comp_return_def, evaluate_type_def, value_has_type_def] >>
  simp[gas_path_mem_rules, val_in_memory_def]
QED
