Theory placeTypedCopyPath
Ancestors
  typedMemoryCopy fragGasSeq fragGasMode entryDecodeProps
  exprLowering exprLoweringProps compileEnv loweringSlice emitHelper emitHelperProps
  valueEncoding valueEncodingProps context valueCopy venomExecSemantics fragGasPath
  venomState venomInst fragExec list rich_list arithmetic

Theorem place_copy_seq_path:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb)
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def] >>
     gvs[IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     simp[DROP_APPEND, DROP_LENGTH_APPEND] >>
     `LENGTH sa.cs_current_insts -
        (LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)) = 0` by
       decide_tac >> simp[]) >>
  drule_all tuple_run_inst_seq_gas_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[EVERY_MEM]) >>
  simp[gas_marked_path_def]
QED

Theorem place_typed_copy_word_path:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  mem_word_at (w2n a) s0.vs_memory = typed_val_to_w256 tv v /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_copy_word_run_seq >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def] >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]) >>
  drule_all place_copy_seq_path >> strip_tac >>
  qexists_tac `(mstore (w2n d) (mload (w2n a) s0)
    (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n a) s0) s0))
      with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[typed_copy_word_state_frame] >>
  drule_all exprSimPropsTheory.val_in_memory_word >> strip_tac >>
  simp[mstore_mem_word_at_same, GSYM mem_word_at_eq_mload,
       mstore_def, write_memory_with_expansion_def, update_var_def,
       same_blocks_def] >> gvs[same_blocks_def]
QED

Theorem place_typed_copy_dynamic_path:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  eval_operand len s0 = SOME w /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= w2n w /\ w2n w <= type_memory_size tv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_copy_dynamic_run_seq >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _` mp_tac >>
     simp[compile_copy_memory_dynamic_def, emit_void_def, comp_bind_def,
          fresh_id_def, emit_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]) >>
  drule_all place_copy_seq_path >> strip_tac >>
  qexists_tac `(mcopy (w2n d) (w2n a) (w2n w) s0)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  conj_tac
  >- (irule typed_copy_state_frame_subinterval >>
      qexistsl_tac [`w2n d`, `w2n w`] >>
      simp[typed_copy_mcopy_state_frame]) >>
  gvs[mcopy_def, write_memory_with_expansion_def, same_blocks_def]
QED

Theorem place_typed_copy_fixed_path:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ n < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\ n <= type_memory_size tv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexists_tac `s0` >> simp[gas_marked_path_def, gas_path_rules] >>
      irule val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`, `0`, `s0.vs_memory`] >> simp[mem_bytes_at_def]) >>
  `compile_copy_memory_dynamic dst src (Lit (n2w n)) sa = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def, compile_copy_memory_dynamic_def]) >>
  irule place_typed_copy_dynamic_path >> simp[] >>
  qexistsl_tac [`a`, `dst`, `Lit (n2w n)`, `src`, `n2w n`] >>
  simp[eval_operand_def]
QED

Theorem place_typed_copy_bytestring_path:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d /\
  mem_word_at (w2n a) s0.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= type_memory_size tv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s0 t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all store_bytestring_run_exact >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
     simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
          emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]) >>
  drule_all place_copy_seq_path >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  conj_tac
  >- (simp[typed_copy_state_frame_def] >> conj_tac
      >- gvs[venom_state_component_equality] >>
      conj_tac >- gvs[lookup_var_def] >>
      simp[typed_copy_frame_def] >> conj_tac
      >- (rpt gen_tac >> strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
          decide_tac) >>
      simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
           MAX_DEF]) >>
  gvs[venom_state_component_equality, same_blocks_def]
QED

Theorem place_typed_copy_offset_path:
  !ptr off sa op sb s0 w dst len.
  compile_with_byte_offset ptr off sa = (op,sb) /\
  eval_operand ptr s0 = SOME w /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      eval_operand op t = SOME (w + n2w off) /\
      t.vs_memory = s0.vs_memory /\
      typed_copy_state_frame sa dst len s0 t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      qexists_tac `s0` >>
      simp[gas_marked_path_def, gas_path_rules, wordsTheory.WORD_ADD_0]) >>
  drule_all typed_copy_offset_run_seq >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
     simp[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
          comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]) >>
  drule_all place_copy_seq_path >> strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString sa.cs_next_var))
     (w + n2w off) s0) with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_update_var, typed_copy_state_frame_def,
       update_var_def, lookup_var_def, venom_state_component_equality,
       same_blocks_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  reverse conj_tac >- gvs[same_blocks_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem place_typed_copy_emit_op_path:
  !opc args a op b s w off len.
    emit_op opc args a = (op,b) /\
    opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS /\
    (!out. step_inst_base (mk_inst a.cs_next_id opc args [out]) s =
           OK (update_var out w s)) /\
    fn_has_code a b func /\ ~s.vs_halted /\
    s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
        typed_copy_state_frame a off len s t /\
        ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  `run_inst_seq (emitted_insts a b) s =
     OK (update_var (STRING #"%" (toString a.cs_next_var)) w s)` by
    (qpat_x_assum `!out. step_inst_base _ s = _`
       (qspec_then `STRING #"%" (toString a.cs_next_var)` mp_tac) >>
     simp[mk_inst_def, run_inst_seq_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts a b) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts a b)` by simp[mk_inst_def] >>
  `b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b` by simp[] >>
  drule_all place_copy_seq_path >> strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString a.cs_next_var)) w s)
    with vs_inst_idx := LENGTH b.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_update_var, typed_copy_state_frame_def,
       update_var_def, lookup_var_def, venom_state_component_equality,
       same_blocks_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  reverse conj_tac >- gvs[same_blocks_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString a.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem place_typed_copy_assign_path:
  emit_inst ASSIGN [op] [counter] a = ((),b) /\
  eval_operand op s = SOME w /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      lookup_var counter t = SOME w /\ t.vs_memory = s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. x <> counter ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  `same_blocks a b /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   emitted_insts a b = [mk_inst a.cs_next_id ASSIGN [op] [counter]]` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[same_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts a b) s = OK (update_var counter w s)` by
    simp[run_inst_seq_def, step_inst_base_def, mk_inst_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts a b) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts a b)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all place_copy_seq_path >> strip_tac >>
  qexists_tac `(update_var counter w s) with vs_inst_idx := LENGTH b.cs_current_insts` >>
  simp[lookup_var_update_var, update_var_def, lookup_var_def,
       venom_state_component_equality, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[same_blocks_def]
QED

Theorem place_copy_emit_instruction:
  emit_inst opc args outs a = ((),b) /\ fn_has_code a b func ==>
  ?bb. lookup_block a.cs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb (LENGTH a.cs_current_insts) =
         SOME (mk_inst a.cs_next_id opc args outs)
Proof
  strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[get_instruction_def, EL_APPEND_EQN, EL_LENGTH_APPEND]
QED
