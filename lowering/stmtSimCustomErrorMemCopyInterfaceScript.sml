Theory stmtSimCustomErrorMemCopyInterface
Ancestors
  stmtSimCustomErrorMemCopyPrimitive placeTypedCopyRecursivePath
  placeMemoryFieldsForward bodyFieldMemoryProps context compileEnv
  venomState venomExecSemantics fragGasMode fragGasPathMem
  exprSimMemUnwrap valueEncoding valueEncodingProps words list
  fragExecMem emitHelperProps exprLoweringProps typedMemoryCopy
  placeMemoryTypedBase externalReturnNormalizeMem exprSimProps valueCopyBytes
  valueCopy valueEncodingDefs exprSimBufferStore bodyMemAggregateStore
  immutableBytestringFootprint typedCopyAgreement valueTypingMemoryProps
  allocaFootprint placeTypedCopyPath unitTransformDefs contextCodegenRel
  venomInst codegenRel memSafeRun loweringStateRelDefs arithmetic
  emitHelper rich_list fragExec venomMemDefs stmtForRangeMemoryParts allocaHistory

Definition typed_copy_checked_entry_def:
  typed_copy_checked_entry cenv ctx dty sty dtv stv v <=>
    !func dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      alloca_inv s /\ alloca_history func s /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?t. gas_marked_path T ctx func s 0 (OK t) /\
          val_in_memory dtv v (w2n dw) t.vs_memory /\
          typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
          ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
End

Theorem typed_copy_checked_entry_run:
  typed_copy_checked_entry cenv ctx dty sty dtv stv v /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  simp_tac std_ss [typed_copy_checked_entry_def] >> strip_tac >>
  first_x_assum irule >> simp[] >> qexistsl_tac [`dst`, `src`, `sw`] >> simp[]
QED

Theorem compile_with_byte_offset_checked:
  compile_with_byte_offset op off sa = (out_op,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME w /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand out_op t = SOME (w + n2w off) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all compile_with_byte_offset_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (Cases_on `off = 0`
     >- (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
         simp[compile_with_byte_offset_def, comp_return_def] >>
         strip_tac >> simp[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
     irule attr_add_prefix_mem_ok >>
     qexistsl_tac [`out_op`, `[op; Lit (n2w off)]`] >>
     gvs[compile_with_byte_offset_def]) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[EVERY_MEM] >> gvs[EVERY_MEM]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[lookup_var_def]
QED

Theorem typed_copy_word_checked_post:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  mem_word_at (w2n a) s.vs_memory = typed_val_to_w256 tv v /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  w2n a + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all typed_memory_word_sequence >> strip_tac >>
  drule_all typed_copy_word_mem_ok >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK u` >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[EVERY_MEM] >> gvs[EVERY_MEM]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[Abbr `u`, typed_copy_word_state_frame] >>
  drule_all val_in_memory_word >> strip_tac >>
  simp[mstore_mem_word_at_same, GSYM mem_word_at_eq_mload,
       mstore_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem typed_copy_checked_word_entry:
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv dty = SOME dtv /\
  evaluate_type tenv sty = SOME stv /\ value_has_type dtv v ==>
  typed_copy_checked_entry cenv ctx dty sty dtv stv v
Proof
  strip_tac >> drule_all typed_copy_word_widening >> strip_tac >> gvs[] >>
  `type_memory_size dtv = 32` by metis_tac[word_tv_memory_size] >>
  simp[typed_copy_checked_entry_def] >> rpt strip_tac >>
  `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 dtv v` by
    metis_tac[val_in_memory_word] >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all typed_copy_word_checked_post >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[gas_marked_path_def]
QED

Theorem typed_copy_bulk_checked_post:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\ n <= type_memory_size tv ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all compile_copy_memory_checked_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[LET_THM] >> strip_tac >>
  qexists_tac `(if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  Cases_on `n = 0`
  >- (gvs[] >> conj_tac
      >- (irule val_in_memory_relocate >> simp[] >>
          qexistsl_tac [`w2n sw`, `0`, `s.vs_memory`] >> simp[mem_bytes_at_def]) >>
      simp[typed_copy_state_frame_def, lookup_var_def,
           venom_state_component_equality]) >>
  simp[] >> conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  irule typed_copy_state_frame_subinterval >> qexistsl_tac [`w2n dw`, `n`] >>
  simp[typed_copy_mcopy_state_frame]
QED

Theorem store_bytestring_checked_post:
  compile_store_bytestring src dst sa = ((),sb) /\
  is_bytestring_type ty /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size len /\
  32 + 32 * word_size len <= type_memory_size tv ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all buffer_store_bytestring_run >> strip_tac >>
  drule_all store_bytestring_mem_ok >> strip_tac >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  `compile_store_memory ARB src dst ty ty sa = ((),sb)` by
    simp[compile_store_memory_def, is_bytestring_word_type] >>
  drule aggregate_store_memory_no_gas >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  conj_tac
  >- (simp[typed_copy_state_frame_def] >> conj_tac
      >- gvs[venom_state_component_equality] >>
      conj_tac >- gvs[lookup_var_def] >>
      irule typed_copy_frame_subinterval >>
      qexistsl_tac [`w2n d`, `32 + 32 * word_size len`] >>
      simp[typed_copy_frame_def] >> conj_tac
      >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
      simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
           arithmeticTheory.MAX_DEF]) >>
  qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]
QED

Theorem typed_copy_checked_bytestring_entry:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  evaluate_type tenv dty = SOME dtv /\
  evaluate_type tenv sty = SOME stv /\
  value_has_type dtv v /\ value_has_type stv v ==>
  typed_copy_checked_entry cenv ctx dty sty dtv stv v
Proof
  strip_tac >> simp[typed_copy_checked_entry_def] >> rpt strip_tac >>
  `?len. mload (w2n sw) s = n2w len /\
     val_footprint dtv v = 32 + len /\
     32 + len <= 32 * (1 + word_size len) /\
     32 * (1 + word_size len) <= type_memory_size stv /\
     32 * (1 + word_size len) <= type_memory_size dtv` by
    metis_tac[immutable_bytestring_runtime_extent] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> simp[] >>
     qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> simp[]) >>
  `compile_store_bytestring src dst sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_store_memory_typed_bytes]) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `32 + 32 * word_size len < dimword (:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   val_footprint dtv v <= 32 + 32 * word_size len /\
   32 + 32 * word_size len <= type_memory_size dtv` by decide_tac >>
  `val_wf dtv v` by metis_tac[value_has_type_memory_wf] >>
  drule_all store_bytestring_checked_post >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[gas_marked_path_def]
QED

Theorem typed_copy_emit_op_checked:
  emit_op opc args a = (op,b) /\
  opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc /\
  run_inst_seq_mem_ok (emitted_insts a b) s /\
  (!out. step_inst_base (mk_inst a.cs_next_id opc args [out]) s =
         OK (update_var out w s)) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  `run_inst_seq (emitted_insts a b) s =
     OK (update_var (STRING #"%" (toString a.cs_next_var)) w s)` by
    (qpat_x_assum `!out. step_inst_base _ s = _`
       (qspec_then `STRING #"%" (toString a.cs_next_var)` mp_tac) >>
     simp[mk_inst_def, run_inst_seq_def]) >>
  `gas_path_mem ctx func s 0
       (OK ((update_var (STRING #"%" (toString a.cs_next_var)) w s)
             with vs_inst_idx := LENGTH b.cs_current_insts)) /\
   alloca_history func ((update_var (STRING #"%" (toString a.cs_next_var)) w s)
             with vs_inst_idx := LENGTH b.cs_current_insts) /\
   ~(update_var (STRING #"%" (toString a.cs_next_var)) w s).vs_halted /\
   (update_var (STRING #"%" (toString a.cs_next_var)) w s).vs_current_bb = b.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `a` >>
     gvs[mk_inst_def, venomInstTheory.is_terminator_def]) >>
  qexists_tac `(update_var (STRING #"%" (toString a.cs_next_var)) w s)
             with vs_inst_idx := LENGTH b.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_update_var, typed_copy_state_frame_def,
       update_var_def, lookup_var_def, venom_state_component_equality,
       same_blocks_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString a.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem typed_copy_control_emit_op_checked:
  emit_op opc args a = (op,b) /\
  (opc = ADD \/ opc = MUL \/ opc = LT \/ opc = GT \/ opc = ISZERO) /\
  (!out. step_inst_base (mk_inst a.cs_next_id opc args [out]) s =
         OK (update_var out w s)) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule typed_copy_emit_op_checked >> simp[] >>
  (conj_tac
   >- (qexistsl_tac [`args`, `opc`] >> gvs[is_terminator_def]) >>
   irule emit_op_mem_ok >> goal_assum (drule_at Any) >>
  gvs[inst_mem_below_frontier_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, inst_dload_in_section_def, mk_inst_def])
QED

Theorem typed_copy_assign_checked:
  emit_inst ASSIGN [op] [counter] a = ((),b) /\
  eval_operand op s = SOME w /\ fn_has_code a b func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      lookup_var counter t = SOME w /\ t.vs_memory = s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. x <> counter ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
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
  `run_inst_seq_mem_ok (emitted_insts a b) s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def, mk_inst_def]) >>
  `gas_path_mem ctx func s 0
       (OK ((update_var counter w s) with vs_inst_idx := LENGTH b.cs_current_insts)) /\
   alloca_history func ((update_var counter w s) with vs_inst_idx := LENGTH b.cs_current_insts) /\
   ~(update_var counter w s).vs_halted /\
   (update_var counter w s).vs_current_bb = b.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `a` >>
     gvs[mk_inst_def, is_terminator_def]) >>
  qexists_tac `(update_var counter w s) with vs_inst_idx := LENGTH b.cs_current_insts` >>
  simp[lookup_var_update_var, update_var_def, lookup_var_def,
       venom_state_component_equality, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[same_blocks_def]
QED

Theorem typed_copy_counter_init_checked:
  emit_inst ASSIGN [Lit 0w] [counter] a = ((),b) /\
  (!x. not_fresh_at a x ==> x <> counter) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      lookup_var counter t = SOME 0w /\ t.vs_memory = s.vs_memory /\
      typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all typed_copy_assign_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
  gvs[venom_state_component_equality] >> metis_tac[]
QED

Theorem typed_copy_two_ops_checked:
  emit_op opc1 args1 a = (op1,b) /\ emit_op opc2 args2 b = (op2,c) /\
  (opc1 = ADD \/ opc1 = MUL \/ opc1 = LT \/ opc1 = GT \/ opc1 = ISZERO) /\
  (opc2 = ADD \/ opc2 = MUL \/ opc2 = LT \/ opc2 = GT \/ opc2 = ISZERO) /\
  (!out. step_inst_base (mk_inst a.cs_next_id opc1 args1 [out]) s =
         OK (update_var out w1 s)) /\
  (!t out. eval_operand op1 t = SOME w1 /\
     t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t ==>
     step_inst_base (mk_inst b.cs_next_id opc2 args2 [out]) t =
     OK (update_var out w2 t)) /\
  fn_has_code a c func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand op1 t = SOME w1 /\ eval_operand op2 t = SOME w2 /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c` by metis_tac[typed_copy_emit_op_mono] >>
  `cs_extends a b /\ cs_extends b c` by gvs[ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func` by metis_tac[fn_has_code_split] >>
  qpat_assum `emit_op opc1 _ _ = _`
    (mp_then Any mp_tac typed_copy_control_emit_op_checked) >>
  disch_then (qspecl_then [`w1`, `s`, `off`, `len`, `func`, `ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  qpat_assum `emit_op opc2 _ _ = _`
    (mp_then Any mp_tac typed_copy_control_emit_op_checked) >>
  disch_then (qspecl_then [`w2`, `t`, `off`, `len`, `func`, `ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `eval_operand op1 t' = SOME w1` by
    metis_tac[typed_copy_state_frame_operand, typed_copy_emit_op_fresh] >>
  `typed_copy_state_frame a off len s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `b` >> simp[]) >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[]
QED

Theorem typed_copy_header_checked:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  eval_operand length s = SOME (n2w N) /\ k <= N /\ N < dimword (:256) /\
  fn_has_code a c func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand done t = SOME (if k < N then 0w else 1w) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `k < dimword (:256)` by decide_tac >>
  `?t. gas_path_mem ctx func s 0 (OK t) /\
       eval_operand lt t = SOME (bool_to_word (k < N)) /\
       eval_operand done t = SOME (bool_to_word (bool_to_word (k < N) = 0w)) /\
       t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
       ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
       t.vs_inst_idx = LENGTH c.cs_current_insts /\
       alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule typed_copy_two_ops_checked >> simp[] >>
     qexistsl_tac [`[Var counter; length]`, `[lt]`, `b`, `LT`, `ISZERO`] >>
     simp[] >> conj_tac
     >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
             eval_operand_def, w2n_n2w, LESS_MOD] >>
     rpt strip_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_pure1_def]) >>
  qexists_tac `t` >> Cases_on `k < N` >> gvs[bool_to_word_def]
QED

Theorem typed_copy_branch_checked:
  emit_inst JNZ [test; Label yes; Label no] [] a = ((),b) /\
  fn_has_code a b func /\ eval_operand test s = SOME w /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_path_mem ctx func s 0 (OK (jump_to (if w = 0w then no else yes) s)) /\
  alloca_history func (jump_to (if w = 0w then no else yes) s)
Proof
  strip_tac >> conj_tac
  >- (drule_all place_copy_emit_instruction >> strip_tac >>
      `gas_path_mem ctx func s 0
         (OK (jump_to (if w <> 0w then yes else no) s))` by
        (irule for_range_jnz_zero_path_mem >> simp[] >>
         qexistsl_tac [`a.cs_next_id`, `test`] >> simp[]) >>
      Cases_on `w = 0w` >> gvs[]) >>
  irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `s` >> simp[]
QED

Theorem typed_copy_counter_increment_checked:
  emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
  emit_inst ASSIGN [inc] [counter] b = ((),c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  k + 1 < dimword (:256) /\
  fn_has_code a c func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      lookup_var counter t = SOME (n2w (k + 1)) /\
      t.vs_memory = s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at a x /\ x <> counter ==>
           lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_inst, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b c` by gvs[ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func` by metis_tac[fn_has_code_split] >>
  qpat_assum `emit_op _ _ _ = _`
    (mp_then Any mp_tac typed_copy_control_emit_op_checked) >>
  disch_then (qspecl_then [`n2w (k+1)`, `s`, `0`, `0`, `func`, `ctx`] mp_tac) >>
  (impl_tac >- simp[step_inst_base_def, mk_inst_def,
                       exec_pure2_def, eval_operand_def, word_add_n2w]) >> strip_tac >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  drule_all typed_copy_assign_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  qpat_x_assum `typed_copy_state_frame a _ _ s t` mp_tac >>
  simp[typed_copy_state_frame_def] >> strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem typed_copy_index_offsets_checked:
  emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  fn_has_code a c func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand so t = SOME (n2w (k * ss)) /\
      eval_operand doff t = SOME (n2w (k * ds)) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule typed_copy_two_ops_checked >> simp[] >>
  qexistsl_tac [`[Var counter; Lit (n2w ss)]`, `[Var counter; Lit (n2w ds)]`,
               `b`, `MUL`, `MUL`] >>
  simp[] >> conj_tac
  >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operand_def, word_mul_n2w] >>
  rpt strip_tac >>
  `lookup_var counter t = SOME (n2w k)` by gvs[typed_copy_state_frame_def] >>
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, word_mul_n2w]
QED

Theorem typed_copy_index_adds_checked:
  emit_op ADD [src;so] a = (sp,b) /\
  emit_op ADD [dst;doff] b = (dp,c) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. doff = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand so s = SOME sv /\ eval_operand doff s = SOME dv /\
  fn_has_code a c func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand sp t = SOME (sw + sv) /\
      eval_operand dp t = SOME (dw + dv) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule typed_copy_two_ops_checked >> simp[] >>
  qexistsl_tac [`[src;so]`, `[dst;doff]`, `b`, `ADD`, `ADD`] >>
  simp[] >> conj_tac
  >- simp[step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  rpt strip_tac >>
  `eval_operand dst t = SOME dw /\ eval_operand doff t = SOME dv` by
    metis_tac[typed_copy_state_frame_operand] >>
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def]
QED

Theorem typed_copy_jump_checked:
  emit_inst JMP [Label target] [] a = ((),b) /\ fn_has_code a b func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_path_mem ctx func s 0 (OK (jump_to target s)) /\
  alloca_history func (jump_to target s)
Proof
  strip_tac >> conj_tac
  >- (drule_all place_copy_emit_instruction >> strip_tac >>
      irule for_range_jump_at_zero_path_mem >> simp[] >>
      simp[mk_inst_def, is_terminator_def, step_inst_base_def,
           inst_mem_below_frontier_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `s` >> simp[]
QED

Theorem typed_copy_index_addresses_checked:
  emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code a e func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand sp t = SOME (sw + n2w (k * ss)) /\
      eval_operand dp t = SOME (dw + n2w (k * ds)) /\
      t.vs_memory = s.vs_memory /\ typed_copy_state_frame a off len s t /\
      ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
      t.vs_inst_idx = LENGTH e.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono a c /\ ci_mono c e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends a c /\ cs_extends c e` by gvs[ci_mono_def] >>
  `fn_has_code a c func /\ fn_has_code c e func` by metis_tac[fn_has_code_split] >>
  drule_all typed_copy_index_offsets_checked >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `!x. dst = Var x ==> not_fresh_at c x` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  `!x. doff = Var x ==> not_fresh_at c x` by
    metis_tac[typed_copy_emit_op_fresh] >>
  `alloca_inv t` by
    (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
         typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  drule_all typed_copy_index_adds_checked >>
  disch_then (qspecl_then [`off`, `len`, `ctx`] strip_assume_tac) >>
  `typed_copy_state_frame a off len s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> simp[] >>
     irule typed_copy_state_frame_mono >> qexists_tac `c` >> simp[]) >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[]
QED
