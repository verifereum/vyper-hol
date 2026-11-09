(* Bounded execution of array-copy setup and traversal. *)
Theory placeTypedCopyArrayMem
Ancestors
  placeTypedCopyPrimitiveMem placeMemoryArrayForward placeMemoryDynarrayForward
  immutableMemoryFrame placeTypedFieldsMem freshWrites
  bodyDeclMemoryCounted fragGasPathMem fragExecMem instMemFrontier
  venomState venomExecSemantics venomInst context compileEnv emitHelper
  emitHelperProps exprLoweringProps valueEncodingProps list rich_list
  ASCIInumbers finite_map memSafeRun placeMemoryCopyEffect valueCopy placeMemoryTypedPrimitive

Theorem typed_memory_dynarray_data_mem_ok[local]:
  (do data_sz <- emit_op MUL [length; Lit (n2w stride)];
      compile_copy_memory_dynamic dst src data_sz
   od) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w n) /\ n * stride < dimword (:256) /\
  w2n sw + n * stride <= s.vs_alloca_next /\
  w2n dw + n * stride <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!w t. eval_operand src (update_var (STRING #"%" (toString sa.cs_next_var)) w t) = eval_operand src t /\
         eval_operand dst (update_var (STRING #"%" (toString sa.cs_next_var)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[compile_copy_memory_dynamic_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, run_inst_seq_mem_ok_def,
       mk_inst_def, below_frontier_no_ranges, inst_dload_in_section_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       wordsTheory.word_mul_n2w] >>
  simp[GSYM mk_inst_def, GSYM update_var_def, below_frontier_MCOPY,
       eval_operand_def, lookup_var_update_var,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem typed_memory_dynarray_data_path_mem:
  (do data_sz <- emit_op MUL [length; Lit (n2w stride)];
      compile_copy_memory_dynamic dst src data_sz
   od) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w n) /\ n * stride < dimword (:256) /\
  w2n sw + n * stride <= s.vs_alloca_next /\
  w2n dw + n * stride <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      t.vs_memory = (mcopy (w2n dw) (w2n sw) (n * stride) s).vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (n * stride)
Proof
  strip_tac >> drule_all typed_memory_dynarray_data_sequence >> strip_tac >>
  drule_all typed_memory_dynarray_data_mem_ok >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> conj_tac >- simp[] >>
     qexists_tac `sa` >> simp[] >> fs[EVERY_MEM]) >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[gas_path_mem_exec, fragGasModeTheory.gas_marked_path_def] >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[typed_copy_effect_def] >>
  gvs[venom_state_component_equality] >>
  simp[mcopy_memory_length] >> conj_tac
  >- (fs[lookup_var_def] >> metis_tac[]) >>
  rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED

Theorem typed_memory_dynarray_setup_mem_ok[local]:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long]; emit_void ASSERT [ok];
      emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\
  w2n dw + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!k w t. sa.cs_next_var <= k ==>
     eval_operand src (update_var (STRING #"%" (toString k)) w t) = eval_operand src t /\
     eval_operand dst (update_var (STRING #"%" (toString k)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((_,_,_),sb)` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1] >>
  simp[run_inst_seq_mem_ok_def, below_frontier_MLOAD, mk_inst_def,
       inst_dload_in_section_def, step_inst_base_opcode_eqs, exec_read1_def] >>
  simp[GSYM update_var_def, eval_operand_def, lookup_var_update_var,
       exec_pure1_def, exec_pure2_def, toString_inj] >>
  simp[GSYM mk_inst_def, below_frontier_MSTORE, below_frontier_no_ranges,
       inst_dload_in_section_def, eval_operand_def, lookup_var_update_var,
       update_var_def, toString_inj] >>
  Cases_on `w2n (mload (w2n sw) s) > cap MOD dimword (:256)` >> simp[] >>
  simp[GSYM update_var_def, eval_operand_def, lookup_var_update_var,
       toString_inj, exec_write2_def, step_inst_base_opcode_eqs,
       mk_inst_def, mstore_def, write_memory_with_expansion_def] >>
  `!x k. (src = Var x \/ dst = Var x) /\ sa.cs_next_var <= k ==>
     x <> STRING #"%" (toString k)` by metis_tac[not_fresh_at_def] >>
  `!x. not_fresh_at sa x ==>
     STRING #"%" (toString sa.cs_next_var) <> x /\
     STRING #"%" (toString (sa.cs_next_var + 1)) <> x /\
     STRING #"%" (toString (sa.cs_next_var + 2)) <> x /\
     STRING #"%" (toString (sa.cs_next_var + 3)) <> x /\
     STRING #"%" (toString (sa.cs_next_var + 4)) <> x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  Cases_on `dst` >> Cases_on `src` >>
  gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem typed_memory_dynarray_setup_path_mem:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long]; emit_void ASSERT [ok];
      emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) /\
  w2n sw + 32 <= s.vs_alloca_next /\
  w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand length t = SOME (n2w n) /\
      eval_operand src_data t = SOME (sw + 32w) /\
      eval_operand dst_data t = SOME (dw + 32w) /\
      t.vs_memory = (mstore (w2n dw) (n2w n) s).vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) 32
Proof
  strip_tac >> drule_all typed_memory_dynarray_setup_sequence >> strip_tac >>
  drule_all typed_memory_dynarray_setup_mem_ok >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> conj_tac >- simp[] >>
     qexists_tac `sa` >> simp[] >> fs[EVERY_MEM]) >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[gas_path_mem_exec, fragGasModeTheory.gas_marked_path_def] >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[typed_copy_effect_def, eval_operand_def, lookup_var_def] >>
  gvs[venom_state_component_equality] >>
  simp[immutable_mstore_capacity, arithmeticTheory.MAX_DEF] >>
  conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem typed_memory_array_element_forward_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
      doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw + i * type_memory_size stv) s.vs_memory /\
  (w2n sw + i * type_memory_size stv + type_memory_size stv <=
     w2n dw + i * type_memory_size dtv \/
   w2n dw + i * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + i * type_memory_size stv) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv + 64 < dimword (:256) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  fn_has_code sa b4 func /\ fn_has_code b4 b5 func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dp sp a b u dw sw.
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. gas_path_mem ctx func u 0 (OK t) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw + i * type_memory_size dtv) t.vs_memory /\
      typed_copy_effect ctx func sa b5 s t
        (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_memory_array_addresses_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule typed_memory_array_addresses_fresh >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `w2n (sw + n2w (i * type_memory_size stv)) = w2n sw + i * type_memory_size stv /\
   w2n (dw + n2w (i * type_memory_size dtv)) = w2n dw + i * type_memory_size dtv` by
    (`w2n sw + i * type_memory_size stv < dimword (:256) /\
      w2n dw + i * type_memory_size dtv < dimword (:256) /\
      i * type_memory_size stv < dimword (:256) /\
      i * type_memory_size dtv < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `?t. gas_path_mem ctx func u 0 (OK t) /\
       val_in_memory dtv v (w2n (dw + n2w (i * type_memory_size dtv))) t.vs_memory /\
       typed_copy_effect ctx func b4 b5 u t
         (w2n (dw + n2w (i * type_memory_size dtv))) (type_memory_size dtv)` by
    (first_x_assum irule >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> gvs[]) >>
  `typed_copy_effect ctx func sa b4 s u
      (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)` by
    (irule typed_fields_address_effect >> simp[]) >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  conj_tac >- gvs[] >>
  irule typed_copy_effect_then >> qexistsl_tac [`b4`,`b4`,`u`] >>
  gvs[] >> metis_tac[not_fresh_at_mono]
QED
