Theory bodyWidenedCopyPrimitive
Ancestors
  bodyWidenedCopyPath placeMemoryTypedPrimitive externalReturnNormalizeMem
  fragGasSeqMem fragGasMode fragExec compileEnv venomState venomInst
  emitHelper context valueCopy list rich_list exprLoweringProps fragExecMem
  venomExecSemantics valueEncoding valueEncodingDefs valueEncodingProps
  placeMemoryTypedBase immutableMemoryFrame ASCIInumbers finite_map
  valueEncodingProofs exprSimProps loweringStateRelDefs exprSimBufferStore
  valueCopyBytes placeMemoryDynarrayForward instMemFrontier emitHelperProps

Theorem straight_line_zero_gas_path_mem:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  EVERY (\i. i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK u /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path T ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
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

Theorem compile_copy_memory_checked_sequence:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\
  (n = 0 \/ w2n sw + n <= s.vs_alloca_next) /\
  (n = 0 \/ w2n dw + n <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `n` >>
  simp[compile_copy_memory_def, comp_return_def] >> strip_tac
  >- gvs[emitted_insts_def, run_inst_seq_mem_ok_def] >>
  drule allocaFootprintTheory.emit_mcopy_mem_ok >>
  disch_then irule >>
  simp[eval_operand_def, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD]
QED

Theorem compile_copy_memory_path_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\
  (n = 0 \/ w2n sw + n <= s.vs_alloca_next) /\
  (n = 0 \/ w2n dw + n <= s.vs_alloca_next) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path T ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
       with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all compile_copy_memory_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_copy_memory_checked_sequence >>
     qexistsl_tac [`dst`, `dw`, `n`, `src`, `sw`] >> simp[]) >>
  irule straight_line_zero_gas_path_mem >> simp[] >>
  qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
  gvs[same_blocks_def]
QED

Theorem compile_copy_memory_forward_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\
  (n = 0 \/ w2n sw + n <= s.vs_alloca_next) /\
  (n = 0 \/ w2n dw + n <= s.vs_alloca_next) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      mem_bytes_at (w2n dw) n t.vs_memory = mem_bytes_at (w2n sw) n s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + n <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_tac >>
  `gas_marked_path T ctx func s 0
     (OK ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
       with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule compile_copy_memory_path_mem >> metis_tac[]) >>
  qpat_x_assum `_ /\ _` (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_copy_memory_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  qexists_tac `(if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
       with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  Cases_on `n = 0`
  >- (gvs[valueEncodingDefsTheory.mem_bytes_at_def, lookup_var_def] >>
      simp[venom_state_component_equality]) >>
  gvs[] >> simp[mcopy_mem_bytes_at_same, mcopy_memory_length] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def,
          venom_state_component_equality] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem typed_memory_word_forward_mem:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME tv /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\
  w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all typed_memory_word_sequence >> strip_tac >>
  drule_all typed_copy_word_mem_ok >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK u` >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path_mem >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 tv v` by
    metis_tac[val_in_memory_word] >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >>
  `val_in_memory tv v (w2n dw) u.vs_memory` by
    (qspecl_then [`tenv`, `dty`, `tv`, `v`] mp_tac val_in_memory_word >>
     simp[] >> disch_then (fn th => rewrite_tac[th]) >>
     simp[Abbr `u`, mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]) >>
  simp[] >> rpt conj_tac
  >- simp[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def,
          venom_state_component_equality]
  >- (rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
      simp[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def,
           lookup_var_def, FLOOKUP_UPDATE])
  >- simp[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def]
  >- (rpt strip_tac >>
      `s.vs_memory = (update_var (STRING #"%" (toString sa.cs_next_var))
         (mload (w2n sw) s) s).vs_memory` by simp[update_var_def] >>
      simp[Abbr `u`] >> metis_tac[mstore_mem_bytes_at_disjoint])
  >- simp[Abbr `u`, immutable_mstore_capacity, update_var_def, arithmeticTheory.MAX_DEF] >>
  simp[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem store_bytestring_forward_mem:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mem_word_at (w2n sw) s.vs_memory = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      t.vs_memory =
        (mcopy (w2n dw) (w2n sw) (32 + 32 * word_size len) s).vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all store_bytestring_run_exact >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `mload (w2n sw) s = n2w len` by
    simp[GSYM mem_word_at_eq_mload] >>
  drule_all store_bytestring_mem_ok >> strip_tac >>
  `compile_store_memory cenv src dst (BaseT (BytesT (Dynamic 1)))
     (BaseT (BytesT (Dynamic 1))) sa = ((),sb)` by
    simp[compile_store_memory_def, is_word_type_def, is_bytestring_type_def] >>
  drule placeMemoryPrimitiveForwardTheory.compile_store_memory_same_type_no_gas >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path_mem >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb,z.vs_allocas)`) >>
     simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def] >>
  qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
    (mp_tac o Q.AP_TERM `\z. z with vs_inst_idx := s.vs_inst_idx`) >>
  simp[] >> metis_tac[lookup_var_def]
QED

Theorem typed_memory_bytestring_frontier_forward_mem:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `~is_word_type dty` by metis_tac[is_bytestring_word_type] >>
  `compile_store_bytestring src dst sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def]) >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> metis_tac[]) >>
  `val_store_size stv v = val_store_size dtv v` by
    (irule bytestring_val_store_size_eq >> metis_tac[]) >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  `val_store_size stv v <= type_memory_size stv /\
   val_store_size dtv v <= type_memory_size dtv` by
    metis_tac[val_store_size_le] >>
  `32 + 32 * word_size len < dimword (:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next` by decide_tac >>
  `mem_word_at (w2n sw) s.vs_memory = n2w len` by
    simp[mem_word_at_eq_mload] >>
  drule_all store_bytestring_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> rpt conj_tac
  >- (irule mcopy_val_in_memory >> simp[] >>
      gvs[val_footprint_le_store_size])
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mcopy_memory_length]
QED
Theorem typed_memory_bytestring_forward_mem:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule_all typed_memory_bytestring_frontier_forward_mem >> simp[]
QED


Theorem typed_memory_sarray_fast_frontier_forward_mem:
  ~is_abi_dynamic cenv.ce_struct_fields det /\
  type_widens_to tenv (ArrayT src_et (Fixed m)) (ArrayT det (Fixed n)) /\
  compile_copy_sarray_typed cenv dst det src src_et n sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv (ArrayT src_et (Fixed m)) = SOME stv /\
  evaluate_type tenv (ArrayT det (Fixed n)) = SOME dtv /\
  val_wf dtv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv (ArrayT det (Fixed n)) = type_memory_size dtv /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ArrayT src_et (Fixed m) = ArrayT det (Fixed n)` by
    (irule (INST_TYPE [``:'a`` |-> ``:string``, ``:'b`` |-> ``:num``]
              typed_memory_static_widening) >> conj_tac
     >- (qexists_tac `cenv.ce_struct_fields` >> simp[is_abi_dynamic_def]) >>
     qexists_tac `tenv` >> simp[]) >>
  gvs[] >>
  `compile_copy_memory dst src (type_memory_size dtv) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def] >>
     gvs[type_memory_bytes_def]) >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule compile_copy_memory_forward_mem >> simp[] >>
  disch_then (drule_at Any) >> simp[] >>
  disch_then (qspecl_then [`func`, `ctx`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  irule valueEncodingPropsTheory.val_in_memory_relocate >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `type_memory_size dtv`, `w2n sw`] >> simp[]
QED
Theorem typed_memory_sarray_fast_forward_mem:
  ~is_abi_dynamic cenv.ce_struct_fields det /\
  type_widens_to tenv (ArrayT src_et (Fixed m)) (ArrayT det (Fixed n)) /\
  compile_copy_sarray_typed cenv dst det src src_et n sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv (ArrayT src_et (Fixed m)) = SOME stv /\
  evaluate_type tenv (ArrayT det (Fixed n)) = SOME dtv /\
  val_wf dtv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv (ArrayT det (Fixed n)) = type_memory_size dtv /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule_all typed_memory_sarray_fast_frontier_forward_mem >> simp[]
QED


Theorem typed_memory_dynarray_data_checked:
  (do data_sz <- emit_op MUL [length; Lit (n2w stride)];
      compile_copy_memory_dynamic dst src data_sz
   od) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w n) /\ n * stride < dimword (:256) /\
  (n * stride = 0 \/ w2n sw + n * stride <= s.vs_alloca_next) /\
  (n * stride = 0 \/ w2n dw + n * stride <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!w t. eval_operand src (update_var (STRING #"%" (toString sa.cs_next_var)) w t) = eval_operand src t /\
         eval_operand dst (update_var (STRING #"%" (toString sa.cs_next_var)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[compile_copy_memory_dynamic_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, run_inst_seq_mem_ok_cons,
       below_frontier_no_ranges, mk_inst_def, step_inst_base_opcode_eqs,
       exec_pure2_def, eval_operand_def, lookup_var_update_var,
       wordsTheory.word_mul_n2w] >>
  simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last, below_frontier_MCOPY,
       eval_operand_def, lookup_var_update_var, wordsTheory.word_mul_n2w,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rewrite_tac[GSYM update_var_def] >> simp[]
QED

Theorem typed_memory_dynarray_setup_checked:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok];
      emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next ==>
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
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_APPEND] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_MLOAD, below_frontier_MSTORE, below_frontier_no_ranges,
       mk_inst_def, step_inst_base_opcode_eqs,
       exec_read1_def, exec_write2_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, toString_inj] >>
  simp[mstore_def, write_memory_with_expansion_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem typed_memory_dynarray_setup_forward_mem:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok];
      emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      eval_operand length t = SOME (n2w n) /\
      eval_operand src_data t = SOME (sw + 32w) /\
      eval_operand dst_data t = SOME (dw + 32w) /\
      t.vs_memory = (mstore (w2n dw) (n2w n) s).vs_memory /\
      mem_word_at (w2n dw) t.vs_memory = n2w n /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_dynarray_setup_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule typed_memory_dynarray_setup_checked >> metis_tac[]) >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path_mem >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, mstore_mem_word_at_same] >>
  rpt conj_tac
  >- (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      simp[venom_state_component_equality])
  >- metis_tac[lookup_var_def]
  >- metis_tac[mstore_mem_bytes_at_disjoint]
  >> simp[immutable_mstore_capacity, arithmeticTheory.MAX_DEF]
QED

Theorem typed_memory_dynarray_data_forward_mem:
  (do data_sz <- emit_op MUL [length; Lit (n2w stride)];
      compile_copy_memory_dynamic dst src data_sz
   od) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w n) /\ n * stride < dimword (:256) /\
  (n * stride = 0 \/ w2n sw + n * stride <= s.vs_alloca_next) /\
  (n * stride = 0 \/ w2n dw + n * stride <= s.vs_alloca_next) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      mem_bytes_at (w2n dw) (n * stride) t.vs_memory =
        mem_bytes_at (w2n sw) (n * stride) s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + n * stride <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_memory_dynarray_data_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule typed_memory_dynarray_data_checked >> metis_tac[]) >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path_mem >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def, mcopy_mem_bytes_at_same] >> rpt conj_tac
  >- (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      simp[venom_state_component_equality])
  >- metis_tac[lookup_var_def]
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mcopy_memory_length]
QED

Theorem typed_memory_dynarray_fast_bytes_forward_mem:
  compile_copy_dynarray_typed cenv dst et cap src et sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) /\
  n * type_memory_bytes cenv et < dimword (:256) /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  w2n sw + 32 + n * type_memory_bytes cenv et <= s.vs_alloca_next /\
  w2n dw + 32 + n * type_memory_bytes cenv et <= s.vs_alloca_next /\
  (w2n sw + 32 + n * type_memory_bytes cenv et <= w2n dw \/
   w2n dw + 32 <= w2n sw) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      mem_word_at (w2n dw) t.vs_memory = n2w n /\
      mem_bytes_at (w2n dw + 32) (n * type_memory_bytes cenv et) t.vs_memory =
        mem_bytes_at (w2n sw + 32) (n * type_memory_bytes cenv et) s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/
               w2n dw + 32 + n * type_memory_bytes cenv et <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule typed_memory_dynarray_fast_split >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (gvs[fn_has_code_def, same_blocks_def, emitted_blocks_def] >>
     metis_tac[IS_PREFIX_TRANS]) >>
  `w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all typed_memory_dynarray_setup_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path T ctx func s 0 (OK mid)` >>
  `w2n (sw + 32w) = w2n sw + 32 /\ w2n (dw + 32w) = w2n dw + 32` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `mid.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  `n MOD dimword (:256) = n` by simp[arithmeticTheory.LESS_MOD] >>
  drule typed_memory_dynarray_data_forward_mem >>
  disch_then (drule_at Any) >> simp[] >>
  disch_then (qspecl_then [`n`, `func`, `ctx`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.LESS_MOD] >> decide_tac)) >> strip_tac >>
  rename1 `gas_marked_path T ctx func mid 0 (OK t)` >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  conj_tac
  >- (`mem_bytes_at (w2n dw) 32 t.vs_memory =
         mem_bytes_at (w2n dw) 32 mid.vs_memory` by simp[] >>
      gvs[mem_word_at_def, mem_bytes_at_def]) >>
  conj_tac
  >- (`mem_bytes_at (w2n sw + 32) (n * type_memory_bytes cenv et) mid.vs_memory =
         mem_bytes_at (w2n sw + 32) (n * type_memory_bytes cenv et) s.vs_memory` by
        (first_assum irule >> simp[] >> decide_tac) >> gvs[]) >>
  conj_tac
  >- (qpat_x_assum `_ = mid` mp_tac >>
      qpat_x_assum `_ = s` mp_tac >>
      simp[venom_state_component_equality] >> metis_tac[]) >>
  reverse conj_tac
  >- (gvs[] >> decide_tac) >>
  rpt strip_tac >>
  `mem_bytes_at a len t.vs_memory = mem_bytes_at a len mid.vs_memory` by
    (simp[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `mem_bytes_at a len mid.vs_memory = mem_bytes_at a len s.vs_memory` by
    (first_assum irule >> simp[] >> decide_tac) >> simp[]
QED

Theorem typed_memory_dynarray_fast_forward_mem:
  compile_copy_dynarray_typed cenv dst et cap src et sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  value_has_type (ArrayTV tv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV tv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n sw) s.vs_memory /\
  type_memory_bytes cenv et = type_memory_size tv /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  LENGTH vs * type_memory_size tv < dimword (:256) /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  w2n sw + type_memory_size (ArrayTV tv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  (w2n sw + type_memory_size (ArrayTV tv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= w2n sw) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/
               w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH vs <= scap` by metis_tac[typed_memory_dynarray_length] >>
  `LENGTH vs * type_memory_size tv <= scap * type_memory_size tv /\
   LENGTH vs * type_memory_size tv <= cap * type_memory_size tv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[val_in_memory_dynarray, mem_word_at_eq_mload] >>
  Q.SUBGOAL_THEN
    `w2n sw + 32 + LENGTH vs * type_memory_bytes cenv et <= w2n dw \/
     w2n dw + 32 <= w2n sw` assume_tac
  >- (qpat_x_assum `w2n sw + type_memory_size _ <= _ \/ _` mp_tac >>
      simp[type_memory_size_def] >> decide_tac) >>
  `LENGTH vs * type_memory_bytes cenv et < dimword (:256)` by simp[] >>
  `w2n sw + 32 + LENGTH vs * type_memory_bytes cenv et <= s.vs_alloca_next /\
   w2n dw + 32 + LENGTH vs * type_memory_bytes cenv et <= s.vs_alloca_next` by
    (qpat_x_assum `w2n sw + type_memory_size _ <= s.vs_alloca_next` mp_tac >>
     qpat_x_assum `w2n dw + type_memory_size _ <= s.vs_alloca_next` mp_tac >>
     pure_rewrite_tac[type_memory_size_def] >>
     asm_rewrite_tac[] >> decide_tac) >>
  drule_all typed_memory_dynarray_fast_bytes_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  conj_tac
  >- (simp[val_in_memory_dynarray] >>
      irule (cj 3 valueEncodingProofsTheory.val_in_memory_relocate_proof) >>
      conj_tac >- gvs[val_wf_def] >>
      qexistsl_tac [`w2n sw + 32`, `s.vs_memory`] >>
      gvs[val_in_memory_dynarray, val_wf_def]) >>
  conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  rpt gen_tac >> disch_tac >> first_x_assum irule >>
  qpat_x_assum `_ \/ _` mp_tac >>
  simp[type_memory_size_def] >> decide_tac
QED
