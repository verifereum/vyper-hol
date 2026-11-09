(* Bounded primitive paths used by recursive place copies. *)
Theory placeTypedCopyPrimitiveMem
Ancestors
  placeTypedCopyMem placeMemoryTypedPrimitive placeMemoryCopyEffect
  bodyCopyMemory bodyDeclMemoryCounted fragGasPathMem fragGasMode
  valueEncodingProps venomState venomExecSemantics context compileEnv
  exprLoweringProps fragExec list rich_list
  placeMemoryFieldsForward externalReturnNormalizeMem
  stmtForRangeMemoryParts fragGasSeqMem placeMemoryArrayControl
  instMemFrontier memSafeRun venomInst venomExecProofs emitHelperProps emitHelper
  valueCopy bodyDeclMemoryCore placeMemoryPrimitiveForward valueCopyBytes

Theorem compile_copy_memory_path_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all compile_copy_memory_sequence >> strip_tac >>
  drule_all compile_copy_memory_body_mem_ok >> strip_tac >>
  irule body_decl_zero_gas_path >>
  conj_tac >- simp[] >> qexists_tac `sa` >> simp[] >> fs[EVERY_MEM]
QED

Theorem compile_copy_memory_effect_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_effect ctx func sa sb s t (w2n dw) n /\
    mem_bytes_at (w2n dw) n t.vs_memory =
      mem_bytes_at (w2n sw) n s.vs_memory
Proof
  strip_tac >> drule_all compile_copy_memory_path_mem >> strip_tac >>
  qexists_tac `(if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule_all compile_copy_memory_sequence >> simp[same_blocks_def]) >>
  `gas_marked_path F ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[gas_path_mem_exec, gas_marked_path_def] >>
  simp[typed_copy_effect_def] >> Cases_on `n = 0`
  >- gvs[valueEncodingTheory.mem_bytes_at_def, lookup_var_def,
         venom_state_component_equality] >>
  simp[mcopy_mem_bytes_at_same, mcopy_memory_length] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def,
          venom_state_component_equality] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem compile_with_byte_offset_path_mem:
  compile_with_byte_offset op off sa = (out_op,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand out_op t = SOME (w + n2w off) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all compile_with_byte_offset_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule normalize_byte_offset_mem_ok >> simp[]) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> conj_tac >- simp[] >>
     qexists_tac `sa` >> simp[] >> fs[EVERY_MEM]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- (qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  metis_tac[lookup_var_def]
QED

Theorem typed_memory_prefix_jump_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = prefix ++ [term] /\
  s.vs_inst_idx + LENGTH prefix = k /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
  EVERY (\i. i.inst_opcode <> GAS) prefix /\
  run_inst_seq prefix s = OK u /\ run_inst_seq_mem_ok prefix s /\
  is_terminator term.inst_opcode /\ term.inst_opcode <> INVOKE /\
  term.inst_opcode <> GAS /\
  inst_mem_below_frontier term (u with vs_inst_idx := k) /\
  inst_dload_in_section term (u with vs_inst_idx := k) /\
  step_inst_base term (u with vs_inst_idx := k) =
    OK (jump_to lbl (u with vs_inst_idx := k)) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to lbl (u with vs_inst_idx := k)))
Proof
  strip_tac >>
  `isPREFIX prefix (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `FILTER (\i. i.inst_opcode = GAS) prefix = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[EVERY_MEM]) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := k))` by
    (drule_all run_inst_seq_gas_path_mem >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (conj_tac >> irule run_inst_seq_preserves_field >>
     qexists_tac `prefix` >> simp[] >> rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (qpat_x_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `i` mp_tac) >> simp[]) >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all venomInstProofsTheory.step_preserves_halted >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  `DROP k bb.bb_instructions = [term]` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP (LENGTH prefix)`) >>
     pure_rewrite_tac[DROP_DROP_T] >>
     `LENGTH prefix + s.vs_inst_idx = k` by decide_tac >> simp[DROP_APPEND]) >>
  `k < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP k _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_DROP]) >>
  `get_instruction bb k = SOME term` by
    (simp[venomInstTheory.get_instruction_def] >>
     qpat_x_assum `DROP k _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  `gas_path_mem ctx func (u with vs_inst_idx := k) 0
     (OK (jump_to lbl (u with vs_inst_idx := k)))` by
    (irule for_range_jump_at_zero_path_mem >> gvs[]) >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem typed_memory_array_init_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ASSIGN [Lit 0w] [counter]; mk_inst id2 JMP [Label hdr] []] ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr ((update_var counter 0w s) with
                     vs_inst_idx := s.vs_inst_idx + 1)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_path_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, eval_operand_def,
       fragExecMemTheory.run_inst_seq_mem_ok_def, inst_dload_in_section_def,
       below_frontier_no_ranges] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem typed_memory_array_backedge_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  lookup_var counter s = SOME (n2w i) /\ SUC i < dimword (:256) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) s)) with
        vs_inst_idx := s.vs_inst_idx + 2)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_path_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, wordsTheory.word_add_n2w, arithmeticTheory.ADD1,
       fragExecMemTheory.run_inst_seq_mem_ok_def, inst_dload_in_section_def,
       below_frontier_no_ranges] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem typed_memory_array_condition_path_mem:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  eval_operand (Var counter) s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_path_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_update_var,
       fragExecMemTheory.run_inst_seq_mem_ok_def, inst_dload_in_section_def,
       below_frontier_no_ranges] >>
  `i < dimword (:256)` by decide_tac >> gvs[eval_operand_def] >>
  Cases_on `i < N` >>
  simp[bool_to_word_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
       lookup_var_update_var, below_frontier_no_ranges] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem typed_memory_array_addresses_mem_ok[local]:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      comp_return (sp,dp)
   od) sa = ((sp,dp),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  irule fragExecMemTheory.run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def,
       inst_dload_in_section_def] >> rpt conj_tac >> rpt gen_tac >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem typed_memory_array_addresses_path_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_array_addresses_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule typed_memory_array_addresses_mem_ok >> simp[]) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> conj_tac >- simp[] >>
     qexists_tac `sa` >> simp[] >> fs[EVERY_MEM]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- (qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  metis_tac[lookup_var_def]
QED

Theorem compile_store_memory_nonword_path_mem:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\ ~is_word_type ty /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  w2n sw + val_store_size tv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size tv)
Proof
  strip_tac >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `(if is_word_type ty then sw = typed_val_to_w256 tv v
    else val_in_memory tv v (w2n sw) s.vs_memory)` by simp[] >>
  drule_all compile_store_memory_run_capacity >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (`!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
     drule_all body_typed_store_memory_mem_ok >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (drule compile_store_memory_same_type_no_gas >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> conj_tac >- simp[] >>
     qexists_tac `sa` >> simp[] >> fs[EVERY_MEM]) >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[gas_path_mem_exec, gas_marked_path_def] >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[typed_copy_effect_def] >>
  gvs[venom_state_component_equality] >>
  fs[lookup_var_def] >> first_assum ACCEPT_TAC
QED

Theorem typed_memory_bytestring_path_mem:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\ value_has_type stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)
Proof
  strip_tac >>
  `~is_word_type dty` by metis_tac[is_bytestring_word_type] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> simp[] >>
     qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> simp[]) >>
  `val_store_size stv v = val_store_size dtv v` by
    (irule bytestring_val_store_size_eq >> metis_tac[]) >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, compile_store_memory_def]) >>
  irule compile_store_memory_nonword_path_mem >> simp[] >> metis_tac[]
QED
