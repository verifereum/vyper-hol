(* Memory-free result clamp and memory checks for the extract32 suffix. *)
Theory bodyMemTbExtract32Load
Ancestors
  bodyMemTbExtract32Source bodyMemTbExtract32MemoryTransfer builtinBytesMemory fragGasSeqMem fragGasSeqAbort fragExecMem
  varsExt freshWrites instMemFrontier exprLowering exprLoweringProps compileEnv emitHelper
  emitHelperProps unitTransformDefs contextCodegenRel codegenRel memSafeRun
  venomState venomInst list rich_list

Theorem extract32_clamp_footprint[local]:
  !v ty sa op sb.
    compile_clamp_basetype v ty sa = (op,sb) ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_ext_call_op i.inst_opcode /\ !s. inst_mem_below_frontier i s /\ inst_dload_in_section i s)
      (emitted_insts sa sb)
Proof
  recInduct compile_clamp_basetype_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[compile_clamp_basetype_def, clamp_and_return_def, compile_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >>
  gvs[type_bounds_def, is_signed_type_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def, mk_inst_def, is_terminator_def,
       is_ext_call_op_def]
QED

Theorem extract32_clamp_mem_ok[local]:
  compile_clamp_basetype v ty sa = (op,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_every >>
  drule extract32_clamp_footprint >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem extract32_load_straight_line[local]:
  compile_extract32_load l d off sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_ext_call_op i.inst_opcode /\
      ((!s. inst_mem_below_frontier i s /\ inst_dload_in_section i s) \/
       ?id addr out. i = mk_inst id MLOAD [addr] [out]))
    (emitted_insts sa sb)
Proof
  strip_tac >>
  Cases_on `compile_assert_slice_bounds off (Lit 32w) l sa` >>
  rename1 `compile_assert_slice_bounds off (Lit 32w) l sa = (u,sc)` >>
  Cases_on `u` >>
  drule builtinBytesMemoryTheory.slice_bounds_shape >> strip_tac >>
  gvs[builtinBytesTheory.compile_extract32_load_def, comp_bind_def,
      comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def,
      emit_def, comp_return_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def] >>
  metis_tac[mk_inst_def]
QED

Theorem extract32_suffix_mem_ok[local]:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand l s = SOME len /\ eval_operand d s = SOME data /\
  eval_operand off s = SOME start /\
  w2n data + w2n len <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb) s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_append >> conj_tac
  >- (rpt strip_tac >> irule extract32_clamp_mem_ok >> metis_tac[]) >>
  irule compile_extract32_load_mem_ok >> metis_tac[]
QED

Theorem extract32_suffix_safe_gas_paths:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  code = emitted_insts sa sc ++ emitted_insts sc sb /\
  run_inst_seq_mem_ok code s /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  (!t. run_inst_seq code s = OK t ==>
    gas_path_mem ctx func s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))) /\
  (!a t. run_inst_seq code s = Abort a t ==>
    ?n j. gas_path_mem ctx func s n (Abort a (t with vs_inst_idx := j)))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     code` by
    (qpat_x_assum `code = _` (fn th => rewrite_tac[th]) >>
     simp[EVERY_APPEND] >> conj_tac
     >- (drule extract32_load_straight_line >> simp[EVERY_MEM] >> metis_tac[]) >>
     drule extract32_clamp_footprint >> simp[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule run_inst_seq_gas_path_mem >> metis_tac[]) >>
  rpt strip_tac >>
  drule_all (run_inst_seq_abort_gas_path |> Q.SPEC `T` |> SIMP_RULE (srw_ss())
    [fragGasModeTheory.gas_marked_path_def]) >> simp[]
QED

Theorem extract32_suffix_total_mem_transfer[local]:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  vars_ext s big /\
  ((?t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t) \/
   (?a t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = Abort a t)) /\
  run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb) s ==>
  run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb) big
Proof
  strip_tac >> drule extract32_load_straight_line >>
  drule extract32_clamp_footprint >> rpt strip_tac >>
  (irule run_inst_seq_mem_ok_total_vars_ext >> conj_tac
   >- (rpt gen_tac >> strip_tac >>
       fs[EVERY_MEM, MEM_APPEND] >>
       first_x_assum drule >> strip_tac >>
       gvs[] >> metis_tac[mload_total_vars_ext_frontier]) >>
   conj_tac
   >- (fs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
   qexists_tac `s` >> metis_tac[])
QED

Theorem extract32_suffix_separated_mem_ok:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  (!x. l = Var x \/ d = Var x \/ off = Var x ==> not_fresh_at sa x) /\
  eval_operand l s = SOME len /\ eval_operand d s = SOME data /\
  eval_operand off s = SOME start /\
  w2n data + w2n len <= s.vs_alloca_next /\
  ((?t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb)
          (drop_fresh sa s) = OK t) \/
   (?a t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb)
          (drop_fresh sa s) = Abort a t)) ==>
  run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb) s
Proof
  strip_tac >>
  `eval_operand l (drop_fresh sa s) = SOME len /\
   eval_operand d (drop_fresh sa s) = SOME data /\
   eval_operand off (drop_fresh sa s) = SOME start` by
    simp[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `w2n data + w2n len <= (drop_fresh sa s).vs_alloca_next` by
    simp[drop_fresh_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb)
     (drop_fresh sa s)` by
    (irule extract32_suffix_mem_ok >> metis_tac[]) >>
  (irule extract32_suffix_total_mem_transfer >> conj_tac
   >- metis_tac[] >>
   qexists_tac `drop_fresh sa s` >> simp[vars_ext_drop_fresh] >> metis_tac[])
QED

Theorem extract32_suffix_gas_paths:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  code = emitted_insts sa sc ++ emitted_insts sc sb /\
  fresh_vars_wrt sa s /\
  eval_operand l s = SOME len /\ eval_operand d s = SOME data /\
  eval_operand off s = SOME start /\
  w2n data + w2n len <= s.vs_alloca_next /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  (!t. run_inst_seq code s = OK t ==>
    gas_path_mem ctx func s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))) /\
  (!a t. run_inst_seq code s = Abort a t ==>
    ?n j. gas_path_mem ctx func s n (Abort a (t with vs_inst_idx := j)))
Proof
  strip_tac >> irule extract32_suffix_safe_gas_paths >>
  `run_inst_seq_mem_ok code s` by
    (gvs[] >> irule extract32_suffix_mem_ok >> metis_tac[]) >>
  metis_tac[]
QED
