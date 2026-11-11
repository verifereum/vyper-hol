(* Administrative interfaces for the universal step write footprint.
 * Reuse calleeTransport's setup, merge and output-binding projections and
 * venomInstProofs.step_preserves_control_flow for nonterminator steps.
 *)
Theory stepWriteFootprintBase
Ancestors
  contextRawReachable contextCodegenRel venomExecProofs calleeTransport
  venomInstProofs venomInst regularCallEmitSim codegenRel venomState spillSim
  venomExecSemantics venomCallOracleDefs venomInstProofs3 venomEffects opcodeClass
  venomMemProps contextCodegenRelProps

Theorem raw_reachable_active:
  !vs0 ctx fn inst s.
    raw_reachable vs0 ctx fn inst s ==> active_inst fn inst s
Proof
  ho_match_mp_tac raw_reachable_ind >> simp[]
QED

Theorem enters_block_memory:
  enters_block fn s s1 ==> s1.vs_memory = s.vs_memory
Proof
  rw[enters_block_def] >> drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem adopt_return_fmp_memory[simp]:
  (adopt_return_fmp ir s).vs_memory = s.vs_memory
Proof
  irule adopt_return_fmp_projection >> simp[]
QED

Theorem read_byte_mstore8_outside:
  ~(off <= i /\ i < off + 1) ==>
  read_byte i (mstore8 off value s).vs_memory = read_byte i s.vs_memory
Proof
  `mstore8 off value s =
   write_memory_with_expansion off [w2w value : word8] s` by
    simp[mstore8_def, write_memory_with_expansion_def] >>
  simp[read_byte_write_memory_with_expansion]
QED

Theorem fixed_store_byte_frame:
  (inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8 \/
   inst.inst_opcode = ISTORE) /\
  inst.inst_operands = [dst; value] /\
  step_inst_base inst s = OK t /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
             ~(off <= i /\ i < off + len)) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs, exec_write2_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[source_memory_write_ranges_def, fixed_source_write_range_def] >>
  simp[istore_def] >>
  metis_tac[read_byte_mstore_outside, read_byte_mstore8_outside]
QED

Theorem copy_byte_frame:
  (inst.inst_opcode = MCOPY \/ inst.inst_opcode = CALLDATACOPY \/
   inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = DLOADBYTES \/
   inst.inst_opcode = CODECOPY) /\
  inst.inst_operands = [dst; src; size_op] /\
  step_inst_base inst s = OK t /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
             ~(off <= i /\ i < off + len)) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[source_memory_write_ranges_def, sized_source_write_range_def] >>
  simp[mcopy_def] >> irule write_memory_byte_frame >>
  qexists_tac `w2n (THE (eval_operand size_op s))` >> simp[]
QED

Theorem extcodecopy_byte_frame:
  inst.inst_opcode = EXTCODECOPY /\
  inst.inst_operands = [addr; dst; src; size_op] /\
  step_inst_base inst s = OK t /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
             ~(off <= i /\ i < off + len)) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[source_memory_write_ranges_def, sized_source_write_range_def] >>
  irule write_memory_byte_frame >>
  qexists_tac `w2n (THE (eval_operand size_op s))` >> simp[]
QED

Theorem exec_ext_call_byte_frame:
  exec_ext_call inst s gas addr value ao az ro rz static = OK t /\
  ~(w2n ro <= i /\ i < w2n ro + w2n rz) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  simp[exec_ext_call_def, consume_call_outcome_eq] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def] >>
  irule write_memory_byte_frame >> qexists_tac `w2n rz` >> simp[listTheory.LENGTH_TAKE_EQ]
QED

Theorem extract_venom_result_byte_frame:
  extract_venom_result s output ro rz result = SOME (value,t) /\
  ~(ro <= i /\ i < ro + rz) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >> drule extract_venom_result_memory >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  irule write_memory_byte_frame >> qexists_tac `rz` >>
  simp[listTheory.LENGTH_TAKE_EQ]
QED

Theorem exec_delegatecall_byte_frame:
  exec_delegatecall inst s gas addr ao az ro rz = OK t /\
  ~(w2n ro <= i /\ i < w2n ro + w2n rz) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  simp[exec_delegatecall_def, consume_call_outcome_eq] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def] >>
  irule write_memory_byte_frame >> qexists_tac `w2n rz` >> simp[listTheory.LENGTH_TAKE_EQ]
QED

Theorem exec_create_byte_frame:
  exec_create inst s value off len salt = OK t ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  simp[exec_create_def, AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def] >> drule extract_venom_result_memory >>
  simp[write_memory_with_expansion_def]
QED

Theorem call_byte_frame:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
   inst.inst_opcode = DELEGATECALL) /\
  step_inst_base inst s = OK t /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
             ~(off <= i /\ i < off + len)) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[source_memory_write_ranges_def] >>
  metis_tac[exec_ext_call_byte_frame, exec_delegatecall_byte_frame]
QED

Theorem direct_write_byte_frame:
  (inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8 \/
   inst.inst_opcode = ISTORE \/ inst.inst_opcode = MCOPY \/
   inst.inst_opcode = CALLDATACOPY \/ inst.inst_opcode = RETURNDATACOPY \/
   inst.inst_opcode = DLOADBYTES \/ inst.inst_opcode = CODECOPY \/
   inst.inst_opcode = EXTCODECOPY) /\
  step_inst_base inst s = OK t /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
             ~(off <= i /\ i < off + len)) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >>
  qpat_assum `step_inst_base _ _ = _` (mk_asm "step") >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs, exec_write2_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> asm_x "step" assume_tac
  >~ [`inst.inst_opcode = ISTORE`] >-
    (gvs[source_memory_write_ranges_def, fixed_source_write_range_def] >>
     simp[istore_def] >> metis_tac[read_byte_mstore_outside]) >>
  FIRST [
    (rename1 `inst.inst_operands = [dst; value]` >>
     irule fixed_store_byte_frame >> qexistsl_tac [`dst`, `inst`, `value`]),
    (rename1 `inst.inst_operands = [dop; sop; zop]` >>
     irule copy_byte_frame >> qexistsl_tac [`dop`, `inst`, `zop`, `sop`]),
    (rename1 `inst.inst_operands = [aop; dop; sop; zop]` >>
     irule extcodecopy_byte_frame >>
     qexistsl_tac [`aop`, `dop`, `inst`, `zop`, `sop`])] >>
  simp[istore_def]
QED

Theorem step_inst_base_OK_byte_frame:
  step_inst_base inst s = OK t /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
             ~(off <= i /\ i < off + len)) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >>
  Cases_on `~is_terminator inst.inst_opcode /\
            ~is_alloca_op inst.inst_opcode /\
            Eff_MEMORY NOTIN write_effects inst.inst_opcode`
  >- (fs[] >> drule_all step_inst_base_preserves_memory >> simp[]) >>
  Cases_on `inst.inst_opcode` >>
  fs[is_terminator_def, is_alloca_op_def, write_effects_def,
     empty_effects_def, all_effects_def] >>
  FIRST [
    (irule direct_write_byte_frame >> qexists_tac `inst` >> simp[] >> NO_TAC),
    (irule call_byte_frame >> qexists_tac `inst` >> simp[] >> NO_TAC),
    all_tac] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs(), jump_to_def,
    exec_alloca_def, exec_read1_def, update_var_def] >>
  pairarg_tac >> gvs[]

QED

Theorem pack_dret_dynamic_byte_frame:
  !pairs cursor s ptrs final_cursor t.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,t) /\
    (!off len. MEM (off,len) (dret_source_write_ranges cursor pairs) ==>
               ~(off <= i /\ i < off + len)) ==>
    read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  Induct >> simp[pack_dret_dynamic_def, dret_source_write_ranges_def] >>
  rpt gen_tac >> PairCases_on `h` >> rename1 `(src,sz)` >>
  simp[pack_dret_dynamic_def, dret_source_write_ranges_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  first_x_assum drule >> (impl_tac >- metis_tac[]) >> strip_tac >>
  simp[mcopy_def] >> irule write_memory_byte_frame >>
  qexists_tac `w2n sz` >> simp[] >> metis_tac[]
QED

Theorem step_inst_base_IntRet_byte_frame:
  step_inst_base inst s = IntRet ret t /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
             ~(off <= i /\ i < off + len)) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >> drule step_inst_base_intret_opcodes >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  gvs[source_memory_write_ranges_def] >>
  drule pack_dret_dynamic_byte_frame >> simp[]
QED
