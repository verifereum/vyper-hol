Theory regularWriteEmitSim
Ancestors
  regularCallEmitSim regularMemorySim emitSim asmOpSim instSimHelpers
  spillSim stackOpSim stackModel codegenRel list rich_list arithmetic
  venomState asmSem planSpillBounds strongPrefixSim venomExecSemantics
  stackPlanGen contextCodegenRel asmIR byte venomInst vfmState vfmExecution

(* Restrict the related stacks, allowing a source step that preserves vars. *)
Theorem plan_stack_rel_pop_vars:
  plan_stack_rel lo vs stk astk /\ vs'.vs_vars = vs.vs_vars ==>
  plan_stack_rel lo vs' (stack_pop n stk) (DROP n astk)
Proof
  strip_tac >>
  `!op. operand_val vs' lo op = operand_val vs lo op` by
    (Cases >> simp[operand_val_def]) >>
  Cases_on `n <= LENGTH stk`
  >- (simp[stack_pop_def, plan_stack_rel_def] >>
      drule_all plan_stack_rel_pop >> simp[plan_stack_rel_def]) >>
  `LENGTH stk = LENGTH astk` by fs[plan_stack_rel_def] >>
  `LENGTH astk - n = 0` by decide_tac >>
  simp[stack_pop_def, DROP_LENGTH_TOO_LONG]
QED

Theorem matched_write_venom_asm_rel:
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  (LENGTH bytes = 0 \/ off + LENGTH bytes <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= off) /\
  (!i. read_byte i am' =
    if off <= i /\ i < off + LENGTH bytes then EL (i - off) bytes
    else read_byte i st.as_memory) ==>
  venom_asm_rel lo (ps with ps_stack := stack_pop n ps.ps_stack)
    (write_memory_with_expansion off bytes vs)
    (asm_next (st with <|as_stack := DROP n st.as_stack; as_memory := am'|>))
Proof
  strip_tac >>
  `plan_stack_rel lo (write_memory_with_expansion off bytes vs)
     (stack_pop n ps.ps_stack) (DROP n st.as_stack)` by
    (irule plan_stack_rel_pop_vars >> qexists_tac `vs` >>
     fs[venom_asm_rel_def, write_memory_with_expansion_def]) >>
  `!op. operand_val (write_memory_with_expansion off bytes vs) lo op =
        operand_val vs lo op` by
    (Cases >> simp[operand_val_def, write_memory_with_expansion_def]) >>
  `plan_spill_rel lo (write_memory_with_expansion off bytes vs)
     ps.ps_spilled am'` by
    (irule plan_spill_rel_matched_write_frame >>
     qexistsl_tac [`ps.ps_alloc`, `st.as_memory`, `LENGTH bytes`, `off`, `vs`] >>
     simp[] >>
     fs[venom_asm_rel_def, plan_slots_bounded_def, alloc_slots_bounded_def] >>
     metis_tac[]) >>
  `memory_rel ps.ps_alloc
    (write_memory_with_expansion off bytes vs).vs_memory am'` by
    (rw[memory_rel_def, read_byte_write_memory_with_expansion] >>
     fs[venom_asm_rel_def, memory_rel_def]) >>
  gvs[venom_asm_rel_def, asm_next_def, write_memory_with_expansion_def]
QED

(* Expansion szn may include an additional source interval (MCOPY). *)
Theorem read_byte_expanded_write:
  off + LENGTH bytes <= expn ==>
  read_byte i
    (TAKE off (asm_expand_memory expn mem) ++ bytes ++
     DROP (off + LENGTH bytes) (asm_expand_memory expn mem)) =
  if off <= i /\ i < off + LENGTH bytes then EL (i - off) bytes
  else read_byte i mem
Proof
  strip_tac >>
  `off + LENGTH bytes <= LENGTH (asm_expand_memory expn mem)` by
    (irule LESS_EQ_TRANS >> qexists_tac `expn` >> simp[]) >>
  simp[read_byte_overwrite, read_byte_expand]
QED

Theorem mstore_arranged_emit_sim:
  inst.inst_opcode = MSTORE /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "MSTORE" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def,
       AllCaseEqs()] >> strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [aop; vop]` >>
  rename1 `operand_val vs lo aop = SOME addr` >>
  rename1 `operand_val vs lo vop = SOME value` >>
  `eval_operands [aop; vop] vs = SOME [addr; value]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  `w2n addr + 32 <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n addr` by
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, fixed_source_write_range_def]) >>
  `mstore (w2n addr) value vs =
   write_memory_with_expansion (w2n addr) (word_to_bytes value T) vs` by
    simp[mstore_def, write_memory_with_expansion_def, LENGTH_word_to_bytes,
         fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  qexists_tac `asm_next (st with <|as_stack := DROP 2 st.as_stack;
    as_memory := TAKE (w2n addr) (asm_expand_memory (w2n addr + 32) st.as_memory) ++
      word_to_bytes value T ++
      DROP (w2n addr + 32) (asm_expand_memory (w2n addr + 32) st.as_memory)|>)` >>
  (conj_tac >-
    (simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_mstore_def] >>
     qpat_assum `st.as_stack = _` (fn th => once_rewrite_tac [th]) >> simp[])) >>
  (conj_tac >- simp[asm_next_def]) >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  qpat_assum `mstore _ _ _ = _` (fn th => rewrite_tac [th]) >>
  irule matched_write_venom_asm_rel >>
  simp[LENGTH_word_to_bytes,
    fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  (conj_tac >- (gen_tac >>
    irule (SRULE [LENGTH_word_to_bytes,
      fcpLib.INDEX_CONV ``dimindex(:256)``]
      (Q.INST [`bytes` |-> `word_to_bytes (value:bytes32) T`] read_byte_expanded_write)) >> simp[])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem mstore8_arranged_emit_sim:
  inst.inst_opcode = MSTORE8 /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "MSTORE8" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def,
       AllCaseEqs()] >> strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [aop; vop]` >>
  rename1 `operand_val vs lo aop = SOME addr` >>
  rename1 `operand_val vs lo vop = SOME value` >>
  `eval_operands [aop; vop] vs = SOME [addr; value]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  `w2n addr + 1 <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n addr` by
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, fixed_source_write_range_def]) >>
  `mstore8 (w2n addr) value vs =
   write_memory_with_expansion (w2n addr) [w2w value : word8] vs` by
    simp[mstore8_def, write_memory_with_expansion_def] >>
  qexists_tac `asm_next (st with <|as_stack := DROP 2 st.as_stack;
    as_memory := TAKE (w2n addr) (asm_expand_memory (w2n addr + 1) st.as_memory) ++
      [w2w value : word8] ++
      DROP (w2n addr + 1) (asm_expand_memory (w2n addr + 1) st.as_memory)|>)` >>
  (conj_tac >-
    (simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_mstore8_def] >>
     qpat_assum `st.as_stack = _` (fn th => once_rewrite_tac [th]) >> simp[])) >>
  (conj_tac >- simp[asm_next_def]) >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  qpat_assum `mstore8 _ _ _ = _` (fn th => rewrite_tac [th]) >>
  irule matched_write_venom_asm_rel >> simp[] >>
  (conj_tac >- (gen_tac >>
    irule (SRULE [] (Q.INST [`bytes` |-> `[w2w (value:bytes32) : word8]`]
      read_byte_expanded_write)) >> simp[])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem sstore_arranged_emit_sim:
  inst.inst_opcode = SSTORE /\ venom_asm_rel lo ps vs st /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "SSTORE" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def,
       AllCaseEqs()] >> strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [kop; vop]` >>
  rename1 `operand_val vs lo kop = SOME key` >>
  rename1 `operand_val vs lo vop = SOME value` >>
  `eval_operands [kop; vop] vs = SOME [key; value]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  `plan_stack_rel lo (sstore key value vs)
    (stack_pop 2 ps.ps_stack) (DROP 2 st.as_stack)` by
    (irule plan_stack_rel_pop_vars >> qexists_tac `vs` >>
     fs[venom_asm_rel_def, sstore_def]) >>
  qexists_tac `asm_next (st with <|as_stack := DROP 2 st.as_stack;
    as_accounts := (sstore key value vs).vs_accounts|>)` >>
  (conj_tac >-
    (simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_sstore_def] >>
     qpat_assum `st.as_stack = _` (fn th => once_rewrite_tac [th]) >>
     fs[venom_asm_rel_def, sstore_def, update_account_def])) >>
  simp[asm_next_def] >>
  gvs[venom_asm_rel_def, sstore_def, plan_spill_rel_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!op off. FLOOKUP _ op = SOME off ==> _` drule >>
  Cases_on `op` >> simp[operand_val_def]
QED

Theorem tstore_arranged_emit_sim:
  inst.inst_opcode = TSTORE /\ venom_asm_rel lo ps vs st /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "TSTORE" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def,
       AllCaseEqs()] >> strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [kop; vop]` >>
  rename1 `operand_val vs lo kop = SOME key` >>
  rename1 `operand_val vs lo vop = SOME value` >>
  `eval_operands [kop; vop] vs = SOME [key; value]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  `plan_stack_rel lo (tstore key value vs)
    (stack_pop 2 ps.ps_stack) (DROP 2 st.as_stack)` by
    (irule plan_stack_rel_pop_vars >> qexists_tac `vs` >>
     fs[venom_asm_rel_def, tstore_def]) >>
  qexists_tac `asm_next (st with <|as_stack := DROP 2 st.as_stack;
    as_transient := (tstore key value vs).vs_transient|>)` >>
  (conj_tac >-
    (simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_tstore_def] >>
     qpat_assum `st.as_stack = _` (fn th => once_rewrite_tac [th]) >>
     fs[venom_asm_rel_def, tstore_def, lookup_transient_storage_def,
        update_transient_storage_def])) >>
  simp[asm_next_def] >>
  gvs[venom_asm_rel_def, tstore_def, plan_spill_rel_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!op off. FLOOKUP _ op = SOME off ==> _` drule >>
  Cases_on `op` >> simp[operand_val_def]
QED

Theorem read_byte_sized_write:
  LENGTH bytes = szn ==>
  read_byte i
    (TAKE off (if szn = 0 then mem else asm_expand_memory (off + szn) mem) ++
     bytes ++ DROP (off + szn)
       (if szn = 0 then mem else asm_expand_memory (off + szn) mem)) =
  if off <= i /\ i < off + LENGTH bytes then EL (i - off) bytes
  else read_byte i mem
Proof
  strip_tac >> Cases_on `szn = 0` >> gvs[] >>
  irule read_byte_expanded_write >> simp[]
QED

Theorem padded_copy_slice:
  TAKE szn (DROP soff (if szn = 0 then src
    else asm_expand_memory (soff + szn) src)) =
  TAKE szn (DROP soff src ++ REPLICATE szn (0w:byte))
Proof
  Cases_on `szn = 0` >> simp[expanded_slice_padded_range,
    venom_returndata_read_byte]
QED

Theorem copy_to_mem_venom_asm_rel:
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  st.as_stack = dst :: srcOff :: sz :: DROP 3 st.as_stack /\
  (w2n sz = 0 \/ w2n dst + w2n sz <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n dst) ==>
  ?ab. asm_copy_to_mem src st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo (ps with ps_stack := stack_pop 3 ps.ps_stack)
      (write_memory_with_expansion (w2n dst)
        (TAKE (w2n sz) (DROP (w2n srcOff) src ++ REPLICATE (w2n sz) 0w)) vs) ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `asm_next (st with <|as_stack := DROP 3 st.as_stack;
    as_memory :=
      TAKE (w2n dst) (if w2n sz = 0 then st.as_memory
        else asm_expand_memory (w2n dst + w2n sz) st.as_memory) ++
      TAKE (w2n sz) (DROP (w2n srcOff) src ++ REPLICATE (w2n sz) 0w) ++
      DROP (w2n dst + w2n sz) (if w2n sz = 0 then st.as_memory
        else asm_expand_memory (w2n dst + w2n sz) st.as_memory)|>)` >>
  (conj_tac >-
    (simp[asm_copy_to_mem_def] >>
     qpat_assum `st.as_stack = _` (fn th => once_rewrite_tac [th]) >>
     Cases_on `sz = 0w` >>
     simp[expanded_slice_padded_range, venom_returndata_read_byte])) >>
  (conj_tac >- simp[asm_next_def]) >>
  irule matched_write_venom_asm_rel >>
  simp[LENGTH_TAKE_EQ] >>
  (conj_tac >- (gen_tac >>
    irule (SRULE [LENGTH_TAKE_EQ] (Q.INST
      [`szn` |-> `w2n (sz:bytes32)`,
       `bytes` |-> `TAKE (w2n (sz:bytes32))
         (DROP (w2n (srcOff:bytes32)) src ++ REPLICATE (w2n sz) (0w:byte))`]
      read_byte_sized_write)) >> simp[LENGTH_TAKE_EQ])) >>
  (conj_tac >- (Cases_on `sz = 0w` >> gvs[])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem calldatacopy_arranged_emit_sim:
  inst.inst_opcode = CALLDATACOPY /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "CALLDATACOPY" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [dop; sop; zop]` >>
  rename1 `operand_val vs lo dop = SOME dst` >>
  rename1 `operand_val vs lo sop = SOME srcOff` >>
  rename1 `operand_val vs lo zop = SOME sz` >>
  `eval_operands [dop; sop; zop] vs = SOME [dst; srcOff; sz]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  `st.as_call_ctx = vs.vs_call_ctx` by fs[venom_asm_rel_def] >>
  simp[NoAsms, asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
    asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
    asm_step_extcall_def, asm_step_copy_def] >>
  qpat_assum `st.as_call_ctx = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule copy_to_mem_venom_asm_rel >> simp[] >>
  (conj_tac >-
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, sized_source_write_range_def])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem codecopy_arranged_emit_sim:
  inst.inst_opcode = CODECOPY /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "CODECOPY" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [dop; sop; zop]` >>
  rename1 `operand_val vs lo dop = SOME dst` >>
  rename1 `operand_val vs lo sop = SOME srcOff` >>
  rename1 `operand_val vs lo zop = SOME sz` >>
  `eval_operands [dop; sop; zop] vs = SOME [dst; srcOff; sz]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  `st.as_code = vs.vs_code` by fs[venom_asm_rel_def] >>
  simp[NoAsms, asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
    asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
    asm_step_extcall_def, asm_step_copy_def] >>
  qpat_assum `st.as_code = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule copy_to_mem_venom_asm_rel >> simp[] >>
  (conj_tac >-
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, sized_source_write_range_def])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem extcodecopy_to_mem_venom_asm_rel:
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  st.as_stack = addr :: dst :: srcOff :: sz :: DROP 4 st.as_stack /\
  (w2n sz = 0 \/ w2n dst + w2n sz <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n dst) ==>
  ?ab. asm_extcodecopy st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo (ps with ps_stack := stack_pop 4 ps.ps_stack)
      (write_memory_with_expansion (w2n dst)
        (TAKE (w2n sz) (DROP (w2n srcOff)
          (lookup_account (w2w addr) vs.vs_accounts).code ++
          REPLICATE (w2n sz) 0w)) vs) ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `st.as_accounts = vs.vs_accounts` by fs[venom_asm_rel_def] >>
  simp[asm_extcodecopy_def] >>
  qpat_assum `st.as_stack = _` (fn th => once_rewrite_tac [th]) >>
  `TAKE (w2n sz) (DROP (w2n srcOff)
     (if sz = 0w then (lookup_account (w2w addr) vs.vs_accounts).code
      else asm_expand_memory (w2n srcOff + w2n sz)
        (lookup_account (w2w addr) vs.vs_accounts).code)) =
   TAKE (w2n sz) (DROP (w2n srcOff)
     (lookup_account (w2w addr) vs.vs_accounts).code ++ REPLICATE (w2n sz) 0w)` by
    (Cases_on `sz = 0w` >> simp[expanded_slice_padded_range,
      venom_returndata_read_byte]) >>
  simp[] >>
  (conj_tac >- simp[asm_next_def]) >>
  irule matched_write_venom_asm_rel >>
  simp[LENGTH_TAKE_EQ] >>
  (conj_tac >- (gen_tac >>
    irule (SRULE [LENGTH_TAKE_EQ] (Q.INST
      [`szn` |-> `w2n (sz:bytes32)`,
       `bytes` |-> `TAKE (w2n (sz:bytes32))
         (DROP (w2n (srcOff:bytes32))
           (lookup_account (w2w (addr:bytes32)) vs.vs_accounts).code ++
          REPLICATE (w2n sz) (0w:byte))`]
      read_byte_sized_write)) >> simp[LENGTH_TAKE_EQ])) >>
  (conj_tac >- (Cases_on `sz = 0w` >> gvs[])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem extcodecopy_arranged_emit_sim:
  inst.inst_opcode = EXTCODECOPY /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "EXTCODECOPY" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [aop; dop; sop; zop]` >>
  rename1 `operand_val vs lo aop = SOME addr` >>
  rename1 `operand_val vs lo dop = SOME dst` >>
  rename1 `operand_val vs lo sop = SOME srcOff` >>
  rename1 `operand_val vs lo zop = SOME sz` >>
  `eval_operands [aop; dop; sop; zop] vs = SOME [addr; dst; srcOff; sz]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  simp[NoAsms, asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
    asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
    asm_step_extcall_def, asm_step_copy_def] >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule extcodecopy_to_mem_venom_asm_rel >> simp[] >>
  (conj_tac >-
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, sized_source_write_range_def])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem returndatacopy_as_copy_to_mem:
  st.as_stack = dst :: srcOff :: sz :: tail /\
  w2n srcOff + w2n sz <= LENGTH st.as_returndata ==>
  asm_returndatacopy st = asm_copy_to_mem st.as_returndata st
Proof
  strip_tac >>
  simp[asm_returndatacopy_def, asm_copy_to_mem_def] >>
  Cases_on `sz = 0w` >>
  simp[expanded_slice_padded_range] >>
  rewrite_tac[GSYM (SRULE [ADD_COMM] venom_returndata_read_byte)] >>
  `w2n sz <= LENGTH (DROP (w2n srcOff) st.as_returndata)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  simp[TAKE_APPEND1]
QED

Theorem returndatacopy_arranged_emit_sim:
  inst.inst_opcode = RETURNDATACOPY /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "RETURNDATACOPY" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [dop; sop; zop]` >>
  rename1 `operand_val vs lo dop = SOME dst` >>
  rename1 `operand_val vs lo sop = SOME srcOff` >>
  rename1 `operand_val vs lo zop = SOME sz` >>
  `eval_operands [dop; sop; zop] vs = SOME [dst; srcOff; sz]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  `st.as_returndata = vs.vs_returndata` by fs[venom_asm_rel_def] >>
  `asm_returndatacopy st = asm_copy_to_mem st.as_returndata st` by
    (irule returndatacopy_as_copy_to_mem >>
     qexistsl_tac [`dst`, `srcOff`, `sz`, `DROP 3 st.as_stack`] >> simp[]) >>
  `TAKE (w2n sz) (DROP (w2n srcOff) vs.vs_returndata) =
   TAKE (w2n sz) (DROP (w2n srcOff) vs.vs_returndata ++ REPLICATE (w2n sz) 0w)` by
    (sym_tac >> irule TAKE_APPEND1 >> simp[LENGTH_DROP] >> decide_tac) >>
  simp[NoAsms, asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
    asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
    asm_step_extcall_def, asm_step_copy_def] >>
  qpat_assum `asm_returndatacopy st = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `st.as_returndata = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `TAKE _ _ = _` (fn th => once_rewrite_tac [th]) >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule copy_to_mem_venom_asm_rel >> simp[] >>
  (conj_tac >-
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, sized_source_write_range_def])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem mcopy_to_mem_venom_asm_rel:
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  st.as_stack = dst :: srcOff :: sz :: DROP 3 st.as_stack /\
  (w2n sz = 0 \/ w2n dst + w2n sz <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n dst) /\
  (w2n sz = 0 \/ w2n srcOff + w2n sz <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n srcOff) ==>
  ?ab. asm_mcopy st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo (ps with ps_stack := stack_pop 3 ps.ps_stack)
      (mcopy (w2n dst) (w2n srcOff) (w2n sz) vs) ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `TAKE (w2n sz) (DROP (w2n srcOff)
     (if w2n sz = 0 then st.as_memory else asm_expand_memory
       (MAX (w2n srcOff + w2n sz) (w2n dst + w2n sz)) st.as_memory)) =
   TAKE (w2n sz) (DROP (w2n srcOff) vs.vs_memory ++ REPLICATE (w2n sz) 0w)` by
    (Cases_on `sz = 0w` >- simp[] >>
     drule_at (Pat `venom_asm_rel _ _ _ _`) (iffLR venom_asm_rel_def) >>
     strip_tac >>
     drule_all memory_rel_mcopy_source_slice >>
     disch_then (qspec_then `w2n dst` mp_tac) >>
     simp[expanded_slice_padded_range, venom_returndata_read_byte, MAX_DEF]) >>
  gnvs[] >> simp[asm_mcopy_def] >>
  qpat_assum `st.as_stack = _` (fn th => once_rewrite_tac [th]) >>
  simp[] >>
  (conj_tac >- simp[asm_next_def]) >>
  simp[NoAsms, mcopy_def] >>
  irule matched_write_venom_asm_rel >>
  simp[LENGTH_TAKE_EQ] >>
  (conj_tac >- (gen_tac >> Cases_on `sz = 0w` >- simp[] >>
    simp[] >>
    irule (SRULE [LENGTH_TAKE_EQ] (Q.INST
      [`bytes` |-> `TAKE (w2n (sz:bytes32))
         (DROP (w2n (srcOff:bytes32)) vs.vs_memory ++ REPLICATE (w2n sz) (0w:byte))`]
      read_byte_expanded_write)) >> simp[MAX_DEF])) >>
  (conj_tac >- (Cases_on `sz = 0w` >> gvs[])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem mcopy_arranged_emit_sim:
  inst.inst_opcode = MCOPY /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  EVERY (\(off,len). len = 0 \/ off + len <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc "MCOPY" st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `inst.inst_operands = [dop; sop; zop]` >>
  rename1 `operand_val vs lo dop = SOME dst` >>
  rename1 `operand_val vs lo sop = SOME srcOff` >>
  rename1 `operand_val vs lo zop = SOME sz` >>
  `eval_operands [dop; sop; zop] vs = SOME [dst; srcOff; sz]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  simp[NoAsms, asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
    asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
    asm_step_extcall_def, asm_step_copy_def] >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule mcopy_to_mem_venom_asm_rel >> simp[] >>
  (conj_tac >-
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, sized_source_write_range_def])) >>
  (conj_tac >-
    (qpat_x_assum `EVERY _ (source_memory_read_ranges _ _)` mp_tac >>
     simp[source_memory_read_ranges_def])) >>
  qexists_tac `sb` >> simp[]
QED

Theorem write_arranged_emit_sim:
    MEM inst.inst_opcode [MSTORE; MSTORE8; MCOPY; SSTORE; TSTORE;
      CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY] /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
    ps.ps_stack = residual ++ compute_operands inst /\
    EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
    (!op. MEM op (compute_operands inst) ==>
      eval_operand op vs = operand_val vs lo op) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps.ps_alloc.sa_spill_base \/
      ps.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
    inst_memory_safe ps.ps_alloc inst vs vs' /\
    step_inst fuel ctx inst vs = OK vs' ==>
      ?ab. asm_step_op o2pc name st = AsmOK ab /\
        ab.as_pc = st.as_pc + 1 /\
        venom_asm_rel lo
          (ps with ps_stack :=
             stack_pop (LENGTH (compute_operands inst)) ps.ps_stack) vs' ab
Proof
  pure_rewrite_tac [MEM] >> strip_tac >>
  gvs[venom_to_evm_name_def] >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th])
  >- (irule mstore_arranged_emit_sim >> metis_tac[])
  >- (irule mstore8_arranged_emit_sim >> metis_tac[])
  >- (irule mcopy_arranged_emit_sim >>
      qpat_x_assum `EVERY _ (source_memory_read_ranges _ _)` mp_tac >>
      simp_tac (srw_ss()) [ADD_COMM] >> strip_tac >> metis_tac[])
  >- (irule sstore_arranged_emit_sim >> metis_tac[])
  >- (irule tstore_arranged_emit_sim >> metis_tac[])
  >- (irule calldatacopy_arranged_emit_sim >> metis_tac[])
  >- (irule returndatacopy_arranged_emit_sim >> metis_tac[])
  >- (irule codecopy_arranged_emit_sim >> metis_tac[])
  >> irule extcodecopy_arranged_emit_sim >> metis_tac[]
QED
