Theory regularReadEmitSim
Ancestors
  regularCallEmitSim regularMemorySim emitSim asmOpSim instSimHelpers
  spillSim stackModel opcodeClass venomWf stackPlanGen asmIR
  venomExecSemantics venomInst asmSem codegenRel contextCodegenRel list rich_list words
  byte cv_std vfmTypes arithmetic fcp divides

Theorem read_outputs_singleton[local]:
  (ef_read0 inst.inst_opcode \/ ef_read1 inst.inst_opcode \/
   inst.inst_opcode = SHA3) /\ inst_wf inst ==>
  ?out. inst.inst_outputs = [out]
Proof
  strip_tac >>
  gvs[ef_read0_def, ef_read1_def, inst_wf_def, LENGTH_EQ_NUM_compute]
QED

Theorem read0_compute_operands[local]:
  ef_read0 inst.inst_opcode /\ inst.inst_operands = [] ==>
  compute_operands inst = []
Proof
  strip_tac >>
  gvs[ef_read0_def, compute_operands_def, python_stack_operands_def,
      ir_specific_operand_order_def]
QED

Theorem read1_compute_operands[local]:
  ef_read1 inst.inst_opcode /\ inst_wf inst ==>
  ?arg. inst.inst_operands = [arg] /\ compute_operands inst = [arg]
Proof
  strip_tac >>
  gvs[ef_read1_def, inst_wf_def, LENGTH_EQ_NUM_compute,
      compute_operands_def, python_stack_operands_def,
      ir_specific_operand_order_def]
QED

Theorem sha3_compute_operands[local]:
  inst.inst_opcode = SHA3 /\ inst_wf inst ==>
  ?off sz. inst.inst_operands = [off; sz] /\
           compute_operands inst = [sz; off]
Proof
  strip_tac >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, compute_operands_def,
      python_stack_operands_def, ir_specific_operand_order_def]
QED

Theorem read0_value_step[local]:
  ef_read0 inst.inst_opcode /\ inst.inst_opcode <> GAS /\
  ~is_pre_codegen_opcode inst.inst_opcode /\
  inst.inst_operands = [] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  venom_asm_rel lo ps vs st /\ step_inst fuel ctx inst vs = OK vs' ==>
  ?out result. inst.inst_outputs = [out] /\
    vs' = update_var out result vs /\
    asm_step_op o2pc name st =
      AsmOK (asm_next (st with as_stack := result :: st.as_stack))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[ef_read0_def, is_pre_codegen_opcode_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read0_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[venom_to_evm_name_def] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def, asm_step_copy_def, asm_step_context_def,
       asm_push_val_def] >>
  fs[venom_asm_rel_def] >>
  qmatch_goalsub_abbrev_tac `update_var out answer vs` >>
  qexists_tac `answer` >> simp[]
QED

Theorem read0_arranged_emit_sim:
  ef_read0 inst.inst_opcode /\ inst.inst_opcode <> GAS /\
  ~is_pre_codegen_opcode inst.inst_opcode /\
  inst.inst_operands = [] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  venom_asm_rel lo ps vs st /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
        EVERY (\out. case op of Var x => x <> out | _ => T)
              inst.inst_outputs) /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc name st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
         (stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
         inst.inst_outputs) vs' ab
Proof
  strip_tac >> drule_all read0_value_step >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  drule_all read0_compute_operands >> strip_tac >>
  gvs[] >>
  `venom_asm_rel lo
     (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))
     (update_var out result vs)
     (asm_next (st with as_stack := result :: DROP 0 st.as_stack))` by
    (irule emit_output_venom_asm_rel >> simp[]) >>
  simp[asm_next_def] >> gvs[asm_next_def]
QED

Theorem read_padded_word32[local]:
  word_of_bytes F (0w:bytes32) (REVERSE (take_pad_0 32 bs)) =
  word_of_bytes T (0w:bytes32) (TAKE 32 (bs ++ REPLICATE 32 0w))
Proof
  `TAKE 32 (bs ++ REPLICATE 32 0w) = take_pad_0 32 bs` by
    (pure_rewrite_tac[take_pad_0_pad_take, PAD_RIGHT,
       REPLICATE_GENLIST, TAKE_APPEND, TAKE_GENLIST] >>
     Cases_on `LENGTH bs < 32` >> simp[MIN_DEF, TAKE_TAKE] >>
     Cases_on `LENGTH bs = 0` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  `divides 8 256` by EVAL_TAC >>
  rewrite_tac[GSYM byteTheory.word_of_bytes_be_def,
              GSYM byteTheory.word_of_bytes_le_def] >>
  simp[cv_stdTheory.word_of_bytes_be_eq_num_of_bytes
         |> INST_TYPE [alpha |-> ``:256``]
         |> REWRITE_RULE [fcpLib.INDEX_CONV ``dimindex(:256)``]
         |> SIMP_RULE (srw_ss()) [EVAL ``divides 8 256``],
       cv_stdTheory.word_of_bytes_le_eq_num_of_bytes
         |> INST_TYPE [alpha |-> ``:256``]
         |> REWRITE_RULE [fcpLib.INDEX_CONV ``dimindex(:256)``]
         |> SIMP_RULE (srw_ss()) [EVAL ``divides 8 256``]] >>
  `TAKE 32 (take_pad_0 32 bs ++ REPLICATE 32 0w) = take_pad_0 32 bs` by
    metis_tac[LENGTH_take_pad_0, TAKE_LENGTH_APPEND] >>
  simp[byteTheory.be_bytes_thm]
QED

Theorem read1_value_step[local]:
  ef_read1 inst.inst_opcode /\ inst.inst_opcode <> MLOAD /\
  inst.inst_opcode <> ILOAD /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  venom_asm_rel lo ps vs st /\ step_inst fuel ctx inst vs = OK vs' ==>
  ?arg value out result. inst.inst_operands = [arg] /\
    eval_operand arg vs = SOME value /\ inst.inst_outputs = [out] /\
    vs' = update_var out result vs /\
    (!rest. st.as_stack = value :: rest ==>
      asm_step_op o2pc name st =
        AsmOK (asm_next (st with as_stack := result :: rest)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[ef_read1_def, venom_to_evm_name_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out answer vs` >>
  qexists_tac `answer` >> simp[] >> rpt strip_tac >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def, asm_step_copy_def, asm_step_context_def,
       asm_state_unop_def] >>
  fs[venom_asm_rel_def, Abbr `answer`] >>
  simp[asm_sload_def, asm_tload_def, venomStateTheory.sload_def,
       venomStateTheory.tload_def, venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmStateTheory.lookup_storage_def, read_padded_word32]
QED

Theorem read1_arranged_emit_sim:
  ef_read1 inst.inst_opcode /\ inst.inst_opcode <> MLOAD /\
  inst.inst_opcode <> ILOAD /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  venom_asm_rel lo ps vs st /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
        EVERY (\out. case op of Var x => x <> out | _ => T)
              inst.inst_outputs) /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc name st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
         (stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
         inst.inst_outputs) vs' ab
Proof
  strip_tac >> drule_all read1_value_step >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  drule_all read1_compute_operands >> strip_tac >> gvs[] >>
  `eval_operands [arg] vs = SOME [value]` by
    simp[venomStateTheory.eval_operands_def] >>
  `st.as_stack = [value] ++ DROP 1 st.as_stack` by
    (irule (arranged_eval_operands_stack |> SPEC_ALL
            |> Q.INST [`operands` |-> `[arg]`]
            |> SIMP_RULE (srw_ss()) []) >>
     qexistsl_tac [`arg`, `lo`, `ps`, `residual`, `vs`] >> simp[]) >>
  `venom_asm_rel lo
     (ps with ps_stack := stack_push (Var out) (stack_pop 1 ps.ps_stack))
     (update_var out result vs)
     (asm_next (st with as_stack := result :: DROP 1 st.as_stack))` by
    (irule emit_output_venom_asm_rel >> simp[]) >>
  qexists_tac `asm_next (st with as_stack := result :: DROP 1 st.as_stack)` >>
  simp[asm_next_def] >> gvs[asm_next_def]
QED

Theorem read_mload_word[local]:
  memory_rel alloc vs.vs_memory am /\
  (off + 32 <= alloc.sa_spill_base \/ alloc.sa_next_offset <= off) ==>
  mload off vs = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP off (asm_expand_memory (off + 32) am)))
Proof
  strip_tac >>
  `mload off vs = word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP off vs.vs_memory))` by
    (simp[venomStateTheory.mload_def, TAKE_APPEND] >>
     irule word_of_bytes_append_zeros >> simp[EVERY_TAKE]) >>
  simp[word_of_bytes_take_drop_expand] >>
  rewrite_tac[GSYM word_of_bytes_padded_range] >>
  AP_TERM_TAC >> irule memory_rel_padded_range >>
  qexists_tac `alloc` >> simp[]
QED

Theorem read_mload_value_step[local]:
  (inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD) /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  venom_asm_rel lo ps vs st /\
  EVERY (\(off,len). len = 0 \/ off + len <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?arg value out. inst.inst_operands = [arg] /\
    eval_operand arg vs = SOME value /\ inst.inst_outputs = [out] /\
    vs' = update_var out (mload (w2n value) vs) vs /\
    (!rest. st.as_stack = value :: rest ==>
      asm_step_op o2pc name st = AsmOK (asm_next (st with <|
        as_stack := mload (w2n value) vs :: rest;
        as_memory := asm_expand_memory (w2n value + 32) st.as_memory |>)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[venom_to_evm_name_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  rpt strip_tac >> rename1 `st.as_stack = addr :: rest` >>
  `mload (w2n addr) vs = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n addr)
      (asm_expand_memory (w2n addr + 32) st.as_memory)))` by
    (irule read_mload_word >> qexists_tac `ps.ps_alloc` >>
     gvs[venom_asm_rel_def, source_memory_read_ranges_def]) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_mload_def]
QED

Theorem read_expand_rel[local]:
  venom_asm_rel lo ps vs st ==>
  venom_asm_rel lo ps vs (st with as_memory := asm_expand_memory n st.as_memory)
Proof
  simp[venom_asm_rel_def] >> strip_tac >> simp[] >> conj_tac
  >- (irule plan_spill_rel_expand >> simp[]) >>
  irule strongPrefixSimTheory.memory_rel_expand >> simp[]
QED

Theorem read_mload_arranged_emit_sim:
  (inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD) /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  venom_asm_rel lo ps vs st /\
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
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc name st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
         (stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
         inst.inst_outputs) vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all read_mload_value_step >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `ef_read1 inst.inst_opcode` by gvs[ef_read1_def] >>
  drule_all read1_compute_operands >> strip_tac >> gvs[] >>
  `eval_operands [arg] vs = SOME [value]` by
    simp[venomStateTheory.eval_operands_def] >>
  `st.as_stack = [value] ++ DROP 1 st.as_stack` by
    (irule (arranged_eval_operands_stack |> SPEC_ALL
            |> Q.INST [`operands` |-> `[arg]`]
            |> SIMP_RULE (srw_ss()) []) >>
     qexistsl_tac [`arg`, `lo`, `ps`, `residual`, `vs`] >> simp[]) >>
  `venom_asm_rel lo ps vs
    (st with as_memory := asm_expand_memory (w2n value + 32) st.as_memory)` by
    (irule read_expand_rel >> simp[]) >>
  qabbrev_tac `expanded = st with as_memory :=
    asm_expand_memory (w2n value + 32) st.as_memory` >>
  `venom_asm_rel lo
     (ps with ps_stack := stack_push (Var out) (stack_pop 1 ps.ps_stack))
     (update_var out (mload (w2n value) vs) vs)
     (asm_next (expanded with
       as_stack := mload (w2n value) vs :: DROP 1 expanded.as_stack))` by
    (irule emit_output_venom_asm_rel >> simp[Abbr `expanded`]) >>
  qexists_tac `asm_next (st with <|
    as_stack := mload (w2n value) vs :: DROP 1 st.as_stack;
    as_memory := asm_expand_memory (w2n value + 32) st.as_memory |>)` >>
  simp[asm_next_def] >> gvs[asm_next_def, Abbr `expanded`]
QED

Theorem read_sha3_source[local]:
  inst.inst_opcode = SHA3 /\ step_inst fuel ctx inst vs = OK vs' ==>
  ?offop szop off sz out.
    inst.inst_operands = [offop; szop] /\
    eval_operand offop vs = SOME off /\ eval_operand szop vs = SOME sz /\
    inst.inst_outputs = [out] /\
    vs' = update_var out
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64
        (read_memory (w2n off) (w2n sz) vs))) vs
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[venomStateTheory.read_memory_def]
QED

Theorem read_sha3_value_step[local]:
  venom_asm_rel lo ps vs st /\
  (w2n sz = 0 \/ w2n off + w2n sz <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n off) /\
  st.as_stack = off :: sz :: rest ==>
  asm_step_op o2pc "SHA3" st = AsmOK (asm_next (st with <|
    as_stack := word_of_bytes T (0w:bytes32) (Keccak_256_w64
      (read_memory (w2n off) (w2n sz) vs)) :: rest;
    as_memory := if w2n sz = 0 then st.as_memory else
      asm_expand_memory (w2n off + w2n sz) st.as_memory |>))
Proof
  strip_tac >>
  `read_memory (w2n off) (w2n sz) vs =
    TAKE (w2n sz) (DROP (w2n off)
      (asm_expand_memory (w2n off + w2n sz) st.as_memory))` by
    (irule related_call_input_bytes >> qexistsl_tac [`lo`, `ps`] >> gvs[]) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def, asm_step_copy_def, asm_step_context_def,
       asm_sha3_def] >>
  Cases_on `w2n sz = 0` >> gvs[venomStateTheory.read_memory_def]
QED

Theorem read_sha3_arranged_emit_sim:
  inst.inst_opcode = SHA3 /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  venom_asm_rel lo ps vs st /\
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
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc name st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
         (stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
         inst.inst_outputs) vs' ab
Proof
  strip_tac >> drule_all read_sha3_source >> strip_tac >>
  drule_all sha3_compute_operands >> strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [offop; szop]` >>
  `eval_operands [offop; szop] vs = SOME [off; sz]` by
    simp[venomStateTheory.eval_operands_def] >>
  `st.as_stack = [off; sz] ++ DROP 2 st.as_stack` by
    (irule (arranged_eval_operands_stack |> SPEC_ALL
            |> Q.INST [`operands` |-> `[offop; szop]`]
            |> SIMP_RULE (srw_ss()) []) >>
     qexistsl_tac [`lo`, `offop`, `ps`, `residual`, `szop`, `vs`] >>
     simp[] >> metis_tac[]) >>
  `w2n sz = 0 \/ w2n off + w2n sz <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n off` by
    gvs[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  mp_tac (read_sha3_value_step |> SPEC_ALL
          |> Q.INST [`rest` |-> `DROP 2 st.as_stack`]) >>
  (impl_tac >- (simp[] >> gvs[])) >> strip_tac >>
  qmatch_goalsub_abbrev_tac `update_var out result vs` >>
  qabbrev_tac `expanded = st with as_memory := if w2n sz = 0 then
    st.as_memory else asm_expand_memory (w2n off + w2n sz) st.as_memory` >>
  `venom_asm_rel lo ps vs expanded` by
    (Cases_on `sz = 0w` >> simp[Abbr `expanded`] >>
     irule read_expand_rel >> simp[]) >>
  `venom_asm_rel lo
     (ps with ps_stack := stack_push (Var out) (stack_pop 2 ps.ps_stack))
     (update_var out result vs)
     (asm_next (expanded with as_stack := result :: DROP 2 expanded.as_stack))` by
    (irule emit_output_venom_asm_rel >> simp[]) >>
  qexists_tac `asm_next (expanded with as_stack := result :: DROP 2 expanded.as_stack)` >>
  gvs[Abbr `expanded`, Abbr `result`, venom_to_evm_name_def, asm_next_def]
QED

Theorem read_arranged_emit_sim:
    (ef_read0 inst.inst_opcode \/ ef_read1 inst.inst_opcode \/
     inst.inst_opcode = SHA3) /\
    inst.inst_opcode <> GAS /\
    ~is_pre_codegen_opcode inst.inst_opcode /\
    inst_wf inst /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
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
          (ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
             (stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)
             inst.inst_outputs) vs' ab
Proof
  strip_tac
  >- (irule read0_arranged_emit_sim >> simp[] >> metis_tac[])
  >- (Cases_on `inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD`
      >- metis_tac[read_mload_arranged_emit_sim] >>
      metis_tac[read1_arranged_emit_sim])
  >> metis_tac[read_sha3_arranged_emit_sim]
QED
