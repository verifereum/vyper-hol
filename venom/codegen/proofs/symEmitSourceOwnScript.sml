(* Own-relation source interfaces.  The real emission proofs are shared
   with the canonical API or imported from their subject owners. *)
Theory symEmitSourceOwn
Ancestors symEmitSim symEmitFrameOwn symEmitStoreOwn symEmitCodecopyOwn
  symEmitCodeEndOwn symEmitNamedOwn asmSymBridge

Theorem sym_initial_fmp_source_emit_own_conditional:
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss') /\
  asm_sym_rel_own lo p env own cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_outputs = [x] /\
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  qs = ps with ps_stack := stack_push (Var x) ps.ps_stack /\
  asm_block_at p ss.sym_base.as_pc [AsmPush (encode_num_bytes initial_fmp)] /\
  asm_steps lo (build_offset_to_pc p) p 1 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own lo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  MATCH_ACCEPT_TAC (Q.INST [`R` |-> `asm_sym_rel_own lo p env own`]
    symEmitFrameOwnTheory.sym_initial_fmp_source_emit_mode_conditional)
QED

Theorem sym_assert_source_emit_own_conditional:
  (!n cs ss ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  step_inst fuel ctx inst vs = OK vs' /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  qs = ps with ps_stack := stack_pop 1 ps.ps_stack /\
  (inst.inst_opcode = ASSERT ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]) /\
  (inst.inst_opcode = ASSERT_UNREACHABLE ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
    INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3)) /\
  asm_steps slo (build_offset_to_pc p) p 3 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 3 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    fs[asm_sym_rel_own_def] >>
  drule_all (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    symEmitFrameOwnTheory.sym_assert_source_emit_mode_conditional) >> simp[]
QED

Theorem sym_bump_source_emit_own_conditional:
  (!n cs ss ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ssa_form fn /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  qs = ps with ps_stack := stack_push (Var next)
    (stack_push (Var ptr) (stack_pop 2 ps.ps_stack)) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] /\
  asm_steps slo (build_offset_to_pc p) p 2 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 2 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  MATCH_ACCEPT_TAC symEmitStoreOwnTheory.sym_bump_source_emit_own_mode_conditional
QED

Theorem sym_istore_source_emit_own_conditional:
  (!n cs ss ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [dst; value] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  context_source_memory_writes_disjoint cplan inst vs /\
  qs = ps with ps_stack := stack_pop 2 ps.ps_stack /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "SWAP1"; AsmOp "MSTORE"] /\
  asm_steps slo (build_offset_to_pc p) p 2 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 2 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  MATCH_ACCEPT_TAC symEmitStoreOwnTheory.sym_istore_source_emit_own_mode_conditional
QED

Theorem sym_named_numeric_source_emit_own_conditional:
  (!cs ss ai cs'. asm_sym_rel_own slo p env own cs ss /\
    asm_block_at p cs.as_pc [ai] /\
    asm_step slo (build_offset_to_pc p) ai cs = AsmOK cs' /\
    (!msg. (if allow_own then sym_step_own p env own ai ss
            else sym_step p env ai ss) <> SymBad msg) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  asm_sym_rel_own slo p env own cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  asm_step slo (build_offset_to_pc p) (AsmOp name) cs = AsmOK cs' /\
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  step_inst fuel ctx inst vs = OK vs' /\
  ~is_pre_codegen_opcode inst.inst_opcode /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> CODECOPY /\ inst.inst_opcode <> CODESIZE /\
  (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
  ~(?op. inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"]) /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\
  fn_shape_ok fn /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) vlo op) /\
  venom_asm_rel vlo ps (frame_view fn ra vs with vs_memory := m) cs /\
  venom_asm_rel vlo qs vsout cs' /\
  qs = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop (LENGTH selected) ps.ps_stack) inst.inst_outputs /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!cs ss. asm_sym_rel_own slo p env own cs ss ==>
    ss.sym_base.as_pc = cs.as_pc /\
    LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    (rpt strip_tac >> gvs[asm_sym_rel_own_def]) >>
  drule_all (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    symEmitSimTheory.sym_named_numeric_source_emit_core) >> simp[]
QED

Theorem sym_log_source_emit_own_conditional:
  (!cs ss ai cs'. asm_sym_rel_own slo p env own cs ss /\
    asm_block_at p cs.as_pc [ai] /\
    asm_step slo (build_offset_to_pc p) ai cs = AsmOK cs' /\
    (!msg. (if allow_own then sym_step_own p env own ai ss
            else sym_step p env ai ss) <> SymBad msg) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  LENGTH selected = w2n tc + 2 /\ REVERSE selected = off :: len :: topics /\
  ALOOKUP log_table name = SOME (w2n tc) /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  venom_asm_rel lo qs vsout cs' /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  qs = ps with ps_stack := stack_pop (LENGTH selected) ps.ps_stack /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  asm_step slo (build_offset_to_pc p) (AsmOp name) cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!cs ss. asm_sym_rel_own slo p env own cs ss ==>
    ss.sym_base.as_pc = cs.as_pc /\
    LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    (rpt strip_tac >> gvs[asm_sym_rel_own_def]) >>
  drule_all (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    symEmitSimTheory.sym_log_source_emit_mode_conditional) >> simp[]
QED

Theorem sym_code_end_add_source_emit_own_conditional:
  (!n cs ss ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"] /\
  inst.inst_outputs = [x] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ selected /\
  (selected = [op; Label "code_end"] \/ selected = [Label "code_end"; op]) /\
  EVERY (\at. at <> dead_stack_marker) selected /\
  (!at. MEM at selected ==>
    eval_operand at (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo at) /\
  sym_data_label p env "code_end" /\
  qs = ps with ps_stack := stack_push (Var x) (stack_pop 2 ps.ps_stack) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "ADD"] /\
  asm_steps slo (build_offset_to_pc p) p 1 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  MATCH_ACCEPT_TAC (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    symEmitCodeEndOwnTheory.sym_code_end_add_source_emit_mode_conditional)
QED

Theorem sym_codesize_source_emit_own_conditional:
  allow_own /\
  (!cs ss cs' ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_step_op_own p env own "CODESIZE" ss = SymOK ss' /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODESIZE") cs = AsmOK cs' ==>
    asm_sym_rel_own slo p env own cs' ss') /\
  sym_step_op_own p env own "CODESIZE" ss = SymOK
    (ss with <|sym_base := asm_next ss.sym_base;
               sym_stack := Val (n2w (LENGTH own)) :: ss.sym_stack|>) /\
  asm_sym_rel_own slo p env own cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  inst.inst_opcode = CODESIZE /\ inst.inst_operands = [] /\
  inst.inst_outputs = [x] /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  qs = ps with ps_stack := stack_push (Var x) ps.ps_stack /\
  asm_block_at p cs.as_pc [AsmOp "CODESIZE"] /\
  asm_step slo (build_offset_to_pc p) (AsmOp "CODESIZE") cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!cs ss. asm_sym_rel_own slo p env own cs ss ==> ss.sym_base.as_pc = cs.as_pc` by
    (rpt strip_tac >> pop_assum mp_tac >> simp[asm_sym_rel_own_def] >>
     rpt strip_tac >> simp[]) >>
  drule_all (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    symEmitNamedOwnTheory.sym_codesize_source_emit_mode_conditional) >> simp[]
QED

Theorem sym_codecopy_source_emit_own_conditional:
  (!cs ss cs' dw l d nw tail. asm_sym_rel_own slo p env own cs ss /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
    ss.sym_stack = Val dw :: Lab l d :: Val nw :: tail /\
    sym_data_label p env l /\ sym_delta_ok d /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n dw) (w2n nw) b) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      asm_sym_rel_own slo p env own cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail) /\
  (!cs ss cs' dw sw nw tail. allow_own /\ asm_sym_rel_own slo p env own cs ss /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
    ss.sym_stack = Val dw :: Val sw :: Val nw :: tail /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n dw) (w2n nw) b) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      asm_sym_rel_own slo p env own cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail) /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; sz] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel vlo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ [sz; src; dst] /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) vlo op) /\
  context_source_memory_writes_disjoint cplan inst vs /\
  sym_data_label p env "code_end" /\
  (MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label p env "runtime_begin") /\
  (!x w off. src = Var x /\ code_end_var fn x /\
    eval_operand src vs = SOME w /\ FLOOKUP slo "code_end" = SOME off ==>
    w2n (w - n2w off) < dimword (:256) DIV 2) /\
  qs = ps with ps_stack := stack_pop 3 ps.ps_stack /\
  asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
  asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!cs ss. asm_sym_rel_own slo p env own cs ss ==>
    LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    (rpt strip_tac >> fs[asm_sym_rel_own_def]) >>
  drule_all (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    symEmitCodecopyOwnTheory.sym_codecopy_source_emit_mode_conditional) >> simp[]
QED

Theorem sym_named_source_emit_own_conditional:
  (!cs ss ai cs'. asm_sym_rel_own slo p env own cs ss /\
    asm_block_at p cs.as_pc [ai] /\
    asm_step slo (build_offset_to_pc p) ai cs = AsmOK cs' /\
    (!msg. (if allow_own then sym_step_own p env own ai ss
            else sym_step p env ai ss) <> SymBad msg) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  (!n cs ss ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  (!cs ss cs' dw l d nw tail. asm_sym_rel_own slo p env own cs ss /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
    ss.sym_stack = Val dw :: Lab l d :: Val nw :: tail /\
    sym_data_label p env l /\ sym_delta_ok d /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n dw) (w2n nw) b) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      asm_sym_rel_own slo p env own cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail) /\
  (!cs ss cs' dw sw nw tail. allow_own /\ asm_sym_rel_own slo p env own cs ss /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
    ss.sym_stack = Val dw :: Val sw :: Val nw :: tail /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n dw) (w2n nw) b) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
      asm_sym_rel_own slo p env own cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail) /\
  (!cs ss cs' ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_step_op_own p env own "CODESIZE" ss = SymOK ss' /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODESIZE") cs = AsmOK cs' ==>
    asm_sym_rel_own slo p env own cs' ss') /\
  (inst.inst_opcode = CODESIZE ==> allow_own /\
    sym_step_op_own p env own "CODESIZE" ss = SymOK
      (ss with <|sym_base := asm_next ss.sym_base;
                 sym_stack := Val (n2w (LENGTH own)) :: ss.sym_stack|>)) /\
  asm_sym_rel_own slo p env own cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  asm_step slo (build_offset_to_pc p) (AsmOp name) cs = AsmOK cs' /\
  asm_steps slo (build_offset_to_pc p) p 1 cs = AsmOK cs' /\
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  step_inst fuel ctx inst vs = OK vs' /\
  ~is_pre_codegen_opcode inst.inst_opcode /\ inst.inst_opcode <> GAS /\
  (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) vlo op) /\
  venom_asm_rel vlo ps (frame_view fn ra vs with vs_memory := m) cs /\
  venom_asm_rel vlo qs vsout cs' /\
  qs = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop (LENGTH selected) ps.ps_stack) inst.inst_outputs /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  sym_data_label p env "code_end" /\
  (MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label p env "runtime_begin") /\
  (!dst x sz w off. inst.inst_opcode = CODECOPY /\
    inst.inst_operands = [dst; Var x; sz] /\ code_end_var fn x /\
    eval_operand (Var x) vs = SOME w /\ FLOOKUP slo "code_end" = SOME off ==>
    w2n (w - n2w off) < dimword (:256) DIV 2) ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!cs ss. asm_sym_rel_own slo p env own cs ss ==>
    ss.sym_base.as_pc = cs.as_pc /\
    LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    (rpt strip_tac >> pop_assum mp_tac >> simp[asm_sym_rel_own_def] >>
     rpt strip_tac >> simp[]) >>
  drule_all (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    symEmitNamedOwnTheory.sym_named_source_emit_mode_conditional) >> simp[]
QED
