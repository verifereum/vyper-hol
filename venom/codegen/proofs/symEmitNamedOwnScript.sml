(* Named source dispatch.  Opcode semantics and the shared source kernels
   remain with their existing owners; this is only the finite family join. *)
Theory symEmitNamedOwn
Ancestors symEmitSim symEmitCodecopyOwn symEmitCodeEndOwn list

Theorem sym_codesize_source_emit_mode_conditional:
  allow_own /\
  (!cs ss. R cs ss ==> ss.sym_base.as_pc = cs.as_pc) /\
  (!cs ss cs' ss'. R cs ss /\
    sym_step_op_own p env own "CODESIZE" ss = SymOK ss' /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODESIZE") cs = AsmOK cs' ==>
    R cs' ss') /\
  sym_step_op_own p env own "CODESIZE" ss = SymOK
    (ss with <|sym_base := asm_next ss.sym_base;
               sym_stack := Val (n2w (LENGTH own)) :: ss.sym_stack|>) /\
  R cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  inst.inst_opcode = CODESIZE /\ inst.inst_operands = [] /\
  inst.inst_outputs = [x] /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  qs = ps with ps_stack := stack_push (Var x) ps.ps_stack /\
  asm_block_at p cs.as_pc [AsmOp "CODESIZE"] /\
  asm_step slo (build_offset_to_pc p) (AsmOp "CODESIZE") cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  MATCH_ACCEPT_TAC symEmitSimTheory.sym_codesize_source_emit_core
QED

Theorem sym_named_source_emit_mode_conditional:
  (!cs ss. R cs ss ==>
    ss.sym_base.as_pc = cs.as_pc /\
    LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack) /\
  (!cs ss ai cs'. R cs ss /\ asm_block_at p cs.as_pc [ai] /\
    asm_step slo (build_offset_to_pc p) ai cs = AsmOK cs' /\
    (!msg. (if allow_own then sym_step_own p env own ai ss
            else sym_step p env ai ss) <> SymBad msg) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss') /\
  (!n cs ss ss'. R cs ss /\ sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\ R cs' ss') /\
  (!cs ss cs' dw l d nw tail. R cs ss /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
    ss.sym_stack = Val dw :: Lab l d :: Val nw :: tail /\
    sym_data_label p env l /\ sym_delta_ok d /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n dw) (w2n nw) b) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail) /\
  (!cs ss cs' dw sw nw tail. allow_own /\ R cs ss /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
    ss.sym_stack = Val dw :: Val sw :: Val nw :: tail /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n dw) (w2n nw) b) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail) /\
  (!cs ss cs' ss'. R cs ss /\
    sym_step_op_own p env own "CODESIZE" ss = SymOK ss' /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODESIZE") cs = AsmOK cs' ==>
    R cs' ss') /\
  (inst.inst_opcode = CODESIZE ==> allow_own /\
    sym_step_op_own p env own "CODESIZE" ss = SymOK
      (ss with <|sym_base := asm_next ss.sym_base;
                 sym_stack := Val (n2w (LENGTH own)) :: ss.sym_stack|>)) /\
  R cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
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
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `inst.inst_opcode = CODECOPY`
  >- suspend "codecopy" >>
  Cases_on `?op. inst.inst_opcode = ADD /\
    inst.inst_operands = [op; Label "code_end"]`
  >- suspend "code_end_add" >>
  Cases_on `inst.inst_opcode = CODESIZE`
  >- suspend "codesize" >>
  drule_all symEmitSimTheory.sym_named_numeric_source_emit_core >> simp[]
QED

Resume sym_named_source_emit_mode_conditional[codecopy]:
  drule_all named_codecopy_selection_shape >> strip_tac >>
  gvs[asmIRTheory.venom_to_evm_name_def,
    stackPlanGenTheory.compute_operands_def, venomInstTheory.python_stack_operands_def,
    venomInstTheory.ir_specific_operand_order_def] >>
  `!cs ss. R cs ss ==>
    LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    metis_tac[] >>
  irule (SRULE [EVERY_MEM, MEM]
    symEmitCodecopyOwnTheory.sym_codecopy_source_emit_mode_conditional) >>
  simp[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  goal_assum (drule_at (Pat `_.inst_operands = _`)) >>
  simp[MEM] >> qexists `slo` >> simp[] >> rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume sym_named_source_emit_mode_conditional[code_end_add]:
  pop_assum strip_assume_tac >>
  drule_all named_code_end_add_selection_shape >> strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[] >>
  `name = "ADD"` by gvs[asmIRTheory.venom_to_evm_name_def] >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "ADD"]` by metis_tac[] >>
  drule_at (Pat `asm_steps _ _ _ _ _ = _`)
    symEmitCodeEndOwnTheory.sym_code_end_add_source_emit_mode_conditional >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `_.inst_opcode = ADD`)) >>
  disch_then (drule_at (Pat `_.ps_stack = _`)) >>
  simp[] >> disch_then (qspecl_then [`own`, `env`, `ctx`, `allow_own`, `R`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Resume sym_named_source_emit_mode_conditional[codesize]:
  gvs[asmIRTheory.venom_to_evm_name_def, venomWfTheory.inst_wf_def,
    stackPlanGenTheory.compute_operands_def, venomInstTheory.python_stack_operands_def,
    venomInstTheory.ir_specific_operand_order_def, LENGTH_EQ_NUM_compute,
    stackModelTheory.stack_pop_def, stackModelTheory.stack_push_def,
    opcodeClassTheory.ef_read0_def] >>
  irule sym_codesize_source_emit_mode_conditional >>
  simp[stackModelTheory.stack_push_def] >>
  conj_tac >- (qexistsl [`cs`, `slo`] >> simp[] >> metis_tac[]) >>
  qexistsl [`inst`, `ps`, `h`] >> simp[]
QED

Finalise sym_named_source_emit_mode_conditional
