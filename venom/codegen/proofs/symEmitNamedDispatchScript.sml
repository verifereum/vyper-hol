(* Normalize named instruction layouts before invoking the selected emitter.
   slo is the execution/concretization map; vlo is the source-value map. *)
Theory symEmitNamedDispatch
Ancestors symInstKinds codegenSymRel asmSem finite_map list

Theorem named_codecopy_selection_shape:
  inst_wf inst /\ inst.inst_opcode = CODECOPY /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) ==>
  ?dst src sz. inst.inst_operands = [dst;src;sz] /\
    inst.inst_outputs = [] /\ selected = [sz;src;dst]
Proof
  strip_tac >>
  gvs[venomWfTheory.inst_wf_def, stackPlanGenTheory.compute_operands_def,
    venomEffectsTheory.is_commutative_def, venomInstTheory.python_stack_operands_def,
    venomInstTheory.ir_specific_operand_order_def, LENGTH_EQ_NUM_compute]
QED

Theorem named_code_end_add_selection_shape:
  inst_wf inst /\ inst.inst_opcode = ADD /\
  inst.inst_operands = [op; Label "code_end"] /\
  (selected = compute_operands inst \/
   (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
    selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) ==>
  (?x. inst.inst_outputs = [x]) /\
  (selected = [op;Label "code_end"] \/ selected = [Label "code_end";op])
Proof
  strip_tac >>
  gvs[venomWfTheory.inst_wf_def, stackPlanGenTheory.compute_operands_def,
    venomInstTheory.python_stack_operands_def,
    venomInstTheory.ir_specific_operand_order_def, LENGTH_EQ_NUM_compute]
QED

Theorem sym_named_source_emit_dispatch:
  ss.sym_base.as_pc = cs.as_pc /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  asm_step slo (build_offset_to_pc p) (AsmOp name) cs = AsmOK cs' /\
  venom_to_evm_name inst.inst_opcode = SOME name /\ inst_wf inst /\
  (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
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
  qs = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop (LENGTH selected) ps.ps_stack) inst.inst_outputs /\
  (!dst x sz w off. inst.inst_opcode = CODECOPY /\
    inst.inst_operands = [dst; Var x; sz] /\ code_end_var fn x /\
    eval_operand (Var x) vs = SOME w /\ FLOOKUP slo "code_end" = SOME off ==>
    w2n (w - n2w off) < dimword (:256) DIV 2) /\
  (!dst src sz. inst.inst_opcode = CODECOPY /\
    inst.inst_operands = [dst;src;sz] /\ inst.inst_outputs = [] /\
    selected = [sz;src;dst] /\ ps.ps_stack = residual ++ [sz;src;dst] /\
    EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
    (!op. MEM op inst.inst_operands ==>
      eval_operand op (frame_view fn ra vs with vs_memory := m) =
      operand_val (frame_view fn ra vs with vs_memory := m) vlo op) /\
    (!x w off. src = Var x /\ code_end_var fn x /\
      eval_operand src vs = SOME w /\ FLOOKUP slo "code_end" = SOME off ==>
      w2n (w - n2w off) < dimword (:256) DIV 2) /\
    qs = ps with ps_stack := stack_pop 3 ps.ps_stack /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ sym_kinds_ok cplan fn ret srest qs ss') /\
  (!op x. inst.inst_opcode = ADD /\ inst.inst_operands = [op;Label "code_end"] /\
    inst.inst_outputs = [x] /\
    (selected = [op;Label "code_end"] \/ selected = [Label "code_end";op]) /\
    name = "ADD" /\ asm_block_at p ss.sym_base.as_pc [AsmOp "ADD"] /\
    qs = ps with ps_stack := stack_push (Var x) (stack_pop 2 ps.ps_stack) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ sym_kinds_ok cplan fn ret srest qs ss') /\
  (!x. inst.inst_opcode = CODESIZE /\ inst.inst_operands = [] /\
    inst.inst_outputs = [x] /\
    qs = ps with ps_stack := stack_push (Var x) ps.ps_stack /\
    asm_block_at p cs.as_pc [AsmOp "CODESIZE"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODESIZE") cs = AsmOK cs' ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ sym_kinds_ok cplan fn ret srest qs ss') /\
  (inst.inst_opcode <> CODECOPY /\ inst.inst_opcode <> CODESIZE /\
    ~(?op. inst.inst_opcode = ADD /\ inst.inst_operands = [op;Label "code_end"]) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ sym_kinds_ok cplan fn ret srest qs ss') ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\ sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `inst.inst_opcode = CODECOPY`
  >- (drule_all named_codecopy_selection_shape >>
      disch_then (qx_choose_then `dst` (qx_choose_then `src` (qx_choose_then `sz` strip_assume_tac))) >>
      qpat_x_assum `!dst src sz. _ ==> ?ss'. _` (qspecl_then [`dst`, `src`, `sz`] irule) >>
      fs[asmIRTheory.venom_to_evm_name_def, venomEffectsTheory.is_commutative_def,
         EVERY_MEM, MEM] >> metis_tac[]) >>
  Cases_on `?op. inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"]`
  >- (pop_assum (qx_choose_then `op` strip_assume_tac) >>
      drule_all named_code_end_add_selection_shape >>
      disch_then (CONJUNCTS_THEN2 (qx_choose_then `x` assume_tac) assume_tac) >>
      qpat_x_assum `!op x. _ ==> ?ss'. _` (qspecl_then [`op`, `x`] irule) >>
      fs[asmIRTheory.venom_to_evm_name_def] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = CODESIZE`
  >- (gvs[asmIRTheory.venom_to_evm_name_def, venomWfTheory.inst_wf_def,
           stackPlanGenTheory.compute_operands_def, venomInstTheory.python_stack_operands_def,
           venomInstTheory.ir_specific_operand_order_def, LENGTH_EQ_NUM_compute,
           stackModelTheory.stack_pop_def, opcodeClassTheory.ef_read0_def] >> metis_tac[]) >>
  metis_tac[]
QED
