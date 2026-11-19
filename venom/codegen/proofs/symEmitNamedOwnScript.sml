(* Mode-dependent emitters for the shared named-source dispatch. *)
Theory symEmitNamedOwn
Ancestors symEmitSim symEmitCodecopyOwn symEmitCodeEndOwn
  symEmitNamedDispatch symEmitCodesizeOwn list

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
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[] >>
  drule_at (Pat `asm_step _ _ (AsmOp _) _ = _`) sym_named_source_emit_dispatch >>
  disch_then (drule_at (Pat `!op. MEM op selected ==> eval_operand op st = operand_val st vlo op`)) >>
  disch_then (drule_at (Pat `qs = ps with ps_stack := FOLDL _ _ _`)) >>
  disch_then (drule_at (Pat `ps.ps_stack = residual ++ selected`)) >>
  disch_then irule >> rpt conj_tac >> IF (first_assum ACCEPT_TAC) all_tac all_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `!cs ss. R cs ss ==> ss.sym_base.as_pc = cs.as_pc` by metis_tac[] >>
      qpat_assum `inst.inst_opcode = CODESIZE ==> _` (drule_then strip_assume_tac) >>
      drule_all sym_codesize_source_emit_kernel >> simp[])
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all symEmitSimTheory.sym_code_end_add_source_emit_mode_conditional >> simp[])
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `!cs ss. R cs ss ==>
        LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
        metis_tac[] >>
      drule_all symEmitSimTheory.sym_codecopy_source_emit_core >> simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all sym_named_numeric_source_emit_core >> simp[]
QED
