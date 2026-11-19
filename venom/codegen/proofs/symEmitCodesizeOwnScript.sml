(* Consume the own CODESIZE opcode equation and correspondence at the source
   boundary; the opcode simulation itself is supplied by asmSymOwnStep. *)
Theory symEmitCodesizeOwn
Ancestors asmSymOwnCode[qualified,ignore_grammar] codegenSymRel symInstKinds list

Theorem sym_codesize_source_emit_kernel:
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
  strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[] >>
  qmatch_asmsub_abbrev_tac `sym_step_op_own p env own "CODESIZE" ss = SymOK final` >>
  qexists `final` >> rpt conj_tac
  >- (mp_tac (Q.INST [`inst` |-> `AsmOp "CODESIZE"`] sym_steps_mode_single) >>
      simp[asmSymOwnCodeTheory.sym_step_own_def])
  >- metis_tac[]
  >- simp[Abbr `final`] >>
  simp[Abbr `final`] >>
  `op_kind_ok fn ret (Var x) (Val (n2w (LENGTH own)))` by
    (irule ordinary_output_kind >> simp[] >> qexists `inst` >> simp[]) >>
  fs[sym_kinds_ok_def, stackModelTheory.stack_push_def, SNOC_APPEND,
     REVERSE_APPEND] >> metis_tac[]
QED
