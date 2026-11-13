Theory bodyPtrBopHashStep
Ancestors
  typedCopyPtr fragGasSeqPtr ptrSafeRun ptrDiscipline venomInst
  contextCodegenRel codegenRel venomExecSemantics venomState memLocDefs

Theorem ptr_inst_ok_sha3:
  eval_operand (Var p) s = SOME a /\
  eval_operand lenop s = SOME nw /\
  op_taint tn (Var p) = {} /\ op_taint tn lenop = {} /\
  (0 < w2n nw ==> ptr_covers G tn p s (w2n nw)) /\
  (!i. w2n a <= i /\ i < w2n a + w2n nw ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id SHA3 [Var p;lenop] [out]) s
Proof
  rpt strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def,
       ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
       ptrDisciplineTheory.allocas_from_def, venomInstTheory.mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       memory_range_of_operands_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `0 < w2n nw` by
        metis_tac[wordsTheory.w2n_eq_0, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
      first_x_assum drule >>
      rw[bodyPtrDefsTheory.ptr_covers_def] >>
      gvs[eval_operand_def, mem_read_ops_def] >> metis_tac[]) >>
  conj_tac
  >- (conj_tac >- metis_tac[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
  simp[eval_operand_def, AllCaseEqs(), update_var_def]
QED

Theorem bop_hash_sha3_edge:
  eval_operand (Var p) s = SOME a /\
  eval_operand lenop s = SOME nw /\
  op_taint tn (Var p) = {} /\ op_taint tn lenop = {} /\
  (0 < w2n nw ==> ptr_covers G tn p s (w2n nw)) /\
  (!i. w2n a <= i /\ i < w2n a + w2n nw ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id SHA3 [Var p;lenop] [out]) /\
  step_inst_base (mk_inst id SHA3 [Var p;lenop] [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id SHA3 [Var p;lenop] [out]) u)
    (step_taint (mk_inst id SHA3 [Var p;lenop] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id SHA3 [Var p;lenop] [out]) s` by
    (irule ptr_inst_ok_sha3 >> metis_tac[]) >>
  `(mk_inst id SHA3 [Var p;lenop] [out]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id SHA3 [Var p;lenop] [out]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >> simp[mk_inst_def]
QED
