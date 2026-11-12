(* Observations inside a LowerDload expansion need not complete it. *)
Theory o1CodeEndLowerPacket
Ancestors
  o1CodeEndLowerBoundary lowerDloadSafetyKernel
  lowerDloadDefs venomInst venomState words list

Theorem lower_dload_generated_index:
  lower_dload_inst_supply u inst = (xs,u') /\ h < LENGTH xs /\
  MEM (Label "code_end") (EL h xs).inst_operands /\
  ~MEM (Label "code_end") inst.inst_operands ==>
  (h = 1 /\ inst.inst_opcode = DLOAD /\
   ?a c d av u1. xs = [a;EL h xs;c;d] /\
     fresh_ir_var u = (av,u1) /\
     a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
     a.inst_outputs = [av]) \/
  (h = 0 /\ inst.inst_opcode = DLOADBYTES)
Proof
  rw[lower_dload_inst_supply_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `n` >> gvs[] >>
  Cases_on `n'` >> gvs[] >> Cases_on `n` >> gvs[]
QED

Theorem lower_dload_prefix_code_end_bound:
  lower_dload_inst_supply u inst = (xs,u') /\
  ~MEM (Label "code_end") inst.inst_operands /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v u.irs_used_vars) /\
  inst_dload_in_section inst s /\
  LENGTH s.vs_data_section < dimword(:256) DIV 2 /\
  ld_prefix C fn xs p h s t /\
  MEM (Label "code_end") (EL h xs).inst_operands ==>
  (EL h xs).inst_opcode = ADD /\
  !op w. MEM op (EL h xs).inst_operands /\ op <> Label "code_end" /\
         eval_operand op t = SOME w ==>
         w2n w < dimword(:256) DIV 2
Proof
  strip_tac >>
  `h < LENGTH xs` by metis_tac[ld_prefix_bound] >>
  `MEM (EL h xs) xs` by simp[EL_MEM] >>
  drule_all lower_dload_generated_index >> disch_tac >>
  drule_all lower_dload_generated_code_end >> strip_tac >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (gvs[] >>
      qpat_x_assum `ld_prefix _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[arithmeticTheory.ONE] >>
      disch_then (strip_assume_tac o MATCH_MP ld_prefix_predecessor) >>
      gvs[ld_prefix_zero] >>
      `HD xs = a` by (qpat_assum `xs = _` (fn th => simp[Once th])) >>
      gvs[] >>
      irule dload_generated_add_half_bound >> metis_tac[MEM]) >>
  gvs[ld_prefix_zero] >>
  irule dload_in_section_half_bound >> metis_tac[]
QED
