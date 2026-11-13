(* Local value-sensitive boundary of LowerDload. *)
Theory o1CodeEndLowerBoundary
Ancestors
  memSafeRun lowerDloadDefs lowerDloadSupplyProofs venomExecSemantics
  venomExecProofs venomState irSupply finite_map

Theorem dload_in_section_half_bound:
  inst_dload_in_section inst s /\
  LENGTH s.vs_data_section < dimword(:256) DIV 2 /\
  ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [op]) \/
   (inst.inst_opcode = DLOADBYTES /\
    ?dst n. inst.inst_operands = [dst;op;n])) /\
  eval_operand op s = SOME w ==>
  w2n w < dimword(:256) DIV 2
Proof
  rw[inst_dload_in_section_def] >>
  first_x_assum (qspecl_then [`op`,`w`] mp_tac) >> simp[]
QED

Theorem lower_dload_generated_code_end:
  lower_dload_inst_supply u inst = (xs,u') /\ MEM j xs /\
  MEM (Label "code_end") j.inst_operands /\
  ~MEM (Label "code_end") inst.inst_operands ==>
  j.inst_opcode = ADD /\
  ?op. j.inst_operands = [op; Label "code_end"] /\
    ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [op]) \/
     (inst.inst_opcode = DLOADBYTES /\
      ?dst n. inst.inst_operands = [dst;op;n]))
Proof
  rw[lower_dload_inst_supply_def, AllCaseEqs()] >> gvs[]
QED

(* The only prefix before the DLOAD-generated ADD is a fresh ALLOCA.
   Reflect evaluation backwards, including unsuccessful/undefined reads. *)
Theorem dload_generated_add_half_bound:
  inst_dload_in_section inst s /\
  LENGTH s.vs_data_section < dimword(:256) DIV 2 /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [op] /\
  fresh_ir_var u = (av,u1) /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v u.irs_used_vars) /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit z] /\
  a.inst_outputs = [av] /\ step_inst fuel C a s = OK t /\
  eval_operand op (t with vs_inst_idx := k) = SOME w ==>
  w2n w < dimword(:256) DIV 2
Proof
  strip_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  `op <> Var av` by (strip_tac >> gvs[]) >>
  `eval_operand op s = SOME w` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, exec_alloca_def,
          AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
     Cases_on `op` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  irule dload_in_section_half_bound >> metis_tac[]
QED

Theorem lower_dload_generated_add_position:
  lower_dload_inst_supply u inst = (xs,u') /\ MEM j xs /\
  MEM (Label "code_end") j.inst_operands /\
  ~MEM (Label "code_end") inst.inst_operands ==>
  (inst.inst_opcode = DLOAD /\
   ?a c d av u1. xs = [a;j;c;d] /\
     fresh_ir_var u = (av,u1) /\
     a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
     a.inst_outputs = [av]) \/
  (inst.inst_opcode = DLOADBYTES /\ ?c. xs = [j;c])
Proof
  rw[lower_dload_inst_supply_def, AllCaseEqs()] >> gvs[] >>
  metis_tac[]
QED
