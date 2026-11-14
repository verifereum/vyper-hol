Theory o1CodeEndLowerProvenance
Ancestors
  codegenSymRel lowerDloadPtrStatic o1ContractLowerDload
  lowerDloadDefs lowerDloadSupplyProofs irSupply venomInst list

Theorem lower_dload_seed_fresh[local]:
  lower_dload_inst_supply u i = (xs,v) /\ MEM j xs /\
  ~MEM (Label "code_end") i.inst_operands /\
  j.inst_opcode = ADD /\
  j.inst_operands = [op; Label "code_end"] /\ MEM x j.inst_outputs ==>
  ~MEM x u.irs_used_vars
Proof
  rw[lower_dload_inst_supply_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac fresh_ir_var_contract >> gvs[]
QED

Theorem lower_dload_function_seed_fresh[local]:
  lower_dload_function_supply u fn = (fn',u') /\
  ir_supply_covers_fn u fn /\
  (!i. MEM i (fn_insts fn) ==>
       ~MEM (Label "code_end") i.inst_operands) /\
  MEM j (fn_insts fn') /\ j.inst_opcode = ADD /\
  j.inst_operands = [op; Label "code_end"] /\ MEM x j.inst_outputs ==>
  ~MEM x (fn_ir_vars fn)
Proof
  strip_tac >>
  drule_all lower_dload_function_supply_member_covered >> strip_tac >>
  `~MEM (Label "code_end") i.inst_operands` by metis_tac[] >>
  drule_all lower_dload_seed_fresh >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_code_end_var_fresh:
  !fn' x. code_end_var fn' x ==> !u fn u'.
  lower_dload_function_supply u fn = (fn',u') /\
  ir_supply_covers_fn u fn /\
  (!i. MEM i (fn_insts fn) ==>
       ~MEM (Label "code_end") i.inst_operands) ==>
  ~MEM x (fn_ir_vars fn)
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- metis_tac[lower_dload_function_seed_fresh] >>
  `MEM inst (fn_insts fn)` by
    (irule lower_dload_function_supply_control >>
     simp[] >> metis_tac[]) >>
  metis_tac[fn_ir_vars_operand, MEM]
QED
