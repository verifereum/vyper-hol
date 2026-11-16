Theory o1CodeEndLowerProvenance
Ancestors
  codegenSymRel lowerDloadPtrStatic o1ContractLowerDload
  lowerDloadDefs lowerDloadSupplyProofs irSupply venomInst list o1LabelFlowLowerDload

Theorem lower_dload_code_end_var_fresh:
  !fn' x. code_end_var fn' x ==> !u fn u'.
  lower_dload_function_supply u fn = (fn',u') /\
  ir_supply_covers_fn u fn /\
  (!i. MEM i (fn_insts fn) ==>
       ~MEM (Label "code_end") i.inst_operands) ==>
  ~MEM x (fn_ir_vars fn)
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- metis_tac[lower_dload_function_code_end_seed] >>
  `MEM inst (fn_insts fn)` by
    (irule lower_dload_function_supply_control >>
     simp[] >> metis_tac[]) >>
  metis_tac[fn_ir_vars_operand, MEM]
QED
