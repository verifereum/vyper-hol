Theory o1LabelReadinessDload
Ancestors
  o1ContractLowerDload o1PassContract venomPassDispatcher venomInst

(* The existing operand-provenance interface is supply-independent.  Its only
   generated label is code_end, so no supply-freshness premise is needed. *)
Theorem dload_pass_no_runtime_begin:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s fn out /\
  o1_fn_shape observed.cu_context fn /\
  (!inst. MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !inst. MEM inst (fn_insts out.fpo_function) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  gvs[fn_pass_step_def, execute_configured_fn_pass_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all lower_dload_function_supply_operand_provenance >>
  simp[] >> metis_tac[]
QED
