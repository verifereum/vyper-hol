(* Preserve the absence of the constructor runtime symbol through an
   actual configured pass. Function shape excludes reserved block labels,
   including labels introduced into PHIs or substituted by CFG passes. *)
Theory o1LabelReadiness
Ancestors
  o1PassContract venomInst list o1LabelReadinessSimple o1LabelReadinessFmp
  o1LabelReadinessCfgNorm o1LabelReadinessDload o1LabelReadinessSsa
  o1LabelReadinessSimplify singleUseExpansionSupplyLabels venomPassDispatcher

Theorem fn_pass_step_no_runtime_begin:
  fn_pass_step rpolicy pass observed s fn out /\
  o1_fn_shape observed.cu_context fn /\
  (!inst. MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !inst. MEM inst (fn_insts out.fpo_function) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  Cases_on `pass` >> rename1 `CFP_Simple tag` >>
  Cases_on `tag` >> rpt strip_tac
  >- metis_tac[simple_pass_no_runtime_begin, MEM]
  >- metis_tac[cfgnorm_pass_no_runtime_begin]
  >- metis_tac[simple_pass_no_runtime_begin, MEM]
  >- metis_tac[simple_pass_no_runtime_begin, MEM]
  >- metis_tac[fmp_pass_no_runtime_begin]
  >- metis_tac[dload_pass_no_runtime_begin]
  >- metis_tac[ssa_pass_no_runtime_begin]
  >- metis_tac[simplify_pass_no_runtime_begin] >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_def, AllCaseEqs()] >>
  metis_tac[sue_expand_function_supply_label_origin]
QED
