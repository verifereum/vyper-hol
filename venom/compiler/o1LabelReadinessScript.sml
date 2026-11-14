(* Preserve the absence of the constructor runtime symbol through an
   actual configured pass. Function shape excludes reserved block labels,
   including labels introduced into PHIs or substituted by CFG passes. *)
Theory o1LabelReadiness
Ancestors
  o1PassContract venomInst list

Theorem fn_pass_step_no_runtime_begin:
  fn_pass_step rpolicy pass observed s fn out /\
  o1_fn_shape observed.cu_context fn /\
  (!inst. MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !inst. MEM inst (fn_insts out.fpo_function) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  cheat
QED
