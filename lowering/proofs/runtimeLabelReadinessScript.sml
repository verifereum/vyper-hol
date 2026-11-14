(* Runtime lowering cannot emit the constructor's runtime data symbol.
   Runtime packages use ordinary locations; generated branch and function
   labels occupy disjoint prefixed namespaces. *)
Theory runtimeLabelReadiness
Ancestors
  compileVyper venomInst list runtimeLabelInvariant runtimeLabelValues
  runtimeLabelABI runtimeLabelBuiltins runtimeLabelExpr

Theorem lower_vyper_runtime_unit_no_runtime_begin:
  !tops rpolicy unit fn inst.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  cheat
QED
