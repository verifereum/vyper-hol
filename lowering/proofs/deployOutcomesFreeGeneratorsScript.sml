Theory deployOutcomesFreeGenerators
Ancestors
  ctorCallFreeRules
  exprLowering context emitHelper compileEnv
  exprBopLowering builtinSimple list pair venomInst
  ctorCallFreeValues

(* Pointer companion of exprBopLowering's as_stack_val_pair. *)
Theorem as_ptr_val_pair:
  !ty loc p. as_ptr_val ty loc p = (LocatedValue ty (mk_ptr (FST p) loc), SND p)
Proof
  Cases_on `p` >> simp[as_ptr_val_def]
QED
