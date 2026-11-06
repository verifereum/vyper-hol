(* Pointer simulations deliberately quantify only runtime executions.
   Constructor immutable accesses are fixed-address ILOADs, outside this
   judgment's scope; no constructor exclusion is added to the target. *)
Theory bodyPtrMakeArrayRuntimeScope
Ancestors bodyPtrDefs

Theorem constructor_expr_pointer_judgments:
  cenv.ce_is_ctor ==>
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  simp[expr_sim_ptr_def, expr_vv_sim_ptr_def]
QED
