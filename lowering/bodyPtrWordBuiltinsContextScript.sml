(* stmt_state_rel fixes the entire function, not just its fragment prefix.
   body_inv additionally identifies ctx with the lowered unit's context. *)
Theory bodyPtrWordBuiltinsContext
Ancestors exprLoweringProps

Theorem stmt_state_rel_lookup_function:
  stmt_state_rel ctx func cenv cx es s ==>
  lookup_function func.fn_name ctx.ctx_functions = SOME func
Proof
  simp[stmt_state_rel_def, alloca_room_def]
QED
