(* The frozen abi_args_post body failed isolated elaboration: wb_frame's
   third argument is an evaluation_state, but expr_val_at fixes sa as a
   compile_state.  This checked signature fact records the current interface;
   it is not a logical counterexample to the requested theorem. *)
Theory exprSimAbiEncodeArgsContractProbe
Ancestors
  loweringPosts exprSimDefs

Theorem wb_frame_current_signature:
  (wb_frame ce es : evaluation_state -> compile_state ->
     venom_state -> venom_state -> bool) = wb_frame ce es
Proof
  simp[]
QED
