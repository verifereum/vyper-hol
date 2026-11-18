Theory bodyFullAbiDecodeLoopObservedSyntax
Ancestors
  bodyFullAbiDecodeRuntimeLoopSyntax fragGasPath bodyPtrDefs
Libs
  bodyFullAbiDecodeLoopObservedSyntaxLib

(* The first conjunct of the generated loop IH is the guarded child
   call; specialize its offset-branch flag and operands at the setup cut. *)
Theorem abi_decode_loop_observed_recursive_call_schema[local]:
  ^observed_recursive_call_schema
Proof
  gen_tac >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspecl_then [`dec_info_needs_offset ei`, `child_dst`, `child_src`] mp_tac) >>
  rewrite_tac[]
QED

Theorem abi_decode_loop_observed_recursive_call:
  (^observed_loop_ih) /\
  abi_decode_array_element_setup ip src dst opc base_op hi ei asz msz body_st =
    ((idx,child_src,child_dst),child) ==>
  (^guarded_plus) child_dst child_src opc base_op hi ei
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  ACCEPT_TAC (CONV_RULE (REDEPTH_CONV BETA_CONV) (SPEC robust_at abi_decode_loop_observed_recursive_call_schema))
QED

Theorem abi_decode_loop_observed_recursive_call_typed:
  (^observed_loop_ih_typed) /\
  abi_decode_array_element_setup ip src dst opc base_op hi ei asz msz body_st =
    ((idx,child_src,child_dst),child) ==>
  (^guarded_plus_typed) child_dst child_src opc base_op hi ei
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  ACCEPT_TAC (CONV_RULE (REDEPTH_CONV BETA_CONV) (SPEC robust_at_typed abi_decode_loop_observed_recursive_call_schema))
QED
