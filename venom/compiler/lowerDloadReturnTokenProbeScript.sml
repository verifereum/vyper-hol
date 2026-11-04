Theory lowerDloadReturnTokenProbe
Ancestors
  o1PassContract unitShapeDefs venomExecSemantics venomInst venomWf
  contextCodegenRel list

(* The proposed return-token control-flow witness is excluded by a frozen
   premise. This covers copies and PHIs of the token, not just its seed. *)
Theorem ld_return_token_control_probe_excluded:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ retpc_var fn x /\
  MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [EQ; JNZ; RETURN; MLOAD; MSTORE; INVOKE] ==>
  ~MEM (Var x) inst.inst_operands
Proof
  strip_tac >> strip_tac >>
  `opaque_use_ok fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_shape_ok_def] >>
     metis_tac[]) >>
  `retpc_use_ok inst x` by metis_tac[opaque_use_ok_retpc_use] >>
  gvs[retpc_use_ok_def]
QED

(* setup_callee can indeed copy a relocated LAST argument into the token.
   However the proposed comparison/branch/observation of that token violates
   opaque_use_ok, which is part of o1_ctx_shape, even in an unreachable block.
   No falsehood of lower_dload_stage_taint is claimed. The remaining possible
   repair of the proof interface is to ignore unequal opaque return-PC values,
   tracking their copy/PHI closure and permitted final RET position rather
   than demanding equality of every scalar-looking source variable. *)
