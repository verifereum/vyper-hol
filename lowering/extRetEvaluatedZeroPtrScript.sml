Theory extRetEvaluatedZeroPtr
Ancestors
  extRetAbiSourceComplexDispatchPtr exprLowering vyperValue valueEncoding
  fragGasPathPtr compileEnv venomState ptrDiscipline pred_set

(* None is an evaluated zero-byte child, outside the old ABI-plan domain.
   The execution fact itself is reused from the existing empty dispatcher. *)
Theorem ext_ret_evaluated_none_dispatch:
  evaluate_type tenv NoneT = SOME NoneTV /\
  type_memory_size NoneTV = 0 /\
  type_to_abi_enc_info sf ce NoneT = AbiComplex []
Proof
  simp[evaluate_type_def, type_memory_size_def, type_to_abi_enc_info_def]
QED

(* No source operand evaluation, allocation or endpoint bound is needed.
   The existential endpoint exposes exact identity for recursive framing. *)
Theorem ext_ret_empty_child_endpoint_ptr:
  compile_abi_encode_to_buf dst src (AbiComplex []) sa = (out,sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  ?sf Gf tnf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = s /\ Gf = G /\ tnf = tn /\ sb = sa /\ out = Lit 0w /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME 0w /\ op_taint tnf out = {} /\
    (!base i. base <= i /\ i < base + 0 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >>
  drule_all abi_complex_empty_dispatch_counted_ptr >> strip_tac >>
  qexistsl_tac [`s`, `G`, `tn`] >> simp[]
QED
