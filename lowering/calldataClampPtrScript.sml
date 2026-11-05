(* Clean scalar validation fragments used by calldata decoders. *)
Theory calldataClampPtr
Ancestors abiDecoderClamp abiEncoder compileEnv emitHelper exprLoweringProps
  fragExec venomInst list arithmetic words bodyPtrDefs decoderGhostFramePtr
  ptrDiscipline ptrSafeRun venomState venomExecSemantics entryDispatchPtr
  fragExecPtr ghostPcTransportPtr finite_map pred_set codegenRel instIdxIndep

Theorem calldata_clamp_instructions:
  compile_abi_clamp_basetype op clamp sa = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  (emitted_insts sa sb = [] \/
   ?opc shift signed.
     MEM opc [SIGNEXTEND; SHR; SHL] /\
     emitted_insts sa sb =
       [mk_inst sa.cs_next_id opc [Lit shift; op]
          ["%" ++ toString sa.cs_next_var];
        mk_inst (sa.cs_next_id + 1) (if signed then EQ else ISZERO)
          (if signed then [op; Var ("%" ++ toString sa.cs_next_var)]
           else [Var ("%" ++ toString sa.cs_next_var)])
          ["%" ++ toString (sa.cs_next_var + 1)];
        mk_inst (sa.cs_next_id + 2) ASSERT
          [Var ("%" ++ toString (sa.cs_next_var + 1))] []])
Proof
  Cases_on `clamp`
  >- simp[compile_abi_clamp_basetype_def, comp_return_def, emitted_insts_def] >>
  TRY (rename1 `IntClamp bits signed` >> Cases_on `signed`) >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC, DROP_PREFIX] >>
  metis_tac[]
QED

(* A clean scalar is not necessarily provenance-free.  Signed validation
   compares two variables, and therefore needs a provenance side condition. *)
Theorem clamp_comparison_unmatched_provenance:
  FLOOKUP G u <> NONE /\ FLOOKUP G v = NONE ==>
  ~access_ok lo G fn (mk_inst id EQ [Var u; Var v] [out]) s
Proof
  simp[access_ok_def, mk_inst_def, FLOOKUP_DEF] >> metis_tac[]
QED
