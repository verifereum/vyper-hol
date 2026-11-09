(* Caller allocation, size-prefix and successful return decoding. *)
Theory extcallReturnCallerSuccess
Ancestors
  extcallReturnUnifiedCounted extcallReturnEntryBridge extcallReturnFrameBridge
  abiReturnSize abiBoundaryChecks abiDecoderCoherence abiReturnPrefixTransport
  abiMalformedRecursiveInterface abiMalformedSiteFrame abiValidAllocatedContract
  exprLoweringProps exprSimWordArgs placeMemoryPrimitiveForward fragExec fragGasSeq fragGasMode
  compileEnv venomState venomInst venomExecSemantics exprLowering emitHelper
  builtinSimple list rich_list finite_map words

Theorem return_size_counted:
  compile_return_value_decode lo cap a = (hi,b) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a b) s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts a b)` by
    (qpat_x_assum `compile_return_value_decode _ _ _ = _` mp_tac >>
     simp[compile_return_value_decode_def, compile_select_def,
          comp_bind_def, comp_ignore_bind_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pure_rewrite_tac[emitted_insts_def] >>
     simp_tac (srw_ss()) [] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule abi_return_size_code >> strip_tac >>
  irule straight_line_zero_gas_path >>
  fs[same_blocks_def, EVERY_MEM] >> metis_tac[]
QED
