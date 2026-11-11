(* Memory-safe setup and finish around the live-window encoder. *)
Theory abiEncodeWindowMemory
Ancestors
  abiBuiltinEncodeCode abiEncoderWindowRunMem windowPhaseMem
  abiEncoderWindowPhase abiBuiltinEncodeCorrect abiBuiltinEncodeContext
  externalReturnDestinationMem abiEncoderWindowChild abiEncoderRegisteredEffect
  emitHelperProps exprLoweringProps emitHelper compileEnv
  venomState venomExecSemantics venomInst words list arithmetic pred_set
  fragExec abiEncoderAddressReach instIdxIndep venomMemProps
  abiEncoderWindowContract memContinuation

Theorem abi_encode_finish_window_mem:
  abi_builtin_encode_finish buf len mid st = ((),en) /\
  fn_has_code st en func /\ eval_operand buf s = SOME (n2w p) /\
  eval_operand len s = SOME w /\
  (!x. buf = Var x ==> not_fresh_at st x) /\
  p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [(p,32)] s t /\
    mem_cont_sim ctx func s t /\
    eval_operand buf t = SOME (n2w p) /\
    mload p t = w + n2w mid
Proof
  Cases_on `mid > 0`
  >- (asm_simp_tac bool_ss [abi_builtin_encode_finish_def, comp_bind_def, LET_THM] >>
      pairarg_tac >> strip_tac >> gvs[] >>
      rename1 `emit_op ADD [len;Lit (n2w mid)] st = (total_op,add_st)` >>
      `fn_has_code st add_st func /\ fn_has_code add_st en func /\
       st.cs_next_var <= add_st.cs_next_var` by
        (drule abi_encoder_emit_address_shape >> strip_tac >>
         drule window_child_void_shape >> strip_tac >>
         drule window_child_emit_counter >> strip_tac >>
         drule_all fn_has_code_split >> simp[]) >>
      `eval_operand (Lit (n2w mid)) s = SOME (n2w mid)` by simp[eval_operand_def] >>
      drule_all window_emit_add_phase_mem >> strip_tac >>
      rename1 `window_phase ctx func st add_st {} [] s prepared` >>
      `eval_operand buf prepared = SOME (n2w p)` by
        metis_tac[window_phase_operand] >>
      `alloca_inv prepared /\ alloca_room ctx func prepared /\
       ~prepared.vs_halted /\ prepared.vs_current_bb = add_st.cs_current_bb /\
       prepared.vs_inst_idx = LENGTH add_st.cs_current_insts /\
       p+32 <= prepared.vs_alloca_next` by
        (fs[window_phase_def, window_alloca_growth_def] >> decide_tac) >>
      drule_all window_output_store_phase_mem >> strip_tac >>
      qexists_tac `(mstore p (w+n2w mid) prepared) with vs_inst_idx := LENGTH en.cs_current_insts` >>
      conj_tac
      >- (irule window_phase_chain >> qexistsl_tac [`{}`, `[]`, `add_st`,
            `{}`, `[(p,32)]`, `prepared`] >> simp[]) >>
      conj_tac >- metis_tac[mem_cont_sim_trans] >>
      simp[eval_operand_mstore, eval_op_inst_idx] >>
      `mload p (mstore p (w+n2w mid) prepared) = w+n2w mid` by simp[mload_mstore_same] >>
      gvs[mload_def]) >>
  `mid = 0` by decide_tac >>
  asm_simp_tac bool_ss [abi_builtin_encode_finish_def] >> strip_tac >>
  drule_all window_output_store_phase_mem >> strip_tac >>
  qexists_tac `(mstore p w s) with vs_inst_idx := LENGTH en.cs_current_insts` >>
  simp[eval_operand_mstore, eval_op_inst_idx] >>
  `mload p (mstore p w s) = w` by simp[mload_mstore_same] >>
  gvs[mload_def, WORD_ADD_0]
QED
