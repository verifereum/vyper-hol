Theory abiDecodePtrSelectionOutcome
Ancestors
  abiDecodePtrHead abiDecoderGuard abiDecoderRange arithmeticProps
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words list
  abiEncoderWindowSequence abiEncoderWindowLookup abiEncoder
  abiDecodePtrPrims

(* Defined scalar operands make the underflow guard either succeed or revert. *)
Theorem abi_decode_ge_guard_outcome:
  abi_decode_ge_guard a b sa = ((),sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u \/
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op LT [a;b] sa = (underflow,c1)` >>
  rename1 `emit_op ISZERO [underflow] c1 = (ok,c2)` >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
      emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Ntimes run_inst_seq_def 2, Ntimes step_inst_base_def 2, mk_inst_def,
       exec_pure2_def, eval_operands_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure1_def, eval_operands_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, eval_operands_def] >>
  simp[run_inst_seq_def, step_inst_base_def, exec_pure1_def,
       eval_operands_def, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[exec_pure2_def, eval_operands_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `w2n va < w2n vb` >> simp[bool_to_word_def]
QED

(* The selection prefix is total on live operands, independently of freshness
   of the runtime variable map and independently of whether the guard holds. *)
Theorem abi_decode_getelemptr_outcome:
  compile_getelemptr_abi pos T off MLOAD (Var src) hi sa = (v,sb) /\
  not_fresh_at sa src /\ (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ eval_operand (Var src) s = SOME b ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u \/
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u
Proof
  strip_tac >> drule abi_decode_getelemptr_dynamic_split >> strip_tac >>
  `emit_op ADD [Var src;head] c1 = (addr,c2)` by
    fs[compile_abi_dec_addr_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by
    simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq sa c1 s t1` >>
  `eval_operand (Var src) t1 = SOME b` by
    (irule window_seq_eval >> qexistsl_tac [`s`, `sa`, `c1`] >>
     fs[window_pure_seq_def]) >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq c1 c2 t1 t2` >>
  `eval_operand addr t2 = SOME (n2w (w2n (b + (z+n2w off))))` by
    simp[] >>
  `w2n (b + (z+n2w off)) < dimword(:256)` by simp[w2n_lt] >>
  drule_all window_emit_load_pure >> strip_tac >>
  rename1 `window_pure_seq c2 c3 t2 t3` >>
  `window_pure_seq sa c3 s t3` by metis_tac[window_pure_seq_chain] >>
  `eval_operand pos t3 = SOME z` by
    (irule window_seq_eval >> qexistsl_tac [`s`, `sa`, `c3`] >>
     fs[window_pure_seq_def]) >>
  qpat_assum `emit_op ADD [pos;offset] c3 = (v,mid)`
    (mp_then Any mp_tac window_emit_add_pure) >>
  disch_then (qspec_then `t3` mp_tac) >> simp[] >> strip_tac >>
  rename1 `window_pure_seq c3 mid t3 t4` >>
  `window_pure_seq sa mid s t4` by metis_tac[window_pure_seq_chain] >>
  Cases_on `hi = Lit 0w`
  >- (gvs[window_pure_seq_def, window_seq_def] >> metis_tac[]) >>
  `eval_operand pos t4 = SOME z` by
    (irule window_seq_eval >> qexistsl_tac [`s`, `sa`, `mid`] >>
     fs[window_pure_seq_def]) >>
  `abi_decode_ge_guard v pos mid = ((),sb)` by gvs[] >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> fs[window_pure_seq_def, window_seq_def,
                                    inst_extends_def]) >>
  `run_inst_seq (emitted_insts sa sb) s =
   run_inst_seq (emitted_insts mid sb) t4` by
    (asm_rewrite_tac[] >> irule run_inst_seq_append >>
     fs[window_pure_seq_def, window_seq_def]) >>
  drule_all abi_decode_ge_guard_outcome >> metis_tac[]
QED
