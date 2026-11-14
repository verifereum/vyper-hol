(* Bounded accepted scalar decoder, with one concrete joint trace. *)
Theory dispatchedDecoderWordJoint
Ancestors calldataWordPtr dispatchedDecoderLoadJoint dispatchedDecoderClampJoint
  dispatchedDecoderStoreJoint dispatchedDecoderTrace calldataOverwritePtr
  calldataWordStepsPtr calldataClampPtr calldataDecodePtr abiDecoderClampedWord
  abiDecoderContract abiDecoderClamp abiEncoder compileEnv loweringStateRelDefs
  emitHelper emitHelperProps exprLoweringProps fragExec venomInst list arithmetic
  words bodyPtrDefs decoderGhostFramePtr ptrDiscipline ptrSafeRun venomState
  venomExecSemantics entryDispatchPtr fragExecPtr ghostPcTransportPtr finite_map
  pred_set codegenRel instIdxIndep ptrSafetyTransport

Theorem calldata_word_accepted_joint:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\
  abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD sw s) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s 32 /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ w2n dw + 32 <= s.vs_alloca_next ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    alloca_inv s' /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK s',G',tn'))
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  `inst_extends sa c1 /\ inst_extends c2 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `same_blocks sa c1 /\ same_blocks c2 sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa c1 /\ cs_extends c2 sb` by
    (fs[inst_extends_def, same_blocks_def, cs_extends_def] >>
     conj_tac >> qexists_tac `[]` >> simp[]) >>
  `cs_extends c1 c2` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa c1 fn /\ fn_has_code c1 sb fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code c1 c2 fn /\ fn_has_code c2 sb fn` by
    metis_tac[fn_has_code_split] >>
  drule_all calldata_load_accepted_joint >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  rename1 `fresh_vars_wrt c1 s1` >>
  `not_fresh_at sa p` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `fresh_vars_wrt sa s` mp_tac >>
     simp[fresh_vars_wrt_def] >> qexists_tac `n` >>
     gvs[eval_operand_def, lookup_var_def, FLOOKUP_DEF]) >>
  `lookup_var p s1 = lookup_var p s` by
    metis_tac[eval_operand_def, optionTheory.SOME_11] >>
  `ptr_covers H u p s1 32` by metis_tac[ptr_covers_frame] >>
  `allocas_from lo s1` by
    (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  drule_all calldata_clamp_accepted_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `fresh_vars_wrt c2 s2` >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x` by
    (qpat_x_assum `emit_op CALLDATALOAD _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, DECIDE ``n <= n + 1``]) >>
  `lookup_var p s2 = lookup_var p s1` by
    metis_tac[eval_operand_def, optionTheory.SOME_11] >>
  `ptr_covers G' tn' p s2 32` by metis_tac[ptr_covers_frame] >>
  `eval_operand (Var p) s2 = SOME dw /\
   eval_operand value s2 = SOME (abi_decode_load CALLDATALOAD sw s)` by metis_tac[] >>
  `op_taint tn' value = {}` by
    (Cases_on `value` >> fs[op_taint_def] >>
     rename1 `eval_operand (Var x) s1 = _` >>
     `not_fresh_at c1 x` by
       (simp[not_fresh_at_def] >> rpt strip_tac >>
        qpat_x_assum `fresh_vars_wrt c1 s1` mp_tac >>
        simp[fresh_vars_wrt_def] >> qexists_tac `n` >>
        gvs[eval_operand_def, lookup_var_def, FLOOKUP_DEF]) >> metis_tac[]) >>
  `allocas_from lo s2` by
    (qpat_x_assum `allocas_from lo s1` mp_tac >> simp[allocas_from_def]) >>
  `w2n dw + 32 <= s2.vs_alloca_next` by metis_tac[] >>
  drule_all clean_mstore_accepted_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!a z. eval_operand a s = SOME z ==> eval_operand a t = SOME z` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> FLOOKUP H' x = FLOOKUP G x /\
     op_taint u' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `(!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H' u' t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)` by metis_tac[] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H',u')` by
    metis_tac[dispatched_decoder_joint_then] >>
  qexistsl_tac [`t`, `H'`, `u'`] >> simp[] >>
  suspend "word_sequence"
QED

Resume calldata_word_accepted_joint[word_sequence]:
  reverse conj_tac >- metis_tac[SUBSET_TRANS, SUBSET_REFL] >>
  `c1.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c1 /\
   c2.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 c2 /\
   sb.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 sb` by
    (drule calldata_clamp_instructions >> fs[inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[mk_inst_def, is_terminator_def] >> fs[MEM] >>
     Cases_on `signed` >> simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 sb)` by
    (drule emitted_insts_emit_void >> simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts c1 c2) (s1 with vs_inst_idx := s.vs_inst_idx) =
    OK (s2 with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `run_inst_seq (emitted_insts c2 sb) (s2 with vs_inst_idx := s.vs_inst_idx) =
    OK (t with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qspecl_then [`sa`, `c1`, `sb`, `s`, `s1 with vs_inst_idx := s.vs_inst_idx`]
    mp_tac run_inst_seq_chain >> simp[]
QED

Finalise calldata_word_accepted_joint
