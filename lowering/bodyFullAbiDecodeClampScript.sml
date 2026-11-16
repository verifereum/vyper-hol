Theory bodyFullAbiDecodeClamp
Ancestors
  abiDecodeClampShape abiDecodePtrScalarAbort bodyPtrBopScalarOutcome
  abiEncoder bodyPtrBopScalarDynamic bodyPtrBopScalarCompile bodyPtrBopScalarSeq
  bodyFullAbiDecodePath instSeqPtrLo abiDecoderReentry emitHelperProps
  exprLoweringProps emitHelper freshWrites compileEnv list pred_set
  venomState venomExecSemantics venomInst fragExecMem ptrDiscipline
  codegenRel contextCodegenRel memSafeRun instSeqComposePtr finite_map
  rich_list fragGasOriginPtrDead fragGasOriginPtrLoop loweringStateRelDefs

(* Static availability of the finite clamp, independent of its outcome. *)
Theorem abi_decode_live_update[local]:
  abi_decoder_operand_live next op /\ next <= n ==>
  eval_operand op (update_var (STRING #"%" (toString n)) v s) =
  eval_operand op s
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem abi_decode_clamp_runtime[local]:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  eval_operand value s = SOME w /\
  abi_decoder_operand_live sa.cs_next_var value ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t \/
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  Cases_on `clamp`
  >- (simp[compile_abi_clamp_basetype_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_def, run_inst_seq_def])
  >~ [`IntClamp bits signed`] >>> HEADGOAL (Cases_on `signed`) >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >>
  qpat_assum `emit_op _ _ sa = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa cs' ++
      emitted_insts cs' cs'' ++ emitted_insts cs'' sb` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  gvs[] >>
  `!v. eval_operand value (update_var (STRING #"%" (toString sa.cs_next_var)) v s) = SOME w` by
    metis_tac[abi_decode_live_update, arithmeticTheory.LESS_EQ_REFL] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, exec_pure2_def, eval_operand_def,
       lookup_var_update_var] >>
  IF_CASES_TAC >> simp[]
QED

Theorem abi_decode_clamp_joint:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand value s = SOME w /\ op_prov G value = NONE /\
  op_taint tn value = {} /\ abi_decoder_operand_live sa.cs_next_var value /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?r Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (r,Gf,tnf)) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       eval_operand value t = SOME w /\
       op_prov Gf value = NONE /\ op_taint tnf value = {} /\
       t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
       tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
       tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
       (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
          op_taint tnf (Var x) = op_taint tn (Var x))))
Proof
  strip_tac >>
  drule abi_decode_clamp_scalar >>
  disch_then (qspecl_then [`{x | not_fresh_at sa x}`, `{value} UNION {Lit w | T}`] mp_tac) >>
  simp[] >> strip_tac >>
  `!op. op IN {value} UNION {Lit w | T} ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  `inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb` by
    gvs[inst_extends_def, same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[bop_scalar_seq_opcodes] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by metis_tac[bop_scalar_seq_mem_ok] >>
  drule_all abi_decode_clamp_runtime >> strip_tac
  >- (drule_all (bop_scalar_seq_run |> Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
      disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
      `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
         d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
         (emitted_insts sa sb) s G' tn'` by
        (irule inst_seq_ptr_zero_to_lo >> simp[] >>
         qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
           d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
      qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
      drule_all emitted_origin_ptr_path >>
      disch_then (qspec_then `explicit` assume_tac) >>
      qexistsl_tac [`OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`, `G'`, `tn'`] >>
      conj_tac
      >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> asm_rewrite_tac[]) >>
      drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
      `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
         op_taint tn' (Var x) = op_taint tn (Var x)` by
        (rpt strip_tac >> simp[lookup_var_def, op_taint_def] >> gvs[]) >>
      `eval_operand value t = SOME w` by
        (Cases_on `value` >> gvs[eval_operand_def, abi_decoder_operand_live_def,
           abi_decoder_older_vars_def, not_fresh_at_def] >>
         qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      simp[lookup_var_def, eval_operand_def] >>
      qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      simp[lookup_var_def, eval_operand_def])
  >> drule_all (scalar_seq_abort_replay_ptr |> Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
      (emitted_insts sa sb) s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all abi_decode_emitted_abort_origin_ptr_path >>
  disch_then (qspec_then `explicit` strip_assume_tac) >>
  qexistsl_tac [`Abort Revert_abort (t with vs_inst_idx := j)`, `G'`, `tn'`] >>
  simp[] >> gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  asm_rewrite_tac[]
QED
