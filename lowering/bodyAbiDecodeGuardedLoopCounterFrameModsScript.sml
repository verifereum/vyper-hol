Theory bodyAbiDecodeGuardedLoopCounterFrameMods
Ancestors
  bodyFullAbiDecodeLoopHeaderExact bodyFullAbiDecodeRelativeLoadExact
  bodyFullAbiDecodeFiniteObserved assignBasePtrBytesPrefix
  allocaFootprint gasOriginPtrLabels instSeqPtrLo fragGasOriginPtrDead
  fragGasOriginPtrLoop fragGasCopyLoop stmtReasonLitFragMemory fragExec fragGasPath
  fragGasCopySeqLiftProps stateFrame emitHelperProps loweringShapeRules
  compileEnv emitHelper venomInst venomExecSemantics venomState
  words list finite_map exprLoweringProps freshWrites rich_list loweringStateRelDefs

local
  val (entry, post) = dest_imp (concl abi_decode_loop_counter_load_exact)
  val (results, body) = strip_exists post
  val tnf = List.last results
  val tn = List.find (fn v => fst (dest_var v) = "tn") (free_vars entry) |> valOf
  val frame = ``^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
                ^tnf.t_imm = ^tn.t_imm``
  val raw = mk_imp (entry, list_mk_exists (results, mk_conj (body, frame)))
  val tm = rhs (concl (DEPTH_CONV BETA_CONV raw))
  val vars = free_vars tm
in
  val counter_frame_stmt = list_mk_forall (vars, tm)
  (* Keep the owned-state application intact during transport. *)
  val fold_counter_frame = CONV_TAC (REWR_CONV (GSYM
    (DEPTH_CONV BETA_CONV (list_mk_forall (vars, raw)))))
  val owned_decoder_state = #1 (strip_comb (find_term (fn tm =>
    let val (head,args) = strip_comb tm
    in is_abs head andalso length args = 4 end) body))
end

Theorem abi_decode_loop_counter_load_frame_exact:
  ^counter_frame_stmt
Proof
  fold_counter_frame >> rpt gen_tac >> strip_tac >>
  drule_all (assign_base_bytes_mload_seq |> Q.SPECL
    [`<|d_stor := K (K {}); d_trans := K (K {});
                d_imm := K {}; d_ret := K {}|>`, `ctx`, `fn`, `PG`]) >>
  disch_then (qspecl_then [`fn`, `PG`, `sa.cs_next_id`, `out`] strip_assume_tac) >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] /\
   inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   (!x. not_fresh_at sa x ==> x <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def, emitted_insts_def,
      inst_extends_def, not_fresh_at_def, DROP_APPEND1] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
   t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[Abbr `t`, update_var_def, state_frame_def] >>
  `!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `t`, lookup_var_update_var, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `lo <= s.vs_alloca_next /\ alloca_history fn s` by fs[] >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[mk_inst_def] >>
     gvs[inst_extends_def, IS_PREFIX_APPEND]) >>
  `(^owned_decoder_state) sb t G' tn'` by
    (irule abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]` by
    gvs[inst_extends_def, emitted_insts_def] >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)` by
    (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] /\
      LENGTH (FILTER (\i. i.inst_opcode = GAS)
        [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]) = 0` by
       simp[mk_inst_def, is_terminator_def] >>
     qpat_x_assum `fn_has_code sa sb fn` kall_tac >>
     rpt strip_tac >> drule_all abi_decode_finite_success_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[Abbr `t`]) >>
  drule_all fn_has_code_code >> strip_tac >>
  `run_inst_seq_mem_ok [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] s` by
    (drule emit_mload_mem_ok >>
     disch_then (qspec_then `s` mp_tac) >> simp[eval_operand_def]) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> 0 ctx fn PG G tn
      [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] s G' tn'` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  reverse conj_tac >- simp[Abbr `t`, eval_operand_def, lookup_var_def,
    update_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
     [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]` by
    simp[mk_inst_def, is_terminator_def] >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
      [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]` by
       (qpat_assum `[_] = pre ++ i::post` SUBST1_TAC >> simp[MEM_APPEND]) >>
     fs[mk_inst_def]) >>
  drule_all run_inst_seq_origin_ptr_lift >>
  simp[Abbr `t`]
QED
