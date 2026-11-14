(* Uniform dynamic-argument lower-bound guard, without runtime freshness. *)
Theory defaultBytesGuardPrelude
Ancestors moduleLowering abiDecoderGuard abiDecodeGuardScalar emitHelperProps emitHelper compileEnv
  exprLoweringProps bodyPtrBopScalarCompile bodyPtrBopScalarSeq
  fragGasSeqPtr fragGasOriginPtrLoop fragGasCopyLoop fragExecMem
  bodyPtrDefs ptrDiscipline ptrSafeRun venomState venomExecSemantics venomInst
  finite_map pred_set words list rich_list arithmetic fragExec
  ctorDeployMemoryRunMemEntryRegistration ctorDeployMemoryRunMemEntryCompositeSetup abiDecoderReentry
  loweringStateRelDefs loweringShapeDefs instIdxIndep entryDispatchPtr

Theorem default_bytes_guard_shape:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) ==>
  abi_decode_ge_guard src (Lit 4w) sa = ((),sb) /\
  inst_extends sa sb /\ same_blocks sa sb /\
  sb.cs_next_var = sa.cs_next_var + 2 /\
  sb.cs_next_id = sa.cs_next_id + 3 /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id LT [src;Lit 4w] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id+1) ISZERO [Var ("%" ++ toString sa.cs_next_var)]
       ["%" ++ toString (sa.cs_next_var+1)];
     mk_inst (sa.cs_next_id+2) ASSERT [Var ("%" ++ toString (sa.cs_next_var+1))] []]
Proof
  simp[compile_abi_arg_ptr_guard_def, abi_decode_ge_guard_def] >> strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, inst_extends_def, same_blocks_def,
    APPEND_ASSOC, DROP_PREFIX]
QED

Theorem default_bytes_guard_exec:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) /\
  eval_operand src s = SOME w /\ 4 <= w2n w ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (update_var ("%" ++ toString (sa.cs_next_var + 1)) 1w
      (update_var ("%" ++ toString sa.cs_next_var) 0w s))
Proof
  strip_tac >> drule default_bytes_guard_shape >> strip_tac >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  `step_inst_base (mk_inst sa.cs_next_id LT [src;Lit 4w] [v0]) s =
    OK (update_var v0 0w s)` by
    (qspecl_then [`src`,`Lit 4w`,`w`,`4w`] mp_tac step_LT >>
     simp[eval_operand_def, bool_to_word_def, dimword_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) ISZERO [Var v0] [v1])
    (update_var v0 0w s) = OK (update_var v1 1w (update_var v0 0w s))` by
    (qspecl_then [`Var v0`,`0w`] mp_tac step_ISZERO >>
     simp[eval_operand_def, lookup_var_update_var, bool_to_word_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) ASSERT [Var v1] [])
    (update_var v1 1w (update_var v0 0w s)) =
    OK (update_var v1 1w (update_var v0 0w s))` by
    (irule step_ASSERT_ok >> qexists `1w` >>
     simp[eval_operand_def, lookup_var_update_var]) >>
  gvs[Abbr `v0`, Abbr `v1`] >> simp[run_inst_seq_def]
QED

Theorem default_bytes_guard_uniform_sequence:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) /\
  eval_operand src s = SOME w /\ 4 <= w2n w /\
  op_prov G src = NONE /\ op_taint tn src = {} /\ ~ctx_has_dalloca ctx ==>
  ?H u.
    (!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H u) /\
    op_prov H src = NONE /\ op_taint u src = {} /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP u.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {src;Lit 4w}
      (emitted_insts sa sb) B` by
    (irule (Q.INST [`a` |-> `src`, `b` |-> `Lit (4w:bytes32)`]
       abi_decode_ge_guard_scalar) >>
     fs[compile_abi_arg_ptr_guard_def, abi_decode_ge_guard_def] >> metis_tac[]) >>
  `!op. op IN {src;Lit 4w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  drule_all default_bytes_guard_exec >> strip_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`,`PG`,`ARB`] strip_assume_tac) >>
  qexistsl [`G'`,`tn'`] >> simp[] >>
  reverse conj_tac
  >- (drule bop_scalar_seq_available >> simp[SUBSET_DEF] >> metis_tac[]) >>
  gen_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  metis_tac[inst_seq_ptr_ghost_unique]
QED

(* A finite checked scalar prefix pulls a continuation back without any
   requirement on phi prefixes in other blocks. *)
Theorem scalar_inst_seq_ptr_pullback:
  !code s raw G tn H u.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      (!a b. step_inst_base i a = OK b ==> b.vs_current_bb = a.vs_current_bb)) code /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (!j. j < LENGTH code ==>
      get_instruction bb (s.vs_inst_idx+j) = SOME (EL j code)) /\
    run_inst_seq code s = OK raw /\
    inst_seq_ptr D lo ctx fn PG G tn code s H u /\
    (!fuel. ptr_safe_run D lo fuel ctx fn PG H u
      (raw with vs_inst_idx := s.vs_inst_idx + LENGTH code)) ==>
    !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  Induct
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >>
      gvs[] >> metis_tac[venom_state_accfupds]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[Once run_inst_seq_def, Once inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK t` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq code (t with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[fragExecTheory.run_inst_seq_inst_idx, exec_result_map_def] >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG (step_prov PG G h t)
    (step_taint h s t tn) (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (first_x_assum irule >>
     `t.vs_current_bb = s.vs_current_bb` by metis_tac[] >> simp[] >>
     conj_tac
     >- (gen_tac >> strip_tac >>
         qpat_x_assum `!j. j < SUC _ ==> _` (qspec_then `SUC j` mp_tac) >> simp[ADD1]) >>
     qexistsl [`H`,`u`] >>
     `LENGTH code + SUC s.vs_inst_idx = SUC (LENGTH code) + s.vs_inst_idx`
       by decide_tac >> simp[]) >>
  gen_tac >> irule entryDispatchPtrTheory.ptr_safe_run_scalar_continuation >>
  qexistsl [`bb`,`h`,`t`] >> simp[step_inst_non_invoke] >>
  conj_tac
  >- (qpat_x_assum `!j. j < SUC _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  simp[ptr_safe_step_def] >> metis_tac[ptr_inst_ok_fuel]
QED

Theorem default_bytes_guard_prelude:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) /\
  eval_operand src s = SOME w /\ 4 <= w2n w /\
  abi_decoder_operand_live sa.cs_next_var src /\
  op_prov G src = NONE /\ op_taint tn src = {} /\
  fn_has_code sa sb fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  alloca_history fn s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?ready H u.
    ready = (update_var ("%" ++ toString (sa.cs_next_var+1)) 1w
      (update_var ("%" ++ toString sa.cs_next_var) 0w s))
      with vs_inst_idx := LENGTH sb.cs_current_insts /\
    ready = s with <|vs_vars := ready.vs_vars;
      vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~ready.vs_halted /\ ready.vs_current_bb = sb.cs_current_bb /\
    ready.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand src ready = SOME w /\ op_prov H src = NONE /\ op_taint u src = {} /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op ready = eval_operand op s) /\
    (!v. not_fresh_at sa v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    allocas_from lo ready /\ alloca_history fn ready /\
    sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
    gas_path_mem ctx fn s 0 (OK ready) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK ready,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u ready) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all default_bytes_guard_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK raw` >>
  drule_all default_bytes_guard_uniform_sequence >>
  disch_then (qspecl_then [`fn`,`PG`] (qx_choose_then `H`
    (qx_choose_then `u` strip_assume_tac))) >>
  drule default_bytes_guard_shape >> strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    gvs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule ctor_arithmetic_tail_mem_ok >> simp[mk_inst_def]) >>
  `raw.vs_allocas = s.vs_allocas /\ raw.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `raw`, update_var_def] >>
  drule_all ctor_checked_arg_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl [`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`H`,`u`] >>
  pure_rewrite_tac[CONJ_ASSOC] >>
  reverse conj_tac >- suspend "pullback" >>
  reverse conj_tac >- suspend "origin" >>
  suspend "fields"
QED
Resume default_bytes_guard_prelude[fields]:
  `!op. abi_decoder_operand_live sa.cs_next_var op ==>
    eval_operand op (raw with vs_inst_idx := LENGTH sb.cs_current_insts) =
    eval_operand op s` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, Abbr `raw`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       not_fresh_at_def] >>
     rpt strip_tac >>
     `s' <> "%" ++ toString sa.cs_next_var /\
      s' <> "%" ++ toString (sa.cs_next_var+1)` by
       (rpt strip_tac >> gvs[ASCIInumbersTheory.toString_11]) >> simp[]) >>
  simp[Abbr `raw`, update_var_def, allocas_from_def,
    op_taint_def, venom_state_component_equality] >>
  fs[allocas_from_def]
QED
Resume default_bytes_guard_prelude[origin]:
  rpt gen_tac >> irule emitted_origin_ptr_path >>
  simp[] >> qexists `sa` >> simp[EVERY_CONJ, is_terminator_def] >>
  irule inst_seq_ptr_lower_bound_transport >>
  simp[mk_inst_def] >> qexists `0` >>
  qpat_x_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (qspec_then `D` mp_tac) >>
  simp[mk_inst_def]
QED
Resume default_bytes_guard_prelude[pullback]:
  gen_tac >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    !j. j < LENGTH (emitted_insts sa sb) ==>
      get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts sa sb))` by
    (qpat_assum `s.vs_current_bb = _` SUBST1_TAC >>
     qpat_assum `s.vs_inst_idx = _` SUBST1_TAC >>
     irule fn_has_code_same_block >> qexists `sb` >>
     fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def,
       DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def,
       DROP_LENGTH_APPEND] >> gvs[] >> simp[]) >>
  irule scalar_inst_seq_ptr_pullback >>
  qexistsl [`H`,`bb`,`emitted_insts sa sb`,`raw`,`u`] >>
  simp[] >> conj_tac
  >- (simp[is_terminator_def] >>
      rpt conj_tac >> rpt strip_tac
      >- (drule (SRULE [] (Q.INST [`opc` |-> `LT`] bodyPtrBopScalarStepTheory.bop_scalar_state_frame)) >>
          simp[venom_state_component_equality] >> metis_tac[])
      >- (drule (SRULE [] (Q.INST [`opc` |-> `ISZERO`] bodyPtrBopScalarStepTheory.bop_scalar_state_frame)) >>
          simp[venom_state_component_equality] >> metis_tac[]) >>
      metis_tac[bodyPtrBopAssertTheory.bop_assert_success_state]) >>
  irule inst_seq_ptr_lower_bound_transport >> simp[mk_inst_def] >>
  qexists `0` >>
  qpat_x_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `D` mp_tac) >> simp[mk_inst_def]
QED
Finalise default_bytes_guard_prelude
