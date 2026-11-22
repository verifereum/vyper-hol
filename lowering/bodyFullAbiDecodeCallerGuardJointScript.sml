(* The pre-allocation length guard, with one endpoint for all observers. *)
Theory bodyFullAbiDecodeCallerGuardJoint
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeCallerHeaderGuard
  bodyFullAbiDecodeClampMemory bodyFullAbiDecodeLeafCases
  bodyFullAbiDecodeFiniteGuard bodyFullAbiDecodeFiniteObserved
  bodyFullBopWordSuccess
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  exprSimAbiDecodeBuiltinHeader exprSimAbiDecodeFreshProbe
  abiDecoderAbortReentry abiDecoderVarSequence abiDecoderVarExtend abiDecoderReentry
  abiDecoderReentryPointer abiBuiltinPrefix
  emitHelperProps exprLoweringProps compileEnv emitHelper freshWrites
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome bodyPtrBopScalarDynamic
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPathMem fragGasPath
  venomExecSemantics venomState venomInst words list rich_list pred_set
  bodyPtrBopScalarCompile fragGasCopyLoop entryDecoderHistoryFrame stateRelProj
  abiBuiltinDecodeSetup abiBuiltinAllocation fragExec calldataClampPtr
  abiDecodePtrMemberFrame bodyPtrDefs ptrDiscipline stateFrame fragGasPathPtr
  instSeqPtrLo fragGasSeqPtr fragGasOriginPtrDead arithmetic
  bodyFullAbiDecodeRelativeLoadExact[qualified]

Theorem abi_decode_caller_guard_reentry[local]:
  abi_builtin_length_guard len mn mx sa = ((),sb) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)
Proof
  Cases_on `mn = mx` >>
  simp[abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
    abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_caller_guard_runtime[local]:
  abi_builtin_length_guard len mn mx sa = ((),sb) /\
  eval_operand len u = SOME (n2w cnt) /\
  mn <= mx /\ mx < dimword (:256) /\ cnt < dimword (:256) /\
  abi_decoder_operand_live sa.cs_next_var len ==>
  ((mn <= cnt /\ cnt <= mx) ==>
     ?v. run_inst_seq (emitted_insts sa sb) u = OK v) /\
  (~(mn <= cnt /\ cnt <= mx) ==>
     ?v. run_inst_seq (emitted_insts sa sb) u = Abort Revert_abort v)
Proof
  strip_tac >> drule abi_builtin_length_guard_shape >> strip_tac >>
  `fresh_vars_wrt sb (abi_decoder_prune_vars sa.cs_next_var u)` by
    (irule abi_decode_pruned_limit_fresh >> simp[]) >>
  `eval_operand len (abi_decoder_prune_vars sa.cs_next_var u) = SOME (n2w cnt)` by
    simp[abi_decoder_prune_eval] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)` by
    metis_tac[abi_decode_caller_guard_reentry] >>
  `abi_decoder_vars_extend u.vs_vars (abi_decoder_prune_vars sa.cs_next_var u) u` by
    irule abi_decoder_prune_extension >>
  `sb.cs_next_var <= sb.cs_next_var` by simp[] >>
  conj_tac
  >- (strip_tac >> drule_all abi_builtin_length_guard >> strip_tac >>
      gvs[abi_builtin_prefix_def] >>
      drule_all abi_decoder_sequence_vars_extend >> metis_tac[]) >>
  strip_tac >> `mn < dimword (:256)` by decide_tac >>
  drule_all abi_decode_builtin_length_guard_revert >> strip_tac >>
  metis_tac[abi_decoder_sequence_revert_reentry]
QED

Theorem abi_decode_caller_guard_joint:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ (?H. V H) /\
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name a sz. local_region ce es0.scopes s0 name a sz ==>
    a+sz <= s.vs_alloca_next) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  data = Var data_var /\ eval_operand data s = SOME (n2w b) /\
  op_taint tn data = {} /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_decode_ptr_window G tn s data_var (n2w b) (32+LENGTH input_bytes) /\
  mload b s = n2w (LENGTH input_bytes) /\
  mem_bytes_at (b+32) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  b+32+LENGTH input_bytes <= s.vs_alloca_next /\
  b+32+LENGTH input_bytes < dimword (:256) /\
  min_size <= max_size /\ max_size < dimword (:256) /\
  outsz < dimword (:256) /\ d+outsz < dimword (:256) /\
  (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
     SOME (d,outsz)) /\
  emit_op MLOAD [data] st = (len,sa) /\
  emit_op ADD [data;Lit 32w] sa = (src,sb) /\
  abi_builtin_length_guard len min_size max_size sb = ((),header_st) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (?input. src = Var input /\
    abi_decode_ptr_window Gp tnp u input (n2w (b+32)) (LENGTH input_bytes)) /\
  eval_operand len u = SOME (n2w (LENGTH input_bytes)) /\
  op_prov Gp len = NONE /\ op_taint tnp len = {} /\ op_taint tnp src = {} /\
  abi_decoder_operand_live sb.cs_next_var len /\ abi_decoder_operand_live sb.cs_next_var src /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
  tnp.t_mem = tn.t_mem /\ tnp.t_stor = tn.t_stor /\
  tnp.t_trans = tn.t_trans /\ tnp.t_imm = tn.t_imm /\ alloca_history fn u /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\
    ghost_inv_at (DF H) lo delta ce cx es Gp tnp u /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gp tnp) ==>
  ?r Gh tnh.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gp,tnp) [] (r,Gh,tnh)) /\
    (!obs. fn_has_code sb header_st obs ==> gas_path ctx obs u 0 r) /\
    ((?v. r = Abort Revert_abort v) \/
     (?v. r = OK v /\ ~v.vs_halted /\ v.vs_current_bb = header_st.cs_current_bb /\
       v.vs_inst_idx = LENGTH header_st.cs_current_insts /\
       (?input. src = Var input /\
         abi_decode_ptr_window Gh tnh v input (n2w (b+32)) (LENGTH input_bytes)) /\
       eval_operand len v = SOME (n2w (LENGTH input_bytes)) /\
       min_size <= LENGTH input_bytes /\ LENGTH input_bytes <= max_size /\
       op_prov Gh len = NONE /\ op_taint tnh len = {} /\ op_taint tnh src = {} /\
       abi_decoder_operand_live header_st.cs_next_var len /\
       abi_decoder_operand_live header_st.cs_next_var src /\
       v.vs_memory = s.vs_memory /\ v.vs_allocas = s.vs_allocas /\
       v.vs_alloca_next = s.vs_alloca_next /\
       state_frame v = state_frame (s with vs_inst_idx := v.vs_inst_idx) /\
       tnh.t_mem = tn.t_mem /\ tnh.t_stor = tn.t_stor /\
       tnh.t_trans = tn.t_trans /\ tnh.t_imm = tn.t_imm /\ alloca_history fn v /\
       (!x. not_fresh_at st x ==> lookup_var x v = lookup_var x s /\
         FLOOKUP Gh x = FLOOKUP G x /\ op_taint tnh (Var x) = op_taint tn (Var x)) /\
       (!H. V H ==> stmt_state_rel H ctx fn ce cx es v /\
         ghost_inv_at (DF H) lo delta ce cx es Gh tnh v /\
         ghost_kept_at lo ce es0 origin G0 tn0 s0 Gh tnh)))
Proof
  disch_then (fn th =>
    map_every assume_tac (CONJUNCTS th)) >>
  `LENGTH input_bytes < dimword (:256)` by decide_tac >>
  drule_all abi_decode_caller_guard_runtime >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule abi_builtin_decode_setup_trace >> strip_tac >>
  `?buf. compile_alloc_buffer outsz header_st = (buf,ready)` by
    (qpat_x_assum `abi_builtin_decode_header _ _ _ _ = _` mp_tac >>
     simp[abi_builtin_decode_header_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> strip_tac >> gvs[]) >>
  `cs_extends st sa /\ cs_extends sa sb /\ cs_extends header_st ready` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     rpt conj_tac >> irule cs_extends_same_block >>
     metis_tac[emit_op_extends, same_blocks_def, IS_PREFIX_APPEND]) >>
  drule abi_builtin_length_guard_shape >> strip_tac >>
  `cs_extends st sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sb header_st` by metis_tac[cs_extends_same_block] >>
  `fn_has_code sb header_st fn` by metis_tac[fn_has_code_mid] >>
  `st.cs_next_var <= sb.cs_next_var` by
    (`sa.cs_next_var = st.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
     `sb.cs_next_var = sa.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
     decide_tac) >>
  `sb.cs_next_var <= header_st.cs_next_var` by
    (Cases_on `min_size = max_size` >> simp[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    metis_tac[ghost_inv_at_def] >>
  qabbrev_tac `R = {x | not_fresh_at sb x}` >>
  qabbrev_tac `A = len INSERT {Lit w | T}` >>
  `len IN A /\ (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at sb x)` by
    simp[Abbr `R`, Abbr `A`] >>
  `!p. p IN A ==> op_prov Gp p = NONE /\ op_taint tnp p = {}` by
    (simp[Abbr `A`] >> gen_tac >>
     disch_then (DISJ_CASES_THEN2 SUBST1_TAC (CHOOSE_THEN SUBST1_TAC))
     >- asm_rewrite_tac[] >> simp[op_prov_def, op_taint_def]) >>
  `?B. bop_scalar_seq R A (emitted_insts sb header_st) B /\ A SUBSET B` by
    (irule abi_decode_caller_length_guard_scalar >> asm_rewrite_tac[] >>
     qexistsl [`len`,`min_size`,`max_size`] >> asm_rewrite_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) (emitted_insts sb header_st)` by
    metis_tac[bop_scalar_seq_opcodes] >>
  `header_st.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb header_st` by
    fs[inst_extends_def] >>
  `?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sb header_st) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sb header_st fn` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND, DROP_APPEND1, DROP_LENGTH_NIL,
          PULL_EXISTS] >> metis_tac[APPEND_ASSOC]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `?H. V H` (qx_choose_then `h` assume_tac) >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\ _`
       (qspec_then `h` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (mp_tac o CONJUNCT1) >>
     MATCH_ACCEPT_TAC
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  Cases_on `min_size <= LENGTH input_bytes /\ LENGTH input_bytes <= max_size`
  >- suspend "success"
  >> suspend "reject"
QED

Resume abi_decode_caller_guard_joint[success]:
  `?t. run_inst_seq (emitted_insts sb header_st) u = OK t` by metis_tac[] >>
  drule_all bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `v = t with vs_inst_idx := LENGTH header_st.cs_current_insts` >>
  `v = t with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sb header_st)` by
    simp[Abbr `v`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sb header_st) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sb header_st)) = 0` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\
        ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS) _`
       (assume_tac o SRULE [EVERY_MEM]) >>
     simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `!obs. fn_has_code sb header_st obs ==> gas_path ctx obs u 0 (OK v)` by
    (qpat_x_assum `fn_has_code sb header_st fn` kall_tac >>
     rpt strip_tac >> drule_all abi_decode_finite_success_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[Abbr `v`]) >>
  `!x. not_fresh_at sb x ==> lookup_var x v = lookup_var x u /\
      FLOOKUP G' x = FLOOKUP Gp x /\ op_taint tn' (Var x) = op_taint tnp (Var x)` by
    (simp[Abbr `v`, lookup_var_def, op_taint_def] >>
     qpat_assum `!x. x IN R ==> FLOOKUP t.vs_vars x = _` mp_tac >>
     qpat_assum `!x. x IN R ==> FLOOKUP G' x = _ /\ _` mp_tac >>
     simp[Abbr `R`] >> metis_tac[]) >>
  `state_frame v = state_frame (u with vs_inst_idx := v.vs_inst_idx)` by
    (simp[Abbr `v`, state_frame_def] >>
     qpat_assum `t = u with vs_vars := t.vs_vars` (fn th => once_rewrite_tac[th]) >>
     simp[]) >>
  `state_frame v = state_frame (s with vs_inst_idx := v.vs_inst_idx)` by
    (qpat_assum `state_frame v = _` SUBST1_TAC >>
     `u = (s with vs_inst_idx := u.vs_inst_idx) with vs_vars := u.vs_vars` by
       (qpat_assum `state_frame u = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[state_frame_eq_reconstruct]) >>
     qpat_assum `u = _` SUBST1_TAC >> simp[NoAsms, state_frame_def]) >>
  `alloca_history fn v` by
    (`alloca_inv u` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
     qunabbrev_tac `v` >> irule entry_straight_line_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb header_st)` by
       (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) _`
         mp_tac >> simp[NoAsms, EVERY_MEM]) >>
     qexistsl [`u`,`sb`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at st x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by metis_tac[] >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es v /\
    ghost_inv_at (DF H) lo delta ce cx es G' tn' v /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tn'` by
    (ho_match_mp_tac (Q.INST [`sa` |-> `st`] bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_scalar_joint_frame_lower) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~v.vs_halted /\ v.vs_current_bb = header_st.cs_current_bb /\
   v.vs_inst_idx = LENGTH header_st.cs_current_insts /\
   v.vs_memory = s.vs_memory /\ v.vs_allocas = s.vs_allocas /\
   v.vs_alloca_next = s.vs_alloca_next` by
    (simp[Abbr `v`] >> qpat_assum `t = u with vs_vars := _`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `(?input. src = Var input /\
      abi_decode_ptr_window G' tn' v input (n2w (b+32)) (LENGTH input_bytes)) /\
   op_taint tn' src = {}` by
    (qpat_assum `?input. src = Var input /\ _` strip_assume_tac >>
     `not_fresh_at sb input` by
       (UNDISCH_TAC ``abi_decoder_operand_live sb.cs_next_var src`` >>
        qpat_assum `src = Var input` SUBST1_TAC >>
        simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
             loweringStateRelDefsTheory.not_fresh_at_def]) >>
     conj_tac >- (qexists_tac `input` >> conj_tac >- first_assum ACCEPT_TAC >>
       match_mp_tac (Q.INST [`G` |-> `Gp`, `s` |-> `u`, `tn` |-> `tnp`]
         (SPEC_ALL abi_decode_ptr_window_frame)) >>
       qpat_assum `!x. not_fresh_at sb x ==> lookup_var x v = lookup_var x u /\ _`
         (fn frame => qpat_assum `not_fresh_at sb input`
           (strip_assume_tac o MATCH_MP (Q.SPEC `input` frame))) >>
       asm_rewrite_tac[]) >>
     metis_tac[]) >>
  `eval_operand len v = SOME (n2w (LENGTH input_bytes))` by
    (`?x. len = Var x` by metis_tac[emitted_insts_emit_op] >>
     `not_fresh_at sb x` by
       (UNDISCH_TAC ``abi_decoder_operand_live sb.cs_next_var len`` >>
        qpat_assum `len = Var x` SUBST1_TAC >>
        simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
             loweringStateRelDefsTheory.not_fresh_at_def]) >>
     `lookup_var x v = lookup_var x u` by metis_tac[] >>
     qpat_assum `eval_operand len u = SOME (n2w (LENGTH input_bytes))` mp_tac >>
     qpat_assum `len = Var x` SUBST1_TAC >> simp[eval_operand_def]) >>
  `op_prov G' len = NONE /\ op_taint tn' len = {}` by metis_tac[SUBSET_DEF] >>
  `abi_decoder_operand_live header_st.cs_next_var len /\
   abi_decoder_operand_live header_st.cs_next_var src` by
    metis_tac[abi_decoder_operand_live_mono] >>
  Q_TAC (C SUBGOAL_THEN ASSUME_TAC) `?p. src = Var p /\
    abi_decode_ptr_window G' tn' v p (n2w (b+32)) (LENGTH input_bytes)`
  >- (qexists_tac `input` >> asm_rewrite_tac[]) >>
  qpat_assum `min_size <= LENGTH input_bytes /\ _`
    (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qexistsl [`OK v`,`G'`,`tn'`] >>
  conj_tac >- (rpt strip_tac >> qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `DF H` mp_tac) >> qpat_assum `v = _` SUBST1_TAC >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> disj2_tac >> qexists_tac `v` >>
  conj_tac >- REFL_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_caller_guard_joint[reject]:
  `?t. run_inst_seq (emitted_insts sb header_st) u = Abort Revert_abort t` by
    metis_tac[] >>
  drule_all bop_scalar_seq_abort_prefix >>
  disch_then (REPEAT_TCL CHOOSE_THEN
    (fn th => map_every assume_tac (CONJUNCTS th))) >>
  rename1 `step_inst_base (mk_inst id opc [cond] []) p = Abort Revert_abort t` >>
  `EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE)
     (emitted_insts sb header_st)` by
    (qpat_x_assum `abi_builtin_length_guard _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `min_size = max_size` >>
     simp[abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
       abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  `opc <> ASSERT_UNREACHABLE` by
    (qpat_x_assum `EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) _` mp_tac >>
     simp[EVERY_APPEND, mk_inst_def]) >>
  `opc = ASSERT` by
    (qpat_x_assum `opc = ASSERT \/ opc = ASSERT_UNREACHABLE` mp_tac >> simp[]) >>
  qpat_x_assum `opc = ASSERT` SUBST_ALL_TAC >>
  qabbrev_tac `cut = prefix ++ [mk_inst id ASSERT [cond] []]` >>
  `emitted_insts sb header_st = cut ++ suffix` by simp[Abbr `cut`] >>
  `isPREFIX cut (DROP u.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (emitted_insts sb header_st) _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> disch_then (qx_choose_then `tail` SUBST1_TAC) >>
     qexists_tac `suffix ++ tail` >> simp[APPEND_ASSOC]) >>
  `bop_scalar_seq R A cut C` by
    (simp[Abbr `cut`] >> irule bop_scalar_seq_append >>
     goal_assum (drule_at Any) >> irule bop_scalar_seq_assert >> simp[]) >>
  `run_inst_seq_mem_ok cut u` by
    (irule abi_decode_scalar_seq_mem_ok >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) cut` by
    (qpat_x_assum `EVERY (\i. _ /\ _ /\ ~is_alloca_op _) _` mp_tac >>
     qpat_x_assum `EVERY (\i. _ /\ _ /\ i.inst_opcode <> GAS) _` mp_tac >>
     simp[EVERY_APPEND, EVERY_MEM] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[cj 1 is_alloca_op_def]) >>
  `run_inst_seq cut u = Abort Revert_abort t` by
    (simp[Abbr `cut`] >> drule run_inst_seq_append >>
     disch_then (qspec_then `[mk_inst id ASSERT [cond] []]` mp_tac) >>
     simp[run_inst_seq_def]) >>
  qpat_x_assum `bop_scalar_seq R A (emitted_insts sb header_st) B` kall_tac >>
  qpat_x_assum `bop_scalar_seq R A prefix C` kall_tac >>
  drule_all calldataClampPtrTheory.scalar_seq_abort_replay_ptr >>
  disch_then (qspecl_then [`fn`, `PG`,
    `<| d_stor := K (K {}); d_trans := K (K {});
        d_imm := K {}; d_ret := K {} |>`] strip_assume_tac) >>
  `(ctx_has_dalloca ctx ==>
    !pre i post z. cut = pre ++ i::post /\ run_inst_seq pre u = OK z ==>
      unitTransformDefs$dalloca_no_wrap i z)` by
    (rpt strip_tac >>
     `MEM i cut` by simp[MEM_APPEND] >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     drule_all bop_scalar_seq_outputs >>
     disch_then (assume_tac o CONJUNCT1) >> strip_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     qpat_assum `i.inst_opcode = DALLOCA` (fn th => simp[NoAsms, th])) >>
  drule_all run_inst_seq_origin_ptr_abort_lift >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qabbrev_tac `rj = Abort Revert_abort (t with vs_inst_idx := j)` >>
  qabbrev_tac `rp = Abort Revert_abort
    (t with vs_inst_idx := LENGTH sb.cs_current_insts + LENGTH prefix)` >>
  `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gp,tnp) [] (rj,G',tn')` by
    (rpt strip_tac >> irule gas_origin_ptr_path_from_no_dead >>
     qunabbrev_tac `rj` >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `header_st.cs_current_insts = sb.cs_current_insts ++
      (prefix ++ mk_inst id ASSERT [cond] [] :: suffix)` by
    (qpat_assum `header_st.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb header_st`
       SUBST1_TAC >>
     qpat_assum `emitted_insts sb header_st = cut ++ suffix` SUBST1_TAC >>
     simp[NoAsms, Abbr `cut`, APPEND_ASSOC]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
    LENGTH (FILTER (\i. i.inst_opcode = GAS) prefix) = 0` by
    (qpat_x_assum `EVERY (\i. _ /\ _ /\ _ /\ i.inst_opcode <> GAS) cut` mp_tac >>
     simp[Abbr `cut`, EVERY_APPEND, EVERY_MEM, FILTER_EQ_NIL] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!obs. fn_has_code sb header_st obs ==> gas_path ctx obs u 0 rp` by
    (qpat_x_assum `fn_has_code sb header_st fn` kall_tac >>
     rpt strip_tac >> drule_all abi_decode_finite_revert_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[Abbr `rp`]) >>
  `gas_path ctx fn u 0 rj` by
    (qpat_assum `?H. V H` (qx_choose_then `h` assume_tac) >>
     qpat_assum `!H. V H ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `h` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (mp_tac o cj 1 o MATCH_MP gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP gas_origin_path_erase) >>
     simp[] >> metis_tac[gas_marked_path_exec]) >>
  `gas_path ctx fn u 0 rp` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  (* Compare the exits on fn, which is itself a compatible observer. *)
  `exit_result rj` by simp[Abbr `rj`, exit_result_def] >>
  `exit_result rp` by simp[Abbr `rp`, exit_result_def] >>
  `?k. run_from k ctx fn u = rj` by
    (irule gas_path_exit >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `0` >> first_assum ACCEPT_TAC) >>
  `?m. run_from m ctx fn u = rp` by
    (irule gas_path_exit >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `0` >> first_assum ACCEPT_TAC) >>
  `run_from (k+m) ctx fn u = rj` by
    (irule gas_run_from_fuel_mono >> conj_tac >- simp[Abbr `rj`] >>
     qexists_tac `k` >> asm_rewrite_tac[] >> decide_tac) >>
  `run_from (k+m) ctx fn u = rp` by
    (irule gas_run_from_fuel_mono >> conj_tac >- simp[Abbr `rp`] >>
     qexists_tac `m` >> asm_rewrite_tac[] >> decide_tac) >>
  `rj = rp` by
    (qpat_assum `run_from (k+m) ctx fn u = rj` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `rj = rp` (SUBST_ALL_TAC o SYM) >>
  qexistsl [`rj`,`G'`,`tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> simp[Abbr `rj`]
QED

Finalise abi_decode_caller_guard_joint
