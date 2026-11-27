(* The length guard on a reached linked decoder prefix.  Neither branch
   uses a source-specific ghost invariant. *)
Theory bodyAbiDecodeLinkedSetupGuardMods
Ancestors
  abiBuiltinLengthGuard abiBuiltinBoundTests abiBuiltinPrefix
  exprSimAbiDecodeBuiltinHeader exprSimAbiDecodeFreshProbe
  abiDecoderAbortReentry abiDecoderVarSequence abiDecoderVarExtend abiDecoderReentry
  bodyFullAbiDecodeCallerHeaderGuard bodyFullAbiDecodeFiniteObserved
  bodyFullBopWordSuccess bodyPtrBopScalarOutcome bodyPtrBopScalarDynamic bodyPtrBopScalarSeq
  bodyFullAbiDecodeRelativeLoadExact bodyFullAbiDecodeFiniteGuard abiDecodePtrMemberFrame
  bodyPtrDefs finite_map arithmetic vyperAST
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath
  exprLoweringProps fragExec loweringStateRelDefs stateFrame
  emitHelperProps compileEnv emitHelper ptrDiscipline
  venomExecSemantics venomState venomInst words list rich_list pred_set

Theorem linked_length_guard_code[local]:
  abi_builtin_length_guard len mn mx sa = ((),sb) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
             i.inst_opcode <> ASSERT_UNREACHABLE) (emitted_insts sa sb)
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

Theorem linked_length_guard_runtime[local]:
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
    (drule linked_length_guard_code >> simp[EVERY_MEM]) >>
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

Theorem linked_length_guard_revert_observer[local]:
  abi_builtin_length_guard len mn mx sa = ((),sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  bop_scalar_seq R A (emitted_insts sa sb) B /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  ?j. !obs. fn_has_code sa sb obs ==>
    gas_path ctx obs s 0 (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >>
  drule linked_length_guard_code >>
  simp_tac pure_ss [EVERY_MEM] >> strip_tac >>
  drule abi_builtin_length_guard_shape >> strip_tac >>
  drule_all bop_scalar_seq_abort_prefix >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  rename1 `step_inst_base (mk_inst id opc [cond] []) _ = _` >>
  `opc <> ASSERT_UNREACHABLE` by
    (first_x_assum (qspec_then `mk_inst id opc [cond] []` mp_tac) >>
     simp[MEM_APPEND, mk_inst_def]) >>
  qpat_x_assum `opc = ASSERT \/ opc = ASSERT_UNREACHABLE`
    (DISJ_CASES_THEN2 SUBST_ALL_TAC (fn th => FULL_SIMP_TAC bool_ss [th])) >>
  `sb.cs_current_insts = sa.cs_current_insts ++
     (prefix ++ mk_inst id ASSERT [cond] [] :: suffix)` by
    fs[inst_extends_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) prefix) = 0` by
    (qpat_assum `bop_scalar_seq R A prefix C` (mp_tac o MATCH_MP bop_scalar_seq_opcodes) >>
     simp[EVERY_MEM, FILTER_EQ_NIL]) >>
  qexists_tac `LENGTH sa.cs_current_insts + LENGTH prefix` >>
  rpt strip_tac >> irule abi_decode_finite_revert_observed >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cond`,`id`,`sb`,`suffix`] >> simp[APPEND_ASSOC]
QED

Theorem linked_guard_revert_index[local]:
  gas_path ctx fn s 0 (Abort Revert_abort (t with vs_inst_idx := j)) /\
  gas_path ctx fn s 0 (Abort Revert_abort (t with vs_inst_idx := k)) ==>
  j = k
Proof
  strip_tac >>
  `?fuel. run_from fuel ctx fn s = Abort Revert_abort (t with vs_inst_idx := j)` by
    (irule gas_path_exit >> simp[exit_result_def] >> qexists_tac `0` >> simp[]) >>
  `?fuel'. run_from fuel' ctx fn s = Abort Revert_abort (t with vs_inst_idx := k)` by
    (irule gas_path_exit >> simp[exit_result_def] >> qexists_tac `0` >> simp[]) >>
  `run_from (fuel + fuel') ctx fn s = Abort Revert_abort (t with vs_inst_idx := j)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `run_from (fuel + fuel') ctx fn s = Abort Revert_abort (t with vs_inst_idx := k)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel'` >> simp[]) >>
  `t with vs_inst_idx := j = t with vs_inst_idx := k` by
    metis_tac[exec_result_11] >>
  pop_assum (mp_tac o AP_TERM ``venom_state_vs_inst_idx``) >> simp[]
QED

Theorem linked_guard_operand_frame[local]:
  v.vs_labels = u.vs_labels /\
  (!x. not_fresh_at sb x ==> lookup_var x v = lookup_var x u /\
    FLOOKUP Gh x = FLOOKUP Gp x /\ op_taint tnh (Var x) = op_taint tnp (Var x)) /\
  abi_decoder_operand_live sb.cs_next_var op ==>
  eval_operand op v = eval_operand op u /\
  op_prov Gh op = op_prov Gp op /\ op_taint tnh op = op_taint tnp op
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, eval_operand_def, op_prov_def, op_taint_def] >>
  metis_tac[op_taint_def, GREATER_EQ]
QED

Theorem abi_decode_linked_setup_guard_mods:
  abi_builtin_length_guard len mn mx sb = ((),header_st) /\
  fn_has_code sb header_st fn /\
  mn <= mx /\ mx < dimword (:256) /\ LENGTH (bs:word8 list) < dimword (:256) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn u /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  eval_operand len u = SOME (n2w (LENGTH bs)) /\
  op_prov Gp len = NONE /\ op_taint tnp len = {} /\
  abi_decoder_operand_live sb.cs_next_var len /\
  abi_decoder_operand_live sb.cs_next_var src /\
  src = Var input /\ abi_decode_ptr_window Gp tnp u input (n2w (b+32)) (LENGTH bs) /\
  (?H:(bool # bytes32 # type_value) list # num list. V H) ==>
  ?rg Gh tnh.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gp,tnp) [] (rg,Gh,tnh)) /\
    (!obs. fn_has_code sb header_st obs ==> gas_path ctx obs u 0 rg) /\
    ((?z. rg = Abort Revert_abort z /\ ~(mn <= LENGTH bs /\ LENGTH bs <= mx)) \/
     (?v. rg = OK v /\ ~v.vs_halted /\ v.vs_current_bb = header_st.cs_current_bb /\
       v.vs_inst_idx = LENGTH header_st.cs_current_insts /\
       mn <= LENGTH bs /\ LENGTH bs <= mx /\
       eval_operand len v = SOME (n2w (LENGTH bs)) /\
       op_prov Gh len = NONE /\ op_taint tnh len = {} /\ op_taint tnh src = {} /\
       abi_decode_ptr_window Gh tnh v input (n2w (b+32)) (LENGTH bs) /\
       abi_decoder_operand_live header_st.cs_next_var len /\
       abi_decoder_operand_live header_st.cs_next_var src /\
       v.vs_memory = u.vs_memory /\ v.vs_allocas = u.vs_allocas /\
       v.vs_alloca_next = u.vs_alloca_next /\ alloca_history fn v /\
       state_frame v = state_frame (u with vs_inst_idx := v.vs_inst_idx) /\
       tnh.t_mem = tnp.t_mem /\ tnh.t_stor = tnp.t_stor /\
       tnh.t_trans = tnp.t_trans /\ tnh.t_imm = tnp.t_imm /\
       (!x. not_fresh_at sb x ==> lookup_var x v = lookup_var x u /\
         FLOOKUP Gh x = FLOOKUP Gp x /\ op_taint tnh (Var x) = op_taint tnp (Var x))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all linked_length_guard_runtime >> strip_tac >>
  drule abi_builtin_length_guard_shape >> strip_tac >>
  `sb.cs_next_var <= header_st.cs_next_var` by simp[] >>
  qabbrev_tac `R = {x | not_fresh_at sb x}` >>
  qabbrev_tac `A = len INSERT {Lit w | T}` >>
  `len IN A /\ (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at sb x)` by
    simp[Abbr `R`, Abbr `A`] >>
  `!p. p IN A ==> op_prov Gp p = NONE /\ op_taint tnp p = {}` by
    (simp[Abbr `A`] >> gen_tac >>
     disch_then (DISJ_CASES_THEN2 SUBST1_TAC (CHOOSE_THEN SUBST1_TAC))
     >- asm_rewrite_tac[] >> simp[op_prov_def, op_taint_def]) >>
  drule_all abi_decode_caller_length_guard_scalar >> strip_tac >>
  Cases_on `mn <= LENGTH bs /\ LENGTH bs <= mx`
  >- suspend "success" >> suspend "reject"
QED

Resume abi_decode_linked_setup_guard_mods[success]:
  `?t. run_inst_seq (emitted_insts sb header_st) u = OK t` by metis_tac[] >>
  `header_st.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb header_st` by
    fs[inst_extends_def] >>
  `?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sb header_st) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sb header_st fn` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND, DROP_APPEND1, DROP_LENGTH_NIL,
          PULL_EXISTS] >> metis_tac[APPEND_ASSOC]) >>
  drule_all bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `v = t with vs_inst_idx := LENGTH header_st.cs_current_insts` >>
  `v = t with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sb header_st)` by
    simp[Abbr `v`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sb header_st) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sb header_st)) = 0` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_MEM, FILTER_EQ_NIL]) >>
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
  `state_frame v = state_frame (u with vs_inst_idx := v.vs_inst_idx) /\
   ~v.vs_halted /\ v.vs_current_bb = header_st.cs_current_bb /\
   v.vs_inst_idx = LENGTH header_st.cs_current_insts /\ v.vs_memory = u.vs_memory /\
   v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next /\
   v.vs_labels = u.vs_labels` by
    (simp[Abbr `v`, state_frame_def] >>
     qpat_assum `t = u with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sb header_st)` by
    (simp_tac pure_ss [EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) _`
       (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[is_alloca_op_def]) >>
  `alloca_history fn v` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`u`,`sb`,`header_st`] >> simp[]) >>
  `eval_operand len v = eval_operand len u /\
   op_prov G' len = op_prov Gp len /\ op_taint tn' len = op_taint tnp len` by
    (irule linked_guard_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand len v = SOME (n2w (LENGTH bs)) /\
   op_prov G' len = NONE /\ op_taint tn' len = {}` by
    (pure_asm_rewrite_tac[] >> simp[]) >>
  `abi_decode_ptr_window G' tn' v input (n2w (b+32)) (LENGTH bs)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gp`,`u`,`tnp`] >>
     `not_fresh_at sb input` by
       fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     qpat_assum `!x. not_fresh_at sb x ==> lookup_var x v = _ /\ _`
       (qspec_then `input` mp_tac) >> simp[]) >>
  `op_taint tn' src = {}` by fs[abi_decode_ptr_window_def, ptr_covers_def] >>
  `abi_decoder_operand_live header_st.cs_next_var len /\
   abi_decoder_operand_live header_st.cs_next_var src` by
    metis_tac[abi_decoder_operand_live_mono] >>
  qexistsl_tac [`OK v`,`G'`,`tn'`] >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `v = t with vs_inst_idx := _ + _` SUBST1_TAC >>
    first_assum irule) >>
  conj_tac >- first_assum ACCEPT_TAC >> disj2_tac >> qexists_tac `v` >>
  conj_tac >- REFL_TAC >>
  qpat_assum `mn <= LENGTH bs /\ LENGTH bs <= mx`
    (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_linked_setup_guard_mods[reject]:
  `?t. run_inst_seq (emitted_insts sb header_st) u = Abort Revert_abort t` by
    metis_tac[] >>
  drule_all abi_decode_scalar_guard_abort_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all linked_length_guard_revert_observer >>
  disch_then (qspec_then `ctx` (qx_choose_then `k` assume_tac)) >>
  `gas_path ctx fn u 0 (Abort Revert_abort (t with vs_inst_idx := j))` by
    (qpat_assum `?H. V H` (qx_choose_then `h` assume_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF h` mp_tac) >>
     disch_then (mp_tac o cj 1 o MATCH_MP gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP gas_origin_path_erase) >>
     simp[] >> metis_tac[gas_marked_path_exec]) >>
  `j = k` by (irule linked_guard_revert_index >> simp[] >> metis_tac[]) >>
  qpat_x_assum `j = k` SUBST_ALL_TAC >>
  qexistsl_tac [`Abort Revert_abort (t with vs_inst_idx := k)`,`Gf`,`tnf`] >>
  conj_tac >- (rpt strip_tac >> first_assum irule) >>
  conj_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Finalise abi_decode_linked_setup_guard_mods
