Theory bodyAbiDecodeGuardedComplexPrefixMods
Ancestors abiDecoderReentry[qualified,ignore_grammar] loweringStateRelDefs[qualified,ignore_grammar]
  bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeComplexPrefixSlice bodyFullAbiDecodeComplexPrefix
  bodyFullAbiDecodeFiniteObserved bodyFullAbiDecodeClampMemory
  bodyFullAbiDecodeRelativeLoadExact[qualified]
  fragGasOriginPtrLoop fragGasOriginPtrDead instSeqPtrLo gasPathPtrExec
  stateFrame bodyPtrBopScalarOutcome bodyPtrBopScalarSeq
  abiDecodePtrPrims externalEntryShape list venomState ptrDiscipline emitHelperProps
  bodyFullAbiDecodeScalarObserved fragExec fragGasOriginPtr fragGasPathPtr
  compileEnv words finite_map freshWrites
Libs
  bodyFullAbiDecodeComplexPrefixSyntaxLib
  bodyAbiDecodeGuardedEffectSyntaxLib[qualified]

Theorem complex_scalar_success[local]:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK raw /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  t = raw with vs_inst_idx := LENGTH sb.cs_current_insts ==>
  ?Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (^owned_decoder_state) sb t Gf tnf /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ abi_decode_guarded_effect s tn t tnf
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (bop_scalar_seq_run |> Q.INST [`D` |->
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
      (emitted_insts sa sb) s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by metis_tac[bop_scalar_seq_opcodes] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[abi_decode_scalar_seq_mem_ok] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     drule_all bop_scalar_seq_outputs >> simp[] >>
     Cases_on `i.inst_opcode = DALLOCA` >> simp[]) >>
  drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  suspend "owned_and_effect"
QED

Resume complex_scalar_success[owned_and_effect]:
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
   t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `raw = _` (fn th => once_rewrite_tac[th]) >> simp[state_frame_def]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `raw = _` (fn th => once_rewrite_tac[th]) >>
     gvs[lookup_var_def, op_taint_def]) >>
  `alloca_history fn t` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl [`s`, `sa`, `sb`] >> simp[] >> gvs[inst_extends_def]) >>
  `(^owned_decoder_state) sb t G' tn'` by
    (BETA_TAC >> MATCH_MP_TAC (BETA_RULE
      bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower) >>
     asm_rewrite_tac[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  qexistsl [`G'`, `tn'`] >> conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
      qpat_assum `t = _` (fn th => once_rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[abi_decode_guarded_effect_def]
QED

Finalise complex_scalar_success[local]

val (bound, imp) = dest_forall (concl (BETA_RULE abi_decode_complex_prefix_observed_slice));
val (pre, post) = dest_imp imp;
val (reject, normal) = dest_disj post;
val (witnesses, normal_body) = strip_exists normal;
val entry = free_vars pre;
val par = bodyAbiDecodeGuardedEffectSyntaxLib.param;
val effect = bodyAbiDecodeGuardedEffectSyntaxLib.effect;
val normal_effect = effect (par entry "s") (par entry "tn")
                           (par witnesses "t") (par witnesses "tnf");
val prefix_effect = mk_forall (bound, mk_imp (pre,
  mk_disj (reject, list_mk_exists (witnesses, mk_conj (normal_body, normal_effect)))));
val _ = bodyAbiDecodeGuardedEffectSyntaxLib.checked "complex prefix"
  (concl abi_decode_complex_prefix_observed_slice) prefix_effect;

Theorem abi_decode_complex_prefix_observed_effect_mods:
  ^prefix_effect
Proof
  gen_tac >>
  disch_then (fn th =>
    mp_tac (MATCH_MP (SPEC_ALL (BETA_RULE abi_decode_complex_prefix_raw_endpoint_effect)) th) >>
    map_every assume_tac (CONJUNCTS th)) >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- suspend "reject" >>
  qpat_x_assum `?raw. run_inst_seq _ _ = OK raw /\ _` strip_assume_tac >>
  suspend "normal"
QED

Resume abi_decode_complex_prefix_observed_effect_mods[reject]:
  `cs_extends start sb` by
    (irule cs_extends_trans >> qexists `sm` >> conj_tac
     >- (drule exprSimAccountsTheory.emit_op_extends_next_var >> simp[]) >>
     mp_tac (Q.SPECL [`src`, `e`, `hi`, `sm`, `K T`]
       compile_abi_decode_range_check_labels) >> simp[]) >>
  `cs_extends sb finish'` by
    (drule_all abi_decode_complex_bounded_split >> strip_tac >>
     `sb = sb'` by gvs[] >>
     mp_tac (Q.SPECL [`dst`, `src`, `opc`, `base_op`, `hi`, `infos`, `0`, `0`, `sb`]
       (cj 2 compile_abi_decode_labels)) >> gvs[]) >>
  `fn_has_code start sb fn` by metis_tac[fn_has_code_split] >>
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at start x}
    {src;hi;Lit (n2w (FOLDR (\(_,asz,_) acc. asz+acc) 0 infos))}
    (emitted_insts start sb) B` by
    (irule abi_decode_complex_header_scalar >>
     conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!op. op IN {src;hi;Lit (n2w (FOLDR (\(_,asz,_) acc. asz+acc) 0 infos))} ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
     rpt strip_tac >>
     first_x_assum (fn th => once_rewrite_tac [th]) >> simp[op_prov_def, op_taint_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o CONJUNCT1 o UNDISCH)) >>
     disch_then (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `allocas_from lo s` by
    (qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >>
     metis_tac[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  drule_all member_scalar_revert_observed >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `t = u` by
    (qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> gas_origin_ptr_path _ _ _ (Abort Revert_abort t,_,_)`
       (qspec_then `H` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ (Abort Revert_abort u,_,_)`
       (qspec_then `DF H` mp_tac) >>
     qpat_assum `V H` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> rpt strip_tac >>
     imp_res_tac gas_origin_ptr_path_projections >>
     `Abort Revert_abort t = Abort Revert_abort u` suffices_by simp[] >>
     irule (cj 3 gas_path_ptr_exit_unique) >> simp[exit_result_def] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> qexistsl [`t`, `Gf`, `tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> metis_tac[fn_has_code_split]) >>
  qexistsl [`e`, `sm`, `sb`] >> asm_rewrite_tac[]
QED

Resume abi_decode_complex_prefix_observed_effect_mods[normal]:
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  `cs_extends start sb` by
    (irule cs_extends_trans >> qexists `sm` >> conj_tac
     >- (drule exprSimAccountsTheory.emit_op_extends_next_var >> simp[]) >>
     mp_tac (Q.SPECL [`src`, `e`, `hi`, `sm`, `K T`]
       compile_abi_decode_range_check_labels) >> simp[]) >>
  `cs_extends sb finish'` by
    (mp_tac (Q.SPECL [`dst`, `src`, `opc`, `base_op`, `hi`, `infos`, `0`, `0`, `sb`]
       (cj 2 compile_abi_decode_labels)) >> simp[]) >>
  `fn_has_code start sb fn` by metis_tac[fn_has_code_split] >>
  qabbrev_tac `hsz = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)` >>
  `?B. bop_scalar_seq {x | not_fresh_at start x} {src;hi;Lit (n2w hsz)}
       (emitted_insts start sb) B` by
    (irule abi_decode_complex_header_scalar >> conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!op. op IN {src;hi;Lit (n2w hsz)} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
     rpt strip_tac >>
     first_x_assum (fn th => once_rewrite_tac [th]) >> simp[op_prov_def, op_taint_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (qspec_then `H` (mp_tac o CONJUNCT1 o UNDISCH)) >>
     disch_then (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `allocas_from lo s` by
    (qpat_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (qspec_then `H` mp_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >>
     metis_tac[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts start sb)` by
    (qpat_assum `EVERY (\i. (fresh_write_op _ \/ _) /\ _) _` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
     first_x_assum drule >> Cases_on `i.inst_opcode = ALLOCA` >> simp[fresh_write_op_def]) >>
  `start.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `compile_abi_decode_range_check _ _ _ _ = _` mp_tac >>
     qpat_assum `emit_op ADD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderTheory.compile_abi_decode_range_check_def, comp_bind_def,
       comp_ignore_bind_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  `not_fresh_at start input` by
    (`abi_decoder_operand_live start.cs_next_var (Var input)` by metis_tac[] >>
     pop_assum mp_tac >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `origin` >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `start`, `A` |-> `{src;hi;Lit (n2w hsz)}`]
    (BETA_RULE complex_scalar_success)) >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then (qx_choose_then `Gn` (qx_choose_then `tnn`
    (CONJUNCTS_THEN2 (mk_asm "new_path")
      (CONJUNCTS_THEN2 (mk_asm "new_owned") (map_every assume_tac o CONJUNCTS))))) >>
  suspend "normal_member"
QED

Resume abi_decode_complex_prefix_observed_effect_mods[normal_member]:
  rpt (PRED_ASSUM (fn tm => List.exists
    (fn v => mem (fst (dest_var v)) ["Gf", "tnf"]) (free_vars tm)) kall_tac) >>
  `t.vs_allocas = s.vs_allocas` by
    (drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
     qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `raw = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!obs. fn_has_code start sb obs ==> gas_path ctx obs s 0 (OK t)` by
    (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     `sb.cs_current_insts = start.cs_current_insts ++ emitted_insts start sb` by
       gvs[inst_extends_def] >>
     drule bop_scalar_seq_opcodes >> strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts start sb)` by gs[EVERY_MEM] >>
     `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts start sb)) = 0` by
       gs[EVERY_MEM, FILTER_EQ_NIL] >>
     rpt strip_tac >> drule_all abi_decode_finite_success_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gn,tnn)` by
    (rpt strip_tac >> asm "new_path" MATCH_ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`env'`, `sf'`, `tys`, `tvs`, `e`, `sm`, `sb`, `t`, `Gn`, `tnn`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "member_fields"
QED

Resume abi_decode_complex_prefix_observed_effect_mods[member_fields]:
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
     op_prov Gn op = op_prov G op /\ op_taint tnn op = op_taint tn op` by
    (qpat_assum `!x. not_fresh_at start x ==> _ /\ FLOOKUP Gn x = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> Cases >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       loweringStateRelDefsTheory.not_fresh_at_def, op_prov_def, op_taint_def] >>
     metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, op_taint_def]) >>
  `?p. dst = Var p /\ ptr_covers Gn tnn p t (d-d+SUM (MAP (type_memory_bytes ce) tys)) /\
     FLOOKUP Gn p = SOME (output_base,output_cap)` by
    (qpat_assum `?p. dst = Var p /\ ptr_covers G tn p s _ /\ _` strip_assume_tac >>
     `not_fresh_at start p` by
       (`abi_decoder_operand_live start.cs_next_var (Var p)` by metis_tac[] >>
        pop_assum mp_tac >> simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
          abiDecoderReentryTheory.abi_decoder_older_vars_def, loweringStateRelDefsTheory.not_fresh_at_def]) >>
     qpat_assum `!x. not_fresh_at start x ==> _ /\ FLOOKUP Gn x = _ /\ _`
       (qspec_then `p` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qexists `p` >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `ptr_covers G tn p s _` mp_tac >>
         simp_tac bool_ss [bodyPtrDefsTheory.ptr_covers_def] >>
         asm_rewrite_tac[]) >>
     asm_rewrite_tac[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "remaining"
QED

Resume abi_decode_complex_prefix_observed_effect_mods[remaining]:
  qunabbrev_tac `hsz` >>
  `?off h. eval_operand src t = SOME (n2w off) /\ eval_operand hi t = SOME (n2w h) /\
    off <= h /\ h <= LENGTH input_bytes` by
    (qpat_assum `?off h. eval_operand src t = _ /\ _` strip_assume_tac >>
     qexistsl [`off`, `h`] >> simp[] >> decide_tac) >>
  `op_prov Gn src = NONE /\ op_prov Gn hi = NONE /\
    op_taint tnn dst = {} /\ op_taint tnn src = {} /\
    op_taint tnn base_op = {} /\ op_taint tnn hi = {}` by
    (rpt conj_tac >> qpat_assum `!op. abi_decoder_operand_live _ op ==> _` drule >> simp[]) >>
  asm "new_owned" (map_every assume_tac o CONJUNCTS) >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  qexists `p` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_decode_complex_prefix_observed_effect_mods
