Theory bodyAbiDecodeGuardedLoopSelectFrameMods
Ancestors bodyFullAbiDecodeLoopSelectExact
  bodyFullAbiDecodeRelativeLoadExact bodyFullAbiDecodeFiniteGuard
  bodyFullAbiDecodeFiniteObserved bodyFullAbiDecodeClampMemory
  bodyFullAbiDecodeLeafCases abiDecodePtrBytesMember abiDecoderRange
  abiDecodePtrPosition abiDecoderGuard abiDecoderCoherence abiDecoderReentry
  decoderArraySetupPtr abiDecodePtrPrims abiEncoder abiDecodePtrMemberFrame
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome bodyPtrBopScalarCompile
  fragExec[qualified,ignore_grammar] fragExecMem fragGasPath fragGasPathPtr
  fragGasOriginPtrLoop emitHelperProps compileEnv emitHelper venomInst
  venomExecSemantics venomState words list rich_list arithmetic
  loweringStateRelDefs exprLoweringProps stateFrame ptrDiscipline
  bodyPtrBopScalarDynamic loweringShapeRules freshWrites instSeqPtrLo
  fragGasSeqPtrContext fragGasOriginPtrDead abiDecoderArrayInitReentry

(* Keep the raw computation conditional, independent of the proof of this
   phase.  Strengthen only the existing normal existential. *)
val raw_suffix_contract =
  let
    val tm = ``
      emit_op ADD [data;loadval] s2 = (child_src,s3) /\
      abi_decode_ge_guard child_src data s3 = ((),s4) /\
      emit_op ADD [child_src;Lit (n2w asz)] s4 = (e,s5) /\
      compile_abi_decode_range_check child_src e hi s5 = ((),sb) /\
      emitted_insts s2 sb = emitted_insts s2 s4 ++ emitted_insts s4 sb /\
      eval_operand data t = SOME dw /\ eval_operand loadval t = SOME lw /\
      eval_operand hi t = SOME (n2w h) /\
      abi_decoder_operand_live s2.cs_next_var data /\
      abi_decoder_operand_live s2.cs_next_var loadval /\
      abi_decoder_operand_live s2.cs_next_var hi /\
      asz < dimword(:256) /\ h < dimword(:256) ==>
      (?v. run_inst_seq (emitted_insts s2 sb) t = Abort Revert_abort v) \/
      (?v q. run_inst_seq (emitted_insts s2 sb) t = OK v /\
        eval_operand child_src v = SOME (n2w q) /\ q < dimword(:256) /\
        w2n dw <= q /\ q+asz <= h)``
  in list_mk_forall (free_vars tm,tm) end;

local
  val (entry, result) = dest_imp (concl abi_decode_loop_select_joint_exact)
  val (reject, normal) = dest_disj result
  val (binders, body) = strip_exists normal
  val [_,_,tnu,_] = binders
  val tn = List.find (fn v => fst (dest_var v) = "tn") (free_vars entry) |> valOf
  val effects = ``^tnu.t_stor = ^tn.t_stor /\
                  ^tnu.t_trans = ^tn.t_trans /\ ^tnu.t_imm = ^tn.t_imm``
  val raw = mk_imp (entry, mk_disj (reject,
    list_mk_exists (binders, mk_conj (body,effects))))
  val tm = rhs (concl (DEPTH_CONV BETA_CONV raw))
  val vars = free_vars tm
in
  val selector_contract = list_mk_forall (vars,tm)
  val fold_selector = CONV_TAC (REWR_CONV (GSYM
    (DEPTH_CONV BETA_CONV (list_mk_forall (vars,raw)))))
  val owned_decoder_state = #1 (strip_comb (find_term (fn tm =>
    let val (head,args) = strip_comb tm
    in is_abs head andalso length args = 4 end) body))
end

Theorem select_segments[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var input) head data hi asz sa =
    (child_src,sb) /\ hi <> Lit 0w ==>
  ?addr loadval e s1 s2 s3 s4 s5.
    compile_abi_dec_addr (Var input) head sa = (addr,s1) /\
    emit_op MLOAD [addr] s1 = (loadval,s2) /\
    emit_op ADD [data;loadval] s2 = (child_src,s3) /\
    abi_decode_ge_guard child_src data s3 = ((),s4) /\
    emit_op ADD [child_src;Lit (n2w asz)] s4 = (e,s5) /\
    compile_abi_decode_range_check child_src e hi s5 = ((),sb)
Proof
  strip_tac >>
  Cases_on `compile_abi_dec_addr (Var input) head sa` >>
  rename1 `compile_abi_dec_addr (Var input) head sa = (addr,s1)` >>
  Cases_on `emit_op MLOAD [addr] s1` >>
  rename1 `emit_op MLOAD [addr] s1 = (lv,s2)` >>
  Cases_on `emit_op ADD [data;lv] s2` >>
  rename1 `emit_op ADD [data;lv] s2 = (actual,s3)` >>
  Cases_on `abi_decode_ge_guard actual data s3` >>
  rename1 `abi_decode_ge_guard actual data s3 = (unit,s4)` >>
  Cases_on `unit` >>
  Cases_on `emit_op ADD [actual;Lit (n2w asz)] s4` >>
  rename1 `emit_op ADD [actual;Lit (n2w asz)] s4 = (e,s5)` >>
  Cases_on `compile_abi_decode_range_check actual e hi s5` >>
  gvs[compile_abi_decode_dyn_elem_ptr_def, abi_decode_ge_guard_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
      emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (goal_assum (drule_at Any))
QED

Theorem select_suffix_geometry[local]:
  emit_op ADD [data;offset] sa = (actual,s1) /\
  abi_decode_ge_guard actual data s1 = ((),s2) /\
  emit_op ADD [actual;Lit (n2w asz)] s2 = (e,s3) /\
  compile_abi_decode_range_check actual e hi s3 = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  s1.cs_next_var <= s2.cs_next_var /\ sa.cs_next_var <= s2.cs_next_var /\
  s1.cs_next_var <= sb.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) (emitted_insts sa sb)
Proof
  simp[abi_decode_ge_guard_def,compile_abi_decode_range_check_def,
       emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND,mk_inst_def]
QED

Theorem select_suffix_scalar[local]:
  emit_op ADD [data;offset] sa = (actual,s1) /\
  abi_decode_ge_guard actual data s1 = ((),s2) /\
  emit_op ADD [actual;Lit (n2w asz)] s2 = (e,s3) /\
  compile_abi_decode_range_check actual e hi s3 = ((),sb) /\
  data IN A /\ offset IN A /\ hi IN A /\ Lit (n2w asz) IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ actual IN B
Proof
  strip_tac >>
  `?C. bop_scalar_seq R A (emitted_insts sa s2) C /\ actual IN C` by
    (irule abiDecodePtrHeadTheory.abi_decode_position_suffix_scalar >>
     conj_tac >- simp[] >>
     qexistsl_tac [`Lit 1w`, `s1`, `offset`, `data`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `A SUBSET C` by metis_tac[bop_scalar_seq_available] >>
  `inst_extends sa s2` by
    metis_tac[inst_extends_emit_op, abi_decode_ge_guard_shape, inst_extends_trans] >>
  drule_all select_suffix_geometry >> strip_tac >>
  `!x. x IN R ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `?B. bop_scalar_seq R C (emitted_insts s2 sb) B /\ C SUBSET B /\ e IN B` by
    (irule abi_decode_add_range_scalar >> conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `compile_abi_decode_range_check _ _ _ _ = _`)) >>
     simp[] >> metis_tac[pred_setTheory.SUBSET_DEF]) >>
  pop_assum strip_assume_tac >>
  `inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op, compile_abi_decode_range_check_shape,
              inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa s2 ++ emitted_insts s2 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  qexists_tac `B` >> conj_tac
  >- (simp[] >> irule bop_scalar_seq_append >> qexists_tac `C` >> simp[]) >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

Theorem select_revert_observed[local]:
  bop_scalar_seq R A (emitted_insts sa sb) B /\
  EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) (emitted_insts sa sb) /\
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort v ==>
  ?k. !obs. fn_has_code sa sb obs ==>
     gas_path ctx obs s 0 (Abort Revert_abort (v with vs_inst_idx := k))
Proof
  strip_tac >> drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  `opc = ASSERT` by
    (qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
     simp[EVERY_APPEND,mk_inst_def]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++
     (prefix ++ mk_inst id ASSERT [op] [] :: suffix)` by fs[inst_extends_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) prefix) = 0` by
    (qpat_assum `bop_scalar_seq R A prefix _` (mp_then Any mp_tac bop_scalar_seq_opcodes) >>
     simp[EVERY_MEM, LENGTH_NIL, FILTER_EQ_NIL]) >>
  qexists_tac `LENGTH sa.cs_current_insts + LENGTH prefix` >>
  `step_inst_base (mk_inst id ASSERT [op] []) u = Abort Revert_abort v` by
    (qpat_assum `opc = ASSERT` (fn th => once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  rpt strip_tac >> irule abi_decode_finite_revert_observed >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem select_revert_cursor[local]:
  gas_path ctx fn s 0 (Abort Revert_abort u) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (Abort Revert_abort v,Gf,tnf)) ==> u = v
Proof
  strip_tac >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `ARB` (strip_assume_tac o MATCH_MP
      fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >>
  drule gas_path_ptr_erase >> simp[] >> strip_tac >>
  `(?f. run_from f ctx fn s = Abort Revert_abort u) /\
   (?g. run_from g ctx fn s = Abort Revert_abort v)` by
    (conj_tac >> irule gas_path_exit >> simp[fragExecTheory.exit_result_def] >>
     qexists_tac `0` >> simp[]) >>
  `run_from (f+g) ctx fn s = Abort Revert_abort u` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `f` >> simp[]) >>
  `run_from (f+g) ctx fn s = Abort Revert_abort v` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `g` >> simp[]) >>
  fs[]
QED

Theorem select_observe_append[local]:
  cs_extends sa sm /\ cs_extends sm sb /\
  (!obs. fn_has_code sa sm obs ==> gas_path ctx obs s 0 (OK t)) /\
  (!obs. fn_has_code sm sb obs ==> gas_path ctx obs t 0 r) ==>
  !obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 r
Proof
  rpt strip_tac >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `gas_path ctx obs s 0 (OK t) /\ gas_path ctx obs t 0 r` by simp[] >>
  drule_all gas_path_then >> simp[]
QED

Theorem select_old_operand[local]:
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
  t.vs_labels = s.vs_labels /\ abi_decoder_operand_live st.cs_next_var op ==>
  eval_operand op t = eval_operand op s /\ op_taint u op = op_taint tn op /\
  op_prov HG op = op_prov G op
Proof
  strip_tac >> irule old_operand_ghost_frame >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  qexists_tac `st` >> asm_rewrite_tac[] >>
  rpt strip_tac >> gvs[abi_decoder_operand_live_def,
    abi_decoder_older_vars_def, not_fresh_at_def]
QED

Theorem select_load_opcodes[local]:
  compile_abi_dec_addr (Var input) head sa = (addr,s1) /\
  emit_op MLOAD [addr] s1 = (loadval,s2) ==>
  inst_extends sa s2 /\ s2.cs_current_bb = sa.cs_current_bb /\
  sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
  abi_decoder_operand_live s2.cs_next_var loadval /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
             ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
             i.inst_opcode <> DALLOCA) (emitted_insts sa s2)
Proof
  strip_tac >>
  `emit_op ADD [Var input;head] sa = (addr,s1)` by
    fs[compile_abi_dec_addr_def] >>
  `inst_extends sa s1 /\ inst_extends s1 s2` by metis_tac[inst_extends_emit_op] >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa s2 = emitted_insts sa s1 ++ emitted_insts s1 s2` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  simp[mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  irule abi_decoder_generated_var_live >> simp[]
QED

Theorem abi_decode_loop_select_frame_exact_conditional:
  ^raw_suffix_contract ==> ^selector_contract
Proof
  disch_then (mk_asm "raw") >> fold_selector >> rpt gen_tac >>
  reverse (Cases_on `dec_info_needs_offset ei`)
  >- (simp_tac bool_ss [COND_CLAUSES, pairTheory.PAIR_EQ] >>
      strip_tac >> gvs[] >> disj2_tac >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules, gas_path_rules] >>
      metis_tac[]) >>
  simp_tac bool_ss [COND_CLAUSES] >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all select_segments >> strip_tac >>
  suspend "load_and_split"
QED

Resume abi_decode_loop_select_frame_exact_conditional[load_and_split]:
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s2 s3 /\ cs_extends s3 s4 /\
   cs_extends s4 s5 /\ cs_extends s5 sb` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`compile_abi_dec_addr _ _ _ = _`, `emit_op MLOAD _ _ = _`,
        `emit_op ADD [data;loadval] _ = _`, `abi_decode_ge_guard _ _ _ = _`,
        `emit_op ADD [child_src;Lit _] _ = _`, `compile_abi_decode_range_check _ _ _ _ = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,
       externalEntryShapeTheory.compile_abi_dec_addr_labels,
       exprSimConvertTheory.straight_fresh_extends,
       abi_decode_ge_guard_straight_fresh,
       externalEntryShapeTheory.compile_abi_decode_range_check_labels, pairTheory.SND]) >>
  `cs_extends sa s2 /\ cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s2 fn /\ fn_has_code s2 sb fn` by
    (drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  drule_all select_load_opcodes >> strip_tac >>
  drule_all select_suffix_geometry >> strip_tac >>
  `abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
   lo <= s.vs_alloca_next /\
   w2n input_word+LENGTH input_bytes <= s.vs_alloca_next /\
   alloca_history fn s /\ p+32 <= LENGTH input_bytes` by fs[] >>
  drule_all abi_decode_relative_load_joint_lower >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   allocas_below_fmp t = allocas_below_fmp s` by
    (qpat_assum `state_frame t = _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [state_frame_def] o
        AP_TERM ``\v:venom_state.
          (v.vs_alloca_next,v.vs_labels,v.vs_allocas,v.vs_fmp,v.vs_initial_fmp)``) >>
     simp[allocas_below_fmp_def]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (conj_tac >-
       (qpat_assum `allocas_from lo s` mp_tac >>
        pure_rewrite_tac[allocas_from_def] >> asm_rewrite_tac[]) >>
     asm_rewrite_tac[]) >>
  `!obs. fn_has_code sa s2 obs ==> gas_path ctx obs s 0 (OK t)` by
    (rpt strip_tac >>
     `gas_path ctx obs s 0 (OK ((t with vs_inst_idx := s.vs_inst_idx) with
          vs_inst_idx := LENGTH s2.cs_current_insts))` by
       (irule abi_decode_finite_success_observed >>
        conj_tac >- asm_rewrite_tac[] >>
        qexistsl_tac [`emitted_insts sa s2`,`sa`] >>
        fs[inst_extends_def, EVERY_MEM, FILTER_EQ_NIL, LENGTH_NIL]) >>
     qpat_x_assum `gas_path ctx obs s 0 (OK _)` mp_tac >>
     simp[] >>
     `t with vs_inst_idx := LENGTH s2.cs_current_insts = t` by
       metis_tac[analysisSimProofsBaseTheory.venom_state_idx_self_update] >>
     asm_rewrite_tac[]) >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`,`sa`,`s2`] >> fs[inst_extends_def,IS_PREFIX_APPEND,EVERY_MEM]) >>
  `(^owned_decoder_state) s2 t Gf tnf` by
    (irule abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`,`s`,`sa`,`tn`] >> asm_rewrite_tac[] >>
     CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qexists_tac `inst` >> asm_rewrite_tac[] >> NO_TAC) >>
     rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `eval_operand loadval t = SOME (mload (w2n input_word+p) s)` by
    simp[eval_operand_def] >>
  `eval_operand data t = SOME dw /\ eval_operand hi t = SOME (n2w h) /\
   op_prov Gf data = NONE /\ op_prov Gf hi = NONE /\
   op_taint tnf data = {} /\ op_taint tnf hi = {}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`,
        `t.vs_labels = s.vs_labels`,
        `abi_decoder_operand_live sa.cs_next_var data`,
        `abi_decoder_operand_live sa.cs_next_var hi`,
        `eval_operand data s = _`, `eval_operand hi s = _`,
        `op_prov G data = NONE`, `op_prov G hi = NONE`,
        `op_taint tn data = {}`, `op_taint tn hi = {}`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     rpt conj_tac >> metis_tac[select_old_operand]) >>
  `abi_decoder_operand_live s2.cs_next_var data /\
   abi_decoder_operand_live s2.cs_next_var hi` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `?B. bop_scalar_seq (abi_decoder_older_vars s2.cs_next_var)
      {data;loadval;hi;Lit (n2w asz)} (emitted_insts s2 sb) B /\ child_src IN B` by
    (irule select_suffix_scalar >>
     simp[] >> conj_tac
     >- simp[abi_decoder_older_vars_def, not_fresh_at_def] >>
     qexistsl_tac [`asz`,`data`,`e`,`hi`,`loadval`,`s3`,`s4`,`s5`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `inst_extends s2 s4 /\ inst_extends s4 sb /\ inst_extends s2 sb` by
    (map_every (fn (pat,th) => qpat_assum pat (assume_tac o MATCH_MP th))
       [(`emit_op ADD [data;loadval] _ = _`, inst_extends_emit_op),
        (`abi_decode_ge_guard _ _ _ = _`, abi_decode_ge_guard_shape),
        (`emit_op ADD [child_src;Lit _] _ = _`, inst_extends_emit_op),
        (`compile_abi_decode_range_check _ _ _ _ = _`, compile_abi_decode_range_check_shape)] >>
     metis_tac[inst_extends_trans]) >>
  `emitted_insts s2 sb = emitted_insts s2 s4 ++ emitted_insts s4 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def,IS_PREFIX_APPEND]) >>
  `!op. op IN {data;loadval;hi;Lit (n2w asz)} ==>
     op_prov Gf op = NONE /\ op_taint tnf op = {}` by
    (gen_tac >> simp_tac std_ss [pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY] >>
     qpat_x_assum `loadval = Var out` kall_tac >>
     strip_tac >- asm_rewrite_tac[] >- asm_rewrite_tac[] >- asm_rewrite_tac[] >>
     first_x_assum SUBST1_TAC >> simp_tac (srw_ss()) [op_prov_def,op_taint_def]) >>
  asm_x "raw" drule_all >> strip_tac >>
  qpat_x_assum `emitted_insts s2 sb = _` kall_tac
  >- suspend "reject" >>
  suspend "success"
QED

Resume abi_decode_loop_select_frame_exact_conditional[reject]:
  drule_all abi_decode_scalar_guard_abort_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all select_revert_observed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `v with vs_inst_idx := k = v with vs_inst_idx := j` by
    (irule select_revert_cursor >>
     goal_assum (drule_at Any) >>
     qpat_assum `!obs. fn_has_code s2 sb obs ==> gas_path _ _ _ _ (Abort _ _)`
       (qspec_then `fn` irule) >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexistsl_tac [`v with vs_inst_idx := j`,`Gf'`,`tnf'`] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gf`,`t`,`tnf`] >> simp[]) >>
  qpat_assum `v with vs_inst_idx := k = v with vs_inst_idx := j`
    (fn th => once_rewrite_tac[SYM th]) >>
  match_mp_tac (select_observe_append |> Q.INST [`sm` |-> `s2`, `t` |-> `t`]) >>
  asm_rewrite_tac[]
QED

Resume abi_decode_loop_select_frame_exact_conditional[success]:
  drule_all (bop_scalar_seq_run |>
    Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG Gf tnf
      (emitted_insts s2 sb) t G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts s2 sb)` by
    metis_tac[bop_scalar_seq_opcodes] >>
  `run_inst_seq_mem_ok (emitted_insts s2 sb) t` by
    metis_tac[abi_decode_scalar_seq_mem_ok] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post w. emitted_insts s2 sb = pre ++ i::post /\
      run_inst_seq pre t = OK w ==> unitTransformDefs$dalloca_no_wrap i w)` by
    (rpt strip_tac >>
     `MEM i (emitted_insts s2 sb)` by simp[MEM_APPEND] >>
     drule_all bop_scalar_seq_outputs >> strip_tac >>
     simp[unitTransformDefsTheory.dalloca_no_wrap_def] >> CCONTR_TAC >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts s2 sb)` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt gen_tac >> disch_tac >>
     CCONTR_TAC >> drule_all bop_scalar_seq_outputs >>
     disch_then (mp_tac o CONJUNCT1) >>
     qpat_assum `~(i.inst_opcode <> ALLOCA)`
       (fn th => simp_tac (srw_ss()) [SIMP_RULE bool_ss [] th,MEM])) >>
  drule_all emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `u = v with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!obs. fn_has_code s2 sb obs ==> gas_path ctx obs t 0 (OK u)` by
    (simp[Abbr `u`] >>
     match_mp_tac (abi_decode_finite_success_observed |>
       Q.INST [`sa` |-> `s2`, `code` |-> `emitted_insts s2 sb`]) >>
     fs[inst_extends_def,EVERY_MEM,FILTER_EQ_NIL,LENGTH_NIL]) >>
  `state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = t.vs_allocas /\
   u.vs_memory = t.vs_memory /\ u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_labels = t.vs_labels /\ allocas_below_fmp u = allocas_below_fmp t` by
    (qpat_assum `Abbrev (u = _)` (fn th =>
       PURE_ONCE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `v = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp_tac (srw_ss()) [state_frame_def,allocas_below_fmp_def] >>
     asm_rewrite_tac[]) >>
  `!x. not_fresh_at s2 x ==>
     lookup_var x u = lookup_var x t /\ FLOOKUP G' x = FLOOKUP Gf x /\
     op_taint tn' (Var x) = op_taint tnf (Var x)` by
    (simp[Abbr `u`,lookup_var_def,op_taint_def,not_fresh_at_def,abi_decoder_older_vars_def] >>
     metis_tac[]) >>
  suspend "normal_packet"
QED

Resume abi_decode_loop_select_frame_exact_conditional[normal_packet]:
  `alloca_history fn u` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`t`,`s2`,`sb`] >> fs[inst_extends_def,IS_PREFIX_APPEND]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `(^owned_decoder_state) sb u G' tn'` by
    (irule abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`Gf`,`t`,`s2`,`tnf`] >> asm_rewrite_tac[] >>
     rpt conj_tac
     >- (rpt strip_tac >> first_assum irule >> metis_tac[])
     >- (rpt strip_tac >> first_assum irule >> metis_tac[])
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     first_assum irule >> asm_rewrite_tac[]) >>
  pop_assum (mk_asm "owned") >>
  `eval_operand hi u = SOME (n2w h)` by metis_tac[select_old_operand] >>
  `eval_operand child_src u = SOME (n2w q)` by simp[Abbr `u`,eval_operand_def] >>
  `abi_decoder_operand_live sb.cs_next_var child_src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `s3.cs_next_var` >>
     conj_tac >- asm_rewrite_tac[] >>
     qpat_assum `emit_op ADD [data;loadval] s2 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def,fresh_var_def,fresh_id_def,emit_def,comp_bind_def,
          comp_ignore_bind_def,comp_return_def] >> rpt strip_tac >> gvs[] >>
     irule abi_decoder_generated_var_live >> simp[]) >>
  disj2_tac >> qexistsl_tac [`u`,`G'`,`tn'`,`q`] >> reverse conj_tac
  >- asm_rewrite_tac[] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gf`,`t`,`tnf`] >> conj_tac >- simp[] >>
      irule gas_origin_ptr_path_from_no_dead >> asm_rewrite_tac[]) >>
  conj_tac
  >- (match_mp_tac (select_observe_append |> Q.INST [`sm` |-> `s2`, `t` |-> `t`]) >>
      asm_rewrite_tac[]) >>
  `!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >>
     `not_fresh_at s2 x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  `u.vs_allocas = s.vs_allocas` by asm_rewrite_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by asm_rewrite_tac[] >>
  asm "owned" (strip_assume_tac o CONV_RULE (DEPTH_CONV BETA_CONV)) >>
  simp[] >> rpt conj_tac >> rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> simp[]
QED

Finalise abi_decode_loop_select_frame_exact_conditional
