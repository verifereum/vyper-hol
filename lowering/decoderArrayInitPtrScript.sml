(* Joint count validation, count store and scratch-index initialization. *)
Theory decoderArrayInitPtr
Ancestors wordLoadStorePtr decoderIndexInitCorePtr decoderSetupStepPtr ptrSafetyTransport decoderGuardClampCorePtr decoderCountComparisonCorePtr decoderCountLoadCorePtr abiDecoderGuards abiDecoderArrayInitExec decoderArraySetupPtr decoderIndexInitPtr
  decoderNavigationPtr calldataClampPtr typedCopyPtr bodyPtrDefs
  compileEnv emitHelper venomInst venomExecSemantics venomState words list
  rich_list arithmetic finite_map ptrDiscipline ptrSafeRun venomInstProofs codegenRel contextCodegenRel
  emitHelperProps exprLoweringProps fragExec decoderGhostFramePtr
  abiDecoderContract entryDispatchPtr instIdxIndep fragExecPtr
  abiDecoderReentry calldataDynOwned abiDecoderArrayLoopInit abiDecoderDynarrayPrefix
  abiDecoderArrayInitReentry
  abiDecoderDynarrayBound abiDecoderArrayHeader abiDecoderIndexInit abiDecoderAllocation

(* The calldata address step: base Lit 0w adds no instruction. *)
val calldata_pos_addr = prove(
  ``compile_abi_dec_addr (Lit 0w) pos st = (pos,st)``,
  simp[abiEncoderTheory.compile_abi_dec_addr_def, compileEnvTheory.comp_return_def]);

(* The calldata instance of trunk's position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`, `src_base` |-> `0:num`] th);

Theorem calldata_count_guard_layout[local]:
  abi_decode_count_guard CALLDATALOAD src maxn st = (cnt,st') ==>
  cnt = Var ("%" ++ toString st.cs_next_var) /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_next_var = st.cs_next_var + 3 /\
  st'.cs_next_id = st.cs_next_id + 4 /\
  st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id CALLDATALOAD [src]
       ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id + 1) GT
       [cnt; Lit (n2w maxn)] ["%" ++ toString (st.cs_next_var + 1)];
     mk_inst (st.cs_next_id + 2) ISZERO
       [Var ("%" ++ toString (st.cs_next_var + 1))]
       ["%" ++ toString (st.cs_next_var + 2)];
     mk_inst (st.cs_next_id + 3) ASSERT
       [Var ("%" ++ toString (st.cs_next_var + 2))] []]
Proof
  simp[abi_decode_count_guard_def, emit_op_def, emit_void_def,
    emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem emit_count_comparison_endpoint_ptr[local]:
  !src bound sa out sb s t a G tn cx ctx PG R.
  emit_op GT [src; Lit bound] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_count_comparison_endpoint_ptr_core >>
  disch_then (qspec_then `G` mp_tac) >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[] >> metis_tac[]
QED

Theorem emit_clamp_scalar_endpoint_ptr[local]:
  emit_op opc ops sa = (out,sb) /\
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all emit_clamp_scalar_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[] >> metis_tac[]
QED

Theorem emit_assert_endpoint_ptr[local]:
  emit_void ASSERT [op] sa = ((),sb) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = G /\ z = tn /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\ t = s
Proof
  strip_tac >> drule_all emit_assert_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] strip_assume_tac) >> simp[]
QED

Theorem emit_count_load_endpoint_ptr[local]:
  !src sa out sb s t a G tn cx ctx PG R.
  emit_op CALLDATALOAD [src] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = H /\ z = u /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_count_load_endpoint_ptr_core >>
  disch_then (qspecl_then [`G`,`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[] >> metis_tac[]
QED



Theorem calldata_count_guard_endpoint_ptr_core:
  abi_decode_count_guard CALLDATALOAD src maxn sa = (cnt,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := s.vs_inst_idx + 4)) R /\
    (?vars. t = s with vs_vars := vars) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (cnt,c1)` >>
  rename1 `emit_op GT [cnt; Lit (n2w maxn)] c1 = (cmp,c2)` >>
  rename1 `emit_op ISZERO [cmp] c2 = (ok,c3)` >>
  rename1 `emit_void ASSERT [ok] c3 = ((),sb)` >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\
    inst_extends c2 c3 /\ inst_extends c3 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++
    (emitted_insts c1 c2 ++ (emitted_insts c2 c3 ++ emitted_insts c3 sb))` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac [] >>
  disch_then (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  qpat_x_assum `run_inst_seq (_ ++ _) _ = OK t`
    (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  qpat_x_assum `run_inst_seq (_ ++ _) _ = OK t`
    (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `s2.vs_inst_idx = s.vs_inst_idx /\ s3.vs_inst_idx = s.vs_inst_idx /\
    t.vs_inst_idx = s.vs_inst_idx` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     gvs[run_inst_seq_def, AllCaseEqs()] >>
     imp_res_tac step_inst_base_preserves_inst_idx >>
     gvs[mk_inst_def, is_terminator_def]) >>
  suspend "guard_ghost"
QED

Resume calldata_count_guard_endpoint_ptr_core[guard_ghost]:
  drule_all emit_count_load_endpoint_ptr_core >>
  disch_then (qspec_then `G` mp_tac) >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  rename1 `op_taint u1 cnt = {}` >>
  rename1 `op_prov H1 cnt = NONE` >>
  `?b. eval_operand cnt s1 = SOME b` by
    (qpat_assum `emit_op GT _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq (emitted_insts c1 c2) s1 = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c1 c2)
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (s2 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `emit_op GT _ _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `eval_operand cnt (s1 with vs_inst_idx := SUC s.vs_inst_idx) = SOME b` by
    (Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c1 c2) s1 = _` kall_tac >>
  drule_all emit_count_comparison_endpoint_ptr_core >>
  disch_then (qspec_then `H1` mp_tac) >> simp[NoAsms] >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  rename1 `op_taint u2 cmp = {}` >> rename1 `op_prov H2 cmp = NONE` >>
  `run_inst_seq (emitted_insts c2 c3)
    (s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    OK (s3 with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    (qpat_assum `emit_op ISZERO _ _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c2 c3) s2 = _` kall_tac >>
  `MEM ISZERO [SIGNEXTEND; SHR; SHL; EQ; ISZERO] /\
    EVERY (\op. op_taint u2 op = {} /\ op_prov H2 op = NONE) [cmp]` by simp[] >>
  drule_all emit_clamp_scalar_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] mp_tac) >> simp[NoAsms] >>
  strip_tac >> rename1 `op_taint u3 ok = {}` >> rename1 `op_prov H3 ok = NONE` >>
  qpat_x_assum `emitted_insts sa sb = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts sa c1) _ = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts c1 c2) _ = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts c2 c3) _ = _` kall_tac >>
  `run_inst_seq (emitted_insts c3 sb)
    (s3 with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx))) =
    OK (t with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx)))` by
    (qpat_assum `emit_void ASSERT _ _ = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     simp[run_inst_seq_inst_idx, mk_inst_def, is_terminator_def, exec_result_map_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c3 sb) s3 = _` kall_tac >>
  drule_all emit_assert_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] mp_tac) >> simp[NoAsms] >> strip_tac >>
  `t = s3` by
    (qpat_x_assum `t with vs_inst_idx := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `s2 = s1 with vs_vars := vars'` by
    (qpat_x_assum `s2 with vs_inst_idx := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `s3 = s2 with vs_vars := vars''` by
    (qpat_x_assum `s3 with vs_inst_idx := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  suspend "guard_compose"
QED

Resume calldata_count_guard_endpoint_ptr_core[guard_compose]:
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\ cs_extends c3 sb` by
    (rpt conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def] >>
     metis_tac[emit_op_same_blocks, emit_void_same_blocks, same_blocks_def]) >>
  `frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = H3 /\ z = u3 /\ v = (t with vs_inst_idx := s.vs_inst_idx + 4)) R` by
    (`cs_extends c2 sb /\ cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
     dxrule_all frag_exec_ptr_seq >> strip_tac >>
     dxrule_all frag_exec_ptr_seq >> strip_tac >>
     `s.vs_inst_idx + 4 = SUC (SUC (SUC (SUC s.vs_inst_idx)))` by decide_tac >>
     drule_all frag_exec_ptr_seq >> simp[]) >>
  `!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H3 u3
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s` by
    (suspend "guard_continuation") >>
  suspend "guard_frames"
QED

Resume calldata_count_guard_endpoint_ptr_core[guard_frames]:
  qpat_x_assum `frag_exec_ptr _ _ _ sa c1 _ _ _` kall_tac >>
  qpat_x_assum `frag_exec_ptr _ _ _ c1 c2 _ _ _` kall_tac >>
  qpat_x_assum `frag_exec_ptr _ _ _ c2 c3 _ _ _` kall_tac >>
  qpat_x_assum `frag_exec_ptr _ _ _ c3 sb _ _ _` kall_tac >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!x. cnt = Var x ==> not_fresh_at c1 x` by
    (qpat_assum `emit_op CALLDATALOAD _ sa = _`
      (mp_then Any mp_tac abi_decoder_operand_live_emit) >>
     Cases_on `cnt` >> simp[calldata_operand_live_not_fresh]) >>
  `!x. cnt = Var x ==> not_fresh_at c2 x` by
    (rpt strip_tac >> `not_fresh_at c1 x` by metis_tac[] >>
     gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`H3`,`u3`] >>
  conj_tac >-
    (Cases_on `cnt` >> gvs[op_taint_def] >> metis_tac[]) >>
  conj_tac >-
    (Cases_on `cnt` >> gvs[op_prov_def] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `vars''` >> simp[]) >>
  fs[lookup_var_def] >> rpt strip_tac >> metis_tac[]
QED

Resume calldata_count_guard_endpoint_ptr_core[guard_continuation]:
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `!x. not_fresh_at _ x ==> _` kall_tac) >>
  `c1.cs_current_bb = sa.cs_current_bb /\
   c2.cs_current_bb = sa.cs_current_bb /\ c3.cs_current_bb = sa.cs_current_bb /\
   LENGTH c1.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   LENGTH c2.cs_current_insts = SUC (SUC (LENGTH sa.cs_current_insts)) /\
   LENGTH c3.cs_current_insts = SUC (SUC (SUC (LENGTH sa.cs_current_insts)))` by
    (imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emit_op_same_blocks >> gvs[same_blocks_def, ADD1]) >>
  rpt gen_tac >> strip_tac >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `allocas_from lower (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
   allocas_from lower (s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)) /\
   allocas_from lower (s3 with vs_inst_idx := SUC (SUC (SUC s.vs_inst_idx))) /\
   s1.vs_current_bb = c1.cs_current_bb /\ s2.vs_current_bb = c2.cs_current_bb /\
   s3.vs_current_bb = c3.cs_current_bb` by
    (gvs[allocas_from_def] >> metis_tac[]) >>
  gvs[]
QED

Finalise calldata_count_guard_endpoint_ptr_core

Theorem calldata_count_guard_endpoint_ptr:
  abi_decode_count_guard CALLDATALOAD src maxn sa = (cnt,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := s.vs_inst_idx + 4)) R /\
    (?vars. t = s with vs_vars := vars) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all calldata_count_guard_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[] >> metis_tac[]
QED

Theorem calldata_array_header_endpoint_ptr_core:
  !root src sa cnt sb s t d totalbytes a G tn cx ctx PG R.
  abi_decode_array_header (Var root) src CALLDATALOAD sa = (cnt,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  ptr_covers G tn root s totalbytes /\ 32 <= totalbytes /\
  not_fresh_at sa root /\ eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?H u. frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = H /\ z = u /\
      v = (t with vs_inst_idx := 2 + s.vs_inst_idx)) R /\
    ptr_covers H u root t totalbytes /\
    op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    u.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d + 32} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (cnt,sm)` >>
  rename1 `emit_void MSTORE [Var root; cnt] sm = ((),sb)` >>
  `inst_extends sa sm /\ inst_extends sm sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac [] >>
  disch_then (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK s1` >>
  drule_all emit_count_load_endpoint_ptr_core >>
  disch_then (qspecl_then [`G`,`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  `lookup_var root s1 = SOME (n2w d) /\ ptr_covers H u root s1 totalbytes` by
    (conj_tac >- metis_tac[] >> irule ptr_covers_frame >> metis_tac[]) >>
  `ptr_covers H u root s1 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `?w. eval_operand cnt s1 = SOME w` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def, eval_operand_def, AllCaseEqs()] >> metis_tac[]) >>
  `t = mstore d w s1` by
    (qpat_x_assum `s1 = s with vs_vars := _` kall_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sm sb) _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def, eval_operand_def, w2n_n2w] >>
     Cases_on `cnt` >> fs[eval_operand_def]) >>
  `w2n (n2w d : bytes32) = d` by simp[] >>
  drule_all mstore_ghost_frame >> disch_then (qspecl_then [`PG`,`H`] strip_assume_tac) >>
  qabbrev_tac `u2 = step_taint (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) s1 t u` >>
  `u2.t_var = u.t_var /\ u2.t_stor = tn.t_stor /\
    u2.t_trans = tn.t_trans /\
    u2.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d + 32}` by
    (simp[Abbr `u2`] >> metis_tac[]) >>
  `step_prov PG H (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) t = H` by
    metis_tac[] >>
  qpat_x_assum `!id. _` kall_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `frag_exec_ptr cx ctx PG sm sb
     (\g z v. g = H /\ z = u /\ v = (s1 with vs_inst_idx := SUC s.vs_inst_idx))
     (\g z v. g = H /\ z = u2 /\ v = (t with vs_inst_idx := 2 + s.vs_inst_idx)) R` by
    (irule mstore_frag_ptr >> conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`root`,`sm.cs_next_id`,`cnt`] >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     rpt gen_tac >> simp[NoAsms] >> strip_tac >>
     ntac 3 (pop_assum SUBST_ALL_TAC) >>
     qpat_x_assum `s1 = s with vs_vars := _` kall_tac >>
     conj_tac >- (fs[ptr_covers_def, lookup_var_def]) >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`n2w d`,`w`] >>
     `mstore d w (s1 with vs_inst_idx := SUC s.vs_inst_idx) =
        (t with vs_inst_idx := SUC s.vs_inst_idx)` by
       simp[mstore_def, write_memory_with_expansion_def] >>
     simp[lookup_var_def] >>
     `eval_operand cnt (s1 with vs_inst_idx := SUC s.vs_inst_idx) = SOME w` by
       (Cases_on `cnt` >> fs[eval_operand_def, lookup_var_def]) >>
     simp[Abbr `u2`, ADD1] >> fs[lookup_var_def] >> metis_tac[] ) >>
  `u2.t_imm = tn.t_imm` by
    simp[Abbr `u2`, step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def] >>
  suspend "header_finish"
QED

Resume calldata_array_header_endpoint_ptr_core[header_finish]:
  `same_blocks sa sm /\ same_blocks sm sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def] >> metis_tac[]) >>
  `!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u2
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s` by
    (suspend "header_continuation") >>
  qexistsl_tac [`H`,`u2`] >> conj_tac
  >- (irule frag_exec_ptr_seq >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      gvs[ADD_COMM] >> metis_tac[]) >>
  `!op. op_taint u2 op = op_taint u op` by
    (Cases >> simp[op_taint_def]) >>
  `!x. lookup_var x t = lookup_var x s1` by simp[mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  `ptr_covers H u2 root t totalbytes` by
    (irule ptr_covers_frame >> metis_tac[]) >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Resume calldata_array_header_endpoint_ptr_core[header_continuation]:
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `!x. not_fresh_at _ x ==> _` kall_tac) >>
  rpt gen_tac >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\
    LENGTH sm.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[same_blocks_def]) >>
  `!fuel. ptr_safe_run D lower fuel ctx' func PG H u
     (s1 with vs_inst_idx := SUC s.vs_inst_idx)` suffices_by
    (strip_tac >> qpat_x_assum `!D lower ctx' func. _`
      (qspecl_then [`D`,`lower`,`ctx'`,`func`] mp_tac) >> gvs[]) >>
  `!fuel. ptr_inst_ok D lower fuel ctx' func H u
    (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[] >>
     irule ptr_inst_ok_mstore >> simp[] >>
     gvs[ptr_covers_def, lookup_var_def]) >>
  irule setup_instruction_continuation >>
  qexistsl_tac [`H`, `mk_inst sm.cs_next_id MSTORE [Var root;cnt] []`,
    `sm`, `sb`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `u2`] >>
  simp[mk_inst_def, is_terminator_def] >>
  conj_tac >- gvs[ADD1] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
    eval_operand_def, mstore_def, write_memory_with_expansion_def] >>
  Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def, mstore_def,
    write_memory_with_expansion_def, w2n_n2w]
QED

Finalise calldata_array_header_endpoint_ptr_core

Theorem calldata_array_header_endpoint_ptr:
  !root src sa cnt sb s t d totalbytes a G tn cx ctx PG R.
  abi_decode_array_header (Var root) src CALLDATALOAD sa = (cnt,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  ptr_covers G tn root s totalbytes /\ 32 <= totalbytes /\
  not_fresh_at sa root /\ eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?H u. frag_exec_ptr cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = H /\ z = u /\
      v = (t with vs_inst_idx := 2 + s.vs_inst_idx)) R /\
    ptr_covers H u root t totalbytes /\
    op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    u.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d + 32} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule_all calldata_array_header_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[]
QED

Theorem calldata_array_init_endpoint_ptr_core:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    maxn abi_sz sa = (setup,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  ptr_covers G tn root s totalbytes /\
  32 <= totalbytes /\ not_fresh_at sa root /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  abi_decoder_budget first last b cap s /\ first <= sa.cs_next_id /\
  sb.cs_next_id <= last ==>
  ?H u q p. FST setup = Var q /\
    eval_operand (FST setup) t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ p + 32 < dimword (:256) /\
    mload p t = 0w /\
    ptr_covers H u q
      (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    ptr_covers H u root
      (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) totalbytes /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem = (tn.t_mem DIFF {x | d <= x /\ x < d + 32})
      DIFF {x | p <= x /\ x < p + 32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\
      ~ctx_has_dalloca ctx' /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule (calldata_pos abi_decode_array_loop_init_trace) >> strip_tac >>
  gnvs[] >>
  qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_dynarray_position_prefix_def, calldata_pos_addr,
    abiDecoderBytesBoundTheory.abi_decode_bytes_head_def, abiDecoderDynarrayBoundTheory.abi_decode_dynarray_payload_guard_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >> gnvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn sa = (guard_cnt,guard_st)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_count_guard_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa guard_st ++
    (emitted_insts guard_st header_st ++ emitted_insts header_st sb)` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac [] >>
  disch_then (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts sa guard_st) s = OK s1` >>
  qpat_x_assum `run_inst_seq (_ ++ _) _ = OK t`
    (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) s1 = OK s2` >>
  drule_all calldata_count_guard_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  rename1 `op_taint u1 guard_cnt = {}` >>
  rename1 `op_prov H1 guard_cnt = NONE` >>
  `eval_operand src s1 = SOME a /\ op_taint u1 src = {}` by
    (Cases_on `src` >> fs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `abi_decoder_budget first last b cap s1 /\ ~s1.vs_halted` by
    (conj_tac >-
       (irule (iffRL abi_decoder_budget_transport) >> qexists_tac `s` >> simp[]) >> simp[]) >>
  `guard_st.cs_next_var = sa.cs_next_var + 3` by
    (drule calldata_count_guard_layout >> simp[]) >>
  `not_fresh_at guard_st root` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `lookup_var root s1 = SOME (n2w d) /\ ptr_covers H1 u1 root s1 totalbytes` by
    (conj_tac >- metis_tac[] >> irule ptr_covers_frame >> metis_tac[]) >>
  `s1.vs_allocas = s.vs_allocas /\ s1.vs_alloca_next = s.vs_alloca_next /\
   s1.vs_current_bb = s.vs_current_bb` by simp[] >>
  `run_inst_seq (emitted_insts guard_st header_st)
      (s1 with vs_inst_idx := s.vs_inst_idx + 4) =
    OK (s2 with vs_inst_idx := s.vs_inst_idx + 4)` by
    (qpat_x_assum `s1 = s with vs_vars := _` kall_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts guard_st header_st)` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts guard_st header_st) s1 = _` kall_tac >>
  qpat_x_assum `s1 = s with vs_vars := _` kall_tac >>
  `eval_operand src (s1 with vs_inst_idx := s.vs_inst_idx + 4) = SOME a` by
    (Cases_on `src` >> fs[eval_operand_def, lookup_var_def]) >>
  `lookup_var root (s1 with vs_inst_idx := s.vs_inst_idx + 4) = SOME (n2w d) /\
    ptr_covers H1 u1 root (s1 with vs_inst_idx := s.vs_inst_idx + 4) totalbytes /\
    ~(s1 with vs_inst_idx := s.vs_inst_idx + 4).vs_halted` by
    (gvs[ptr_covers_def, lookup_var_def]) >>
  drule_all calldata_array_header_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  suspend "joint_index"
QED

Resume calldata_array_init_endpoint_ptr_core[joint_index]:
  rename1 `ptr_covers H2 u2 root s2 totalbytes` >>
  `abi_decoder_budget first last b cap s2 /\ ~s2.vs_halted` by
    (conj_tac >-
      (irule (iffRL abi_decoder_budget_transport) >> qexists_tac `s1` >> simp[]) >> metis_tac[]) >>
  `header_st.cs_next_id IN abi_decoder_ids first last` by
    (drule calldata_count_guard_layout >> strip_tac >>
     simp[abi_decoder_ids_def] >> decide_tac) >>
  `run_inst_seq (emitted_insts header_st sb)
     (s2 with vs_inst_idx := s.vs_inst_idx + 6) =
     OK (t with vs_inst_idx := s.vs_inst_idx + 6)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts header_st sb)` by
      (fs[EVERY_MEM] >> metis_tac[]) >>
     simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  `abi_decoder_budget first last b cap (s2 with vs_inst_idx := s.vs_inst_idx + 6)` by
    (irule (iffRL abi_decoder_budget_transport) >> qexists_tac `s2` >> simp[]) >>
  `~(s2 with vs_inst_idx := s.vs_inst_idx + 6).vs_halted` by simp[] >>
  qpat_x_assum `run_inst_seq (emitted_insts header_st sb) s2 = _` kall_tac >>
  drule_all abi_decode_index_init_endpoint_exact_ptr_core >>
  disch_then (qspecl_then [`u2`,`cx`,`ctx`,`R`,`PG`,`H2`] mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  suspend "joint_finish"
QED

Resume calldata_array_init_endpoint_ptr_core[joint_finish]:
  `!x. not_fresh_at sa x ==> not_fresh_at guard_st x /\ not_fresh_at header_st x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x. cnt = Var x ==> not_fresh_at header_st x` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[] >> simp[not_fresh_at_def]) >>
  `LENGTH (emitted_insts sa guard_st) = 4` by
    (drule calldata_count_guard_layout >> strip_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `LENGTH (emitted_insts guard_st header_st) = 2` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `cs_extends sa guard_st /\ cs_extends guard_st header_st /\ cs_extends header_st sb` by
    (drule calldata_count_guard_layout >> strip_tac >>
     rpt conj_tac >> irule cs_extends_same_block >>
     fs[inst_extends_def, same_blocks_def] >> metis_tac[]) >>
  `p + 32 < dimword (:256)` by
    (drule abi_decoder_budget_word_bound >> decide_tac) >>
  `!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\
      ~ctx_has_dalloca ctx' /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s` by
    (suspend "joint_continuation") >>
  rpt (qpat_x_assum `run_inst_seq _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `abi_decoder_budget _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `abi_decode_array_loop_init _ _ _ _ _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `abi_decode_count_guard _ _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `abi_decode_index_init _ = _` kall_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[]) >>
  `ptr_covers H u root t totalbytes` by
    (irule ptr_covers_frame >> goal_assum (drule_at Any) >> fs[lookup_var_def] >> metis_tac[]) >>
  `op_taint u cnt = {} /\ op_prov H cnt = NONE` by
    (Cases_on `cnt` >> fs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  suspend "joint_compose"
QED

Resume calldata_array_init_endpoint_ptr_core[joint_compose]:
  qexistsl_tac [`H`,`u`,`p`] >>
  `mload p t = 0w` by fs[mload_def] >>
  `q = STRING #"%" (toString (guard_st.cs_next_var + 1))` by metis_tac[operand_11] >>
  `eval_operand (Var q) t = SOME (n2w p)` by metis_tac[] >>
  `q = STRING #"%" (toString (sa.cs_next_var + 4))` by simp[] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  irule frag_exec_ptr_seq >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  irule frag_exec_ptr_seq >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[ADD_ASSOC, ADD_COMM] >> metis_tac[]
QED

Resume calldata_array_init_endpoint_ptr_core[joint_continuation]:
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `!x. not_fresh_at _ x ==> _` kall_tac) >>
  rpt gen_tac >> strip_tac >>
  `fn_has_code sa guard_st func /\ fn_has_code guard_st header_st func /\
   fn_has_code header_st sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `guard_st.cs_current_bb = sa.cs_current_bb` by
    (drule calldata_count_guard_layout >> simp[]) >>
  `LENGTH guard_st.cs_current_insts = LENGTH sa.cs_current_insts + 4 /\
   LENGTH header_st.cs_current_insts = LENGTH sa.cs_current_insts + 6` by
    (fs[inst_extends_def] >> simp[] >> decide_tac) >>
  `allocas_from lower (s1 with vs_inst_idx := s.vs_inst_idx + 4) /\
   allocas_from lower (s2 with vs_inst_idx := s.vs_inst_idx + 6)` by
    (gvs[allocas_from_def] >> metis_tac[]) >>
  gvs[]
QED

Finalise calldata_array_init_endpoint_ptr_core

Theorem calldata_array_init_endpoint_ptr:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    maxn abi_sz sa = (setup,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  ptr_covers G tn root s totalbytes /\
  32 <= totalbytes /\ not_fresh_at sa root /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  abi_decoder_budget first last b cap s /\ first <= sa.cs_next_id /\
  sb.cs_next_id <= last /\ (d + totalbytes <= b \/ b + cap <= d) ==>
  ?H u q p. FST setup = Var q /\
    eval_operand (FST setup) t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ p + 32 < dimword (:256) /\
    mload p t = 0w /\
    ptr_covers H u q
      (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    ptr_covers H u root
      (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) totalbytes /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_mem = (tn.t_mem DIFF {x | d <= x /\ x < d + 32})
      DIFF {x | p <= x /\ x < p + 32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all calldata_array_init_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`,`p`] >> simp[]
QED


Theorem calldata_array_init_sequence_ptr:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    maxn abi_sz sa = (setup,sb) /\
  eval_operand src s = SOME (n2w srcpos) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load CALLDATALOAD (n2w srcpos:bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_budget first last b cap s /\ first <= sa.cs_next_id /\
  sb.cs_next_id <= last /\ (d + totalbytes <= b \/ b + cap <= d) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\
  ptr_covers G tn root s totalbytes /\ 32 <= totalbytes /\
  not_fresh_at sa root /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  op_taint tn src = {} ==>
  ?t p H u q.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand (FST setup) t = SOME (n2w p) /\
    eval_operand (SND setup) t = SOME (n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
    b <= p /\ p + 32 <= b + cap /\ p + 32 < dimword (:256) /\
    abi_decoder_budget first last b cap t /\ fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] s t /\
    abi_decode_footprint_frame [(d,32);(p,32)] s t /\
    FLOOKUP t.vs_allocas (sb.cs_next_id - 2) = SOME (p,32) /\
    (!id. id <> sb.cs_next_id - 2 ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_halted = s.vs_halted /\ inst_extends sa sb /\
    FST setup = Var q /\
    ptr_covers H u q (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    ptr_covers H u root (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) totalbytes /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_mem = (tn.t_mem DIFF {x | d <= x /\ x < d + 32})
      DIFF {x | p <= x /\ x < p + 32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var root) s = SOME (n2w d)` by simp[eval_operand_def] >>
  `first <= sb.cs_next_id - 2` by
    (drule (calldata_pos abi_decode_array_loop_init_site_bounds) >>
     simp[abi_decode_source_opcode_def] >> strip_tac >> decide_tac) >>
  drule_at (Pat `abi_decoder_budget _ _ _ _ _`) (calldata_pos abi_decode_array_loop_init_sequence) >>
  disch_then (drule_at (Pat `abi_decode_array_loop_init _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand src s = _`)) >>
  simp[abi_decode_source_opcode_def] >>
  disch_then (qspecl_then [`srcpos`,`n`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all calldata_array_init_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] strip_assume_tac) >>
  `p < dimword (:256)` by
    (drule abi_decoder_budget_word_bound >> decide_tac) >>
  `n2w p = (n2w p':bytes32)` by metis_tac[optionTheory.SOME_11] >>
  `p' < dimword (:256)` by decide_tac >>
  `p = p'` by
    (qpat_x_assum `n2w p = (n2w p':bytes32)` (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     simp[]) >>
  qexistsl_tac [`t`,`p`,`H`,`u`,`q`] >> simp[] >>
  fs[ptr_covers_def, lookup_var_def]
QED

(* Actual dynamic-array compiler phase split, retaining the residual loop. *)
Theorem calldata_array_loop_entry_ptr:
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz elem_dyn maxn) sa = ((),sc) /\
  (elem_dyn \/ dec_info_needs_clamp ei) /\
  eval_operand src s = SOME (n2w srcpos) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load CALLDATALOAD (n2w srcpos:bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_budget first last b cap s /\ first <= sa.cs_next_id /\
  sc.cs_next_id <= last /\ (d + totalbytes <= b \/ b + cap <= d) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\
  ptr_covers G tn root s totalbytes /\ 32 <= totalbytes /\
  not_fresh_at sa root /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  op_taint tn src = {} ==>
  ?setup sb t p H u q.
    abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
      maxn abi_sz sa = (setup,sb) /\
    compile_abi_decode_dyn_loop (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
      ei abi_sz mem_sz (FST setup) (SND setup) sb = ((),sc) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand (FST setup) t = SOME (n2w p) /\
    eval_operand (SND setup) t = SOME (n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
    b <= p /\ p + 32 <= b + cap /\ p + 32 < dimword (:256) /\
    abi_decoder_budget first last b cap t /\ fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] s t /\
    abi_decode_footprint_frame [(d,32);(p,32)] s t /\
    FLOOKUP t.vs_allocas (sb.cs_next_id - 2) = SOME (p,32) /\
    (!id. id <> sb.cs_next_id - 2 ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_halted = s.vs_halted /\ inst_extends sa sb /\
    FST setup = Var q /\ ptr_covers H u q t 32 /\
    ptr_covers H u root t totalbytes /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_mem = (tn.t_mem DIFF {x | d <= x /\ x < d + 32})
      DIFF {x | p <= x /\ x < p + 32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (calldata_pos abi_decode_loop_array_trace) >> strip_tac >>
  rename1 `abi_decode_array_loop_init _ _ _ _ _ _ _ sa = (setup,sb)` >>
  `sb.cs_next_id <= sc.cs_next_id` by
    (mp_tac (cj 3 (calldata_pos ci_mono_compile_abi_decode)) >>
     disch_then (qspecl_then [`Var root`,`src`,`CALLDATALOAD`,`Lit 0w`,
       `ei`,`abi_sz`,`mem_sz`,`FST setup`,`SND setup`,`sb`] mp_tac) >>
     simp[ci_mono_def, cs_extends_def]) >>
  `sb.cs_next_id <= last` by decide_tac >>
  drule_all calldata_array_init_sequence_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`setup`,`sb`,`t`,`p`,`H`,`u`,`q`] >>
  simp[] >> fs[ptr_covers_def, lookup_var_def]
QED
