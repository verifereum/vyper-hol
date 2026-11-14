(* The return-size guard shares the decoder's scalar availability proof. *)
Theory extcallReturnSizeJoint
Ancestors
  abiReturnSize extcallReturnEntryBridge bodyPtrBopScalarCompile
  abiDecodePtrScalarReplay bodyPtrBopScalarOutcome bodyPtrBopScalarSeq
  bodyPtrBopScalarDynamic
  stmtReasonLitFragMemory fragExec instIdxIndep
  emitHelperProps freshWrites builtinSimple builtinProps exprLoweringProps
  loweringStateRelDefs returndataSizePtr bodyFullUnwrapRun fragGasCopyLoop
  ptrDiscipline ptrSafeRun fragGasSeqPtr fragExecMem venomInst venomState
  venomExecSemantics codegenRel contextCodegenRel finite_map
  compileEnv exprLowering emitHelper list rich_list pred_set arithmetic

Theorem return_size_read_joint:
  emit_op RETURNDATASIZE [] a = (rds,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,H,tm)) /\
    eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata)) /\
    op_prov H rds = NONE /\ op_taint tm rds = {} /\
    H = DRESTRICT G (COMPL {STRING #"%" (toString a.cs_next_var)}) /\
    tm = tn with t_var :=
      tn.t_var |+ (STRING #"%" (toString a.cs_next_var),{}) /\
    u = (update_var (STRING #"%" (toString a.cs_next_var))
      (n2w (LENGTH s.vs_returndata)) s)
      with vs_inst_idx := LENGTH b.cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `i = mk_inst a.cs_next_id RETURNDATASIZE [] [x]` >>
  `rds = Var x /\ b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++ [i] /\
   emitted_insts a b = [i]` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
      emit_def, comp_return_def, Abbr `x`, Abbr `i`, emitted_insts_def] >>
     simp[DROP_LENGTH_APPEND]) >>
  qabbrev_tac `v = update_var x (n2w (LENGTH s.vs_returndata)) s` >>
  `run_inst_seq [i] s = OK v` by
    simp[run_inst_seq_def, Abbr `i`, Abbr `v`,
      raw_call_returndatasize_step_base] >>
  qexistsl_tac [`v with vs_inst_idx := LENGTH b.cs_current_insts`,
    `DRESTRICT G (COMPL {x})`, `tn with t_var := tn.t_var |+ (x,{})`] >>
  conj_tac >- suspend "path" >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    eval_operand_def, lookup_var_def, Abbr `v`, update_var_def]
QED


Resume return_size_read_joint[path]:
  gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`[i]`, `a`] >> simp[Abbr `i`, is_terminator_def] >>
  conj_tac
  >- simp[run_inst_seq_mem_ok_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_base_opcode_eqs, exec_read0_def, bind_outputs_def] >>
  irule inst_seq_ptr_lower_bound_transport >>
  conj_tac >- simp[mk_inst_def] >> simp[] >>
  qexists_tac `0` >> simp[] >>
  simp[inst_seq_ptr_def, raw_call_returndatasize_step_base,
    step_inst_base_opcode_eqs, exec_read0_def, bind_outputs_def,
    ptr_inst_ok_returndatasize, step_prov_def, set_prov_def, out_prov_def,
    step_taint_def, out_taint_def, set_var_taint_def, mem_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, adopt_reset_def,
    store_taint_def, imm_taint_def, range_bytes_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    FLOOKUP_DEF, Abbr `v`, update_var_def, SF CONJ_ss] >>
  simp[op_taint_def, FLOOKUP_UPDATE, taint_component_equality]
QED
Finalise return_size_read_joint

Theorem return_size_scalar_tail:
  compile_return_value_decode low cap a = (hi,b) /\
  (!x. x IN R ==> not_fresh_at a x) ==>
  ?rds m B.
    emit_op RETURNDATASIZE [] a = (rds,m) /\
    emitted_insts a b = emitted_insts a m ++ emitted_insts m b /\
    bop_scalar_seq R (rds INSERT {Lit (n2w low); Lit (n2w cap)})
      (emitted_insts m b) B /\ hi IN B
Proof
  simp[compile_return_value_decode_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_op RETURNDATASIZE [] a = (rds,m)` >>
  rename1 `emit_op LT [rds; Lit (n2w low)] m = (small,c2)` >>
  rename1 `emit_op ISZERO [small] c2 = (good,c3)` >>
  rename1 `emit_void ASSERT [good] c3 = (unit_result,c4)` >>
  Cases_on `unit_result` >>
  rename1 `emit_op LT [rds; Lit (n2w cap)] c4 = (cmp,c5)` >>
  `!x. x IN R ==> not_fresh_at m x /\ not_fresh_at c2 x /\
     not_fresh_at c3 x /\ not_fresh_at c4 x /\ not_fresh_at c5 x` by
    (imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >>
     fs[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  qabbrev_tac `A = rds INSERT {Lit (n2w low); Lit (n2w cap)}` >>
  `bop_scalar_seq R A (emitted_insts m c2) (small INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`LT`, `[rds; Lit (n2w low)]`] >>
     simp[Abbr `A`] >> metis_tac[]) >>
  `bop_scalar_seq R (small INSERT A) (emitted_insts c2 c3)
     (good INSERT small INSERT A)` by
    (irule bop_scalar_seq_emit_op >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ISZERO`, `[small]`] >>
     simp[] >> metis_tac[]) >>
  `bop_scalar_seq R (good INSERT small INSERT A) (emitted_insts c3 c4)
     (good INSERT small INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> qexistsl_tac [`good`, `ASSERT`] >>
     simp[]) >>
  `bop_scalar_seq R (good INSERT small INSERT A) (emitted_insts c4 c5)
     (cmp INSERT good INSERT small INSERT A)` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`LT`, `[rds; Lit (n2w cap)]`] >>
     simp[Abbr `A`] >> metis_tac[]) >>
  mp_tac (Q.INST [`R` |-> `R`,
    `A` |-> `cmp INSERT good INSERT small INSERT A`,
    `cond` |-> `cmp`, `x` |-> `rds`, `y` |-> `Lit (n2w cap)`,
    `st` |-> `c5`, `st'` |-> `b`, `v` |-> `hi`]
      bop_scalar_compile_select) >>
  impl_tac >- (simp[Abbr `A`] >> metis_tac[]) >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  imp_res_tac compile_select_extends >>
  `emitted_insts m c3 = emitted_insts m c2 ++ emitted_insts c2 c3` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  `emitted_insts m c4 = emitted_insts m c3 ++ emitted_insts c3 c4` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  `emitted_insts m c5 = emitted_insts m c4 ++ emitted_insts c4 c5` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  `emitted_insts m b = emitted_insts m c5 ++ emitted_insts c5 b` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  `emitted_insts a b = emitted_insts a m ++ emitted_insts m b` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  qexists_tac `B` >> fs[Abbr `A`] >>
  irule bop_scalar_seq_append >> goal_assum (drule_at Any) >>
  irule bop_scalar_seq_append >> goal_assum (drule_at Any) >>
  irule bop_scalar_seq_append >> goal_assum (drule_at Any) >>
  irule bop_scalar_seq_append >> goal_assum (drule_at Any) >> simp[]
QED

Theorem return_size_success_joint:
  compile_return_value_decode low cap a = (hi,b) /\ fn_has_code a b func /\
  run_inst_seq (emitted_insts a b) s = OK v /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!x. x IN R ==> not_fresh_at a x) ==>
  ?H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (v with vs_inst_idx := LENGTH b.cs_current_insts),H,tm)) /\
    op_prov H hi = NONE /\ op_taint tm hi = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tm.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all return_size_scalar_tail >> strip_tac >>
  drule abi_return_size_code >> strip_tac >>
  `m.cs_blocks = a.cs_blocks /\ m.cs_current_bb = a.cs_current_bb /\
   m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m` by
    (imp_res_tac emit_op_same_blocks >>
     imp_res_tac emitted_insts_emit_op >> fs[same_blocks_def]) >>
  `b.cs_current_bb = m.cs_current_bb /\
   b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b` by
    gvs[same_blocks_def, APPEND_ASSOC] >>
  `cs_extends a m /\ cs_extends m b` by
    (gvs[cs_extends_def, same_blocks_def] >> conj_tac >>
     qexists_tac `[]` >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all return_size_read_joint >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,H1,tm1)` >>
  `!x. x IN R ==> x <> STRING #"%" (toString a.cs_next_var)` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `run_inst_seq (emitted_insts a m) s =
     OK (update_var (STRING #"%" (toString a.cs_next_var))
       (n2w (LENGTH s.vs_returndata)) s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_def, raw_call_returndatasize_step_base]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts m b)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `run_inst_seq (emitted_insts m b) u =
      OK (v with vs_inst_idx := LENGTH m.cs_current_insts)` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `emitted_insts m b` assume_tac) >>
     gvs[run_inst_seq_inst_idx, exec_result_map_def]) >>
  `~u.vs_halted /\ allocas_from lo u /\
   u.vs_current_bb = m.cs_current_bb /\
   u.vs_inst_idx = LENGTH m.cs_current_insts` by
    (gvs[update_var_def, allocas_from_def] >> metis_tac[]) >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts m b) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `!op. op IN rds INSERT {Lit (n2w low); Lit (n2w cap)} ==>
     op_prov H1 op = NONE /\ op_taint tm1 op = {}` by
    (simp[] >> rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  suspend "scalar"
QED

Resume return_size_success_joint[scalar]:
  drule_all scalar_seq_success_replay_ptr >>
  disch_then (qspecl_then [`PG`,`ARB`] strip_assume_tac) >>
  rename1 `inst_seq_ptr ARB 0 ctx func PG H1 tm1 _ u H2 tm2` >>
  qexistsl_tac [`H2`,`tm2`] >> reverse conj_tac
  >- (gvs[] >> rpt strip_tac >>
      fs[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  gen_tac >>
  `?gD tnD. inst_seq_ptr D 0 ctx func PG H1 tm1 (emitted_insts m b) u gD tnD` by
    (drule_all bop_scalar_seq_run >>
     disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
     metis_tac[]) >>
  `gD = H2 /\ tnD = tm2` by metis_tac[inst_seq_ptr_ghost_unique] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts m b)` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     simp[MEM] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts m b) u` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >>
     gen_tac >> disch_tac >> gen_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     simp[MEM] >> strip_tac >>
     simp[instMemFrontierTheory.below_frontier_no_ranges,
       memSafeRunTheory.inst_dload_in_section_other]) >>
  drule_all run_inst_seq_origin_ptr_lift >>
  disch_then (qspec_then `explicit` strip_assume_tac) >>
  `LENGTH m.cs_current_insts + LENGTH (emitted_insts m b) =
     LENGTH b.cs_current_insts` by simp[] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,H1,tm1) []
     (OK (v with vs_inst_idx := LENGTH b.cs_current_insts),H2,tm2)` by
    (qpat_x_assum `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (u,H1,tm1) [] _` mp_tac >>
     simp[venom_state_fupdfupds, combinTheory.o_DEF]) >>
  qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,H1,tm1)` (qspec_then `D` mp_tac) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`u`,`H1`,`tm1`,`[]`,
    `OK (v with vs_inst_idx := LENGTH b.cs_current_insts)`,`H2`,`tm2`] mp_tac) >>
  simp[]
QED
Finalise return_size_success_joint

Theorem return_size_abort_joint:
  compile_return_value_decode low cap a = (hi,b) /\ fn_has_code a b func /\
  run_inst_seq (emitted_insts a b) s = Abort err v /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?j H tm. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort err (v with vs_inst_idx := j),H,tm)
Proof
  strip_tac >>
  `!x. x IN ({}:string set) ==> not_fresh_at a x` by simp[] >>
  drule_all return_size_scalar_tail >> strip_tac >>
  drule abi_return_size_code >> strip_tac >>
  `m.cs_blocks = a.cs_blocks /\ m.cs_current_bb = a.cs_current_bb /\
   m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m` by
    (imp_res_tac emit_op_same_blocks >>
     imp_res_tac emitted_insts_emit_op >> fs[same_blocks_def]) >>
  `b.cs_current_bb = m.cs_current_bb /\
   b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b` by
    gvs[same_blocks_def, APPEND_ASSOC] >>
  `cs_extends a m /\ cs_extends m b` by
    (gvs[cs_extends_def, same_blocks_def] >> conj_tac >>
     qexists_tac `[]` >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all return_size_read_joint >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,H1,tm1)` >>
  `run_inst_seq (emitted_insts a m) s =
     OK (update_var (STRING #"%" (toString a.cs_next_var))
       (n2w (LENGTH s.vs_returndata)) s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_def, raw_call_returndatasize_step_base]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts m b)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `run_inst_seq (emitted_insts m b) u =
      Abort err (v with vs_inst_idx := LENGTH m.cs_current_insts)` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `emitted_insts m b` assume_tac) >>
     gvs[run_inst_seq_inst_idx, exec_result_map_def]) >>
  `~u.vs_halted /\ allocas_from lo u /\
   u.vs_current_bb = m.cs_current_bb /\
   u.vs_inst_idx = LENGTH m.cs_current_insts` by
    (gvs[update_var_def, allocas_from_def] >> metis_tac[]) >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts m b) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `!op. op IN rds INSERT {Lit (n2w low); Lit (n2w cap)} ==>
     op_prov H1 op = NONE /\ op_taint tm1 op = {}` by
    (simp[] >> rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  suspend "abort"
QED

Resume return_size_abort_joint[abort]:
  drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  rename1 `step_inst_base (mk_inst id opc [needle] []) mid =
    Abort err (v with vs_inst_idx := LENGTH m.cs_current_insts)` >>
  `isPREFIX (prefix ++ [mk_inst id opc [needle] []])
      (DROP u.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `run_inst_seq (prefix ++ [mk_inst id opc [needle] []]) u =
     Abort err (v with vs_inst_idx := LENGTH m.cs_current_insts)` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `[mk_inst id opc [needle] []]` mp_tac) >>
     simp[run_inst_seq_def]) >>
  `EVERY (\i. MEM i.inst_opcode
      [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
       EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
       SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN; ASSERT; ASSERT_UNREACHABLE])
     (prefix ++ [mk_inst id opc [needle] []])` by
    (simp[EVERY_APPEND, mk_inst_def, EVERY_MEM] >>
     rpt strip_tac >> drule_all bop_scalar_seq_outputs >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
      (prefix ++ [mk_inst id opc [needle] []])` by
    (rewrite_tac[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (prefix ++ [mk_inst id opc [needle] []]) u` by
    (irule run_inst_seq_mem_ok_every >> rewrite_tac[EVERY_MEM] >>
     rpt gen_tac >> strip_tac >> BETA_TAC >> gen_tac >>
     qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[] >> strip_tac >>
     simp[instMemFrontierTheory.below_frontier_no_ranges,
       memSafeRunTheory.inst_dload_in_section_other]) >>
  drule_all run_inst_seq_origin_ptr_abort_lift >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`]
    (qx_choose_then `j` assume_tac)) >>
  drule bop_scalar_seq_assert_abort_checked >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`func`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `inst_seq_ptr ARB 0 ctx func PG _ _ _ _ H2 tm2` >>
  qexistsl_tac [`j`,`H2`,`tm2`] >> gen_tac >>
  drule bop_scalar_seq_assert_abort_checked >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx func PG _ _ _ _ gD tnD` >>
  `gD = H2 /\ tnD = tm2` by metis_tac[inst_seq_ptr_ghost_unique] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,H1,tm1) []
     (Abort err (v with vs_inst_idx := j),H2,tm2)` by
    (qpat_x_assum `!D G tn G' tn'. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ ==> _`
       (qspecl_then [`D`,`H1`,`tm1`,`H2`,`tm2`] mp_tac) >>
     (impl_tac >- (fs[] >> metis_tac[])) >>
     simp[venom_state_fupdfupds, combinTheory.o_DEF]) >>
  qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,H1,tm1)` (qspec_then `D` mp_tac) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`u`,`H1`,`tm1`,`[]`,
    `Abort err (v with vs_inst_idx := j)`,`H2`,`tm2`] mp_tac) >>
  simp[]
QED
Finalise return_size_abort_joint
