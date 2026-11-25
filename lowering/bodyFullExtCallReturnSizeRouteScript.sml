(* Counted short-data and decoder-entry routes after allocation. *)
Theory bodyFullExtCallReturnSizeRoute
Ancestors
  abiReturnSize extcallReturnEntryBridge abiMalformedRecursiveInterface
  abiDecodeScalarRunSafety[qualified,ignore_grammar]
  bodyPtrBopScalarCompile bodyPtrBopScalarOutcome bodyPtrBopScalarSeq
  bodyPtrBopScalarDynamic bodyFullGhostFrame bodyFullUnwrapRun exprSimWordArgs
  fragGasOriginPtr fragGasCopyLoop fragGasCopySeqLiftProps fragGasSeqPtr fragExec fragExecMem
  fragGasOrigin fragGasMode fragGasPathFrameMem bodyMemAggregatePath
  abiReturnPrefixTransport decoderGhostFramePtr bodyPtrDefs loweringPosts
  stmtReasonLitFragMemory
  instIdxIndep instMemFrontier memSafeRun unitTransformDefs
  rawCallBufferPtr ptrDiscipline ptrSafeRun emitHelperProps freshWrites
  builtinSimple builtinProps exprLoweringProps loweringStateRelDefs
  venomExecSemantics venomInst venomState codegenRel contextCodegenRel
  compileEnv exprLowering emitHelper finite_map list rich_list pred_set arithmetic

Theorem size_route_read[local]:
  emit_op RETURNDATASIZE [] a = (rds,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,H,tm)) /\
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
   b.cs_current_insts = a.cs_current_insts ++ [i]` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def, Abbr `x`, Abbr `i`] >>
  qabbrev_tac `v = update_var x (n2w (LENGTH s.vs_returndata)) s` >>
  `run_inst_seq [i] s = OK v` by
    simp[run_inst_seq_def, Abbr `i`, Abbr `v`, raw_call_returndatasize_step_base] >>
  qexistsl_tac [`v with vs_inst_idx := LENGTH b.cs_current_insts`,
    `DRESTRICT G (COMPL {x})`, `tn with t_var := tn.t_var |+ (x,{})`] >>
  reverse conj_tac >-
    simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
         Abbr `x`, Abbr `v`] >>
  gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`[i]`, `a`] >> simp[Abbr `i`, is_terminator_def] >>
  conj_tac >-
    (rpt strip_tac >> Cases_on `pre` >> gvs[mk_inst_def]) >>
  conj_tac >-
    simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, mk_inst_def,
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

Theorem size_route_scalar_tail[local]:
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
     qexistsl_tac [`ISZERO`, `[small]`] >> simp[] >> metis_tac[]) >>
  `bop_scalar_seq R (good INSERT small INSERT A) (emitted_insts c3 c4)
     (good INSERT small INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> qexistsl_tac [`good`, `ASSERT`] >> simp[]) >>
  `bop_scalar_seq R (good INSERT small INSERT A) (emitted_insts c4 c5)
     (cmp INSERT good INSERT small INSERT A)` by
    (irule bop_scalar_seq_emit_op >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`LT`, `[rds; Lit (n2w cap)]`] >>
     simp[Abbr `A`] >> metis_tac[]) >>
  mp_tac (Q.INST [`R` |-> `R`,
    `A` |-> `cmp INSERT good INSERT small INSERT A`,
    `cond` |-> `cmp`, `x` |-> `rds`, `y` |-> `Lit (n2w cap)`,
    `st` |-> `c5`, `st'` |-> `b`, `v` |-> `hi`] bop_scalar_compile_select) >>
  (impl_tac >- (simp[Abbr `A`] >> metis_tac[])) >> strip_tac >>
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

(* Both routes start with a clean RETURNDATASIZE result; shifting that
   state to the scalar tail does not change the tail's physical outcome. *)
Theorem size_route_tail_entry[local]:
  compile_return_value_decode low cap a = (hi,b) /\ fn_has_code a b func /\
  run_inst_seq (emitted_insts a b) s = res /\
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!x. x IN R ==> not_fresh_at a x) ==>
  ?m u G1 tn1 A B bb.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)) /\
    bop_scalar_seq R A (emitted_insts m b) B /\ hi IN B /\
    (!op. op IN A ==> op_prov G1 op = NONE /\ op_taint tn1 op = {}) /\
    (!x. x IN R ==> FLOOKUP G1 x = FLOOKUP G x /\
      FLOOKUP tn1.t_var x = FLOOKUP tn.t_var x) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    ~u.vs_halted /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts m b) (DROP u.vs_inst_idx bb.bb_instructions) /\
    u.vs_inst_idx + LENGTH (emitted_insts m b) = LENGTH b.cs_current_insts /\
    run_inst_seq (emitted_insts m b) u =
      exec_result_map (\v. v with vs_inst_idx := u.vs_inst_idx) res
Proof
  strip_tac >> drule_all size_route_scalar_tail >> strip_tac >>
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
  drule_all size_route_read >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choose_then `u` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `!x. x IN R ==> x <> STRING #"%" (toString a.cs_next_var)` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `run_inst_seq (emitted_insts a m) s =
     OK (update_var (STRING #"%" (toString a.cs_next_var))
       (n2w (LENGTH s.vs_returndata)) s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_def, raw_call_returndatasize_step_base]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts m b)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `~u.vs_halted /\ allocas_from lo u /\ u.vs_current_bb = m.cs_current_bb /\
   u.vs_inst_idx = LENGTH m.cs_current_insts` by
    (gvs[update_var_def, allocas_from_def] >> metis_tac[]) >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts m b) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> simp[] >> metis_tac[]) >>
  `allocas_below_fmp u = allocas_below_fmp s` by
    (qpat_assum `u = _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[NoAsms,allocas_below_fmp_def,update_var_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by metis_tac[] >>
  qexistsl_tac [`m`,`u`,`G1`,`tn1`,`rds INSERT {Lit (n2w low); Lit (n2w cap)}`,`B`,`bb`] >>
  simp[] >> rpt conj_tac
  >- (simp[] >> rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def])
  >- (rpt strip_tac >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts m b` assume_tac) >>
  gvs[run_inst_seq_inst_idx]
QED

Theorem size_route_path_append[local]:
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,G1,tn1)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (u,G1,tn1) [] (res,G2,tn2)) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (res,G2,tn2)
Proof
  rpt strip_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Theorem size_route_success[local]:
  compile_return_value_decode low cap a = (hi,b) /\ fn_has_code a b func /\
  run_inst_seq (emitted_insts a b) s = OK v /\
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (v with vs_inst_idx := LENGTH b.cs_current_insts),Gf,tm)) /\
    op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!x. x IN {x | not_fresh_at a x} ==> not_fresh_at a x` by simp[] >>
  drule_all size_route_tail_entry >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  fs[exec_result_map_def] >>
  drule abiDecodeScalarRunSafetyTheory.abi_decode_scalar_run_safe >> disch_then (qspec_then `u` strip_assume_tac) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `inst_seq_ptr ARB 0 ctx func PG G1 tn1 _ u G2 tn2` >>
  qexistsl_tac [`G2`,`tn2`] >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> fs[op_taint_def] >> metis_tac[]) >>
  irule size_route_path_append >> goal_assum (drule_at Any) >>
  qx_gen_tac `D` >>
  `?gD tnD. inst_seq_ptr D 0 ctx func PG G1 tn1 (emitted_insts m b) u gD tnD` by
    (drule_all bop_scalar_seq_run >>
     disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >> metis_tac[]) >>
  `gD = G2 /\ tnD = tn2` by metis_tac[inst_seq_ptr_ghost_unique] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post reached. emitted_insts m b = pre ++ i::post /\
      run_inst_seq pre u = OK reached ==> dalloca_no_wrap i reached)` by
    (rpt strip_tac >>
     `MEM i (emitted_insts m b)` by simp[MEM_APPEND] >>
     irule dalloca_no_wrap_non_dalloca >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  gvs[] >> drule_all (SIMP_RULE (srw_ss()) [] run_inst_seq_origin_ptr_lift) >>
  disch_then (qspec_then `explicit` mp_tac) >>
  simp[venom_state_fupdfupds, combinTheory.o_DEF]
QED

Theorem size_route_abort[local]:
  compile_return_value_decode low cap a = (hi,b) /\ fn_has_code a b func /\
  run_inst_seq (emitted_insts a b) s = Abort err v /\
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?z Gf tm. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort err z,Gf,tm)
Proof
  strip_tac >>
  `!x. x IN ({}:string set) ==> not_fresh_at a x` by simp[] >>
  drule_all size_route_tail_entry >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  fs[exec_result_map_def] >>
  drule_all bop_scalar_seq_abort_prefix >>
  disch_then (qx_choose_then `prefix` (qx_choose_then `suffix`
    (qx_choose_then `C` (qx_choose_then `id` (qx_choose_then `opc`
      (qx_choose_then `needle` (qx_choose_then `mid` strip_assume_tac))))))) >>
  `isPREFIX (prefix ++ [mk_inst id opc [needle] []])
      (DROP u.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `run_inst_seq (prefix ++ [mk_inst id opc [needle] []]) u =
     Abort err (v with vs_inst_idx := u.vs_inst_idx)` by
    (qpat_assum `run_inst_seq prefix u = OK mid` (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `[mk_inst id opc [needle] []]` mp_tac) >>
     simp[run_inst_seq_def]) >>
  `bop_scalar_seq {} A (prefix ++ [mk_inst id opc [needle] []]) C` by
    (irule bop_scalar_seq_append >> qexists_tac `C` >>
     simp[] >> irule bop_scalar_seq_assert >> simp[]) >>
  qpat_assum `bop_scalar_seq {} A (prefix ++ [_]) C`
    (mp_then Any (qspec_then `u` strip_assume_tac) abiDecodeScalarRunSafetyTheory.abi_decode_scalar_run_safe) >>
  `(ctx_has_dalloca ctx ==>
    !pre i post reached. prefix ++ [mk_inst id opc [needle] []] =
      pre ++ i::post /\ run_inst_seq pre u = OK reached ==>
      dalloca_no_wrap i reached)` by
    (rpt strip_tac >>
     `MEM i (prefix ++ [mk_inst id opc [needle] []])` by
       metis_tac[MEM_APPEND, MEM] >>
     irule dalloca_no_wrap_non_dalloca >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  drule_all run_inst_seq_origin_ptr_abort_lift >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choose_then `j` assume_tac)) >>
  `!D. ?G2 tn2. inst_seq_ptr D 0 ctx func PG G1 tn1
     (prefix ++ [mk_inst id opc [needle] []]) u G2 tn2` by
    (qx_gen_tac `D` >>
     `opc = ASSERT \/ opc = ASSERT_UNREACHABLE` suffices_by
       (disch_tac >>
              drule_all bop_scalar_seq_assert_abort_checked >>
        disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >> metis_tac[]) >>
     simp[]) >>
  pop_assum (fn th =>
    assume_tac th >> qspec_then `ARB`
      (qx_choose_then `G2` (qx_choose_then `tn2` assume_tac)) th) >>
  qexistsl_tac [`v with vs_inst_idx := j`,`G2`,`tn2`] >>
  irule size_route_path_append >> goal_assum (drule_at Any) >> qx_gen_tac `D` >>
  qpat_assum `!D. ?gD tnD. inst_seq_ptr D 0 _ _ _ _ _ _ _ gD tnD`
    (qspec_then `D` (qx_choose_then `gD` (qx_choose_then `tnD` assume_tac))) >>
  `gD = G2 /\ tnD = tn2` by metis_tac[inst_seq_ptr_ghost_unique] >>
  qpat_assum `!D G tn G' tn'. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ ==> _`
    (qspecl_then [`D`,`G1`,`tn1`,`G2`,`tn2`] mp_tac) >>
  gvs[venom_state_fupdfupds, combinTheory.o_DEF]
QED

(* The caller supplies the path to the common post-allocation entry.
   The size check selects an abort or one prepared endpoint, before any
   decoder or clean-window argument is used. *)
Theorem extcall_return_size_route:
  compile_return_value_decode low cap a = (hi,b) /\ fn_has_code a b func /\
  low < dimword (:256) /\ cap < dimword (:256) /\
  entry.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\
  ~entry.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp entry) /\ allocas_from lo entry /\
  entry.vs_current_bb = a.cs_current_bb /\
  entry.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G,tn) [] (OK entry,GP,tp)) ==>
  if LENGTH bs < low then
    ?z Gf tm. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort z,Gf,tm)
  else
    ?u Gf tm.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (t,G,tn) [] (OK u,Gf,tm)) /\
      (!H. abi_return_decode_ready H ctx func cenv cx ee a sites dstid live
         base_op dst B cap bs dest n entry ==>
        abi_malformed_entry H ctx func cenv cx ee b sites dstid live
          base_op hi (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 dest n u) /\
      op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
      u.vs_current_bb = b.cs_current_bb /\
      u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted /\
      u.vs_memory = entry.vs_memory /\ u.vs_allocas = entry.vs_allocas /\
      u.vs_alloca_next = entry.vs_alloca_next /\ u.vs_returndata = bs /\
      allocas_from lo u /\
      (!x. not_fresh_at a x ==> lookup_var x u = lookup_var x entry /\
        FLOOKUP Gf x = FLOOKUP GP x /\ op_taint tm (Var x) = op_taint tp (Var x)) /\
      tm.t_mem = tp.t_mem /\ tm.t_stor = tp.t_stor /\
      tm.t_trans = tp.t_trans /\ tm.t_imm = tp.t_imm /\
      (fn_inst_ids_distinct func /\ alloca_history func entry /\ alloca_inv entry ==>
        alloca_history func u) /\
      (!D d. ghost_inv_at D lo d cenv cx ee GP tp entry /\
        local_ptrs_reserved cenv a /\
        (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
        (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) ==>
        ghost_inv_at D lo d cenv cx ee Gf tm u) /\
      (!x sz. not_fresh_at a x /\ ptr_covers GP tp x entry sz ==>
        ptr_covers Gf tm x u sz) /\
      (!es sa s0. wb_frame cenv es ee sa s0 entry /\ sa.cs_next_var <= a.cs_next_var ==>
        wb_frame cenv es ee sa s0 u) /\
      (!es sr. ghost_kept_at lo cenv es sr G tn t GP tp /\
        sr.cs_next_var <= a.cs_next_var ==>
        ghost_kept_at lo cenv es sr G tn t Gf tm)
Proof
  strip_tac >>
  `LENGTH entry.vs_returndata < dimword (:256)` by simp[] >>
  drule_all return_size_actual_run >>
  Cases_on `LENGTH bs < low` >> simp[]
  >- (strip_tac >> drule_all size_route_abort >>
      disch_then (qspecl_then [`tp`,`explicit`,`PG`,`GP`] strip_assume_tac) >>
      qexistsl_tac [`z`,`Gf`,`tm`] >>
      irule size_route_path_append >> goal_assum (drule_at Any) >> simp[]) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts a b) entry = OK v` >>
  drule_all size_route_success >>
  disch_then (qspecl_then [`tp`,`explicit`,`PG`,`GP`]
    (qx_choose_then `Gf` (qx_choose_then `tm` strip_assume_tac))) >>
  qabbrev_tac `u = v with vs_inst_idx := LENGTH b.cs_current_insts` >>
  `!x. not_fresh_at a x ==> lookup_var x u = lookup_var x entry /\
     FLOOKUP Gf x = FLOOKUP GP x /\ op_taint tm (Var x) = op_taint tp (Var x)` by
    (fs[Abbr `u`, lookup_var_def]) >>
  drule abi_return_size_code >> strip_tac >>
  `u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
   ~u.vs_halted /\ u.vs_memory = entry.vs_memory /\ u.vs_allocas = entry.vs_allocas /\
   u.vs_alloca_next = entry.vs_alloca_next /\ u.vs_returndata = bs /\
   allocas_from lo u` by
    (qpat_assum `v = entry with vs_vars := _`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >>
     fs[same_blocks_def, allocas_from_def, Abbr `u`] >> metis_tac[]) >>
  qexistsl_tac [`u`,`Gf`,`tm`] >> simp[] >>
  conj_tac
  >- (irule size_route_path_append >> goal_assum (drule_at Any) >> simp[Abbr `u`]) >>
  conj_tac
  >- (qx_gen_tac `H` >> strip_tac >>
      `low <= LENGTH bs` by decide_tac >> drule_all return_decode_ready_entry >>
      strip_tac >> gvs[Abbr `u`]) >>
  conj_tac
  >- (strip_tac >>
      `gas_path_mem ctx func entry 0 (OK u)` by
        (qpat_assum `!D. gas_origin_ptr_path _ (entry,GP,tp) [] _`
           (qspec_then `ARB` (mp_tac o MATCH_MP gas_origin_ptr_path_projections)) >>
         strip_tac >> drule gas_origin_path_erase >> simp[gas_marked_path_def, Abbr `u`]) >>
      irule gas_path_mem_zero_history >> simp[] >>
      qexistsl_tac [`ctx`,`entry`] >> simp[] >>
      metis_tac[aggregate_mem_path_alloca_inv]) >>
  conj_tac
  >- (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
      goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
      qexists_tac `a` >>
      qpat_assum `v = entry with vs_vars := _`
        (strip_assume_tac o SRULE [venom_state_component_equality]) >>
      simp[Abbr `u`]) >>
  conj_tac
  >- (rpt strip_tac >> irule ptr_covers_frame >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule wb_frame_readonly_tail >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >> irule ghost_kept_at_clean_suffix >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
