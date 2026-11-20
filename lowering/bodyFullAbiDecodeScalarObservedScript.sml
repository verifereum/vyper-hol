Theory bodyFullAbiDecodeScalarObserved
Ancestors
  bodyFullAbiDecodeFiniteObserved
  bodyFullBopWordSuccess bodyPtrBopScalarSeq fragExec exprLoweringProps
  venomInst venomState venomExecSemantics list rich_list
  bodyFullAbiDecodeFiniteGuard bodyPtrBopScalarDynamic genBlockSim
  fragGasOriginPtr fragGasPathPtr fragGasPath

(* Both paths end at the cursor fixed by the successful scalar sequence.
   The memory-taint frame belongs to the very same ghost witnesses. *)
Theorem member_scalar_success_observed:
  bop_scalar_seq R A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ allocas_from lo s ==>
  ?Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP Gf x = FLOOKUP G x /\
                       FLOOKUP tnf.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[emitHelperPropsTheory.inst_extends_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1, DROP_LENGTH_NIL]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> conj_tac
  >- (qpat_assum `sb.cs_current_insts = _` (fn th => simp[th]) >>
      qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _` mp_tac >> simp[]) >>
  drule bop_scalar_seq_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by gs[EVERY_MEM] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    gs[EVERY_MEM, FILTER_EQ_NIL] >>
  qpat_x_assum `fn_has_code sa sb fn` kall_tac >> rpt strip_tac >>
  drule_all abi_decode_finite_success_observed >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

(* Identify the abort cursors under the original function, then use the
   fixed-cursor certificate for each compatible observer. *)
Theorem member_scalar_revert_observed:
  bop_scalar_seq R A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  ?u Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort u,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort u))
Proof
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all abi_decode_scalar_guard_abort_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  reverse (drule_all bop_scalar_seq_abort_prefix >> strip_tac)
  >- (`step_inst 0 ctx (mk_inst id ASSERT_UNREACHABLE [op] []) u =
        Abort Revert_abort t` by gvs[step_inst_non_invoke, mk_inst_def] >>
      drule_at (Pat `step_inst _ _ _ _ = _`) step_inst_assert_unreachable_abort >>
      simp[mk_inst_def]) >>
  `step_inst_base (mk_inst id ASSERT [op] []) u = Abort Revert_abort t` by gs[] >>
  `sb.cs_current_insts = sa.cs_current_insts ++
    (prefix ++ mk_inst id ASSERT [op] [] :: suffix)` by
    gs[emitHelperPropsTheory.inst_extends_def, APPEND_ASSOC] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) prefix) = 0` by
    (qpat_assum `bop_scalar_seq R A prefix C`
       (mp_tac o MATCH_MP bop_scalar_seq_opcodes) >>
     simp[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  qabbrev_tac `v = t with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH prefix` >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort v)` by
    (simp[Abbr `v`] >> qpat_x_assum `fn_has_code sa sb fn` kall_tac >>
     rpt strip_tac >> drule_all abi_decode_finite_revert_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  `gas_path ctx fn s 0 (Abort Revert_abort (t with vs_inst_idx := j))` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (mp_tac o SPEC_ALL) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     simp[] >> metis_tac[gas_path_ptr_erase]) >>
  `?m. run_from m ctx fn s = Abort Revert_abort (t with vs_inst_idx := j)` by
    (irule gas_path_exit >> simp[exit_result_def] >> qexists_tac `0` >> simp[]) >>
  `?n. run_from n ctx fn s = Abort Revert_abort v` by
    (irule gas_path_exit >> simp[exit_result_def] >> qexists_tac `0` >> simp[]) >>
  `run_from (m+n) ctx fn s = Abort Revert_abort (t with vs_inst_idx := j)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `m` >> simp[]) >>
  `run_from (m+n) ctx fn s = Abort Revert_abort v` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `n` >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `Gf`, `tnf`] >> gvs[]
QED
