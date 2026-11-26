(* Lift the protected scalar suffix at the endpoint of its actual raw run. *)
Theory bodyExtSizeScalarTailExactMods
Ancestors
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome abiDecodeScalarRunSafety
  fragGasCopySeqLiftProps fragGasSeqPtr fragGasOriginPtr fragExecMem fragExec
  exprLoweringProps ptrDiscipline unitTransformDefs memSafeRun
  venomExecSemantics venomInst venomState finite_map rich_list list pred_set

Theorem ext_size_scalar_tail_exact_mods:
  bop_scalar_seq R A code B /\ hi IN B /\
  (!op. op IN A ==> op_prov G1 op = NONE /\ op_taint t1 op = {}) /\
  run_inst_seq code s = OK w /\ ~s.vs_halted /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G1,t1) []
      (OK (w with vs_inst_idx := s.vs_inst_idx + LENGTH code),Gf,tm)) /\
    op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
    tm.t_mem = t1.t_mem /\ tm.t_stor = t1.t_stor /\
    tm.t_trans = t1.t_trans /\ tm.t_imm = t1.t_imm /\
    (!x. x IN R ==> FLOOKUP Gf x = FLOOKUP G1 x /\
      op_taint tm (Var x) = op_taint t1 (Var x))
Proof
  strip_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `inst_seq_ptr ARB 0 ctx func PG G1 t1 code s G2 t2` >>
  qexistsl_tac [`G2`,`t2`] >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> fs[op_taint_def] >> metis_tac[]) >>
  drule abi_decode_scalar_run_safe >> disch_then (qspec_then `s` strip_assume_tac) >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     `MEM i code` by simp[MEM_APPEND] >>
     irule dalloca_no_wrap_non_dalloca >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  qx_gen_tac `D` >>
  `?gD tD. inst_seq_ptr D 0 ctx func PG G1 t1 code s gD tD` by
    (drule_all bop_scalar_seq_run >>
     disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
     goal_assum drule) >>
  `gD = G2 /\ tD = t2` by metis_tac[inst_seq_ptr_ghost_unique] >>
  gvs[] >> drule_all (SIMP_RULE (srw_ss()) [] run_inst_seq_origin_ptr_lift) >>
  disch_then (qspec_then `explicit` mp_tac) >> simp[]
QED
