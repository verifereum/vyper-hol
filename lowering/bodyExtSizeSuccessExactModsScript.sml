(* The successful size guard reaches the cursor-adjusted raw endpoint. *)
Theory bodyExtSizeSuccessExactMods
Ancestors
  bodyExtSizeScalarCutMods bodyExtSizeReadExactMods bodyExtSizeScalarTailExactMods
  stmtReasonLitFragMemory bodyPtrBopScalarSeq fragExec fragGasOriginPtr
  exprLoweringProps unitTransformDefs memSafeRun ptrDiscipline
  venomExecSemantics venomState finite_map rich_list list pred_set

Theorem ext_size_success_exact_mods:
  compile_return_value_decode low cap k = (hi,hs) /\ fn_has_code k hs func /\
  run_inst_seq (emitted_insts k hs) p = OK v /\
  ~p.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp p) /\ allocas_from lo p /\
  p.vs_current_bb = k.cs_current_bb /\ p.vs_inst_idx = LENGTH k.cs_current_insts ==>
  ?Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (p,Gp,tp) []
      (OK (v with vs_inst_idx := LENGTH hs.cs_current_insts),Gf,tm)) /\
    op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
    tm.t_mem = tp.t_mem /\ tm.t_stor = tp.t_stor /\
    tm.t_trans = tp.t_trans /\ tm.t_imm = tp.t_imm /\
    (!x. not_fresh_at k x ==> FLOOKUP Gf x = FLOOKUP Gp x /\
      op_taint tm (Var x) = op_taint tp (Var x))
Proof
  strip_tac >> drule ext_size_scalar_cut_mods >> strip_tac >>
  rename1 `emit_op RETURNDATASIZE [] k = (rds,m)` >>
  `fn_has_code k m func /\ fn_has_code m hs func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  drule_all ext_size_read_exact_mods >>
  disch_then (qspecl_then [`tp`,`explicit`,`PG`,`Gp`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts k m) p = OK w` >>
  qabbrev_tac `s = w with vs_inst_idx := LENGTH m.cs_current_insts` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts m hs)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `run_inst_seq (emitted_insts m hs) w = OK v` by
    (qpat_assum `run_inst_seq (emitted_insts k m) p = OK w`
       (qspec_then `emitted_insts m hs` (assume_tac o SYM) o
        MATCH_MP run_inst_seq_append) >>
     once_asm_rewrite_tac[] >>
     qpat_assum `emitted_insts k hs = _ ++ _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `run_inst_seq (emitted_insts m hs) s = OK (v with vs_inst_idx := LENGTH m.cs_current_insts)` by
    simp[Abbr `s`, run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
  `~s.vs_halted /\ allocas_from lo s /\ s.vs_current_bb = m.cs_current_bb /\
   s.vs_inst_idx = LENGTH m.cs_current_insts /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (drule emit_op_extends >> strip_tac >>
     simp[Abbr `s`, allocas_from_def, allocas_below_fmp_def] >>
     qpat_assum `w = p with vs_vars := _` SUBST1_TAC >>
     fs[same_blocks_def, allocas_from_def, allocas_below_fmp_def] >>
     rpt strip_tac >> res_tac) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts m hs) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >>
     simp[] >> strip_tac >> HINT_EXISTS_TAC >> simp[]) >>
  rename1 `op_prov G1 rds = NONE` >> rename1 `op_taint t1 rds = {}` >>
  `!op. op IN (rds INSERT {Lit (n2w low); Lit (n2w cap)}) ==>
        op_prov G1 op = NONE /\ op_taint t1 op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all ext_size_scalar_tail_exact_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `op_prov Gf hi = NONE` >> rename1 `op_taint tm hi = {}` >>
  qexistsl_tac [`Gf`,`tm`] >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> fs[] >> metis_tac[]) >>
  qx_gen_tac `D` >>
  `LENGTH hs.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts m hs)` by
    simp[] >>
  qpat_assum `LENGTH hs.cs_current_insts = _` SUBST1_TAC >>
  qpat_assum `!d. gas_origin_ptr_path _ (s,G1,t1) _ _`
    (qspec_then `D` (assume_tac o SIMP_RULE bool_ss
      [venom_state_fupdfupds, combinTheory.o_DEF, combinTheory.K_THM])) >>
  qpat_assum `!d. gas_origin_ptr_path _ (p,Gp,tp) _ _`
    (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
  simp[] >> metis_tac[]
QED
