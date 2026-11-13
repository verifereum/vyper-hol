(* Canonical, horizon-independent ghosts for unsigned AsWeiValue scaling. *)
Theory bodyFullBuiltinWordWeiSuffix
Ancestors
  bodyPtrWordBuiltinsScaling bodyPtrWordBuiltinsScalingSteps
  bodyPtrWordBuiltinsScalarSequence ptrDiscipline venomInst
  instSeqPtrLo bodyFullGhostFrame freshWrites
  exprSimWordBuiltins fragGasSeqPtr fragGasEmitCtrl bodySimFull
  finite_map pred_set list fragExec fragExecMem unitTransformDefs memSafeRun contextCodegenRel codegenRel
  venomExecSemantics venomState exprLoweringProps

Theorem as_wei_value_step_exterior:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  MEM i (emitted_insts sa sb) /\ step_inst_base i s = OK t ==>
  step_taint i s t tn = tn with t_var :=
    set_var_taint tn.t_var i.inst_outputs (out_taint tn i s)
Proof
  strip_tac >> Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[]) >>
  drule_all word_scale_emitted_shape >> strip_tac >>
  `MEM i.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT]` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (`fresh_write_op i.inst_opcode` by fs[fresh_write_op_def, MEM] >>
     drule_all step_fresh_write_op >> simp[]) >>
  `new_site_bytes s t = {}` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
     simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss]) >>
  Cases_on `MEM i.inst_opcode [Div; OR]`
  >- (drule_all word_scale_delta_ghost_step >>
      simp[word_scale_delta_out_taint]) >>
  `MEM i.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL]` by fs[MEM] >>
  metis_tac[bodyPtrWordBuiltinsAbsSequenceTheory.word_abs_ghost_step]
QED

Theorem as_wei_value_prefix_ghosts:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  emitted_insts sa sb = xs ++ ys /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn xs s G' tn') /\
    (!t. run_inst_seq xs s = OK t ==>
      (!x. x IN {z | v = Var z} UNION
        set (FLAT (MAP (\i. i.inst_outputs) xs)) ==>
        FLOOKUP G' x = NONE /\ op_taint tn' (Var x) = {}) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)))
Proof
  strip_tac >> Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[] >>
      qexistsl_tac [`G`, `tn`] >> simp[inst_seq_ptr_def] >>
      rpt strip_tac >> gvs[op_prov_def]) >>
  drule_all word_scale_emitted_shape >> strip_tac >>
  drule word_scale_emitted_dependency >> strip_tac >>
  `!i. MEM i xs ==> MEM i (emitted_insts sa sb)` by simp[] >>
  `!pre i post x. xs = pre ++ i::post /\ MEM (Var x) i.inst_operands ==>
     x IN {z | v = Var z} UNION set (FLAT (MAP (\j. j.inst_outputs) pre))` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     qexistsl_tac [`i`, `post ++ ys`] >> simp[]) >>
  `?G' tn'.
    inst_seq_ptr
      (<|d_stor := K (K {}); d_trans := K (K {});
         d_imm := K {}; d_ret := K {}|>) 0 ctx fn PG G tn
      xs s G' tn' /\
    (!t. run_inst_seq xs s = OK t ==>
      (!x. x IN {z | v = Var z} UNION
        set (FLAT (MAP (\i. i.inst_outputs) xs)) ==>
        FLOOKUP G' x = NONE /\ op_taint tn' (Var x) = {}) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)))` by
    (irule (word_scalar_sequence |> Q.INST
      [`P` |-> `\B H th u.
         (!x. x IN B ==> FLOOKUP H x = NONE /\ op_taint th (Var x) = {}) /\
         th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
         th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
         (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
           op_taint th (Var x) = op_taint tn (Var x))`] |> BETA_RULE) >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `MEM i (emitted_insts sa sb)` by metis_tac[] >>
         `MEM i.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT]` by
           (fs[EVERY_MEM] >> metis_tac[]) >>
         conj_tac
         >- (gen_tac >> disch_tac >>
             irule (word_scale_scalar_transfer |> SIMP_RULE (srw_ss()) [IN_UNION]) >>
             (conj_tac >- fs[MEM]) >> qexists_tac `B` >> simp[]) >>
         drule_all as_wei_value_step_exterior >>
         disch_then (qspec_then `th` SUBST1_TAC) >> simp[] >>
         gen_tac >> strip_tac >>
         `~MEM x i.inst_outputs` by
           (drule word_scale_outputs_fresh >>
            disch_then (qspec_then `sa` mp_tac) >> simp[] >> metis_tac[]) >>
         simp[decoderGhostFramePtrTheory.step_prov_other_output] >>
         Cases_on `i.inst_outputs` >>
         gvs[op_taint_def, set_var_taint_def, FLOOKUP_DRESTRICT] >>
         Cases_on `t` >> gvs[set_var_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
     conj_tac
     >- (rpt strip_tac >> irule word_scale_inst_ok >>
         simp[allocas_from_def] >> fs[EVERY_MEM] >>
         rpt strip_tac >> Cases_on `arg` >>
         gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
     conj_tac >- (Cases_on `v` >> gvs[op_prov_def]) >>
     fs[EVERY_MEM]) >>
  qexistsl_tac [`G'`, `tn'`] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
      qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
         d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  metis_tac[]
QED

Theorem as_wei_value_canonical_ghosts:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn') /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)))
Proof
  strip_tac >>
  drule_all (as_wei_value_prefix_ghosts |> Q.INST
    [`xs` |-> `emitted_insts sa sb`, `ys` |-> `[]`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> gen_tac >> disch_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >>
      gvs[inst_seq_ptr_def]) >>
  drule_all word_scale_emitted_insts >> strip_tac >>
  gvs[op_prov_def] >> first_x_assum irule >> simp[mk_inst_def]
QED

Theorem as_wei_value_suffix_mem_ok:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >>
      gvs[run_inst_seq_mem_ok_def]) >>
  drule_all word_scale_emitted_insts >> strip_tac >>
  simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

Theorem as_wei_value_success_origin:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all as_wei_value_canonical_ghosts >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >>
  reverse conj_tac >- metis_tac[] >> gen_tac >>
  drule_all word_scale_current_block >> strip_tac >>
  drule_all word_scale_code_prefix >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (Cases_on `denomination_multiplier dn = 1`
     >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[]) >>
     drule_all word_scale_emitted_shape >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[as_wei_value_suffix_mem_ok] >>
  first_x_assum (qspec_then `D` assume_tac) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  simp[]
QED

Theorem as_wei_value_prefix_runtime_frame:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  emitted_insts sa sb = xs ++ ys /\
  sc.cs_next_var <= sa.cs_next_var /\
  run_inst_seq xs s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `writes_fresh sc (emitted_insts sa sb)` by
    (Cases_on `denomination_multiplier dn = 1`
     >- (gvs[] >> drule word_scale_identity >> simp[writes_fresh_def]) >>
     drule_all word_scale_emitted_shape >> strip_tac >>
     drule word_scale_outputs_fresh >>
     disch_then (qspec_then `sc` mp_tac) >> simp[] >> strip_tac >>
     rewrite_tac[writes_fresh_def, EVERY_MEM] >> rpt strip_tac
     >- (fs[EVERY_MEM, fresh_write_op_def] >> metis_tac[MEM, MEM_APPEND]) >>
     metis_tac[]) >>
  `writes_fresh sc xs` by
    (fs[writes_fresh_def] >> metis_tac[EVERY_APPEND]) >>
  drule_all run_inst_seq_writes_fresh >> simp[venomStateTheory.lookup_var_def]
QED

Theorem as_wei_value_runtime_frame:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  sc.cs_next_var <= sa.cs_next_var /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> irule (as_wei_value_prefix_runtime_frame |> Q.INST
    [`ys` |-> `[]`] |> SIMP_RULE (srw_ss()) []) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem as_wei_value_success_full:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  sc.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  es'.scopes = es.scopes /\
  ghost_kept_at lo cenv es0 sc G0 tn0 s0 G tn /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'.
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    ghost_kept_at lo cenv es0 sc G0 tn0 s0 G' tn' /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
       (ghost_inv_at D lo d cenv cx es G tn s ==>
        ghost_inv_at D lo d cenv cx es' G' tn'
          (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all as_wei_value_success_origin >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  drule_all as_wei_value_runtime_frame >> strip_tac >>
  `!x. not_fresh_at sc x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> first_x_assum irule >>
     metis_tac[not_fresh_at_mono]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> conj_tac
  >- (fs[bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
  gen_tac >> strip_tac >> irule ghost_inv_at_exterior_frame >>
  goal_assum (drule_at Any) >> qexists_tac `sc` >> simp[] >>
  qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
  fs[venomStateTheory.lookup_var_def]
QED

Theorem as_wei_value_abort_prefix:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  ?u. run_inst_seq (TAKE 5 (emitted_insts sa sb)) s = OK u /\
      step_inst_base (EL 5 (emitted_insts sa sb)) u = Abort Revert_abort t /\
      t = revert_state (set_returndata [] u)
Proof
  strip_tac >> Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >>
      gvs[run_inst_seq_def]) >>
  drule_all word_scale_emitted_insts >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = Abort _ _` mp_tac >>
  simp[run_inst_seq_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
      exec_pure2_def, AllCaseEqs()]
QED

Theorem as_wei_value_abort_origin:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  ?G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx + 5),G',tn')) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all as_wei_value_abort_prefix >> strip_tac >>
  `denomination_multiplier dn <> 1` by
    (strip_tac >> gvs[] >> drule word_scale_identity >> strip_tac >>
     gvs[run_inst_seq_def]) >>
  `emitted_insts sa sb = TAKE 5 (emitted_insts sa sb) ++
     DROP 5 (emitted_insts sa sb)` by simp[TAKE_DROP] >>
  drule_all as_wei_value_prefix_ghosts >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >> reverse conj_tac >- simp[] >>
  gen_tac >>
  drule_all word_scale_code_prefix >> strip_tac >>
  drule_all word_scale_emitted_insts >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base q u = Abort Revert_abort t` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq p s = OK u` >>
  `emitted_insts sa sb = p ++ [q] /\ LENGTH p = 5 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) p /\
   FILTER (\i. i.inst_opcode = GAS) p = []` by
    simp[Abbr `p`, Abbr `q`, mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok p s` by
    (simp[Abbr `p`, run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  `isPREFIX p (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (emitted_insts sa sb) _` mp_tac >>
     pure_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `[q] ++ l` >> metis_tac[APPEND_ASSOC]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := s.vs_inst_idx + 5),G',tn')` by
    (first_x_assum (qspec_then `D` assume_tac) >>
     drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  qpat_x_assum `emitted_insts sa sb = p ++ DROP _ _` kall_tac >>
  `u = s with vs_vars := u.vs_vars` by
    (irule (cj 1 as_wei_value_prefix_runtime_frame) >>
     goal_assum (drule_at Any) >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `get_instruction bb (s.vs_inst_idx + 5) = SOME q` by
    (qpat_x_assum `isPREFIX (emitted_insts sa sb) _` mp_tac >>
     pure_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     disch_then (qx_choose_then `tail` assume_tac) >>
     `isPREFIX [q] (DROP (s.vs_inst_idx + 5) bb.bb_instructions)` by
       (pure_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >>
        qexists_tac `tail` >>
        qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 5`) >>
        simp[rich_listTheory.DROP_APPEND, rich_listTheory.DROP_DROP_T,
             rich_listTheory.DROP_LENGTH_NIL, arithmeticTheory.ADD_COMM]) >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (u with vs_inst_idx := s.vs_inst_idx + 5,G',tn') []
      (Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx + 5),G',tn')` by
    (irule exit_inst_origin_ptr >>
     simp[exit_result_def] >>
     conj_tac >- (qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
     qexistsl_tac [`bb`, `q`] >> simp[] >>
     `q.inst_opcode = ASSERT` by simp[Abbr `q`, mk_inst_def] >>
     conj_tac
     >- (simp[step_inst_non_invoke] >>
         mp_tac (Q.SPECL [`q`, `u`, `LENGTH sa.cs_current_insts + 5`]
           instIdxIndepTheory.step_inst_inst_idx_indep) >>
         simp[is_terminator_def, instIdxIndepTheory.exec_result_map_def]) >>
     simp[gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def,
       mem_safe_step_non_invoke, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
     conj_tac
     >- (qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >>
         simp[] >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     irule word_scale_inst_ok >> simp[] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!x. x IN _ UNION _ ==> _` mp_tac >>
         simp[Abbr `p`, Abbr `q`, mk_inst_def] >>
         qpat_x_assum `MEM arg _` mp_tac >>
         simp[mk_inst_def] >> strip_tac >> simp[op_prov_def]) >>
     qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >>
     simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ (OK _,_,_)`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >> metis_tac[]
QED

Theorem as_wei_value_abort_runtime_frame:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  sc.cs_next_var <= sa.cs_next_var /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  t = revert_state (set_returndata [] (s with vs_vars := t.vs_vars)) /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all as_wei_value_abort_prefix >> strip_tac >>
  `emitted_insts sa sb = TAKE 5 (emitted_insts sa sb) ++
    DROP 5 (emitted_insts sa sb)` by simp[TAKE_DROP] >>
  drule_all as_wei_value_prefix_runtime_frame >> strip_tac >>
  qpat_x_assum `t = revert_state _` SUBST1_TAC >>
  simp[revert_state_def, set_returndata_def, lookup_var_def] >>
  qpat_x_assum `u = s with vs_vars := _` (fn th => rewrite_tac[Once th]) >>
  simp[] >> metis_tac[lookup_var_def]
QED

Theorem as_wei_value_abort_full:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  sc.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  es'.scopes = es.scopes /\
  ghost_kept_at lo cenv es0 sc G0 tn0 s0 G tn /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  ?j G' tn'.
    ghost_kept_at lo cenv es0 sc G0 tn0 s0 G' tn' /\
    t = revert_state (set_returndata [] (s with vs_vars := t.vs_vars)) /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
         (Abort Revert_abort (t with vs_inst_idx := j),G',tn') /\
        (ghost_inv_at D lo d cenv cx es G tn s ==>
         ghost_inv_at D lo d cenv cx es' G' tn' (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all as_wei_value_abort_origin >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  drule_all as_wei_value_abort_runtime_frame >> strip_tac >>
  `!x. not_fresh_at sc x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> first_x_assum irule >>
     metis_tac[not_fresh_at_mono]) >>
  qexistsl_tac [`s.vs_inst_idx + 5`, `G'`, `tn'`] >> simp[] >> conj_tac
  >- (fs[bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
  gen_tac >> strip_tac >> irule ghost_inv_at_exterior_frame >>
  goal_assum (drule_at Any) >> qexists_tac `sc` >> simp[] >>
  qpat_x_assum `t = revert_state _` SUBST1_TAC >>
  fs[revert_state_def, set_returndata_def, lookup_var_def]
QED
