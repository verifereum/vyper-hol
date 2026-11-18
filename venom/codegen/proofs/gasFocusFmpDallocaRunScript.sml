(* Execute the DALLOCA expansion at the restored point of a fixed lowering. *)
Theory gasFocusFmpDallocaRun
Ancestors
  fmpStageFmpStepsDallocaExec fmpStageFmpStepsDallocaCode
  fmpStageFmpStepsInvokePosition fmpStageFmpStepsLive fmpStageControl fmpStageRel
  fmpLowerSequenceExec fmpStepSupply fmpLowerDefs
  ptrStaticDiscipline ptrDiscipline o1PassContract o1LowerDloadRelocationKernel
  livenessProofs venomWfProps cfgWf cfgHelpers
  venomExecSemantics venomInst venomState passSimulationDefs
  finite_map pred_set words list rich_list

Theorem focus_fmp_dalloca_restored_run:
  wf_function fn /\ make_ssa_input_ok fn /\ fn.fn_fmp_signature = NONE /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL s.vs_inst_idx bb.bb_instructions = inst /\ inst.inst_opcode = DALLOCA /\
  ~s.vs_halted /\ dalloca_no_wrap inst s /\ step_inst k C inst s = OK s1 /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\
  (!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v) /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
    (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
     then 1 else 0) /\
  lookup_var runner t = SOME (n2w lo) /\
  fmp_frontier_rel fmp0 raw0 lo s.vs_fmp /\ s.vs_labels = t.vs_labels /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tn.t_var s t ==>
  ?op out sz plus31 mask aligned ai ni mi bi bb' tail t1.
    inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
    eval_operand op s = SOME sz /\ eval_operand op t = SOME sz /\
    let z = ceil32 (w2n sz) in
      s1 = update_var out s.vs_fmp (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
      w2n s.vs_fmp+z < dimword (:256) /\ lo+z < dimword (:256) /\
      fmp_frontier_rel fmp0 raw0 (lo+z) s1.vs_fmp /\
      lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' /\
      DROP t.vs_inst_idx bb'.bb_instructions =
        [mk_inst ai ADD [op;Lit 31w] [plus31];
         mk_inst ni NOT [Lit 31w] [mask];
         mk_inst mi AND [Var plus31;Var mask] [aligned];
         mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] ++ tail /\
      ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
      EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned;runner] /\
      (!k'. fmp_target_run k' C' fn.fn_name t 4 t1) /\
      t1 = (update_var runner (n2w (lo+z))
        (update_var out (n2w lo) (update_var aligned (n2w z)
         (update_var mask (~31w) (update_var plus31 (sz+31w) t)))))
        with vs_inst_idx := t.vs_inst_idx+4 /\
      t.vs_inst_idx+4 = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
        (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions
        (SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `terminates (OK s1)` by simp[terminates_def] >>
  drule_all fmp_dalloca_source >> strip_tac >>
  rename1 `eval_operand size_op s = SOME sz` >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    (fs[lookup_block_def] >> drule FIND_MEM >> drule FIND_P >> simp[]) >>
  `eval_operand size_op t = SOME sz` by
    (`MEM size_op inst.inst_operands` by simp[] >>
     drule_all fmp_dalloca_operand_untainted >> strip_tac >>
     drule_all fmp_dalloca_operand_noprov >> strip_tac >>
     Cases_on `size_op` >> gvs[eval_operand_def, op_prov_def, op_taint_def] >>
     rename1 `lookup_var v s = SOME sz` >>
     `fn_reachable fn s.vs_current_bb` by
       (fs[make_ssa_input_ok_def, all_reachable_def] >> metis_tac[]) >>
     `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
       metis_tac[fn_reachable_in_cfg_dfs_pre] >>
     `MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)` by
       (drule live_vars_at_uses >> simp[] >>
        disch_then irule >> goal_assum (drule_at Any) >>
        simp[operand_var_in_inst_uses, fn_reachable_in_cfg_dfs_pre]) >>
     qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
     simp[fmp_env_rel_def, lookup_var_def] >>
     disch_then (qspec_then `v` mp_tac) >>
     gvs[lookup_var_def, op_taint_def] >> strip_tac >>
     gvs[fmp_value_rel_def, ld_value_agree_def, word_agree_except_bits] >>
     simp[fcpTheory.CART_EQ]) >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  drule_all fmp_dalloca_lowered_needs >> strip_tac >>
  drule_all fmp_stage_root_exists >> strip_tac >>
  `~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp)` by
    metis_tac[fmp_dalloca_not_before_root] >>
  `~MEM runner (fn_ir_vars fn)` by metis_tac[fmp_stage_runner_fresh] >>
  `MEM out (fn_ir_vars fn)` by
    (simp[fn_ir_vars_member] >> qexistsl [`bb`, `inst`] >>
     simp[] >> metis_tac[MEM_EL]) >>
  `runner <> out` by metis_tac[] >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
     bb.bb_label = rl ==> rp <= s.vs_inst_idx` by (rpt strip_tac >> gvs[] >> decide_tac) >>
  drule fmp_stage_tidx_code >>
  disch_then (qspecl_then [`s.vs_inst_idx`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ])) >> strip_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions = inst::DROP (SUC s.vs_inst_idx) bb.bb_instructions`
    by metis_tac[DROP_CONS_EL] >>
  `?plus31 mask aligned ai ni mi bi tail.
     DROP (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
           then 1 else 0) code =
       [mk_inst ai ADD [size_op;Lit 31w] [plus31];
        mk_inst ni NOT [Lit 31w] [mask];
        mk_inst mi AND [Var plus31;Var mask] [aligned];
        mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] ++ tail /\
     ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
     ~MEM plus31 (fn_ir_vars fn) /\ ~MEM mask (fn_ir_vars fn) /\
     ~MEM aligned (fn_ir_vars fn)` by
    (irule fmp_dalloca_indexed_suffix >> simp[] >>
     qexistsl [`ctx`, `infos`, `inst`, `DROP (SUC s.vs_inst_idx) bb.bb_instructions`,
               `leftover`, `restores`, `sp`, `sp'`] >> gvs[]) >>
  drule_all (cj 2 dalloca_relocate_exec) >> strip_tac >>
  drule_all (cj 3 dalloca_relocate_exec) >> strip_tac >>
  drule_all (cj 4 dalloca_relocate_exec) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `DROP _ code = seq ++ tail` >>
  `DROP t.vs_inst_idx bb'.bb_instructions = seq ++ tail` by
    (qpat_x_assum `DROP _ code = _` mp_tac >>
     qpat_x_assum `DROP _ bb'.bb_instructions = code` (SUBST_ALL_TAC o SYM) >>
     simp[DROP_DROP_T]) >>
  `t.vs_inst_idx+4 = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
     (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions
     (SUC s.vs_inst_idx)` by
    (`(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = DALLOCA` by simp[] >>
     drule_all fmp_dalloca_control_advance >> simp[]) >>
  qabbrev_tac `u = update_var runner (n2w (lo+ceil32 (w2n sz)))
      (update_var out (n2w lo) (update_var aligned (n2w (ceil32 (w2n sz)))
       (update_var mask (~31w) (update_var plus31 (sz+31w) t))))` >>
  `!k'. fmp_target_run k' C' fn.fn_name t 4
          (u with vs_inst_idx := t.vs_inst_idx+4)` by
    (gen_tac >> irule fmp_dalloca_target_run >> simp[] >>
     qexistsl [`bb'`, `seq`, `tail`] >> gvs[Abbr `seq`, Abbr `u`]) >>
  qexistsl [`size_op`, `out`, `sz`, `plus31`, `mask`, `aligned`,
    `ai`, `ni`, `mi`, `bi`, `bb'`, `tail`, `u with vs_inst_idx := t.vs_inst_idx+4`] >>
  gvs[Abbr `seq`, Abbr `u`, update_var_def]
QED
