(* Concrete C3/C4 segments under cut-local safety. *)
Theory gasFocusFmpCutSegments
Ancestors
  gasFocusFmpDallocaRun gasFocusFmpDallocaSaved gasFocusFmpDallocaActive
  fmpStageFmpStepsDallocaShared fmpStageFmpStepsDallocaExec
  fmpStageFmpStepsInvokePosition lowerDloadPtrRawReachable
  fmpLowerSequenceExec fmpStageRel o1PassContract unitShapeDefs
  venomState venomInst venomExecProofs finite_map words list

Theorem focus_fmp_cut_dalloca_segment:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  wf_function fn /\ ssa_form fn /\ make_ssa_input_ok fn /\
  fn.fn_fmp_signature = NONE /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~s.vs_halted /\ inst.inst_opcode = DALLOCA /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1 t1 sm1 sz fn' bb' code tail op out runner plus31 mask aligned ai ni mi bi.
    r = OK s1 /\ inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
    eval_operand op s = SOME sz /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    DROP t.vs_inst_idx bb'.bb_instructions = code ++ tail /\
    code = [mk_inst ai ADD [op;Lit 31w] [plus31];
            mk_inst ni NOT [Lit 31w] [mask];
            mk_inst mi AND [Var plus31;Var mask] [aligned];
            mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] /\
    (!k'. fmp_target_run k' C' fn.fn_name t 4 t1) /\
    let z = venomLayout$ceil32 (w2n sz) in
      sm1 = (if z = 0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) /\
      fmp_stage_rel D C' sm1 fmp0 raw0 eom F stk PG
        (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
        (s1 with vs_inst_idx := SUC s.vs_inst_idx) (lo+z) t1 ts
Proof
  strip_tac >>
  drule_all frame_reachable_raw_certificate >> strip_tac >>
  `dalloca_no_wrap inst s` by metis_tac[] >>
  drule_all fmp_dalloca_source >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        s.vs_inst_idx < LENGTH bb.bb_instructions /\
        EL s.vs_inst_idx bb.bb_instructions = inst` by
    (drule_all o1_ctx_shape_active_lookup >>
     simp[get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >>
     qexists `bb` >> simp[] >> metis_tac[MEM_EL]) >>
  `!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `retpc_use_ok inst v` by metis_tac[opaque_use_ok_def] >>
     gvs[retpc_use_ok_def] >> gvs[opaque_use_ok_def, retpc_use_ok_def]) >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_stage_rel_def]) >>
  qpat_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [fmp_frame_rel_def, LET_THM]) >>
  drule_all fmp_dalloca_lowered_needs >> strip_tac >>
  drule_all fmp_stage_root_exists >> strip_tac >>
  `~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp)` by
    metis_tac[fmp_dalloca_not_before_root] >>
  qpat_x_assum `s.vs_current_bb = t.vs_current_bb` (assume_tac o SYM) >>
  qpat_x_assum `(case fmp_stage_root infos ctx fn of NONE => _ | SOME _ => _)` mp_tac >>
  simp[] >> strip_tac >>
  `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
     (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
     (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
      then 1 else 0)` by
    (qpat_x_assum `t.vs_inst_idx = _` mp_tac >> simp[] >> decide_tac) >>
  `step_inst k C inst s = OK s1` by simp[] >>
  drule_all focus_fmp_dalloca_restored_run >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `op = size_op /\ out' = out /\ sz' = sz` by gvs[] >>
  qpat_x_assum `op = size_op` SUBST_ALL_TAC >>
  qpat_x_assum `out' = out` SUBST_ALL_TAC >>
  qpat_x_assum `sz' = sz` SUBST_ALL_TAC >>
  `raw0 <= w2n s.vs_fmp /\ fmp0 <= lo` by fs[fmp_frontier_rel_def] >>
  qabbrev_tac `sm1 = if venomLayout$ceil32 (w2n sz) = 0 then sm else
      sm |+ ((w2n s.vs_fmp,venomLayout$ceil32 (w2n sz)),(lo,inst.inst_id))` >>
  `sm1 = (if venomLayout$ceil32 (w2n sz) = 0 then sm else
      sm |+ ((w2n s.vs_fmp,venomLayout$ceil32 (w2n sz)),(lo,inst.inst_id)))` by simp[Abbr `sm1`] >>
  `fmp_saved_rel C' sm1 fmp0 raw0 stk ts` by
    (simp[Abbr `sm1`] >> irule focus_fmp_dalloca_saved_upto >> metis_tac[]) >>
  `fmp_sites_ok sm1 fmp0 raw0 (lo+venomLayout$ceil32 (w2n sz)) s1.vs_fmp /\
   ld_memory_agree (fmp_ld_sites sm1) eom
     (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
   ld_shared_agree D s1.vs_call_ctx.cc_address (step_taint inst s s1 tn)
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1 /\
   s1.vs_returndata = t1.vs_returndata /\ s1.vs_halted = t1.vs_halted` by
    (drule fmp_dalloca_shared >> disch_then irule >>
     ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (qexists `size_op` >> first_assum ACCEPT_TAC)) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`aligned`,`t.vs_inst_idx+4`,`mask`,`out`,`plus31`,`runner`,`sz`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `fmp_frame_rel sm1 fmp0 raw0 (fmp_frame_base raw0 stk)
     (fmp_frame_lo fmp0 ts) (lo+venomLayout$ceil32 (w2n sz)) F fn fn' PG
     (step_prov PG G inst s1) (step_taint inst s s1 tn).t_var
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1` by
    (drule_at (Pat `fmp_frame_rel _ _ _ _ _ _ T _ _ _ _ _ _ _`)
       focus_fmp_dalloca_active_upto >>
     disch_then (drule_at (Pat `fmp_stage_lowered _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `fmp_ledger_ok _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
     disch_then (drule_at (Pat `gas_cut _ _ _`)) >>
     disch_then (drule_at (Pat `df_at NONE _ _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `fmp_stage_root _ _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `_ = (update_var _ _ _) with vs_inst_idx := _`)) >>
     disch_then irule >>
     qpat_assum `raw0 = w2n vs.vs_fmp` SUBST1_TAC >>
     rpt conj_tac >>> NTH_GOAL (simp[]) 13 >>> NTH_GOAL (simp[]) 14 >>> NTH_GOAL (gvs[]) 24 >> first_assum ACCEPT_TAC) >>
  `fmp_stage_rel D C' sm1 fmp0 raw0 eom F stk PG
     (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
     (s1 with vs_inst_idx := SUC s.vs_inst_idx)
     (lo+venomLayout$ceil32 (w2n sz)) t1 ts` by
    (rewrite_tac[fmp_stage_rel_def,venom_state_accfupds] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists `fn'` >> conj_tac >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`t1`,`bb'`,`tail`,`runner`,`plus31`,`mask`,`aligned`,
    `ai`,`ni`,`mi`,`bi`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `DROP t.vs_inst_idx _ = _` mp_tac >>
     qpat_assum `t.vs_inst_idx = fmp_stage_tidx _ _ _ bb.bb_instructions _ + _`
       SUBST1_TAC >>
     qpat_assum `fmp_stage_root _ _ _ = SOME _` SUBST1_TAC >>
     simp[NoAsms]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `fmp_stage_rel _ _ sm1 _ _ _ F _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `raw0 = _` SUBST1_TAC >>
  qpat_assum `s1 = update_var _ _ _` SUBST1_TAC >>
  simp[NoAsms]
QED
