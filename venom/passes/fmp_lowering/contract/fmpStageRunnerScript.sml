(*
 * FmpLowering's stage simulation: every terminating run of the raw input
 * context C, started at its own free-memory pointer fmp, is matched by a
 * run of the lowered context C' from the real state, up to the dead bytes
 * D.  The raw run never reclaims and places its dynamic allocations from
 * fmp up; the lowered run threads a runner through BUMP and INVOKE and
 * reclaims at the restores.  Row 3's pointer facts (o1_static_inv) keep
 * DALLOCA pointers to address uses within their site, so the relocation
 * is not observable; fmp_variant_room puts the real initial fmp between
 * the static layout's end and fmp.
 *
 * The proof is one induction on fuel (fmp_runner_sim) of two facts at
 * once: the INVOKE step (fmp_invoke_sim) and a block run entered at a
 * related point.  A block run takes fmp_stage_block_sim's result and,
 * after a jump, the next block's run; an INVOKE takes
 * fmp_stage_invoke_call, the callee's run and fmp_stage_invoke_return.
 * fmp_stage_entry starts the context entry's run past its root.
 *
 * fmp_stage_invoke_sim is the INVOKE case of the same simulation (the
 * step_inst half of fmp_runner_sim's induction), exported on its own because the coverage
 * proof (fmpStageCoverage) closes its invariant over INVOKE steps.
 *
 * TOP-LEVEL:
 *   fmp_lowering_stage_sim
 *   fmp_stage_invoke_sim
 *)
Theory fmpStageRunner
Ancestors
  o1PassContract venomPassSchedule venomCompilerTypes fmpStageRel
  fmpStageRunnerFacts fmpStageFmpSteps fmpStageOpSteps fmpStageBlockSim
  fmpStageBlockSimCode
  fmpStageOpBase o1LowerDloadSourceEntry o1PassLift runInstsProps
  dftGasToListReachBoundary ctxLookupAgreeHelpers ptrDiscipline
  contextCodegenRel passSimulationDefs venomExecProofs venomExecSemantics
  unitTransformDefs venomState venomInst venomWf list

(* The step lemmas name the relation's fmp0 and raw0 by equations; unwind
   them so drule_all matches the relation as the runner states it. *)
fun unw th = SIMP_RULE bool_ss [] (GEN_ALL th);

Theorem run_blocks_zero[local]:
  run_blocks 0 C fn s = Error "out of fuel"
Proof
  simp[Once run_blocks_def]
QED

Theorem fmp_stage_ctx_live[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom ==>
  ~vs.vs_halted /\ ?names. callee_first names C.ctx_functions
Proof
  simp[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def] >>
  strip_tac >> gvs[o1_inv_def] >> metis_tac[]
QED

Theorem fmp_stage_ctx_fn[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  lookup_function nm C.ctx_functions = SOME g ==>
  o1_fn_shape C g
Proof
  simp[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM] >>
  metis_tac[venomInstTheory.lookup_function_MEM]
QED

Theorem fmp_target_wf[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom b stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  wf_function fn /\ ALL_DISTINCT (fn_labels fn')
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn` by fs[o1_fn_shape_def] >>
  drule fmp_stage_rel_lowered >> strip_tac >> gvs[] >>
  drule_all fmp_stage_lowered_shape >> gvs[wf_function_def]
QED

Theorem fmp_invoke_zero[local]:
  inst.inst_opcode = INVOKE ==> ~terminates (step_inst 0 C inst s)
Proof
  strip_tac >>
  `!r. step_inst 0 C inst s = r ==> ?e. r = Error e` suffices_by
    (disch_then (qspec_then `step_inst 0 C inst s` mp_tac) >>
     simp[] >> strip_tac >> simp[terminates_def]) >>
  simp[Once step_inst_def, run_blocks_zero, AllCaseEqs()] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >> simp[] >>
  Cases_on `eval_operands x1 s` >> simp[] >>
  qmatch_goalsub_rename_tac `setup_callee cf args s` >>
  Cases_on `setup_callee cf args s` >> simp[]
QED

Theorem fmp_result_shape[local]:
  fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r r' ==>
  terminates r' /\ ((?se. r = OK se) <=> (?te. r' = OK te)) /\
  !se te. r = OK se /\ r' = OK te ==> ~se.vs_halted /\ ~te.vs_halted
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[fmp_stage_result_def, dead_result_rel_def, terminates_def] >>
  rw[] >> gvs[]
QED

Theorem fmp_run_blocks_entered[local]:
  enters_block fn s0 s1 ==>
  s1.vs_current_bb = s0.vs_current_bb /\
  ?bb. lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    !k C. run_blocks (SUC k) C fn s0 =
      case exec_block k C bb s1 of
        OK s' => if s'.vs_halted then Halt s' else run_blocks k C fn s'
      | IntRet v s' => IntRet v s'
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | Error e => Error e
Proof
  rw[enters_block_def]
  >- (imp_res_tac eval_phis_preserves_current_bb >> simp[]) >>
  qexists_tac `bb` >> rw[] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >>
  simp[] >> CASE_TAC >> simp[]
QED

Theorem fmp_fuel_max[local]:
  exec_block k1 C' bb t = OK te /\ terminates (run_blocks k2 C' fn te) ==>
  exec_block (MAX k1 k2) C' bb t = OK te /\
  run_blocks (MAX k1 k2) C' fn te = run_blocks k2 C' fn te
Proof
  strip_tac >> conj_tac
  >- (`exec_block (MAX k1 k2) C' bb t = exec_block k1 C' bb t`
        suffices_by simp[] >>
      irule exec_block_terminates_mono >>
      simp[terminates_def, arithmeticTheory.MAX_DEF]) >>
  irule run_blocks_terminates_mono >> simp[arithmeticTheory.MAX_DEF]
QED

(* Why: the OK case of a block run is a jump (fmp_stage_jump_step); its
   block entry keeps the relation (fmp_stage_block_entry), and the next
   block run starts there, at a related point after the target's PHIs. *)
Theorem fmp_runner_jump[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_result D C C' vs (w2n vs'.vs_initial_fmp) (w2n fmp) eom
    stk PG fn ts (OK se) (OK te) /\
  terminates (run_blocks k C fn se) ==>
  ?ns1 ninst nG ntn nsm nlo nt1 nbb.
    enters_block fn se ns1 /\ active_inst fn ninst ns1 /\
    frame_reachable vs C stk PG nG ntn fn ninst ns1 /\
    fmp_stage_rel D C' nsm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      stk PG nG ntn fn ns1 nlo nt1 ts /\
    enters_block fn' te nt1 /\
    lookup_block te.vs_current_bb fn'.fn_blocks = SOME nbb /\
    nt1.vs_current_bb = te.vs_current_bb
Proof
  simp[Once fmp_stage_result_def] >> strip_tac >> gvs[] >>
  `~vs.vs_halted` by metis_tac[fmp_stage_ctx_live] >>
  `~sb.vs_halted` by metis_tac[fmp_frame_reachable_not_halted] >>
  `terminates (step_inst kb C bi sb)` by simp[terminates_def] >>
  `MEM bi.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  drule_all (unw fmp_stage_jump_step) >> strip_tac >> gvs[] >>
  `wf_function fn /\ ALL_DISTINCT (fn_labels fn')` by
    metis_tac[fmp_target_wf] >>
  `inst' = bi'` by metis_tac[active_inst_unique] >> gvs[] >>
  `is_terminator bi.inst_opcode` by simp[is_terminator_def] >>
  `~(jump_to lbl sb).vs_halted` by simp[jump_to_def] >>
  drule_all ld_terminating_run_entry >> strip_tac >>
  `MEM bi.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  drule_all (unw fmp_stage_block_entry) >> strip_tac >>
  `frame_reachable vs C stk PG (entry_prov fn (jump_to lbl sb) G)
     (entry_taint_vars fn (jump_to lbl sb) tn) fn i s1` by
    (irule frame_reachable_block >> metis_tac[]) >>
  qpat_assum `enters_block fn' _ _`
    (strip_assume_tac o MATCH_MP fmp_run_blocks_entered) >>
  metis_tac[]
QED

(* Why: the INVOKE's callee entry is related (fmp_stage_invoke_call); the
   callee is never the context entry (fmp_invoke_not_entry), and a
   terminating callee run enters its first block. *)
Theorem fmp_runner_call[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ ~s.vs_halted /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  terminates (run_blocks k C callee cs) /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ivk' t ==>
  ?cs1 cinst ops' callee' args' cs' ct1 cbb.
    enters_block callee cs cs1 /\ active_inst callee cinst cs1 /\
    frame_reachable vs C
      (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
          cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee cinst cs1 /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
          cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee cs1
      lo ct1 ((t,lo)::ts) /\
    ivk'.inst_opcode = INVOKE /\ decode_invoke ivk' = SOME (nm,ops') /\
    lookup_function nm C'.ctx_functions = SOME callee' /\
    lookup_function callee.fn_name C'.ctx_functions = SOME callee' /\
    eval_operands ops' t = SOME args' /\
    setup_callee callee' args' t = SOME cs' /\
    enters_block callee' cs' ct1 /\
    lookup_block cs'.vs_current_bb callee'.fn_blocks = SOME cbb /\
    ct1.vs_current_bb = cs'.vs_current_bb
Proof
  strip_tac >>
  `~cs.vs_halted` by metis_tac[ld_setup_callee_not_halted] >>
  `wf_function callee` by metis_tac[fmp_stage_ctx_fn, o1_fn_shape_def] >>
  drule_all ld_terminating_run_entry >> strip_tac >>
  `?names. callee_first names C.ctx_functions` by
    metis_tac[fmp_stage_ctx_live] >>
  `C.ctx_entry <> SOME nm` by metis_tac[fmp_invoke_not_entry] >>
  drule_all (unw fmp_stage_invoke_call) >> strip_tac >>
  `callee.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  `frame_reachable vs C
     (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
         cf_prov := G; cf_tvar := tn.t_var |> :: stk)
     (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee i s1` by
    (irule frame_reachable_call >> metis_tac[]) >>
  qpat_assum `enters_block callee' _ _`
    (strip_assume_tac o MATCH_MP fmp_run_blocks_entered) >>
  gvs[] >> metis_tac[]
QED

(* Why: the callee's return is related (fmp_stage_invoke_return), at the
   RET the callee's result names; the caller resumes at the next
   instruction of its block, and frame_reachable's ret rule reaches it. *)
Theorem fmp_runner_return[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ivk.inst_opcode = INVOKE /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ivk' t /\
  lookup_function callee.fn_name C'.ctx_functions = SOME callee' /\
  fmp_stage_result D C C' vs (w2n vs'.vs_initial_fmp) (w2n fmp) eom
    (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
        cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    (MAP (op_prov G) ops) callee ((t,lo)::ts) (IntRet ret se) cr' /\
  bind_outputs ivk.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME s1 ==>
  ?ret' te t1 tn1 next sm1.
    cr' = IntRet ret' te /\
    bind_outputs ivk'.inst_outputs ret'.iret_values
      (adopt_return_fmp ret' (merge_callee_state t te)) = SOME t1 /\
    active_inst fn next (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    frame_reachable vs C stk PG (DRESTRICT G (COMPL (set ivk.inst_outputs)))
      tn1 fn next (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    fmp_stage_rel D C' sm1 (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      stk PG (DRESTRICT G (COMPL (set ivk.inst_outputs))) tn1 fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
Proof
  simp[Once fmp_stage_result_def] >> strip_tac >> gvs[] >>
  `~vs.vs_halted` by metis_tac[fmp_stage_ctx_live] >>
  `~se.vs_halted` by metis_tac[fmp_frame_reachable_not_halted] >>
  `wf_function fn /\ ALL_DISTINCT (fn_labels fn')` by
    metis_tac[fmp_target_wf] >>
  `s1.vs_current_bb = s.vs_current_bb` by metis_tac[fmp_return_current_bb] >>
  `~is_terminator ivk.inst_opcode` by simp[is_terminator_def] >>
  drule_all fmp_active_next >> strip_tac >>
  `frame_reachable vs C stk PG (DRESTRICT G (COMPL (set ivk.inst_outputs)))
     (tn' with t_var := DRESTRICT tn.t_var (COMPL (set ivk.inst_outputs)))
     fn next (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (mp_tac (Q.SPECL [`vs`, `C`,
       `<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
           cf_prov := G; cf_tvar := tn.t_var |>`] frame_reachable_ret) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  drule_all (fmp_stage_invoke_return
    |> Q.INST [`f` |->
         `<| cf_fn := fc0; cf_inst := ic0; cf_state := sc0;
             cf_params := pc0; cf_prov := gc0; cf_tvar := vc0 |>`]
    |> GEN_ALL |> SIMP_RULE (srw_ss()) []) >>
  strip_tac >> gvs[] >>
  `ivk'' = ivk'` by metis_tac[active_inst_unique] >> gvs[] >>
  metis_tac[]
QED

Theorem fmp_runner_sim[local]:
  !k.
    (!ivk s. fmp_invoke_sim rpolicy D C C' vs vs' fmp eom k ivk s) /\
    !fn s0 s1 inst stk PG G tn sm lo t0 tp t1 ts fn' bb'.
      fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
      enters_block fn s0 s1 /\ active_inst fn inst s1 /\
      frame_reachable vs C stk PG G tn fn inst s1 /\
      fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
        stk PG G tn fn s1 lo t1 ts /\
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      enters_block fn' t0 tp /\
      lookup_block t0.vs_current_bb fn'.fn_blocks = SOME bb' /\
      t1.vs_current_bb = t0.vs_current_bb /\
      (!m. exec_block m C' bb' tp = exec_block m C' bb' t1) /\
      terminates (run_blocks k C fn s0) ==>
      ?m. fmp_stage_result D C C' vs (w2n vs'.vs_initial_fmp) (w2n fmp) eom
            stk PG fn ts (run_blocks k C fn s0) (run_blocks m C' fn' t0)
Proof
  Induct
  >- (conj_tac
      >- (simp[fmp_invoke_sim_def] >> rpt strip_tac >>
          gvs[] >> metis_tac[fmp_invoke_zero]) >>
      simp[run_blocks_zero, terminates_def]) >>
  pop_assum strip_assume_tac >>
  conj_asm2_tac
  >- (simp[fmp_invoke_sim_def] >> rpt strip_tac >>
      `~vs.vs_halted` by metis_tac[fmp_stage_ctx_live] >>
      drule_all (unw ld_terminating_invoke_inversion) >>
      disch_then (qx_choosel_then [`nm`, `ops`, `callee`, `args`, `cs`]
        strip_assume_tac) >>
      drule_all fmp_runner_call >> strip_tac >> gvs[] >>
      qpat_x_assum
        `!fn s0 s1 inst stk PG G tn sm lo t0 tp t1 ts fn' bb'.
           _ ==> ?m. _ (run_blocks (SUC k) C fn s0) _`
        (qspecl_then [`callee`, `cs`, `cs1`, `cinst`,
           `<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
               cf_prov := G; cf_tvar := tn.t_var |> :: stk`,
           `MAP (op_prov G) ops`, `FEMPTY`, `tn with t_var := FEMPTY`,
           `sm`, `lo`, `cs'`, `ct1`, `ct1`, `(t,lo)::ts`, `callee'`, `cbb`]
          mp_tac) >>
      simp[] >> strip_tac >> gvs[]
      >~ [`run_blocks _ _ _ _ = IntRet _ _`]
      >- (drule_all fmp_runner_return >> strip_tac >>
          qexists_tac `m` >>
          `step_inst m C' inv' t = OK t1` by simp[Once step_inst_def] >>
          simp[] >> metis_tac[]) >>
      qpat_x_assum `fmp_stage_result _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      Cases_on `run_blocks m C' callee' cs'` >>
      simp[fmp_stage_result_def, dead_result_rel_def] >> strip_tac >>
      qexists_tac `m` >> simp[Once step_inst_def, dead_result_rel_def]) >>
  rpt strip_tac >>
  `~vs.vs_halted` by metis_tac[fmp_stage_ctx_live] >>
  `~s1.vs_halted` by metis_tac[fmp_frame_reachable_not_halted] >>
  qpat_assum `enters_block fn s0 s1`
    (strip_assume_tac o MATCH_MP fmp_run_blocks_entered) >>
  qpat_assum `enters_block fn' t0 tp`
    (strip_assume_tac o MATCH_MP fmp_run_blocks_entered) >>
  gvs[] >>
  `terminates (exec_block k C bb s1)` by
    (Cases_on `exec_block k C bb s1` >> gvs[terminates_def]) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by gvs[] >>
  drule_all (unw fmp_stage_block_sim) >> strip_tac >> gvs[] >>
  drule fmp_result_shape >> strip_tac >>
  Cases_on `exec_block k C bb s1` >> gvs[terminates_def]
  >~ [`exec_block k C bb s1 = OK se`]
  >- (`?te. exec_block k' C' bb' t1 = OK te` by metis_tac[] >>
      `~se.vs_halted /\ ~te.vs_halted` by metis_tac[] >> gvs[] >>
      `terminates (run_blocks k C fn se)` by fs[terminates_def] >>
      drule_all fmp_runner_jump >> strip_tac >>
      first_x_assum (qspecl_then [`fn`, `se`, `ns1`, `ninst`, `stk`, `PG`,
        `nG`, `ntn`, `nsm`, `nlo`, `te`, `nt1`, `nt1`, `ts`, `fn'`, `nbb`]
        mp_tac) >>
      impl_tac >- fs[] >> strip_tac >>
      qpat_assum `fmp_stage_result _ _ _ _ _ _ _ _ _ _ _ (run_blocks _ _ _ _) _`
        (strip_assume_tac o MATCH_MP fmp_result_shape) >>
      drule_all fmp_fuel_max >> strip_tac >>
      qexists_tac `SUC (MAX k' m)` >> simp[]) >>
  qexists_tac `SUC k'` >> simp[] >>
  Cases_on `exec_block k' C' bb' t1` >> gvs[]
QED

(* Why: the target's root is a straight-line prefix of its entry block
   (fmp_run_insts_straight), so its block run from the start is the run
   from past the root. *)
Theorem fmp_root_skip[local]:
  (!k. fmp_target_run k C' name t0 n t1) /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  lookup_block t0.vs_current_bb fn'.fn_blocks = SOME bb /\
  t0.vs_inst_idx = 0 /\ t0.vs_prev_bb = NONE /\ t1.vs_prev_bb = NONE ==>
  !m. exec_block m C' bb t0 = exec_block m C' bb t1
Proof
  strip_tac >>
  `?u0. run_insts 0 C' (TAKE n bb.bb_instructions) t0 = OK u0 /\
        u0.vs_prev_bb = NONE /\ n <= LENGTH bb.bb_instructions` by
    (first_assum (strip_assume_tac o
       SIMP_RULE std_ss [fmp_target_run_def] o Q.SPEC `0`) >> gvs[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
     (TAKE n bb.bb_instructions)` by metis_tac[fmp_run_insts_straight] >>
  gen_tac >>
  `?u. run_insts m C' (TAKE n bb.bb_instructions) t0 = OK u /\
       t1 = u with vs_inst_idx := n` by
    (first_assum (strip_assume_tac o
       SIMP_RULE std_ss [fmp_target_run_def] o Q.SPEC `m`) >> gvs[]) >>
  qspecl_then [`TAKE n bb.bb_instructions`, `m`, `C'`, `bb`, `t0`, `0`, `u`]
    mp_tac exec_block_skip_prefix >>
  `t0 with vs_inst_idx := 0 = t0` by
    simp[venom_state_component_equality] >>
  simp[EL_TAKE, LENGTH_TAKE]
QED

(* Why: the context entry's first block has no PHIs, the root is skipped
   (fmp_root_skip), and the runner relates the entry's run.  A run of the
   entry never returns (entry_fn_no_return), and run_blocks never ends
   OK. *)
Theorem fmp_runner_entry[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  terminates (run_context fuel C vs) ==>
  ?fuel'. dead_result_rel D (run_context fuel C vs) (run_context fuel' C' vs')
Proof
  strip_tac >>
  `?name. C.ctx_entry = SOME name` by
    (Cases_on `C.ctx_entry` >> gvs[run_context_def, terminates_def]) >>
  `?fn. lookup_function name C.ctx_functions = SOME fn` by
    (Cases_on `lookup_function name C.ctx_functions` >>
     gvs[run_context_def, terminates_def]) >>
  `?lbl. fn_entry_label fn = SOME lbl` by
    (Cases_on `fn_entry_label fn` >>
     gvs[run_context_def, run_function_def, terminates_def]) >>
  `o1_fn_shape C fn` by metis_tac[fmp_stage_ctx_fn] >>
  `fn.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  `wf_function fn /\ first_block_no_phi fn /\ entry_fn_no_return fn` by
    gvs[o1_fn_shape_def] >>
  `run_context fuel C vs =
   run_blocks fuel C fn
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>)` by
    simp[run_context_def, run_function_def] >>
  `~vs.vs_halted` by metis_tac[fmp_stage_ctx_live] >>
  qpat_x_assum `terminates _` mp_tac >> simp[] >> strip_tac >>
  `?i s1. enters_block fn (vs with <| vs_prev_bb := NONE;
             vs_current_bb := lbl; vs_inst_idx := 0 |>) s1 /\
          active_inst fn i s1` by
    (irule ld_terminating_run_entry >> simp[] >> metis_tac[]) >>
  `s1 = vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>` by metis_tac[dload_no_phi_entry] >>
  `frame_reachable vs C [] [] FEMPTY entry_taint fn i s1` by
    (irule frame_reachable_entry >> metis_tac[]) >>
  drule_all (unw fmp_stage_entry) >> strip_tac >>
  drule fmp_stage_rel_lowered >> strip_tac >>
  drule_all fmp_stage_lowered_shape >> strip_tac >>
  `C'.ctx_entry = SOME name` by gvs[fmp_stage_ctx_def, ctx_pass_stage_def] >>
  qabbrev_tac `t0 = vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                                 vs_inst_idx := 0 |>` >>
  `!m. run_context m C' vs' = run_blocks m C' fn' t0` by
    gvs[run_context_def, run_function_def, Abbr `t0`] >>
  `enters_block fn' t0 t0` by
    (simp[Abbr `t0`] >> metis_tac[dload_no_phi_entry]) >>
  `t0.vs_inst_idx = 0 /\ t0.vs_prev_bb = NONE /\ t0.vs_current_bb = lbl` by
    simp[Abbr `t0`] >>
  `t1.vs_prev_bb = NONE /\ t1.vs_current_bb = lbl` by gvs[] >>
  qpat_assum `enters_block fn' _ _`
    (strip_assume_tac o MATCH_MP fmp_run_blocks_entered) >>
  `!m. exec_block m C' bb t0 = exec_block m C' bb t1` by
    (irule fmp_root_skip >> gvs[] >> metis_tac[]) >>
  qspec_then `fuel` (mp_tac o CONJUNCT2) fmp_runner_sim >>
  disch_then (qspecl_then [`fn`, `s1`, `s1`, `i`, `[]`, `[]`, `FEMPTY`,
    `entry_taint`, `FEMPTY`, `w2n vs'.vs_initial_fmp`, `t0`, `t0`, `t1`,
    `[]`, `fn'`, `bb`] mp_tac) >>
  impl_tac >- gvs[] >>
  strip_tac >> qexists_tac `m` >> simp[] >>
  qpat_x_assum `fmp_stage_result _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  Cases_on `run_blocks fuel C fn s1` >>
  gvs[terminates_def, run_blocks_not_OK, fmp_stage_result_def] >>
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  gvs[entry_fn_no_return_def, EVERY_MEM] >> res_tac >> gvs[]
QED

Theorem fmp_lowering_stage_sim:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs' /\
  o1_inv D 3 C (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\
  fmp_variant_room (SOME fmp) C' vs' ==>
  ctx_sim D C C' (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) vs'
Proof
  rpt strip_tac >> simp[ctx_sim_def] >> rpt strip_tac >>
  `?eom. max_live_eom C = SOME eom` by
    (qpat_x_assum `o1_inv D 3 C _` mp_tac >>
     simp[o1_inv_def, o1_static_inv_def] >> metis_tac[]) >>
  irule fmp_runner_entry >> simp[fmp_stage_ctx_def] >> metis_tac[]
QED

Theorem fmp_stage_invoke_sim:
  fmp_invoke_sim rpolicy D C C' vs vs' fmp eom k ivk s
Proof
  simp[fmp_runner_sim]
QED
