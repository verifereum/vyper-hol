(*
 * FmpLowering's stage simulation at block level: the entry into a block
 * after a jump, and one source exec_block from a related point matched by
 * the target's block run.  The INVOKE case is the hypothesis
 * fmp_invoke_sim, which the runner induction (fmpStageRunner) discharges.
 *
 * TOP-LEVEL:
 *   fmp_stage_block_entry - a jump's block entry keeps the relation
 *   fmp_stage_block_sim   - one exec_block, from a point before its restores
 *)
Theory fmpStageBlockSim
Ancestors
  fmpStageOpSteps fmpStageFmpSteps fmpStageRetStep fmpStageBlockSimCode fmpStageControl
  fmpStageOpBase fmpStageRel ptrStaticDiscipline o1PassContract ptrDiscipline
  contextCodegenRel fmpReclaimDefs fmpAnalysisDefs passSimulationDefs
  venomExecProofs venomInstProofs venomStepProps venomWf venomExecSemantics
  venomState venomInst finite_map words list

Theorem fmp_stage_block_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn bi sb /\ active_inst fn bi sb /\
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn sb lo tb ts /\
  step_inst k C bi sb = OK (jump_to lbl sb) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  enters_block fn (jump_to lbl sb) s1 /\ active_inst fn inst s1 ==>
  ?t1. enters_block fn' (jump_to lbl tb) t1 /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
      (entry_prov fn (jump_to lbl sb) G)
      (entry_taint_vars fn (jump_to lbl sb) tn) fn s1 lo t1 ts
Proof
  cheat
QED

(* ===== Glue: one exec_block, block-local facts ===== *)

Theorem lookup_get_active[local]:
  lookup_block st.vs_current_bb f.fn_blocks = SOME b /\
  get_instruction b st.vs_inst_idx = SOME i ==>
  active_inst f i st
Proof
  rw[active_inst_def, get_instruction_def] >> qexists_tac `b` >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >> gvs[]
QED

Theorem fmp_stage_rel_cur[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted
Proof
  simp[fmp_stage_rel_def, fmp_frame_rel_def] >> strip_tac >> gvs[]
QED

Theorem exec_block_not_error_idx[local]:
  !kf ctx b st r. exec_block kf ctx b st = r /\ (!e. r <> Error e) ==>
  st.vs_inst_idx < LENGTH b.bb_instructions
Proof
  rpt gen_tac >> CCONTR_TAC >> gvs[] >>
  qpat_x_assum `!e. _` mp_tac >>
  gvs[Once exec_block_def, get_instruction_def]
QED

Theorem fmp_stage_result_not_error[local]:
  fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r r' ==>
  !e. r' <> Error e
Proof
  Cases_on `r` >> simp[fmp_stage_result_def, dead_result_rel_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `r'` >> gvs[]
QED

(* Source: a non-terminator's OK step continues the block. *)
Theorem exec_block_source_step[local]:
  get_instruction b st.vs_inst_idx = SOME i /\ ~is_terminator i.inst_opcode /\
  step_inst kf ctx i st = OK st1 ==>
  exec_block kf ctx b st =
  exec_block kf ctx b (st1 with vs_inst_idx := SUC st.vs_inst_idx)
Proof
  strip_tac >> gvs[Once exec_block_def]
QED

(* Target: a step followed by the rest of the block, at one fuel. *)
Theorem exec_block_target_step[local]:
  bb_well_formed b /\ get_instruction b st.vs_inst_idx = SOME i /\
  step_inst k1 ctx i st = OK st1 /\ k1 <= kf /\
  exec_block kf ctx b (st1 with vs_inst_idx := SUC st.vs_inst_idx) = r /\
  (!e. r <> Error e) ==>
  exec_block kf ctx b st = r
Proof
  strip_tac >>
  drule_all exec_block_not_error_idx >> simp[] >> strip_tac >>
  `~is_terminator i.inst_opcode` by
    (strip_tac >> gvs[bb_well_formed_def, get_instruction_def] >>
     `st.vs_inst_idx = PRE (LENGTH b.bb_instructions)` by
       (first_x_assum irule >> gvs[]) >>
     Cases_on `b.bb_instructions` >> gvs[]) >>
  `step_inst kf ctx i st = OK st1` by
    (drule_then (qspec_then `kf` mp_tac)
       (CONJUNCT1 venomExecProofsTheory.fuel_mono) >> simp[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  asm_simp_tac (srw_ss()) []
QED

(* Target: a step that halts or aborts ends the block. *)
Theorem exec_block_target_dead[local]:
  get_instruction b st.vs_inst_idx = SOME i /\
  step_inst k1 ctx i st = r /\ k1 <= kf /\
  ((?x. r = Halt x) \/ (?a x. r = Abort a x)) ==>
  exec_block kf ctx b st = r
Proof
  rpt strip_tac >> gvs[] >>
  drule_then (qspec_then `kf` mp_tac)
    (CONJUNCT1 venomExecProofsTheory.fuel_mono) >>
  simp[] >> strip_tac >> gvs[Once exec_block_def]
QED

(* Target: a straight-line run of non-final instructions. *)
Theorem exec_block_target_run[local]:
  (!k. fmp_target_run k C' name t n t1) /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  EVERY bb_well_formed fn'.fn_blocks /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME b /\
  exec_block kf C' b t1 = r /\ (!e. r <> Error e) ==>
  exec_block kf C' b t = r
Proof
  strip_tac >>
  drule_all exec_block_not_error_idx >> strip_tac >>
  first_x_assum (qspec_then `kf` assume_tac) >>
  `t1.vs_inst_idx = t.vs_inst_idx + n` by gvs[fmp_target_run_def] >>
  drule fmp_target_run_exec_block >> simp[]
QED

Theorem dead_result_stage_result[local]:
  dead_result_rel D r r' ==>
  fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[fmp_stage_result_def, dead_result_rel_def]
QED

Theorem terminates_not_error[local]:
  terminates r ==> !e. r <> Error e
Proof
  Cases_on `r` >> simp[terminates_def]
QED

(* The source's next instruction after a non-terminator's OK step. *)
Theorem source_next_active[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\
  step_inst k C inst s = OK s1 /\ exec_block k C bb s = r /\ terminates r ==>
  ?i2. active_inst fn i2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
       exec_block k C bb (s1 with vs_inst_idx := SUC s.vs_inst_idx) = r /\
       s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted /\
       s.vs_inst_idx < LENGTH bb.bb_instructions
Proof
  strip_tac >>
  `exec_block k C bb (s1 with vs_inst_idx := SUC s.vs_inst_idx) = r` by
    metis_tac[exec_block_source_step] >>
  drule terminates_not_error >> strip_tac >>
  `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qspecl_then [`k`,`C`,`bb`,`s1 with vs_inst_idx := SUC s.vs_inst_idx`,
                  `r`] mp_tac exec_block_not_error_idx >> simp[]) >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
  drule venomStepPropsTheory.step_inst_ok_halted >> strip_tac >>
  simp[] >>
  qexists_tac `EL (SUC s.vs_inst_idx) bb.bb_instructions` >>
  irule lookup_get_active >> qexists_tac `bb` >> simp[get_instruction_def]
QED

(* The induction step: the source goes on at the next index, and the
   target reaches the related state by a fuel-monotone prefix. *)
Theorem fmp_stage_block_succ[local]:
  !s1 t2 K0.
  (!kf q. K0 <= kf /\ exec_block kf C' bb' t2 = q /\ (!e. q <> Error e) ==>
         exec_block kf C' bb' t = q) /\
  (?i2 G2 tn2 sm2 lo2.
     frame_reachable vs C stk PG G2 tn2 fn i2
       (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
     active_inst fn i2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
     fmp_stage_rel D C' sm2 fmp0 raw0 eom F stk PG G2 tn2 fn
       (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo2 t2 ts) /\
  (!s2 t2 sm2 lo2 G2 tn2 i2 r2.
     LENGTH bb.bb_instructions - s2.vs_inst_idx <
       LENGTH bb.bb_instructions - s.vs_inst_idx /\
     frame_reachable vs C stk PG G2 tn2 fn i2 s2 /\ active_inst fn i2 s2 /\
     ~s2.vs_halted /\
     fmp_stage_rel D C' sm2 fmp0 raw0 eom F stk PG G2 tn2 fn s2 lo2 t2 ts /\
     lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
     exec_block k C bb s2 = r2 /\ terminates r2 ==>
     ?bb2. lookup_block t2.vs_current_bb fn'.fn_blocks = SOME bb2 /\
       ?k2 q2. exec_block k2 C' bb2 t2 = q2 /\
       fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r2 q2) /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  s1.vs_current_bb = s.vs_current_bb /\ ~s1.vs_halted /\
  exec_block k C bb (s1 with vs_inst_idx := SUC s.vs_inst_idx) = r /\
  terminates r /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' ==>
  ?k' q. exec_block k' C' bb' t = q /\
         fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r q
Proof
  rpt gen_tac >> strip_tac >>
  last_x_assum (qspecl_then [`s1 with vs_inst_idx := SUC s.vs_inst_idx`,
    `t2`, `sm2`, `lo2`, `G2`, `tn2`, `i2`, `r`] mp_tac) >>
  simp[] >> strip_tac >>
  drule fmp_stage_rel_cur >> strip_tac >> gvs[] >>
  drule fmp_stage_result_not_error >> strip_tac >>
  `exec_block (K0 + k2) C' bb' t2 = exec_block k2 C' bb' t2` by
    (irule (CONJUNCT1 (CONJUNCT2 venomExecProofsTheory.fuel_mono)) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `k2` >> simp[]) >>
  qexists_tac `K0 + k2` >>
  first_x_assum (qspec_then `K0 + k2` mp_tac) >> gvs[]
QED

(* Source: a step that doesn't continue ends the block with its result. *)
Theorem exec_block_source_stop[local]:
  get_instruction b st.vs_inst_idx = SOME i /\
  step_inst kf ctx i st = q /\ (!x. q <> OK x) ==>
  exec_block kf ctx b st = q
Proof
  rpt strip_tac >> Cases_on `q` >> gvs[Once exec_block_def]
QED

(* Target: a dead step ends the block with its result. *)
Theorem exec_block_target_dead_rel[local]:
  get_instruction b st.vs_inst_idx = SOME i /\
  step_inst kf ctx i st = q /\ dead_result_rel D r q ==>
  exec_block kf ctx b st = q
Proof
  rpt strip_tac >> Cases_on `r` >> Cases_on `q` >>
  gvs[dead_result_rel_def, Once exec_block_def]
QED

Theorem ret_step_intret[local]:
  inst.inst_opcode = RET /\ step_inst k C inst s = q /\ terminates q ==>
  ?ir. q = IntRet ir s
Proof
  strip_tac >> gvs[step_inst_non_invoke, Once step_inst_base_def] >>
  gvs[AllCaseEqs(), terminates_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[terminates_def]
QED

(* RETURNDATACOPY is the only non-terminator of a revert forwarding. *)
Theorem revert_forward_rdc[local]:
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode ==>
  inst.inst_opcode = RETURNDATACOPY
Proof
  rw[in_revert_forward_def, revert_forward_at_def, revert_forward_pair_def] >>
  gvs[is_terminator_def]
QED

Theorem jump_stage_result[local]:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ active_inst fn inst s /\
  frame_reachable vs C stk PG G tn fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' inst t /\ ~s.vs_halted /\
  step_inst k C inst s = OK (jump_to lbl s) /\
  step_inst k C' inst t = OK (jump_to lbl t) ==>
  fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts
    (OK (jump_to lbl s)) (OK (jump_to lbl t))
Proof
  strip_tac >> simp[fmp_stage_result_def] >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (drule fmp_stage_rel_cur >> gvs[fmp_stage_rel_def]) >>
  qexistsl_tac [`inst`, `s`, `G`, `tn`, `sm`, `lo`, `t`, `inst`, `k`] >>
  gvs[jump_to_def]
QED

Theorem ret_stage_result[local]:
  inst.inst_opcode = RET /\ active_inst fn inst s /\
  frame_reachable vs C stk PG G tn fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' inst t /\
  step_inst k C inst s = IntRet ir s /\ step_inst k C' inst t = IntRet jr t /\
  jr.iret_values = ir.iret_values /\
  ir.iret_adopt_fmp = NONE /\ jr.iret_adopt_fmp = NONE ==>
  fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts
    (IntRet ir s) (IntRet jr t)
Proof
  strip_tac >> simp[fmp_stage_result_def] >> metis_tac[]
QED

Theorem fmp_stage_block_sim_ind[local]:
  !m s t sm lo G tn inst r.
    m = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
    fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
    (!ivk s2. fmp_invoke_sim rpolicy D C C' vs vs' fmp eom k ivk s2) /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    ~s.vs_halted /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    exec_block k C bb s = r /\ terminates r ==>
    ?bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      ?k' r'. exec_block k' C' bb' t = r' /\
      fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r r'
Proof
  cheat (* step 5 in progress: fuel-exact block_sim *)
QED

Theorem fmp_stage_block_sim:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  (!ivk s2. fmp_invoke_sim rpolicy D C C' vs vs' fmp eom k ivk s2) /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block k C bb s = r /\ terminates r ==>
  ?fn' bb' r'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block k C' bb' t = r' /\
    fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r r'
Proof
  cheat (* step 5 in progress: fuel-exact block_sim *)
QED
