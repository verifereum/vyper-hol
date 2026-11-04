Theory cseHistoryProps
Ancestors passSharedProps venomExecSemantics venomState stateEquiv execEquivProofs
  cfgAnalysisProps analysisSimProps venomInstProps venomExecProps
  venomWf venomInst venomExecProofs list cfgDefs cseCanonProps

(* Local copy transport only: the persistence premise must be established
   for the particular later execution occurrence by a separate argument. *)
Theorem cse_assign_historical_transport:
  !fuel ctx inst src dst s t u v.
    inst.inst_outputs = [dst] /\
    eval_operand src s = SOME v /\
    step_inst fuel ctx (mk_assign_inst inst src) s = OK t /\
    lookup_var dst u = lookup_var dst t ==>
    eval_operand (Var dst) u = eval_operand src s
Proof
  rpt strip_tac >>
  drule_all mk_assign_inst_correct >> strip_tac >> gvs[] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

(* All reads in this certificate use the same pre-batch snapshot s. *)
Definition cse_phi_reads_def:
 (cse_phi_reads s [] writes <=> writes = []) /\
 (cse_phi_reads s (inst::rest) writes <=>
   if inst.inst_opcode <> PHI then writes = []
   else ?out v tail. eval_one_phi s inst = SOME (out,v) /\
     cse_phi_reads s rest tail /\ writes = (out,v)::tail)
End

Theorem cse_phi_reads_nil[simp]:
 !s writes. cse_phi_reads s [] writes <=> writes = []
Proof
 simp[cse_phi_reads_def]
QED

Theorem cse_phi_reads_stop:
 !s inst rest writes. inst.inst_opcode <> PHI ==>
 (cse_phi_reads s (inst::rest) writes <=> writes = [])
Proof
 simp[cse_phi_reads_def]
QED

Theorem cse_phi_reads_cons:
 !s inst rest writes. inst.inst_opcode = PHI ==>
 (cse_phi_reads s (inst::rest) writes <=>
  ?out v tail. eval_one_phi s inst = SOME (out,v) /\
    cse_phi_reads s rest tail /\ writes = (out,v)::tail)
Proof
 simp[cse_phi_reads_def]
QED

Theorem cse_phi_reads_length:
 !insts s writes. cse_phi_reads s insts writes ==>
 LENGTH writes = phi_prefix_length insts
Proof
 Induct >> simp[cse_phi_reads_def, phi_prefix_length_def] >>
 rpt gen_tac >> IF_CASES_TAC >> gvs[] >>
 strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem cse_phi_reads_index:
 !insts s writes k. cse_phi_reads s insts writes /\ k < LENGTH writes ==>
 eval_one_phi s (EL k insts) = SOME (EL k writes) /\
 (EL k insts).inst_opcode = PHI
Proof
 Induct >- simp[] >> rpt gen_tac >>
 simp[cse_phi_reads_def] >> IF_CASES_TAC >- (strip_tac >> gvs[]) >>
 strip_tac >> gvs[] >> Cases_on `k` >> gvs[] >>
 metis_tac[]
QED

Theorem cse_phi_reads_eval_phis:
 !insts s t. eval_phis s insts = OK t <=>
 ?writes. cse_phi_reads s insts writes /\
 t = FOLDR (\(out,v) acc. update_var out v acc) s writes
Proof
 Induct >- (simp[eval_phis_def] >> metis_tac[]) >> rpt gen_tac >>
 simp[Once eval_phis_def, cse_phi_reads_def] >>
 IF_CASES_TAC >- (simp[] >> metis_tac[]) >>
 Cases_on `eval_one_phi s h` >- simp[] >>
 rename1 `eval_one_phi s h = SOME pair` >> PairCases_on `pair` >>
 simp[] >>
 Cases_on `eval_phis s insts` >>
 simp[PULL_EXISTS] >>
 first_x_assum (qspec_then `s` mp_tac) >> simp[] >>
 strip_tac >> metis_tac[]
QED

(* API audit: block_sim_function_pointwise[_reachable] quantifies over arbitrary
   block-input states (the latter only adds a prev_bb guard). analysisSim's
   sound predicates likewise contain no entry-origin ordered history.
   exec_block_decompose extracts states only under a successful whole-block
   run and does not link them to function entry. None is a prefix interface.
   The relation below records only successful continuation transitions; it
   does not require future success. INVOKE remains one actual step_inst event.
   A PHI event is one atomic batch, using cse_phi_reads_eval_phis above. *)
Datatype:
 cse_phase = CseRun num venom_state | CseExec num basic_block venom_state
End

Datatype:
 cse_event = CsePhi num basic_block venom_state venom_state
           | CseStep num basic_block instruction venom_state venom_state
End

Inductive cse_prefix:
[~entry:]
 (!ctx fn fuel s.
   s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb ==>
   cse_prefix ctx fn fuel s [] (CseRun fuel s))
[~phi:]
 (!ctx fn fuel0 s0 events fuel s bb t.
   cse_prefix ctx fn fuel0 s0 events (CseRun (SUC fuel) s) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   eval_phis s bb.bb_instructions = OK t ==>
   cse_prefix ctx fn fuel0 s0 (events ++ [CsePhi fuel bb s t])
     (CseExec fuel bb
       (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)))
[~ordinary:]
 (!ctx fn fuel0 s0 events fuel bb s inst t.
   cse_prefix ctx fn fuel0 s0 events (CseExec fuel bb s) /\
   get_instruction bb s.vs_inst_idx = SOME inst /\
   step_inst fuel ctx inst s = OK t /\
   ~is_terminator inst.inst_opcode ==>
   cse_prefix ctx fn fuel0 s0 (events ++ [CseStep fuel bb inst s t])
     (CseExec fuel bb (t with vs_inst_idx := SUC s.vs_inst_idx)))
[~branch:]
 (!ctx fn fuel0 s0 events fuel bb s inst t.
   cse_prefix ctx fn fuel0 s0 events (CseExec fuel bb s) /\
   get_instruction bb s.vs_inst_idx = SOME inst /\
   step_inst fuel ctx inst s = OK t /\
   is_terminator inst.inst_opcode /\ ~t.vs_halted ==>
   cse_prefix ctx fn fuel0 s0 (events ++ [CseStep fuel bb inst s t])
     (CseRun fuel t))
End

Theorem cse_prefix_empty:
 !ctx fn fuel0 s0 phase.
 cse_prefix ctx fn fuel0 s0 [] phase <=>
 s0.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s0.vs_current_bb /\
 phase = CseRun fuel0 s0
Proof
 rpt gen_tac >> once_rewrite_tac[cse_prefix_cases] >> simp[] >> metis_tac[]
QED

Theorem cse_prefix_phi_extend:
 !ctx fn fuel0 s0 events fuel s bb t.
 cse_prefix ctx fn fuel0 s0 events (CseRun (SUC fuel) s) /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 eval_phis s bb.bb_instructions = OK t ==>
 cse_prefix ctx fn fuel0 s0 (events ++ [CsePhi fuel bb s t])
   (CseExec fuel bb
     (t with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
 metis_tac[cse_prefix_rules]
QED

Theorem cse_prefix_ordinary_extend:
 !ctx fn fuel0 s0 events fuel bb s inst t.
 cse_prefix ctx fn fuel0 s0 events (CseExec fuel bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
 cse_prefix ctx fn fuel0 s0 (events ++ [CseStep fuel bb inst s t])
   (CseExec fuel bb (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 metis_tac[cse_prefix_rules]
QED

Theorem cse_prefix_branch_extend:
 !ctx fn fuel0 s0 events fuel bb s inst t.
 cse_prefix ctx fn fuel0 s0 events (CseExec fuel bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 step_inst fuel ctx inst s = OK t /\
 is_terminator inst.inst_opcode /\ ~t.vs_halted ==>
 cse_prefix ctx fn fuel0 s0 (events ++ [CseStep fuel bb inst s t])
   (CseRun fuel t)
Proof
 metis_tac[cse_prefix_rules]
QED

(* Phase inversion is exported by cse_prefix_cases. In particular, CseRun 0
   has no PHI successor; a halting/terminal step has no continuation event.
   The following atomic-PHI inversion also exposes the accepted shared-snapshot
   read certificate, without sequentializing writes. *)
Theorem cse_prefix_phi_snapshot:
 !ctx fn fuel0 s0 events fuel s bb t.
 cse_prefix ctx fn fuel0 s0 events (CseRun (SUC fuel) s) /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 eval_phis s bb.bb_instructions = OK t ==>
 ?writes.
 cse_phi_reads s bb.bb_instructions writes /\
 t = FOLDR (\(out,v) acc. update_var out v acc) s writes /\
 cse_prefix ctx fn fuel0 s0 (events ++ [CsePhi fuel bb s t])
   (CseExec fuel bb
     (t with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
 rpt strip_tac >> drule (iffLR cse_phi_reads_eval_phis) >> strip_tac >>
 qexists_tac `writes` >> simp[] >>
 irule cse_prefix_phi_extend >> simp[]
QED

(* Exec phases denote the remaining function execution, including later blocks. *)
Definition cse_after_block_def:
 cse_after_block fuel ctx fn r =
 case r of
   OK t => if t.vs_halted then Halt t else run_blocks fuel ctx fn t
 | other => other
End

Definition cse_resume_def:
 (cse_resume ctx fn (CseRun fuel s) = run_blocks fuel ctx fn s) /\
 (cse_resume ctx fn (CseExec fuel bb s) =
   cse_after_block fuel ctx fn (exec_block fuel ctx bb s))
End

Theorem cse_after_block_results[simp]:
 (!fuel ctx fn t. cse_after_block fuel ctx fn (OK t) =
   if t.vs_halted then Halt t else run_blocks fuel ctx fn t) /\
 (!fuel ctx fn e. cse_after_block fuel ctx fn (Error e) = Error e) /\
 (!fuel ctx fn t. cse_after_block fuel ctx fn (Halt t) = Halt t) /\
 (!fuel ctx fn a t. cse_after_block fuel ctx fn (Abort a t) = Abort a t) /\
 (!fuel ctx fn vals t.
   cse_after_block fuel ctx fn (IntRet vals t) = IntRet vals t)
Proof
 simp[cse_after_block_def]
QED

Theorem cse_resume_phi:
 !ctx fn fuel s bb t.
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 eval_phis s bb.bb_instructions = OK t ==>
 cse_resume ctx fn (CseRun (SUC fuel) s) =
 cse_resume ctx fn (CseExec fuel bb
   (t with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
 rpt strip_tac >> simp[cse_resume_def, Once run_blocks_def] >>
 Cases_on `exec_block fuel ctx bb
   (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
 simp[cse_after_block_def]
QED

Theorem cse_resume_ordinary:
 !ctx fn fuel bb s inst t.
 get_instruction bb s.vs_inst_idx = SOME inst /\
 step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
 cse_resume ctx fn (CseExec fuel bb s) =
 cse_resume ctx fn (CseExec fuel bb (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt strip_tac >> simp[cse_resume_def] >>
 AP_TERM_TAC >> simp[Once exec_block_def]
QED

Theorem cse_resume_branch:
 !ctx fn fuel bb s inst t.
 get_instruction bb s.vs_inst_idx = SOME inst /\
 step_inst fuel ctx inst s = OK t /\
 is_terminator inst.inst_opcode /\ ~t.vs_halted ==>
 cse_resume ctx fn (CseExec fuel bb s) = cse_resume ctx fn (CseRun fuel t)
Proof
 rpt strip_tac >> simp[cse_resume_def, Once exec_block_def]
QED

Theorem cse_prefix_resume:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 run_blocks fuel0 ctx fn s0 = cse_resume ctx fn phase
Proof
 ho_match_mp_tac cse_prefix_ind >> rpt conj_tac >> rpt gen_tac
 >- simp[cse_resume_def]
 >- (strip_tac >> drule_all cse_resume_phi >> metis_tac[])
 >- (strip_tac >> drule_all cse_resume_ordinary >> metis_tac[]) >>
 strip_tac >> drule_all cse_resume_branch >> metis_tac[]
QED

(* Control projections used by the conditional, occurrence-indexed consumer. *)
Theorem cse_state_equiv_control[local]:
 !s t. state_equiv {} s t ==>
 s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
 s.vs_halted = t.vs_halted /\ execution_equiv {} s t
Proof
 rpt strip_tac >> gvs[state_equiv_def, execution_equiv_def,
   stateFrameTheory.execution_frame_def] >> metis_tac[]
QED

Theorem cse_prefix_exec_sim[local]:
 !ctx fn gn B fuel0 s0 n.
 (!bb i inst. get_instruction bb i = SOME inst ==>
   ?j. get_instruction (B bb) i = SOME j /\
       is_terminator j.inst_opcode = is_terminator inst.inst_opcode) /\
 (!events s t. cse_prefix ctx fn fuel0 s0 events (CseRun n s) /\
   state_equiv {} s t ==>
   (?e. run_blocks n ctx fn s = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (run_blocks n ctx fn s) (run_blocks n ctx gn t)) /\
 (!events bb s t inst j.
   cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
   state_equiv {} s t /\ get_instruction bb s.vs_inst_idx = SOME inst /\
   get_instruction (B bb) s.vs_inst_idx = SOME j ==>
   (?e. step_inst n ctx inst s = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (step_inst n ctx inst s) (step_inst n ctx j t)) ==>
 !events bb s t.
   cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
   state_equiv {} s t ==>
   (?e. cse_resume ctx fn (CseExec n bb s) = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (cse_resume ctx fn (CseExec n bb s))
     (cse_resume ctx gn (CseExec n (B bb) t))
Proof
 rpt gen_tac >> strip_tac >>
 completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
 rpt strip_tac >>
 Cases_on `get_instruction bb s.vs_inst_idx`
 >- simp[cse_resume_def, Once exec_block_def] >>
 rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
 `?j. get_instruction (B bb) s.vs_inst_idx = SOME j /\
       is_terminator j.inst_opcode = is_terminator inst.inst_opcode`
   by metis_tac[] >>
 drule_all cse_state_equiv_control >> strip_tac >>
 qpat_x_assum `!events bb s t inst j. _` drule_all >> strip_tac
 >- (simp[cse_resume_def, Once exec_block_def]) >>
 Cases_on `step_inst n ctx inst s` >>
 Cases_on `step_inst n ctx j t` >> gvs[lift_result_def]
 >- suspend "exec_ok"
 >- suspend "exec_halt"
 >- suspend "exec_abort"
 >- suspend "exec_error" >>
 suspend "exec_return"
QED

Resume cse_prefix_exec_sim[exec_halt]:
 pure_rewrite_tac[cse_resume_def] >>
 pure_once_rewrite_tac[exec_block_def] >>
 simp[lift_result_def]
QED
Resume cse_prefix_exec_sim[exec_abort]:
 pure_rewrite_tac[cse_resume_def] >>
 pure_once_rewrite_tac[exec_block_def] >>
 simp[lift_result_def]
QED
Resume cse_prefix_exec_sim[exec_error]:
 pure_rewrite_tac[cse_resume_def] >>
 pure_once_rewrite_tac[exec_block_def] >>
 simp[lift_result_def]
QED
Resume cse_prefix_exec_sim[exec_return]:
 pure_rewrite_tac[cse_resume_def] >>
 pure_once_rewrite_tac[exec_block_def] >>
 simp[lift_result_def]
QED
Resume cse_prefix_exec_sim[exec_ok]:
 rename1 `step_inst n ctx inst s = OK u` >>
 rename1 `step_inst n ctx j t = OK v` >>
 drule_all cse_state_equiv_control >> strip_tac >>
 `get_instruction bb s.vs_inst_idx = SOME inst` by metis_tac[] >>
 Cases_on `is_terminator inst.inst_opcode`
 >- (Cases_on `u.vs_halted`
     >- (pure_rewrite_tac[cse_resume_def] >>
         pure_once_rewrite_tac[exec_block_def] >> gvs[lift_result_def]) >>
     drule_all cse_prefix_branch_extend >> strip_tac >>
     drule_all cse_resume_branch >> strip_tac >>
     `cse_resume ctx gn (CseExec n (B bb) t) =
      cse_resume ctx gn (CseRun n v)`
       by (irule cse_resume_branch >> gvs[]) >>
     qpat_x_assum `!events s t. _` drule_all >>
     simp[cse_resume_def]) >>
 `cse_prefix ctx fn fuel0 s0 (events ++ [CseStep n bb inst s u])
   (CseExec n bb (u with vs_inst_idx := SUC s.vs_inst_idx))`
   by (irule cse_prefix_ordinary_extend >> simp[]) >>
 `state_equiv {} (u with vs_inst_idx := SUC s.vs_inst_idx)
                  (v with vs_inst_idx := SUC s.vs_inst_idx)`
   by (irule state_equiv_inst_idx >> simp[]) >>
 `LENGTH bb.bb_instructions - SUC s.vs_inst_idx <
  LENGTH bb.bb_instructions - s.vs_inst_idx`
   by (gvs[venomInstTheory.get_instruction_def] >> decide_tac) >>
 drule_all cse_resume_ordinary >> strip_tac >>
 `cse_resume ctx gn (CseExec n (B bb) t) =
  cse_resume ctx gn (CseExec n (B bb)
    (v with vs_inst_idx := SUC s.vs_inst_idx))`
   by (gvs[] >> irule cse_resume_ordinary >> metis_tac[]) >>
 qpat_x_assum `!m. _` (qspec_then
   `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
 simp[] >> disch_then (qspecl_then
   [`bb`, `u with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
 simp[] >> strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED
Finalise cse_prefix_exec_sim

Theorem cse_prefix_run_suc_sim[local]:
 !ctx fn gn B fuel0 s0 n.
 (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
   lookup_block l gn.fn_blocks = SOME (B bb)) /\
 (!bb. phi_prefix_length (B bb).bb_instructions =
        phi_prefix_length bb.bb_instructions) /\
 (!events s bb u t.
   cse_prefix ctx fn fuel0 s0 events (CseRun (SUC n) s) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   state_equiv {} s t /\ eval_phis s bb.bb_instructions = OK u ==>
   ?v. eval_phis t (B bb).bb_instructions = OK v /\ state_equiv {} u v) /\
 (!events bb s t.
   cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
   state_equiv {} s t ==>
   (?e. cse_resume ctx fn (CseExec n bb s) = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (cse_resume ctx fn (CseExec n bb s))
     (cse_resume ctx gn (CseExec n (B bb) t))) ==>
 !events s t.
   cse_prefix ctx fn fuel0 s0 events (CseRun (SUC n) s) /\
   state_equiv {} s t ==>
   (?e. run_blocks (SUC n) ctx fn s = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (run_blocks (SUC n) ctx fn s) (run_blocks (SUC n) ctx gn t)
Proof
 rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
 >- simp[Once run_blocks_def] >>
 rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
 qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
   eval_phis_ok_or_error_defs
 >- suspend "run_phi_ok" >>
 simp[Once run_blocks_def]
QED
Resume cse_prefix_run_suc_sim[run_phi_ok]:
 rename1 `eval_phis s bb.bb_instructions = OK u` >>
 qpat_x_assum `!events s bb u t. _` drule_all >> strip_tac >>
 qpat_assum `state_equiv {} s t`
   (mp_then Any strip_assume_tac cse_state_equiv_control) >>
 `lookup_block t.vs_current_bb gn.fn_blocks = SOME (B bb)`
   by metis_tac[] >>
 `cse_prefix ctx fn fuel0 s0 (events ++ [CsePhi n bb s u])
   (CseExec n bb (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))`
   by (irule cse_prefix_phi_extend >> simp[]) >>
 `state_equiv {} (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)
   (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)`
   by (irule state_equiv_inst_idx >> simp[]) >>
 qpat_x_assum `!events bb s t. _` drule_all >>
 `cse_resume ctx fn (CseRun (SUC n) s) =
  cse_resume ctx fn (CseExec n bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))`
   by (irule cse_resume_phi >> simp[]) >>
 `cse_resume ctx gn (CseRun (SUC n) t) =
  cse_resume ctx gn (CseExec n (B bb)
    (v with vs_inst_idx := phi_prefix_length bb.bb_instructions))`
   by (qsuff_tac `cse_resume ctx gn (CseRun (SUC n) t) =
        cse_resume ctx gn (CseExec n (B bb)
          (v with vs_inst_idx := phi_prefix_length (B bb).bb_instructions))`
       >- simp[] >> irule cse_resume_phi >> simp[]) >>
 metis_tac[cse_resume_def]
QED
Finalise cse_prefix_run_suc_sim

(* No availability or canonical-map assumption is hidden in this consumer.
   Its instruction law is required only at actual source occurrences. *)
Theorem cse_prefix_simulation:
 !ctx fn gn B fuel0 s0.
 (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
   lookup_block l gn.fn_blocks = SOME (B bb)) /\
 (!bb. phi_prefix_length (B bb).bb_instructions =
        phi_prefix_length bb.bb_instructions) /\
 (!bb i inst. get_instruction bb i = SOME inst ==>
   ?j. get_instruction (B bb) i = SOME j /\
       is_terminator j.inst_opcode = is_terminator inst.inst_opcode) /\
 (!events n s bb u t.
   cse_prefix ctx fn fuel0 s0 events (CseRun (SUC n) s) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   state_equiv {} s t /\ eval_phis s bb.bb_instructions = OK u ==>
   ?v. eval_phis t (B bb).bb_instructions = OK v /\ state_equiv {} u v) /\
 (!events n bb s t inst j.
   cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
   state_equiv {} s t /\ get_instruction bb s.vs_inst_idx = SOME inst /\
   get_instruction (B bb) s.vs_inst_idx = SOME j ==>
   (?e. step_inst n ctx inst s = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (step_inst n ctx inst s) (step_inst n ctx j t)) ==>
 !n.
 (!events s t.
   cse_prefix ctx fn fuel0 s0 events (CseRun n s) /\
   state_equiv {} s t ==>
   (?e. run_blocks n ctx fn s = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (run_blocks n ctx fn s) (run_blocks n ctx gn t)) /\
 (!events bb s t.
   cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
   state_equiv {} s t ==>
   (?e. cse_resume ctx fn (CseExec n bb s) = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (cse_resume ctx fn (CseExec n bb s))
     (cse_resume ctx gn (CseExec n (B bb) t)))
Proof
 rpt gen_tac >> strip_tac >> Induct
 >- (conj_asm1_tac
     >- simp[Once run_blocks_def] >>
     rpt gen_tac >> strip_tac >> irule cse_prefix_exec_sim >>
     rpt conj_tac >> asm_rewrite_tac[] >>
     qexistsl_tac [`events`, `fuel0`, `s0`] >>
     rpt conj_tac >> asm_rewrite_tac[] >>
     rpt gen_tac >> strip_tac >> first_x_assum drule_all >> simp[]) >>
 conj_asm1_tac
 >- (rpt gen_tac >> strip_tac >> irule cse_prefix_run_suc_sim >>
     rpt conj_tac >> asm_rewrite_tac[] >>
     qexistsl_tac [`B`, `events`, `fuel0`, `s0`] >>
     rpt conj_tac >> asm_rewrite_tac[] >>
     rpt gen_tac >> strip_tac >> first_x_assum drule_all >> simp[]) >>
 rpt gen_tac >> strip_tac >> irule cse_prefix_exec_sim >>
     rpt conj_tac >> asm_rewrite_tac[] >>
     qexistsl_tac [`events`, `fuel0`, `s0`] >>
     rpt conj_tac >> asm_rewrite_tac[] >>
     rpt gen_tac >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem cse_prefix_simulation_entry:
 !ctx fn gn B fuel0 s0 t0.
 (!l bb. lookup_block l fn.fn_blocks = SOME bb ==>
   lookup_block l gn.fn_blocks = SOME (B bb)) /\
 (!bb. phi_prefix_length (B bb).bb_instructions =
        phi_prefix_length bb.bb_instructions) /\
 (!bb i inst. get_instruction bb i = SOME inst ==>
   ?j. get_instruction (B bb) i = SOME j /\
       is_terminator j.inst_opcode = is_terminator inst.inst_opcode) /\
 (!events n s bb u t.
   cse_prefix ctx fn fuel0 s0 events (CseRun (SUC n) s) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   state_equiv {} s t /\ eval_phis s bb.bb_instructions = OK u ==>
   ?v. eval_phis t (B bb).bb_instructions = OK v /\ state_equiv {} u v) /\
 (!events n bb s t inst j.
   cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
   state_equiv {} s t /\ get_instruction bb s.vs_inst_idx = SOME inst /\
   get_instruction (B bb) s.vs_inst_idx = SOME j ==>
   (?e. step_inst n ctx inst s = Error e) \/
   lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (step_inst n ctx inst s) (step_inst n ctx j t)) /\
 s0.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s0.vs_current_bb /\
 state_equiv {} s0 t0 ==>
 (?e. run_blocks fuel0 ctx fn s0 = Error e) \/
 lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
   (run_blocks fuel0 ctx fn s0) (run_blocks fuel0 ctx gn t0)
Proof
 rpt strip_tac >> drule_all cse_prefix_simulation >>
 disch_then (qspec_then `fuel0` strip_assume_tac) >>
 `cse_prefix ctx fn fuel0 s0 [] (CseRun fuel0 s0)`
   by simp[cse_prefix_empty] >>
 qpat_x_assum `!events s t. _` drule_all >> simp[]
QED

(* A successful continuing terminator follows a real CFG edge. *)
Theorem cse_terminator_boundary:
 !fn bb s inst fuel ctx t.
 wf_function fn /\ fn_inst_wf fn /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 step_inst fuel ctx inst s = OK t /\
 is_terminator inst.inst_opcode /\ ~t.vs_halted ==>
 SUC s.vs_inst_idx = LENGTH bb.bb_instructions /\
 MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) t.vs_current_bb) /\
 (MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre ==>
  MEM t.vs_current_bb (cfg_analyze fn).cfg_dfs_pre)
Proof
 rpt gen_tac >> strip_tac >>
 `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `bb_well_formed bb` by gvs[wf_function_def, EVERY_MEM] >>
 `s.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL s.vs_inst_idx bb.bb_instructions = inst` by
   gvs[get_instruction_def, AllCaseEqs()] >>
 `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
   metis_tac[bb_well_formed_def] >>
 `SUC s.vs_inst_idx = LENGTH bb.bb_instructions` by
   (gvs[bb_well_formed_def] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
 `LAST bb.bb_instructions = inst` by
   (`PRE (LENGTH bb.bb_instructions) = s.vs_inst_idx` by decide_tac >>
    fs[bb_well_formed_def] >> simp[LAST_EL]) >>
 `inst_wf inst` by
   (fs[fn_inst_wf_def, EVERY_MEM] >>
    `MEM inst bb.bb_instructions` by
      (fs[bb_well_formed_def] >>
       `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
         (Cases_on `bb.bb_instructions` >> gvs[]) >>
       metis_tac[MEM_EL, LAST_EL]) >>
    metis_tac[]) >>
 `inst.inst_opcode <> INVOKE` by
   (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
 `MEM t.vs_current_bb (get_successors inst)` by
   metis_tac[step_inst_base_term_succs, step_inst_non_invoke] >>
 `MEM t.vs_current_bb (bb_succs bb)` by
   (Cases_on `bb.bb_instructions` >>
    gvs[bb_succs_def, MEM_nub, MEM_REVERSE]) >>
 `MEM t.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
   metis_tac[cfg_analyze_preserves_bb_succs] >>
 simp[] >> conj_tac
 >- metis_tac[cfg_edge_symmetry_uncond] >>
 strip_tac >> drule cfg_dfs_pre_succs_closed >>
 simp[EVERY_MEM] >> disch_then irule >> simp[]
QED

Theorem cse_prefix_control:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 wf_function fn /\ fn_inst_wf fn ==>
 case phase of
   CseRun n s => MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
 | CseExec n bb s =>
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   bb.bb_label = s.vs_current_bb /\
   MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
   s.vs_inst_idx <= LENGTH bb.bb_instructions
Proof
 ho_match_mp_tac cse_prefix_ind >> rpt conj_tac
 >- (rpt gen_tac >> strip_tac >> strip_tac >> simp[] >>
     gvs[fn_entry_label_def] >> Cases_on `entry_block fn` >> gvs[] >>
     drule cfg_analyze_preorder_entry_first >>
     Cases_on `(cfg_analyze fn).cfg_dfs_pre` >> simp[])
 >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     drule eval_phis_preserves_current_bb >> strip_tac >>
     simp[] >> metis_tac[lookup_block_label, phi_prefix_length_le])
 >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     drule_all step_preserves_control_flow >> strip_tac >>
     gvs[get_instruction_def, AllCaseEqs()])
 >> rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
 drule_all cse_terminator_boundary >> simp[]
QED

Theorem cse_prefix_run_control:
 !ctx fn fuel0 s0 events n s.
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseRun n s) ==>
 MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
 rpt strip_tac >> drule cse_prefix_control >> simp[]
QED

Theorem cse_prefix_exec_control:
 !ctx fn fuel0 s0 events n bb s.
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) ==>
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_label = s.vs_current_bb /\
 MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
 s.vs_inst_idx <= LENGTH bb.bb_instructions
Proof
 rpt gen_tac >> strip_tac >> drule cse_prefix_control >> simp[]
QED

Definition cse_event_survives_def:
 (cse_event_survives e (CsePhi n bb s t) <=> T) /\
 (cse_event_survives e (CseStep n bb inst s t) <=>
  avail_source_survives e inst)
End

Definition cse_source_history_def:
 cse_source_history d events e src <=>
 ?pre post n bb s t.
 events = pre ++ [CseStep n bb src s t] ++ post /\
 avail_source_birth d e src src /\ EVERY (cse_event_survives e) post
End

Theorem cse_source_history_append:
 !d events e src ev.
 cse_source_history d events e src /\ cse_event_survives e ev ==>
 cse_source_history d (events ++ [ev]) e src
Proof
 rpt gen_tac >> simp[cse_source_history_def] >> strip_tac >>
 qexistsl_tac [`pre`, `post ++ [ev]`, `n`, `bb`, `s`, `t`] >>
 simp[APPEND_ASSOC]
QED

Theorem cse_source_history_birth:
 !d events e inst n bb s t.
 avail_source_birth d e inst inst ==>
 cse_source_history d (events ++ [CseStep n bb inst s t]) e inst
Proof
 rpt strip_tac >> simp[cse_source_history_def] >>
 qexistsl_tac [`events`, `[]`, `n`, `bb`, `s`, `t`] >> simp[]
QED

Theorem cse_prefix_source_history:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 wf_function fn /\ fn_inst_wf fn ==>
 case phase of
   CseRun n s => (!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
     ?a. df_at NONE (avail_analyze fn) s.vs_current_bb 0 = SOME a /\
       (!e src. (?xs. FLOOKUP a e = SOME xs /\ MEM src xs) ==>
         cse_source_history (dfg_build_function fn) events e src))
 | CseExec n bb s =>
     ?a. df_at NONE (avail_analyze fn) bb.bb_label s.vs_inst_idx = SOME a /\
       (!e src. (?xs. FLOOKUP a e = SOME xs /\ MEM src xs) ==>
         cse_source_history (dfg_build_function fn) events e src)
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac
 >- suspend "entry"
 >- suspend "phi"
 >- suspend "ordinary"
 >> suspend "branch"
QED
Resume cse_prefix_source_history[entry]:
 rpt gen_tac >> strip_tac >> strip_tac >> simp[] >>
 rpt strip_tac >>
 `cse_prefix ctx fn fuel0 s0 [] (CseRun fuel0 s0)` by
   simp[cse_prefix_empty] >>
 drule_all cse_prefix_run_control >> strip_tac >>
 drule_all cse_avail_entry_empty >> strip_tac >>
 qexists_tac `a` >> simp[] >> metis_tac[]
QED
Resume cse_prefix_source_history[phi]:
 rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
 drule_all cse_prefix_run_control >> strip_tac >>
 `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
 drule_all cse_avail_atomic_phi_some >> strip_tac >>
 qexists_tac `a` >> simp[] >> rpt strip_tac >>
 irule cse_source_history_append >> simp[cse_event_survives_def]
QED
Resume cse_prefix_source_history[ordinary]:
 rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 `s.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL s.vs_inst_idx bb.bb_instructions = inst` by
   gvs[get_instruction_def, AllCaseEqs()] >>
 `SUC s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
 gvs[] >> drule_all cse_avail_at_intra >>
 simp[availExprDefsTheory.avail_transfer_opt_def] >> strip_tac >>
 rpt gen_tac >> strip_tac >>
 rename1 `FLOOKUP (avail_transfer_inst d j a) e = SOME xs` >>
 qspecl_then [`d`, `j`, `a`, `e`, `src`] mp_tac cse_transfer_source_cases >>
 (impl_tac >- metis_tac[]) >> strip_tac
 >- (irule cse_source_history_append >>
     simp[cse_event_survives_def]) >>
 `src = j` by fs[availExprProofsTheory.avail_source_birth_def] >>
 gvs[] >> irule cse_source_history_birth >> simp[]
QED
Resume cse_prefix_source_history[branch]:
 rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 drule_all cse_terminator_boundary >> strip_tac >>
 `s.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL s.vs_inst_idx bb.bb_instructions = inst` by
   gvs[get_instruction_def, AllCaseEqs()] >>
 `SUC s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
 gvs[] >>
 `SUC s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
 drule_all cse_avail_at_intra >>
 simp[availExprDefsTheory.avail_transfer_opt_def,
      availExprDefsTheory.avail_transfer_inst_def] >> strip_tac >>
 rpt gen_tac >> strip_tac >>
 drule_all cse_avail_boundary_member >> strip_tac >>
 drule_all cse_avail_entry_predecessor >> strip_tac >>
 qexists_tac `b'` >> simp[] >> rpt strip_tac >>
 irule cse_source_history_append >>
 simp[cse_event_survives_def, availExprProofsTheory.avail_source_survives_def] >>
 metis_tac[]
QED
Finalise cse_prefix_source_history

Theorem cse_prefix_run_source_history:
 !ctx fn fuel0 s0 events n s bb.
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseRun n s) /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
 ?a. df_at NONE (avail_analyze fn) s.vs_current_bb 0 = SOME a /\
   (!e src. (?xs. FLOOKUP a e = SOME xs /\ MEM src xs) ==>
     cse_source_history (dfg_build_function fn) events e src)
Proof
 rpt strip_tac >> drule cse_prefix_source_history >> simp[]
QED

Theorem cse_prefix_exec_source_history:
 !ctx fn fuel0 s0 events n bb s.
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) ==>
 ?a. df_at NONE (avail_analyze fn) bb.bb_label s.vs_inst_idx = SOME a /\
   (!e src. (?xs. FLOOKUP a e = SOME xs /\ MEM src xs) ==>
     cse_source_history (dfg_build_function fn) events e src)
Proof
 rpt strip_tac >> drule cse_prefix_source_history >> simp[]
QED

Theorem cse_prefix_run_avail_history:
 !ctx fn fuel0 s0 events n s bb e src xs.
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseRun n s) /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 FLOOKUP (ae_lookup_inst fn s.vs_current_bb 0) e = SOME xs /\ MEM src xs ==>
 cse_source_history (dfg_build_function fn) events e src
Proof
 rpt strip_tac >> drule_all cse_prefix_run_source_history >> strip_tac >>
 gvs[availExprDefsTheory.ae_lookup_inst_def, availExprDefsTheory.avail_unwrap_def] >>
 metis_tac[]
QED

Theorem cse_prefix_exec_avail_history:
 !ctx fn fuel0 s0 events n bb s e src xs.
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx) e = SOME xs /\ MEM src xs ==>
 cse_source_history (dfg_build_function fn) events e src
Proof
 rpt strip_tac >> drule_all cse_prefix_exec_source_history >> strip_tac >>
 gvs[availExprDefsTheory.ae_lookup_inst_def, availExprDefsTheory.avail_unwrap_def] >>
 metis_tac[]
QED
