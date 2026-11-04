Theory cseHistoryProps
Ancestors passSharedProps venomExecSemantics venomState stateEquiv execEquivProofs

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
