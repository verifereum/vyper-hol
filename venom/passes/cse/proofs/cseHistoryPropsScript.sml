Theory cseHistoryProps
Ancestors passSharedProps venomExecSemantics venomState stateEquiv execEquivProofs
  cfgAnalysisProps analysisSimProps venomInstIdsProps venomInstProps venomExecProps
  venomWf venomWfProps venomInst venomExecProofs list cfgDefs cseCanonProps instIdxIndep
  cfgCorrectnessProof cfgHelpers

(* Reachable-block restriction of wf_ssa: preserves def_dominates_uses on all
   DFS-reachable blocks so CSE's single-pass step is inductive across OWHILE
   even when unreachable blocks have expressions rewritten to ASSIGN. *)
Definition cse_reachable_wf_ssa_def:
  cse_reachable_wf_ssa fn <=>
    ssa_form fn /\
    !bb inst.
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      MEM inst bb.bb_instructions ==>
      if inst.inst_opcode = PHI then phi_edge_uses_wf fn bb inst
      else !v. MEM (Var v) inst.inst_operands ==> def_available_at fn bb (SOME inst) v
End

Theorem wf_ssa_imp_cse_reachable_wf_ssa:
  !fn. wf_ssa fn ==> cse_reachable_wf_ssa fn
Proof
  rw[wf_ssa_def, def_dominates_uses_def, cse_reachable_wf_ssa_def]
QED

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

Definition cse_event_input_def:
 (cse_event_input (CsePhi n bb s t) = s) /\
 (cse_event_input (CseStep n bb inst s t) = s)
End
Definition cse_event_output_def:
 (cse_event_output (CsePhi n bb s t) = t) /\
 (cse_event_output (CseStep n bb inst s t) = t)
End
Definition cse_phase_state_def:
 (cse_phase_state (CseRun n s) = s) /\
 (cse_phase_state (CseExec n bb s) = s)
End
Definition cse_event_writes_def:
 (cse_event_writes (CsePhi n bb s t) v <=>
   ?inst. MEM inst (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
          MEM v inst.inst_outputs) /\
 (cse_event_writes (CseStep n bb inst s t) v <=> MEM v inst.inst_outputs)
End

Theorem cse_phi_prefix_nonoutput:
 !insts s t v. eval_phis s insts = OK t /\
 (!inst. MEM inst (TAKE (phi_prefix_length insts) insts) ==>
   ~MEM v inst.inst_outputs) ==>
 lookup_var v t = lookup_var v s
Proof
 Induct >> simp[phi_prefix_length_def, eval_phis_def] >>
 rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
 Cases_on `eval_one_phi s h` >> simp[] >>
 rename1 `eval_one_phi s h = SOME pair` >> PairCases_on `pair` >>
 Cases_on `eval_phis s insts` >> simp[] >> strip_tac >> gvs[] >>
 `MEM pair0 h.inst_outputs` by metis_tac[eval_one_phi_output_mem] >>
 `pair0 <> v` by metis_tac[] >>
 `lookup_var v v' = lookup_var v s` by
   (first_x_assum irule >> simp[]) >>
 simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
 gvs[lookup_var_def]
QED

Theorem cse_prefix_nonwriting_events:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 (!ev. MEM ev events ==> !v. ~cse_event_writes ev v ==>
   lookup_var v (cse_event_output ev) = lookup_var v (cse_event_input ev))
Proof
 ho_match_mp_tac cse_prefix_ind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac >> simp[MEM_APPEND] >> rpt strip_tac >>
 gvs[cse_event_writes_def, cse_event_input_def, cse_event_output_def]
 >- (irule cse_phi_prefix_nonoutput >> simp[] >> metis_tac[])
 >- metis_tac[step_preserves_non_output_vars]
 >> metis_tac[step_terminator_preserves_vars]
QED

Theorem cse_prefix_binding_fold:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 !v. lookup_var v (cse_phase_state phase) =
 FOLDL (\acc ev. if cse_event_writes ev v then
          lookup_var v (cse_event_output ev) else acc)
   (lookup_var v s0) events
Proof
 ho_match_mp_tac cse_prefix_ind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac >>
 simp[cse_phase_state_def, rich_listTheory.FOLDL_APPEND,
      cse_event_writes_def, cse_event_output_def, lookup_var_def] >>
 rpt gen_tac >> IF_CASES_TAC >> simp[]
 >- (`lookup_var v t = lookup_var v s` by
       (irule cse_phi_prefix_nonoutput >> simp[] >> metis_tac[]) >>
     gvs[cse_phase_state_def, lookup_var_def])
 >- (drule_all step_preserves_non_output_vars >>
     gvs[cse_phase_state_def, lookup_var_def])
 >> drule_all step_terminator_preserves_vars >>
    gvs[cse_phase_state_def, lookup_var_def]
QED

Theorem cse_binding_fold_nonwriting[local]:
 !events v acc.
 EVERY (\ev. ~cse_event_writes ev v) events ==>
 FOLDL (\a ev. if cse_event_writes ev v then
          lookup_var v (cse_event_output ev) else a) acc events = acc
Proof
 Induct >> simp[] >> rpt strip_tac >> simp[]
QED

Theorem cse_prefix_initial_binding:
 cse_prefix ctx fn fuel0 s0 events phase /\
 EVERY (\ev. ~cse_event_writes ev v) events ==>
 lookup_var v (cse_phase_state phase) = lookup_var v s0
Proof
 strip_tac >> drule cse_prefix_binding_fold >>
 disch_then (qspec_then `v` mp_tac) >>
 simp[cse_binding_fold_nonwriting]
QED

Theorem cse_prefix_last_write_binding:
 cse_prefix ctx fn fuel0 s0 events phase /\
 events = pre ++ [ev] ++ post /\ cse_event_writes ev v /\
 EVERY (\e. ~cse_event_writes e v) post ==>
 lookup_var v (cse_phase_state phase) = lookup_var v (cse_event_output ev)
Proof
 strip_tac >> drule cse_prefix_binding_fold >>
 disch_then (qspec_then `v` mp_tac) >>
 simp[rich_listTheory.FOLDL_APPEND, cse_binding_fold_nonwriting]
QED

Theorem cse_events_last_write[local]:
 !events v.
 EVERY (\ev. ~cse_event_writes ev v) events \/
 ?pre ev post. events = pre ++ [ev] ++ post /\
 cse_event_writes ev v /\ EVERY (\e. ~cse_event_writes e v) post
Proof
 Induct >> simp[] >> rpt gen_tac >>
 Cases_on `EVERY (\ev. ~cse_event_writes ev v) events`
 >- (Cases_on `cse_event_writes h v` >> simp[] >>
     qexistsl [`[]`, `h`, `events`] >> simp[]) >>
 first_x_assum (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
 qexistsl [`h::pre`, `ev`, `post`] >> simp[]
QED

Theorem cse_prefix_last_write_or_initial:
 cse_prefix ctx fn fuel0 s0 events phase ==>
 (EVERY (\ev. ~cse_event_writes ev v) events /\
  lookup_var v (cse_phase_state phase) = lookup_var v s0) \/
 ?pre ev post. events = pre ++ [ev] ++ post /\
 cse_event_writes ev v /\ EVERY (\e. ~cse_event_writes e v) post /\
 lookup_var v (cse_phase_state phase) = lookup_var v (cse_event_output ev)
Proof
 strip_tac >> qspecl_then [`events`, `v`] strip_assume_tac cse_events_last_write
 >- (disj1_tac >> simp[] >> irule cse_prefix_initial_binding >> metis_tac[]) >>
 disj2_tac >> qexistsl [`pre`, `ev`, `post`] >> simp[] >>
 irule cse_prefix_last_write_binding >> metis_tac[]
QED

Theorem cse_prefix_suffix_binding:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 !pre ev post v. events = pre ++ [ev] ++ post /\
 EVERY (\e. ~cse_event_writes e v) post ==>
 lookup_var v (cse_phase_state phase) = lookup_var v (cse_event_output ev)
Proof
 ho_match_mp_tac cse_prefix_ind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
 >- gvs[]
 >> Cases_on `post` using SNOC_CASES
 >> gvs[SNOC_APPEND, APPEND_ASSOC, APPEND_11, EVERY_APPEND,
        cse_phase_state_def, cse_event_output_def, lookup_var_def]
 >> first_x_assum (qspecl_then [`pre`, `ev`, `l`, `v`] mp_tac)
 >> simp[] >> strip_tac
 >- (`lookup_var v t = lookup_var v s` by
       (irule cse_phi_prefix_nonoutput >>
        gvs[cse_event_writes_def] >> metis_tac[]) >>
     gvs[lookup_var_def])
 >- (gvs[cse_event_writes_def] >>
     drule_all step_preserves_non_output_vars >> gvs[lookup_var_def])
 >> drule_all step_terminator_preserves_vars >> gvs[lookup_var_def]
QED

(* A branch appends a visit even when its target is the same label. *)
Definition cse_event_next_visit_def:
 (cse_event_next_visit (CsePhi n bb s t) = []) /\
 (cse_event_next_visit (CseStep n bb inst s t) =
   if is_terminator inst.inst_opcode then [t.vs_current_bb] else [])
End

Definition cse_visit_path_def:
 cse_visit_path s0 events =
 s0.vs_current_bb :: FLAT (MAP cse_event_next_visit events)
End

Theorem cse_visit_path_snoc:
 cse_visit_path s0 (events ++ [ev]) =
 cse_visit_path s0 events ++ cse_event_next_visit ev
Proof
 simp[cse_visit_path_def, FLAT_APPEND]
QED

Theorem cse_terminator_cfg_edge:
 wf_function fn /\ fn_inst_wf fn /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 step_inst fuel ctx inst s = OK t /\
 is_terminator inst.inst_opcode /\ ~t.vs_halted ==>
 fn_cfg_edge fn s.vs_current_bb t.vs_current_bb
Proof
 strip_tac >> drule_all cse_terminator_boundary >> strip_tac >>
 `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
   metis_tac[lookup_block_MEM, lookup_block_label] >>
 `MEM t.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
   metis_tac[cfg_edge_symmetry_uncond] >>
 `MEM t.vs_current_bb (bb_succs bb)` by
   metis_tac[cfg_analyze_preserves_bb_succs] >>
 simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem cse_prefix_visit_path:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 wf_function fn /\ fn_inst_wf fn ==>
 is_fn_path fn (cse_visit_path s0 events) /\
 fn_entry_label fn = SOME (HD (cse_visit_path s0 events)) /\
 LAST (cse_visit_path s0 events) = (cse_phase_state phase).vs_current_bb
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac
 >- (rpt gen_tac >> strip_tac >> strip_tac >>
     simp[cse_visit_path_def, cse_phase_state_def, is_fn_path_def])
 >- (rpt gen_tac >> strip_tac >> strip_tac >>
     drule eval_phis_preserves_current_bb >> strip_tac >>
     gvs[cse_visit_path_snoc, cse_event_next_visit_def, cse_phase_state_def])
 >- (rpt gen_tac >> strip_tac >> strip_tac >>
     drule_all step_preserves_control_flow >> strip_tac >>
     gvs[cse_visit_path_snoc, cse_event_next_visit_def, cse_phase_state_def])
 >> rpt gen_tac >> strip_tac >> strip_tac >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 drule_all cse_terminator_cfg_edge >> strip_tac >>
 gvs[cse_visit_path_snoc, cse_event_next_visit_def, cse_phase_state_def] >>
 conj_tac
 >- (irule is_fn_path_snoc >> simp[cse_visit_path_def]) >>
 simp[cse_visit_path_def]
QED

(* A segment contains one atomic PHI batch and the ordinary occurrences in
   index order.  The endpoint k is the next ordinary instruction index. *)
Inductive cse_visit_segment:
[~phi:]
 (!n bb s t. eval_phis s bb.bb_instructions = OK t ==>
   cse_visit_segment bb [CsePhi n bb s t]
     (phi_prefix_length bb.bb_instructions))
[~step:]
 (!bb es k n inst s t.
   cse_visit_segment bb es k /\ s.vs_inst_idx = k /\
   get_instruction bb k = SOME inst ==>
   cse_visit_segment bb (es ++ [CseStep n bb inst s t]) (SUC k))
End

Theorem cse_prefix_visit_segments:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 wf_function fn /\ fn_inst_wf fn ==>
 ?done current.
 events = FLAT (MAP SND done) ++ current /\
 cse_visit_path s0 events =
   MAP (\visit. (FST visit).bb_label) done ++
   [(cse_phase_state phase).vs_current_bb] /\
 EVERY (\visit. cse_visit_segment (FST visit) (SND visit)
                   (LENGTH (FST visit).bb_instructions)) done /\
 (case phase of CseRun n s => current = []
  | CseExec n bb s => cse_visit_segment bb current s.vs_inst_idx)
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac
 >- (rpt gen_tac >> strip_tac >> strip_tac >>
     qexistsl [`[]`, `[]`] >> simp[cse_visit_path_def, cse_phase_state_def])
 >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     qexistsl [`done`, `[CsePhi fuel bb s t]`] >>
     drule eval_phis_preserves_current_bb >> strip_tac >>
     simp[cse_visit_path_snoc, cse_event_next_visit_def, cse_phase_state_def] >>
     metis_tac[cse_visit_segment_rules])
 >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     qexistsl [`done`, `current ++ [CseStep fuel bb inst s t]`] >>
     drule_all step_preserves_control_flow >> strip_tac >>
     simp[cse_visit_path_snoc, cse_event_next_visit_def, cse_phase_state_def,
          APPEND_ASSOC] >> metis_tac[cse_visit_segment_rules])
 >> rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 drule_all cse_terminator_boundary >> strip_tac >>
 qexists `done ++ [(bb, current ++ [CseStep fuel bb inst s t])]` >>
 simp[cse_visit_path_snoc, cse_event_next_visit_def, cse_phase_state_def,
      FLAT_APPEND, EVERY_APPEND, APPEND_ASSOC] >>
 metis_tac[cse_visit_segment_rules]
QED

Theorem cse_visit_segment_length:
 !bb es k. cse_visit_segment bb es k ==>
 phi_prefix_length bb.bb_instructions <= k /\
 LENGTH es = SUC (k - phi_prefix_length bb.bb_instructions)
Proof
 ho_match_mp_tac cse_visit_segment_ind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac >> simp[]
QED

Theorem cse_visit_segment_phi_head:
 !bb es k. cse_visit_segment bb es k ==>
 ?n s t rest. es = CsePhi n bb s t :: rest /\
 eval_phis s bb.bb_instructions = OK t
Proof
 ho_match_mp_tac cse_visit_segment_ind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac
 >- (qexistsl [`n`, `s`, `t`, `[]`] >> simp[]) >>
 qexistsl [`n'`, `s'`, `t'`, `rest ++ [CseStep n bb inst s t]`] >> simp[]
QED

Theorem cse_visit_segment_ordinary:
 !bb es endpoint. cse_visit_segment bb es endpoint ==>
 !k. phi_prefix_length bb.bb_instructions <= k /\ k < endpoint ==>
 ?pre n inst s t post.
 es = pre ++ [CseStep n bb inst s t] ++ post /\
 LENGTH pre = SUC (k - phi_prefix_length bb.bb_instructions) /\
 s.vs_inst_idx = k /\ get_instruction bb k = SOME inst
Proof
 ho_match_mp_tac cse_visit_segment_strongind >> rpt conj_tac
 >- simp[] >> rpt gen_tac >> strip_tac >>
 rename1 `cse_visit_segment bb es endpoint` >>
 qx_gen_tac `usek` >> strip_tac >>
 Cases_on `usek = endpoint`
 >- (gvs[] >> qexistsl [`es`, `n`, `s`, `t`, `[]`] >>
     simp[] >> drule cse_visit_segment_length >> simp[]) >>
 `usek < endpoint` by decide_tac >>
 first_x_assum (qspec_then `usek` mp_tac) >> simp[] >> strip_tac >>
 qexistsl [`pre`, `n'`, `inst'`, `s'`, `t'`,
           `post ++ [CseStep n bb inst s t]`] >> simp[APPEND_ASSOC]
QED

Definition cse_event_covers_def:
 (cse_event_covers (CsePhi n blk s t) bb k inst <=>
   blk = bb /\ k < phi_prefix_length bb.bb_instructions /\
   get_instruction bb k = SOME inst) /\
 (cse_event_covers (CseStep n blk instr s t) bb k inst <=>
   blk = bb /\ instr = inst /\ s.vs_inst_idx = k)
End

Theorem cse_visit_segment_occurrence:
 cse_visit_segment bb es endpoint /\
 get_instruction bb k = SOME inst /\ k < endpoint ==>
 ?ev. MEM ev es /\ cse_event_covers ev bb k inst
Proof
 strip_tac >> Cases_on `k < phi_prefix_length bb.bb_instructions`
 >- (drule cse_visit_segment_phi_head >> strip_tac >>
     qexists `CsePhi n bb s t` >> simp[cse_event_covers_def]) >>
 `phi_prefix_length bb.bb_instructions <= k` by decide_tac >>
 drule cse_visit_segment_ordinary >>
 disch_then (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
 qexists `CseStep n bb inst s t` >> simp[cse_event_covers_def, MEM_APPEND]
QED

Theorem cse_prefix_current_occurrence:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb k = SOME inst /\ k < s.vs_inst_idx ==>
 ?ev. MEM ev events /\ cse_event_covers ev bb k inst
Proof
 strip_tac >> drule_all cse_prefix_visit_segments >> strip_tac >> gvs[] >>
 drule_all cse_visit_segment_occurrence >> strip_tac >>
 qexists `ev` >> simp[MEM_APPEND]
QED

Theorem cse_prefix_completed_occurrences:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events phase ==>
 ?done current.
 events = FLAT (MAP SND done) ++ current /\
 cse_visit_path s0 events =
   MAP (\visit. (FST visit).bb_label) done ++
   [(cse_phase_state phase).vs_current_bb] /\
 (!j bb es k inst. j < LENGTH done /\ EL j done = (bb,es) /\
   get_instruction bb k = SOME inst ==>
   ?ev. MEM ev es /\ MEM ev events /\ cse_event_covers ev bb k inst)
Proof
 strip_tac >> drule_all cse_prefix_visit_segments >> strip_tac >>
 qexistsl [`done`, `current`] >> simp[] >> rpt strip_tac >>
 `MEM (bb,es) done` by metis_tac[MEM_EL] >>
 `cse_visit_segment bb es (LENGTH bb.bb_instructions)` by
   (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
 `k < LENGTH bb.bb_instructions` by gvs[get_instruction_def, AllCaseEqs()] >>
 drule_all cse_visit_segment_occurrence >> strip_tac >>
 qexists `ev` >> simp[] >>
 `MEM es (MAP SND done)` by (simp[MEM_MAP] >> qexists `(bb,es)` >> simp[]) >>
 gvs[MEM_FLAT, MEM_APPEND] >> metis_tac[]
QED

Theorem cse_prefix_event_provenance:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 wf_function fn /\ fn_inst_wf fn ==>
 !ev. MEM ev events ==>
 case ev of
 CsePhi n bb s t =>
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   eval_phis s bb.bb_instructions = OK t
 | CseStep n bb inst s t =>
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME inst /\
   step_inst n ctx inst s = OK t
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
 simp[MEM_APPEND] >> strip_tac >> gvs[] >>
 drule_all cse_prefix_exec_control >> simp[]
QED

Theorem cse_prefix_covered_block:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\
 MEM ev events /\ cse_event_covers ev bb k inst ==>
 MEM bb fn.fn_blocks
Proof
 strip_tac >> drule_all cse_prefix_event_provenance >>
 Cases_on `ev` >> gvs[cse_event_covers_def] >>
 metis_tac[lookup_block_MEM]
QED

Theorem cse_prefix_covered_write:
 cse_event_covers ev bb k inst /\ MEM v inst.inst_outputs ==>
 cse_event_writes ev v
Proof
 Cases_on `ev` >> simp[cse_event_covers_def, cse_event_writes_def] >>
 strip_tac >> gvs[] >> qexists `inst` >> simp[MEM_EL] >>
 qexists `k` >> gvs[get_instruction_def, AllCaseEqs(), EL_TAKE, LENGTH_TAKE, phi_prefix_length_le]
QED

Theorem cse_prefix_segment_block:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\
 cse_visit_segment bb es k /\
 (!ev. MEM ev es ==> MEM ev events) ==>
 MEM bb fn.fn_blocks
Proof
 strip_tac >> drule cse_visit_segment_phi_head >> strip_tac >>
 `MEM (CsePhi n bb s t) events` by metis_tac[MEM] >>
 drule_all cse_prefix_event_provenance >> simp[] >>
 metis_tac[lookup_block_MEM]
QED

Theorem cse_prefix_available_write:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 def_available_at fn bb (SOME inst) v ==>
 ?ev. MEM ev events /\ cse_event_writes ev v
Proof
 strip_tac >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 gvs[def_available_at_def] >>
 Cases_on `def_bb = bb`
 >- (gvs[] >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
       (`MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
        qpat_x_assum `wf_function fn` mp_tac >>
        simp[wf_function_def, fn_inst_ids_distinct_def] >> strip_tac >>
        qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
        qpat_x_assum `MEM bb _` mp_tac >>
        qspec_tac (`fn.fn_blocks`, `bbs`) >>
        Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[]) >>
     `j = s.vs_inst_idx` by
       (gvs[get_instruction_def, AllCaseEqs()] >>
        metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]) >>
     `get_instruction bb i = SOME (EL i bb.bb_instructions)` by
       simp[get_instruction_def] >>
     `i < s.vs_inst_idx` by decide_tac >>
     `?ev. MEM ev events /\ cse_event_covers ev bb i (EL i bb.bb_instructions)` by
       metis_tac[cse_prefix_current_occurrence] >>
     qexists `ev` >> metis_tac[cse_prefix_covered_write]) >>
 `def_bb.bb_label <> bb.bb_label` by
   (strip_tac >>
    `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
      gvs[wf_function_def, fn_labels_def] >>
    `lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb` by
      metis_tac[MEM_lookup_block] >> gvs[]) >>
 drule_all cse_prefix_visit_path >> strip_tac >>
 `MEM def_bb.bb_label (cse_visit_path s0 events)` by
   (qpat_x_assum `fn_dominates fn _ _` mp_tac >>
    simp[fn_dominates_def] >> strip_tac >>
    first_x_assum (qspec_then `cse_visit_path s0 events` mp_tac) >>
    simp[cse_visit_path_def, cse_phase_state_def]) >>
 drule_all cse_prefix_visit_segments >> strip_tac >>
 gvs[cse_phase_state_def, MEM_APPEND, MEM_MAP] >>
 `cse_visit_segment (FST visit) (SND visit)
    (LENGTH (FST visit).bb_instructions)` by
   (qpat_x_assum `EVERY _ done` mp_tac >> simp[EVERY_MEM] >>
    disch_then (qspec_then `visit` mp_tac) >> simp[]) >>
 `!ev. MEM ev (SND visit) ==>
    MEM ev (FLAT (MAP SND done) ++ current)` by
   (simp[MEM_APPEND, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
 `MEM (FST visit) fn.fn_blocks` by
   (irule cse_prefix_segment_block >> metis_tac[]) >>
 `def_bb = FST visit` by
   (`ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
      gvs[wf_function_def, fn_labels_def] >>
    `lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb` by
      metis_tac[MEM_lookup_block] >>
    `lookup_block (FST visit).bb_label fn.fn_blocks = SOME (FST visit)` by
      metis_tac[MEM_lookup_block] >> gvs[]) >>
 gvs[] >>
 `?k. k < LENGTH (FST visit).bb_instructions /\
       EL k (FST visit).bb_instructions = def_inst` by metis_tac[MEM_EL] >>
 `get_instruction (FST visit) k = SOME def_inst` by simp[get_instruction_def] >>
 drule_all cse_visit_segment_occurrence >> strip_tac >>
 qexists `ev` >> metis_tac[cse_prefix_covered_write, MEM_APPEND]
QED

Theorem cse_prefix_available_last_write:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 def_available_at fn bb (SOME inst) v ==>
 ?pre ev post. events = pre ++ [ev] ++ post /\
 cse_event_writes ev v /\ EVERY (\e. ~cse_event_writes e v) post /\
 lookup_var v s = lookup_var v (cse_event_output ev)
Proof
 strip_tac >> drule_all cse_prefix_available_write >> strip_tac >>
 drule cse_prefix_last_write_or_initial >>
 disch_then (qspec_then `v` mp_tac) >>
 simp[cse_phase_state_def] >> strip_tac
 >- (gvs[EVERY_MEM] >> metis_tac[]) >>
 metis_tac[]
QED

Theorem cse_prefix_ordinary_use_last_write:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
 ?pre ev post. events = pre ++ [ev] ++ post /\
 cse_event_writes ev v /\ EVERY (\e. ~cse_event_writes e v) post /\
 lookup_var v s = lookup_var v (cse_event_output ev)
Proof
 strip_tac >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `MEM inst bb.bb_instructions` by
   (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
 `def_available_at fn bb (SOME inst) v` by
   (qpat_x_assum `cse_reachable_wf_ssa fn` mp_tac >>
    simp[cse_reachable_wf_ssa_def] >> strip_tac >>
    first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >> simp[]) >>
 irule cse_prefix_available_last_write >> metis_tac[]
QED

Theorem cse_prefix_writing_occurrence:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\
 MEM ev events /\ cse_event_writes ev v ==>
 ?bb k inst. MEM bb fn.fn_blocks /\ get_instruction bb k = SOME inst /\
 MEM v inst.inst_outputs /\ cse_event_covers ev bb k inst
Proof
 strip_tac >> drule_all cse_prefix_event_provenance >>
 Cases_on `ev` >> gvs[cse_event_writes_def, cse_event_covers_def] >> strip_tac
 >- (rename1 `MEM inst (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` >>
     `?k. k < LENGTH (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
       EL k (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst` by
       metis_tac[MEM_EL] >>
     gvs[LENGTH_TAKE, phi_prefix_length_le, EL_TAKE] >>
     qexistsl [`k`, `EL k bb.bb_instructions`] >>
     `k < LENGTH bb.bb_instructions` by
       (mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_length_le) >> decide_tac) >>
     simp[get_instruction_def] >> metis_tac[lookup_block_MEM]) >>
 metis_tac[lookup_block_MEM]
QED

Theorem cse_prefix_writing_static_definer:
 wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\
 MEM ev events /\ cse_event_writes ev v /\
 MEM definst (fn_insts fn) /\ MEM v definst.inst_outputs ==>
 ?bb k. MEM bb fn.fn_blocks /\ get_instruction bb k = SOME definst /\
 cse_event_covers ev bb k definst
Proof
 strip_tac >> drule_all cse_prefix_writing_occurrence >> strip_tac >>
 `MEM inst (fn_insts_blocks fn.fn_blocks)` by
   (`MEM inst bb.bb_instructions` by
      (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
    qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
    qspec_tac (`fn.fn_blocks`, `bbs`) >>
    Induct >> simp[fn_insts_blocks_def] >> rpt strip_tac >> gvs[]) >>
 `inst = definst` by
   (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[]) >>
 metis_tac[]
QED

Theorem cse_available_before_final_nonwriter[local]:
 def_available_at fn bb NONE v /\
 get_instruction bb k = SOME term /\ SUC k = LENGTH bb.bb_instructions /\
 term.inst_outputs = [] ==>
 def_available_at fn bb (SOME term) v
Proof
 simp[def_available_at_def] >> strip_tac >>
 qexistsl [`def_bb`, `def_inst`] >> simp[] >> strip_tac >> gvs[] >>
 `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = def_inst` by
   metis_tac[MEM_EL] >>
 `i <> k` by (strip_tac >> gvs[get_instruction_def]) >>
 qexistsl [`i`, `k`] >> gvs[get_instruction_def] >> decide_tac
QED

Theorem cse_prefix_phi_incoming_last_write:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n pred_bb p) /\
 get_instruction pred_bb p.vs_inst_idx = SOME term /\
 step_inst n ctx term p = OK s /\ is_terminator term.inst_opcode /\
 ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI /\
 MEM (pred_bb.bb_label,v) (phi_pairs phi.inst_operands) ==>
 ?pre ev post. events ++ [CseStep n pred_bb term p s] = pre ++ [ev] ++ post /\
 cse_event_writes ev v /\ EVERY (\e. ~cse_event_writes e v) post /\
 lookup_var v s = lookup_var v (cse_event_output ev)
Proof
 strip_tac >> drule_all cse_prefix_exec_control >> strip_tac >>
 drule_all cse_terminator_boundary >> strip_tac >>
 `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
 `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by gvs[] >>
 `phi_edge_uses_wf fn bb phi` by
   (qpat_x_assum `cse_reachable_wf_ssa fn` mp_tac >>
    simp[cse_reachable_wf_ssa_def] >> strip_tac >>
    first_x_assum (qspecl_then [`bb`, `phi`] mp_tac) >> simp[]) >>
 `?incoming_bb. MEM incoming_bb fn.fn_blocks /\
   incoming_bb.bb_label = pred_bb.bb_label /\
   def_available_at fn incoming_bb NONE v` by
   (qpat_x_assum `phi_edge_uses_wf fn bb phi` mp_tac >>
    simp[phi_edge_uses_wf_def] >> strip_tac >>
    first_x_assum (qspecl_then [`pred_bb.bb_label`, `v`] mp_tac) >>
    simp[] >> metis_tac[]) >>
 `incoming_bb = pred_bb` by
   (`ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
      gvs[wf_function_def, fn_labels_def] >>
    `lookup_block incoming_bb.bb_label fn.fn_blocks = SOME incoming_bb` by
      metis_tac[MEM_lookup_block] >> gvs[]) >>
 `inst_wf term` by
   (qpat_x_assum `fn_inst_wf fn` mp_tac >> simp[fn_inst_wf_def] >>
    disch_then (qspecl_then [`pred_bb`, `term`] mp_tac) >>
    impl_tac >- (conj_tac >- metis_tac[lookup_block_MEM] >>
                 gvs[get_instruction_def, AllCaseEqs()] >>
                 simp[MEM_EL] >> qexists `p.vs_inst_idx` >> simp[]) >> simp[]) >>
 `term.inst_outputs = []` by metis_tac[terminator_no_outputs] >>
 `def_available_at fn pred_bb (SOME term) v` by
   (irule cse_available_before_final_nonwriter >> metis_tac[]) >>
 drule_all cse_prefix_available_last_write >> strip_tac >>
 `lookup_var v s = lookup_var v p` by
   (drule_all step_terminator_preserves_vars >> simp[]) >>
 qexistsl [`pre`, `ev`, `post ++ [CseStep n pred_bb term p s]`] >>
 simp[APPEND_ASSOC, EVERY_APPEND, cse_event_writes_def, lookup_var_def] >>
 gvs[lookup_var_def]
QED

Theorem cse_path_prefix_projection:
 !left a tail. is_fn_path fn ((left ++ [a]) ++ tail) ==>
 is_fn_path fn (left ++ [a])
Proof
 Induct >- simp[is_fn_path_def] >> rpt gen_tac >>
 Cases_on `left` >> simp[is_fn_path_def] >> rpt strip_tac >>
 fs[APPEND] >> first_x_assum irule >> qexists_tac `tail` >> simp[]
QED

Theorem cse_first_dominator_excludes[local]:
 fn_dominates fn d a /\ d <> a /\
 is_fn_path fn (pre ++ [d]) /\
 fn_entry_label fn = SOME (HD (pre ++ [d])) /\ ~MEM d pre ==>
 ~MEM a pre
Proof
 rpt strip_tac >>
 imp_res_tac MEM_SPLIT >>
 rename1 `pre = left ++ a::right` >>
 `is_fn_path fn (left ++ [a])` by
   (irule cse_path_prefix_projection >>
    qexists_tac `right ++ [d]` >> fs[APPEND_ASSOC, APPEND]) >>
 `fn_entry_label fn = SOME (HD (left ++ [a]))` by
   (Cases_on `left` >> fs[]) >>
 fs[fn_dominates_def] >>
 first_x_assum (qspec_then `left ++ [a]` mp_tac) >>
 simp[] >> fs[]
QED

Theorem cse_mem_first_split[local]:
 !xs d. MEM d xs ==> ?pre post. xs = pre ++ d::post /\ ~MEM d pre
Proof
 Induct >- simp[] >> qx_gen_tac `h` >> qx_gen_tac `d` >>
 Cases_on `h = d`
 >- (strip_tac >> qexistsl [`[]`, `xs`] >> simp[]) >>
 simp[] >> strip_tac >> first_x_assum drule >> strip_tac >>
 qexistsl [`h::pre`, `post`] >> simp[]
QED

Theorem cse_path_splice[local]:
 !pre d tail. is_fn_path fn (pre ++ [d]) /\ is_fn_path fn (d::tail) ==>
 is_fn_path fn (pre ++ d::tail)
Proof
 Induct >- simp[] >> rpt gen_tac >>
 Cases_on `pre` >> simp[is_fn_path_def] >> rpt strip_tac >>
 fs[APPEND] >> first_x_assum irule >> simp[]
QED

Theorem cse_strict_dominator_suffix_crossing:
 fn_dominates fn d a /\ d <> a /\ fn_dominates fn a c /\
 is_fn_path fn (d::tail) /\ LAST (d::tail) = c ==>
 MEM a (d::tail)
Proof
 rpt strip_tac >>
 `fn_reachable fn d` by metis_tac[fn_dominates_dom_reachable] >>
 fs[fn_reachable_def] >> drule rtc_to_fn_path >> strip_tac >>
 `MEM d path` by (Cases_on `path` >> gvs[rich_listTheory.MEM_LAST]) >>
 drule cse_mem_first_split >> strip_tac >>
 `is_fn_path fn (pre ++ [d])` by
   (irule cse_path_prefix_projection >> qexists_tac `post` >> fs[APPEND_ASSOC]) >>
 `fn_entry_label fn = SOME (HD (pre ++ [d]))` by
   (Cases_on `pre` >> gvs[]) >>
 `~MEM a pre` by metis_tac[cse_first_dominator_excludes] >>
 `is_fn_path fn (pre ++ d::tail)` by metis_tac[cse_path_splice] >>
 `fn_entry_label fn = SOME (HD (pre ++ d::tail))` by
   (Cases_on `pre` >> gvs[]) >>
 `LAST (pre ++ d::tail) = c` by
   (metis_tac[rich_listTheory.LAST_APPEND_NOT_NIL, NOT_CONS_NIL]) >>
 qpat_x_assum `fn_dominates fn a c` mp_tac >>
 simp[fn_dominates_def] >> strip_tac >>
 first_x_assum (qspec_then `pre ++ d::tail` mp_tac) >>
 fs[APPEND]
QED

(* Syntactic PHI expansion shares one atomic event number. NONE denotes
   padding, not an executed instruction. The final cursor is separate. *)
Definition cse_event_points_def:
 (cse_event_points j (CsePhi n bb s t) =
   GENLIST (\k. ((bb.bb_label,k),SOME (j,k)))
     (phi_prefix_length bb.bb_instructions)) /\
 (cse_event_points j (CseStep n bb inst s t) =
   [((bb.bb_label,s.vs_inst_idx),SOME (j,s.vs_inst_idx))] ++
   if is_terminator inst.inst_opcode
   then [((bb.bb_label,LENGTH bb.bb_instructions),NONE)] else [])
End

Definition cse_history_points_def:
 (cse_history_points j [] = []) /\
 (cse_history_points j (ev::events) =
   cse_event_points j ev ++ cse_history_points (SUC j) events)
End

Definition cse_phase_point_def:
 (cse_phase_point (CseRun n s) = (s.vs_current_bb,s.vs_inst_idx)) /\
 (cse_phase_point (CseExec n bb s) = (bb.bb_label,s.vs_inst_idx))
End

Definition cse_project_trace_def:
 cse_project_trace events phase =
   MAP FST (cse_history_points 0 events) ++ [cse_phase_point phase]
End

Theorem cse_history_points_append:
 !xs j ys. cse_history_points j (xs ++ ys) =
 cse_history_points j xs ++ cse_history_points (j + LENGTH xs) ys
Proof
 Induct >> simp[cse_history_points_def] >> rpt gen_tac >>
 simp[listTheory.APPEND_ASSOC, arithmeticTheory.ADD_CLAUSES]
QED

Theorem cse_project_trace_last:
 LAST (cse_project_trace events phase) = cse_phase_point phase
Proof
 simp[cse_project_trace_def]
QED

Theorem cse_event_points_index:
 !ev start p j k. MEM (p,SOME (j,k)) (cse_event_points start ev) ==>
 j = start
Proof
 Cases >> simp[cse_event_points_def, MEM_GENLIST] >> rpt gen_tac >>
 Cases_on `is_terminator i.inst_opcode` >> simp[] >> metis_tac[]
QED

Theorem cse_history_points_occurrence:
 !events start p j k.
 MEM (p,SOME (j,k)) (cse_history_points start events) ==>
 ?pre ev post. events = pre ++ ev::post /\ j = start + LENGTH pre /\
   MEM (p,SOME (j,k)) (cse_event_points j ev)
Proof
 Induct >> simp[cse_history_points_def] >> rpt gen_tac >> strip_tac
 >- (drule cse_event_points_index >> strip_tac >>
     qexistsl_tac [`[]`, `h`, `events`] >> gvs[]) >>
 first_x_assum drule >> strip_tac >>
 qexistsl_tac [`h::pre`, `ev`, `post`] >>
 simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem cse_static_trace_advance:
 !n ps lbl k bb fn.
 cse_static_trace fn ps /\ LAST ps = (lbl,k) /\
 lookup_block lbl fn.fn_blocks = SOME bb /\ k + n <= LENGTH bb.bb_instructions ==>
 cse_static_trace fn
   (ps ++ GENLIST (\i. (lbl,k + SUC i)) n)
Proof
 Induct >> simp[GENLIST] >> rpt gen_tac >> strip_tac >>
 `cse_static_trace fn (ps ++ GENLIST (\i. (lbl,k + SUC i)) n)` by
   (first_x_assum irule >> simp[]) >>
 rewrite_tac[rich_listTheory.SNOC_APPEND, APPEND_ASSOC, arithmeticTheory.ADD_CLAUSES] >>
 irule (cj 2 cse_static_trace_rules) >>
 conj_tac >- (qexists_tac `bb` >> simp[]) >>
 conj_tac >- (Cases_on `n` >> simp[GENLIST]) >>
 gvs[arithmeticTheory.ADD_CLAUSES]
QED

Theorem cse_phi_points_cursor[local]:
 !n lbl. GENLIST (\k. (lbl,k)) n ++ [(lbl,n)] =
   (lbl,0)::GENLIST (\i. (lbl,SUC i)) n
Proof
 Induct >> simp[GENLIST, rich_listTheory.SNOC_APPEND] >>
 rpt gen_tac >> first_x_assum (qspec_then `lbl` mp_tac) >>
 simp[APPEND_ASSOC]
QED

Theorem cse_static_trace_phi:
 cse_static_trace fn (ps ++ [(bb.bb_label,0)]) /\
 lookup_block bb.bb_label fn.fn_blocks = SOME bb ==>
 cse_static_trace fn (ps ++ GENLIST (\k. (bb.bb_label,k))
   (phi_prefix_length bb.bb_instructions) ++
   [(bb.bb_label,phi_prefix_length bb.bb_instructions)])
Proof
 strip_tac >> rewrite_tac[GSYM APPEND_ASSOC, cse_phi_points_cursor] >>
 qspecl_then
   [`phi_prefix_length bb.bb_instructions`, `ps ++ [(bb.bb_label,0)]`,
    `bb.bb_label`, `0`, `bb`, `fn`] mp_tac cse_static_trace_advance >>
 rewrite_tac[GSYM APPEND_ASSOC, APPEND, arithmeticTheory.ADD] >>
 simp[phi_prefix_length_le]
QED

Theorem cse_prefix_project_trace:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 wf_function fn /\ fn_inst_wf fn ==>
 case phase of
   CseRun n s => !bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
     s.vs_inst_idx = 0 /\ cse_static_trace fn (cse_project_trace events phase)
 | CseExec n bb s => cse_static_trace fn (cse_project_trace events phase)
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac
 >- (rpt gen_tac >> strip_tac >> strip_tac >>
     simp[cse_project_trace_def, cse_history_points_def, cse_phase_point_def] >>
     rpt strip_tac >> irule (cj 1 cse_static_trace_rules) >> metis_tac[])
 >- suspend "phi"
 >- suspend "ordinary"
 >> suspend "branch"
QED
Resume cse_prefix_project_trace[phi]:
 rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
 `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
 gvs[cse_project_trace_def, cse_history_points_append,
     cse_history_points_def, cse_event_points_def, cse_phase_point_def,
     MAP_GENLIST, combinTheory.o_DEF] >>
 qpat_assum `bb.bb_label = s.vs_current_bb`
   (fn th => rewrite_tac[GSYM th]) >>
 irule cse_static_trace_phi >> simp[]
QED
Resume cse_prefix_project_trace[ordinary]:
 rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 `s.vs_inst_idx < LENGTH bb.bb_instructions` by
   gvs[get_instruction_def, AllCaseEqs()] >>
 gvs[cse_project_trace_def, cse_history_points_append,
     cse_history_points_def, cse_event_points_def, cse_phase_point_def] >>
 irule (cj 2 cse_static_trace_rules) >> simp[] >> metis_tac[]
QED
Resume cse_prefix_project_trace[branch]:
 rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 drule_all cse_terminator_boundary >> strip_tac >>
 drule_all cse_terminator_cfg_edge >> strip_tac >>
 `inst.inst_opcode <> INVOKE` by
   (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
 `step_inst_base inst s = OK t` by
   gvs[step_inst_def] >>
 `t.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
 simp[] >> rpt strip_tac >>
 gvs[cse_project_trace_def, cse_history_points_append,
     cse_history_points_def, cse_event_points_def, cse_phase_point_def] >>
 irule (cj 3 cse_static_trace_rules) >>
 conj_tac >- metis_tac[] >>
 reverse conj_tac >- (simp[] >> metis_tac[]) >>
 qpat_assum `SUC s.vs_inst_idx = LENGTH bb.bb_instructions`
   (fn th => rewrite_tac[GSYM th]) >>
 `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
 `cse_static_trace fn
    ((MAP FST (cse_history_points 0 events) ++
      [(s.vs_current_bb,s.vs_inst_idx)]) ++
      [(s.vs_current_bb,SUC s.vs_inst_idx)])` suffices_by
    rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
 irule (cj 2 cse_static_trace_rules) >> simp[] >> metis_tac[]
QED
Finalise cse_prefix_project_trace

Theorem cse_prefix_project_exec:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) ==>
 cse_static_trace fn (cse_project_trace events (CseExec n bb s)) /\
 LAST (cse_project_trace events (CseExec n bb s)) = (bb.bb_label,s.vs_inst_idx)
Proof
 strip_tac >> drule cse_prefix_project_trace >>
 simp[cse_project_trace_last, cse_phase_point_def]
QED

Theorem cse_prefix_project_run:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseRun n s) /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
 cse_static_trace fn (cse_project_trace events (CseRun n s)) /\
 LAST (cse_project_trace events (CseRun n s)) = (bb.bb_label,0)
Proof
 strip_tac >> drule cse_prefix_project_trace >> simp[] >>
 strip_tac >>
 simp[cse_project_trace_last, cse_phase_point_def] >>
 metis_tac[lookup_block_label]
QED

Theorem cse_event_points_covers:
 MEM (p,SOME ((j:num),k)) (cse_event_points j ev) ==>
 ?bb inst. p = (bb.bb_label,k) /\ cse_event_covers ev bb k inst
Proof
 Cases_on `ev` >> simp[cse_event_points_def, MEM_GENLIST] >>
 rpt strip_tac
 >- (gvs[] >> rename1 `k < phi_prefix_length bb.bb_instructions` >>
     qexistsl_tac [`bb`, `EL k bb.bb_instructions`] >>
     simp[cse_event_covers_def, get_instruction_def] >>
     metis_tac[phi_prefix_length_le, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
 gvs[cse_event_covers_def, AllCaseEqs()] >>
 Cases_on `is_terminator i.inst_opcode` >> gvs[]
QED

Theorem cse_history_points_covers:
 MEM (p,SOME (j,k)) (cse_history_points 0 events) ==>
 j < LENGTH events /\
 ?bb inst. p = (bb.bb_label,k) /\ cse_event_covers (EL j events) bb k inst
Proof
 strip_tac >> drule cse_history_points_occurrence >> strip_tac >> gvs[] >>
 simp[listTheory.EL_APPEND_EQN] >>
 irule cse_event_points_covers >> metis_tac[]
QED

Theorem cse_event_points_padding:
 MEM (p,NONE) (cse_event_points j ev) ==>
 ?n bb inst s t. ev = CseStep n bb inst s t /\
   is_terminator inst.inst_opcode /\ p = (bb.bb_label,LENGTH bb.bb_instructions)
Proof
 Cases_on `ev` >> simp[cse_event_points_def, MEM_GENLIST] >>
 Cases_on `is_terminator i.inst_opcode` >> simp[] >> metis_tac[]
QED

Theorem cse_history_points_padding:
 !events start. MEM (p,NONE) (cse_history_points start events) ==>
 ?j n bb inst s t. j < LENGTH events /\
   EL j events = CseStep n bb inst s t /\
   is_terminator inst.inst_opcode /\ p = (bb.bb_label,LENGTH bb.bb_instructions)
Proof
 Induct >> simp[cse_history_points_def] >> rpt gen_tac >> strip_tac
 >- (drule cse_event_points_padding >> strip_tac >>
     qexists_tac `0` >> simp[] >> metis_tac[]) >>
 first_x_assum drule >> strip_tac >>
 qexists_tac `SUC j` >> simp[] >> metis_tac[]
QED

Theorem cse_history_points_cut:
 MEM (p,SOME (j,k)) (cse_history_points 0 events) ==>
 ?pre ev post left right.
   events = pre ++ ev::post /\ j = LENGTH pre /\
   cse_event_points j ev = left ++ (p,SOME (j,k))::right /\
   cse_history_points 0 events =
     cse_history_points 0 pre ++ left ++
       (p,SOME (j,k))::(right ++ cse_history_points (SUC j) post)
Proof
 strip_tac >> drule cse_history_points_occurrence >> strip_tac >> gvs[] >>
 qpat_x_assum `MEM _ (cse_event_points _ _)` mp_tac >>
 rewrite_tac[MEM_SPLIT] >>
 disch_then (qx_choose_then `left` (qx_choose_then `right` assume_tac)) >>
 qexistsl_tac [`pre`, `ev`, `post`, `left`, `right`] >>
 simp[cse_history_points_append, cse_history_points_def, APPEND_ASSOC,
      arithmeticTheory.ADD1]
QED

(* Synchronization audit (C2.7.2.8.6). These are proposed obligations,
   NOT theorems or assumptions of the projection results above.

   Abbreviations below are textual: D = dfg_build_function fn,
   C = compute_canon D (avail_analyze fn) fn, and
   A = ae_lookup_inst fn bb.bb_label s.vs_inst_idx.

   Candidate consumer boundary (universally quantified free variables):

     wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
     (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> ALLOCA) /\
     cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
     get_instruction bb s.vs_inst_idx = SOME use /\
     ~cse_skip_opcode use.inst_opcode /\
     ~is_terminator use.inst_opcode /\ use.inst_opcode <> INVOKE /\
     ~avail_nonidempotent use.inst_opcode /\
     cse_lookup C D A use = SOME (src,e)
     ==>
     ?pre post m sb u v pi.
       events = pre ++ [CseStep m sb src u v] ++ post /\
       cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
       EVERY (cse_event_survives e) post /\
       src.inst_opcode = use.inst_opcode /\
       LENGTH src.inst_operands = LENGTH use.inst_operands /\
       (pi = GENLIST I (LENGTH use.inst_operands) \/
        (is_commutative use.inst_opcode /\
         LENGTH use.inst_operands = 2 /\ pi = [1;0])) /\
       (!k. k < LENGTH use.inst_operands ==>
          eval_operand (EL k use.inst_operands) s =
          eval_operand (EL (EL k pi) src.inst_operands) u)

   This existential chooses a suitable historical source occurrence, not
   every occurrence with the same instruction ID. Its event number is
   LENGTH pre, and its input cut is pre; the consumer cut is events.
   Source/output binding persistence is a SEPARATE needed boundary:

     same hypotheses and chosen witness, src.inst_outputs = [out] ==>
       lookup_var out s = lookup_var out v.

   Present facts supply birth plus root-effect-free suffix
   (cse_prefix_exec_avail_history), static representative occurrences on
   each projected cut (compute_canon_representative_occurrence), numbered
   points (cse_history_points_cut/covers), and last-write lookup transport
   (cse_prefix_ordinary_use_last_write). They do NOT supply the equalities
   of eval_operand in the candidate or a write-free suffix for out.

   Exact missing alignment shape, for a representative static ID r:
     ?j. j < LENGTH pre /\
         cse_event_covers (EL j events) rb rk ri /\ ri.inst_id = r /\
         (* the operand's ASSIGN derivation reaches THIS occurrence *)
         eval_operand source_op u = representative_value /\
         eval_operand consumer_op s = representative_value.
   The two equalities here are the obligation, not admissible additional
   hypotheses. Existing preorder theorems only supply separate witnesses
   j_source and j_consumer and cannot equate representative_value.

   Adversarial trace: R_0; copy_0 := R_0; source_0 := f(copy_0);
   R_1; consumer := f(R_1). Static operand_producer(copy) and
   operand_producer(R) agree while values need not. This is a diagnostic
   trace, not a verified CFG counterexample: all-path availability may
   exclude it. To exclude it formally needs a source-availability barrier
   at R_1 plus strict static order R < copy < source. Projected points
   alone do not assert availability of source at that intermediate cut.
   Replacing R by a canonical-equivalent instruction adds the independent
   canonical-fold collision interpretation obligation.

   Cases still requiring proof:
   - ASSIGN: resolve the operand at the copy INPUT cut, not the later
     consumer cut; carry its defining write occurrence through the chain.
   - PHI: all output slots share one event number but different k. Incoming
     values use cse_phi_reads at the pre-batch/predecessor snapshot, never
     the output of an earlier syntactically expanded PHI. Incoming last
     writes are available via cse_prefix_phi_incoming_last_write.
   - NONE producer: literal values follow mk_expr matching/permutation,
     NOT operand_ids_match alone. Labels evaluate through vs_labels, not
     as word literals. Undefined Var operands require wf_ssa/use dominance
     plus DFG completeness to rule out, not an empty initial map premise.
   - Canonical fold: identity/skip cases are structural; recording an
     expression match requires the semantic alignment above recursively.
     Later map updates preserve static order but not yet a value meaning.
   Constructor audit: entry has no available source; ordinary steps need
   the alignment/barrier argument before replay; PHI needs atomic incoming
   alignment; branch needs transport across the selected edge. Root-effect
   survival alone closes none of these variable epoch obligations.
   No closed induction invariant is claimed by this audit. *)

(* Numbered last-write sub-interface needed at each variable operand:
     cse_prefix ctx fn fuel0 s0 cut (CseExec n bb s) /\
     wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
     get_instruction bb s.vs_inst_idx = SOME inst /\
     inst.inst_opcode <> PHI /\ MEM (Var x) inst.inst_operands ==>
     ?j. j < LENGTH cut /\ cse_event_writes (EL j cut) x /\
       EVERY (\ev. ~cse_event_writes ev x) (DROP (SUC j) cut) /\
       lookup_var x s = lookup_var x (cse_event_output (EL j cut)).
   This is a numbered reformulation of the proved ordinary-use last-write
   theorem. Apply independently to cut=pre and cut=events. It identifies
   the two LAST writes, not the earlier representative occurrence reached
   through ASSIGN; equality between those derivations remains missing. *)

Definition cse_phase_has_source_def:
 (cse_phase_has_source fn (CseExec n bb s) e src <=>
   ?xs. FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx) e = SOME xs /\
     MEM src xs) /\
 (cse_phase_has_source fn (CseRun n s) e src <=>
   ?bb xs. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     FLOOKUP (ae_lookup_inst fn s.vs_current_bb 0) e = SOME xs /\ MEM src xs)
End

Theorem cse_prefix_phase_unique[local]:
 cse_prefix ctx fn fuel0 s0 events ph /\
 cse_prefix ctx fn fuel0 s0 events ph' ==> ph = ph'
Proof
 once_rewrite_tac[cse_prefix_cases] >>
 simp[GSYM rich_listTheory.SNOC_APPEND] >>
 rpt strip_tac >> gvs[]
QED

Theorem cse_source_interval_snoc[local]:
 cse_prefix ctx fn fuel0 s0 (events ++ [ev]) phase /\
 cse_phase_has_source fn phase e src /\
 (!k ph. (birth_index:num) < k /\ k <= LENGTH events /\
    cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
    cse_phase_has_source fn ph e src) ==>
 !k ph. (birth_index:num) < k /\ k <= LENGTH (events ++ [ev]) /\
    cse_prefix ctx fn fuel0 s0 (TAKE k (events ++ [ev])) ph ==>
    cse_phase_has_source fn ph e src
Proof
 rpt strip_tac >> Cases_on `k <= LENGTH events`
 >- (gvs[TAKE_APPEND1] >> first_x_assum irule >> metis_tac[]) >>
 `k = LENGTH (events ++ [ev])` by (fs[] >> decide_tac) >>
 gvs[TAKE_LENGTH_ID_rwt] >> metis_tac[cse_prefix_phase_unique]
QED

Theorem cse_prefix_source_interval:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 wf_function fn /\ fn_inst_wf fn ==>
 !e src. cse_phase_has_source fn phase e src ==>
 ?pre post m sb u v.
   events = pre ++ [CseStep m sb src u v] ++ post /\
   cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
   avail_source_birth (dfg_build_function fn) e src src /\
   EVERY (cse_event_survives e) post /\
   (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
      cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
      cse_phase_has_source fn ph e src)
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac
 >- suspend "entry"
 >- suspend "phi"
 >- suspend "ordinary"
 >> suspend "branch"
QED
Resume cse_prefix_source_interval[entry]:
 rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
 strip_tac >>
 `cse_prefix ctx fn fuel0 s0 [] (CseRun fuel0 s0)` by
   simp[cse_prefix_empty] >>
 gvs[cse_phase_has_source_def] >>
 drule_all cse_prefix_run_avail_history >>
 simp[cse_source_history_def]
QED
Resume cse_prefix_source_interval[phi]:
 rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 drule_all cse_prefix_run_control >> strip_tac >>
 `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
 drule_all cse_prefix_run_source_history >> strip_tac >>
 drule_all cse_avail_atomic_phi_some >> strip_tac >>
 gvs[cse_phase_has_source_def,
     availExprDefsTheory.ae_lookup_inst_def,
     availExprDefsTheory.avail_unwrap_def] >>
 qpat_x_assum `!e' src'. _ ==> ?pre post m sb u v. _`
   (qspecl_then [`e`, `src`] mp_tac) >>
 (impl_tac >- metis_tac[]) >> strip_tac >>
 `!k ph. LENGTH pre < k /\ k <= LENGTH (events ++ [CsePhi fuel bb s t]) /\
    cse_prefix ctx fn fuel0 s0 (TAKE k (events ++ [CsePhi fuel bb s t])) ph ==>
    cse_phase_has_source fn ph e src` by
   (match_mp_tac (Q.INST
      [`phase` |-> `CseExec fuel bb (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)`]
      cse_source_interval_snoc) >>
    conj_tac >- metis_tac[cse_prefix_phi_extend] >>
    conj_tac
    >- (simp[cse_phase_has_source_def, availExprDefsTheory.ae_lookup_inst_def,
             availExprDefsTheory.avail_unwrap_def] >> metis_tac[]) >>
    first_assum MATCH_ACCEPT_TAC) >>
 qexistsl_tac [`pre`, `post ++ [CsePhi fuel bb s t]`, `m`, `sb`, `u`, `v`] >>
 gvs[APPEND_ASSOC, cse_event_survives_def] >> first_assum MATCH_ACCEPT_TAC
QED
Resume cse_prefix_source_interval[ordinary]:
 rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 drule_all cse_prefix_exec_source_history >> strip_tac >>
 `s.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL s.vs_inst_idx bb.bb_instructions = inst` by
   gvs[get_instruction_def, AllCaseEqs()] >>
 `SUC s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
 gvs[] >> drule_all cse_avail_at_intra >>
 simp[availExprDefsTheory.avail_transfer_opt_def] >> strip_tac >>
 gvs[cse_phase_has_source_def, availExprDefsTheory.ae_lookup_inst_def,
     availExprDefsTheory.avail_unwrap_def] >>
 rename1 `FLOOKUP (avail_transfer_inst d j a) e = SOME xs` >>
 qspecl_then [`d`, `j`, `a`, `e`, `src`] mp_tac cse_transfer_source_cases >>
 (impl_tac >- metis_tac[]) >> strip_tac
 >- suspend "inherited"
 >> suspend "birth"
QED
Resume cse_prefix_source_interval[inherited]:
 qpat_x_assum `!e' src'. _ ==> ?pre post m sb u v. _`
   (qspecl_then [`e`, `src`] mp_tac) >>
 (impl_tac >- metis_tac[]) >> strip_tac >>
 `!k ph. LENGTH pre < k /\ k <= LENGTH (events ++ [CseStep fuel bb j s t]) /\
    cse_prefix ctx fn fuel0 s0 (TAKE k (events ++ [CseStep fuel bb j s t])) ph ==>
    cse_phase_has_source fn ph e src` by
   (match_mp_tac (Q.INST
      [`phase` |-> `CseExec fuel bb (t with vs_inst_idx := SUC s.vs_inst_idx)`]
      cse_source_interval_snoc) >>
    conj_tac >- metis_tac[cse_prefix_ordinary_extend] >>
    conj_tac
    >- (simp[cse_phase_has_source_def, availExprDefsTheory.ae_lookup_inst_def,
             availExprDefsTheory.avail_unwrap_def] >> metis_tac[]) >>
    first_assum MATCH_ACCEPT_TAC) >>
 qexistsl_tac [`pre`, `post ++ [CseStep fuel bb j s t]`, `m`, `sb`, `u`, `v`] >>
 gvs[APPEND_ASSOC, cse_event_survives_def] >> first_assum MATCH_ACCEPT_TAC
QED
Resume cse_prefix_source_interval[birth]:
 `src = j` by fs[availExprProofsTheory.avail_source_birth_def] >>
 gvs[] >> qexistsl_tac [`events`, `[]`, `fuel`, `bb`, `s`, `t`] >>
 simp[] >> rpt strip_tac >>
 `k = LENGTH (events ++ [CseStep fuel bb j s t])` by (simp[] >> decide_tac) >>
 gvs[TAKE_LENGTH_ID_rwt] >>
 `ph = CseExec fuel bb (t with vs_inst_idx := SUC s.vs_inst_idx)` by
   metis_tac[cse_prefix_phase_unique, cse_prefix_ordinary_extend] >>
 gvs[cse_phase_has_source_def, availExprDefsTheory.ae_lookup_inst_def,
     availExprDefsTheory.avail_unwrap_def] >> metis_tac[]
QED
Resume cse_prefix_source_interval[branch]:
 rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 drule_all cse_prefix_exec_source_history >> strip_tac >>
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
 gvs[cse_phase_has_source_def] >>
 drule_all cse_avail_boundary_member >> strip_tac >>
 drule_all cse_avail_entry_predecessor >> strip_tac >>
 gvs[availExprDefsTheory.ae_lookup_inst_def,
     availExprDefsTheory.avail_unwrap_def] >>
 rename1 `step_inst fuel ctx j s = OK t` >>
 qpat_x_assum `!e' src'. _ ==> ?pre post m sb u v. _`
   (qspecl_then [`e`, `src`] mp_tac) >>
 (impl_tac >- metis_tac[]) >> strip_tac >>
 `!k ph. LENGTH pre < k /\ k <= LENGTH (events ++ [CseStep fuel bb j s t]) /\
    cse_prefix ctx fn fuel0 s0 (TAKE k (events ++ [CseStep fuel bb j s t])) ph ==>
    cse_phase_has_source fn ph e src` by
   (match_mp_tac (Q.INST [`phase` |-> `CseRun fuel t`]
      cse_source_interval_snoc) >>
    conj_tac >- metis_tac[cse_prefix_branch_extend] >>
    conj_tac
    >- (simp[cse_phase_has_source_def, availExprDefsTheory.ae_lookup_inst_def,
             availExprDefsTheory.avail_unwrap_def] >> metis_tac[]) >>
    first_assum MATCH_ACCEPT_TAC) >>
 qexistsl_tac [`pre`, `post ++ [CseStep fuel bb j s t]`, `m`, `sb`, `u`, `v`] >>
 gvs[APPEND_ASSOC, cse_event_survives_def,
     availExprProofsTheory.avail_source_survives_def] >>
 first_assum MATCH_ACCEPT_TAC
QED
Finalise cse_prefix_source_interval

Theorem cse_prefix_exec_avail_interval:
 !ctx fn fuel0 s0 events n bb s e src xs.
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx) e = SOME xs /\ MEM src xs ==>
 ?pre post m sb u v.
   events = pre ++ [CseStep m sb src u v] ++ post /\
   cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
   avail_source_birth (dfg_build_function fn) e src src /\
   EVERY (cse_event_survives e) post /\
   (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
      cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
      cse_phase_has_source fn ph e src)
Proof
 rpt gen_tac >> strip_tac >> drule cse_prefix_source_interval >>
 simp[cse_phase_has_source_def] >> metis_tac[]
QED

(* The interval certificate selects a surviving birth, not an arbitrary older
   visit of the same static source. It establishes analysis membership only.
   Below, cse_prefix_exec_avail_output_persistence adds output-binding
   persistence using SSA ownership and the self-source barrier. Canonical
   representative epoch/value alignment remains a separate obligation. *)

Theorem cse_prefix_exec_predecessor_barrier:
 wf_function fn /\ fn_inst_wf fn /\
 cse_path_preorder fn a src.inst_id /\ a <> src.inst_id /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME ri /\ ri.inst_id = a ==>
 ~cse_phase_has_source fn (CseExec n bb s) e src
Proof
 strip_tac >>
 `cse_static_trace fn (cse_project_trace events (CseExec n bb s))` by
   (drule cse_prefix_project_trace >> simp[]) >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 `cse_point_has_id fn (bb.bb_label,s.vs_inst_idx) a` by
   (gvs[cse_point_has_id_def, get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
 drule cse_static_trace_predecessor_barrier >>
 simp[cse_project_trace_last, cse_phase_point_def, cse_phase_has_source_def] >>
 strip_tac >>
 `LAST (cse_project_trace events (CseExec n bb s)) = (bb.bb_label,s.vs_inst_idx)` by
   simp[cse_project_trace_last, cse_phase_point_def] >> metis_tac[]
QED

Theorem cse_source_interval_predecessor_barrier:
 wf_function fn /\ fn_inst_wf fn /\
 cse_path_preorder fn a src.inst_id /\ a <> src.inst_id /\
 (!j ph. birth_index < j /\ j <= LENGTH events /\
    cse_prefix ctx fn fuel0 s0 (TAKE j events) ph ==>
    cse_phase_has_source fn ph e src) /\
 birth_index < k /\ k <= LENGTH events /\
 cse_prefix ctx fn fuel0 s0 (TAKE k events) (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME ri ==>
 ri.inst_id <> a
Proof
 rpt strip_tac >>
 drule_all cse_prefix_exec_predecessor_barrier >> metis_tac[]
QED

Theorem cse_prefix_exec_self_source_barrier:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME ri /\ ri.inst_id = src.inst_id ==>
 ~cse_phase_has_source fn (CseExec n bb s) e src
Proof
 strip_tac >>
 `cse_static_trace fn (cse_project_trace events (CseExec n bb s))` by
   (drule cse_prefix_project_trace >> simp[]) >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 `cse_point_has_id fn (bb.bb_label,s.vs_inst_idx) src.inst_id` by
   (gvs[cse_point_has_id_def, get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
 `LAST (cse_project_trace events (CseExec n bb s)) = (bb.bb_label,s.vs_inst_idx)` by
   simp[cse_project_trace_last, cse_phase_point_def] >>
 drule cse_static_trace_self_source_barrier >>
 simp[cse_phase_has_source_def] >> strip_tac >> metis_tac[]
QED

Theorem cse_prefix_step_input_cut[local]:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 !pre n bb inst s t post.
 events = pre ++ [CseStep n bb inst s t] ++ post ==>
 cse_prefix ctx fn fuel0 s0 pre (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 Cases_on `post` using SNOC_CASES >>
 gvs[GSYM rich_listTheory.SNOC_APPEND] >> metis_tac[]
QED

Theorem cse_prefix_nonphi_writer_step[local]:
 wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\
 MEM ev events /\ cse_event_writes ev out /\
 MEM src (fn_insts fn) /\ MEM out src.inst_outputs /\
 src.inst_opcode <> PHI ==>
 ?m sb u v. ev = CseStep m sb src u v
Proof
 strip_tac >> drule_all cse_prefix_writing_static_definer >> strip_tac >>
 Cases_on `ev` >> gvs[cse_event_covers_def]
 >- (rename1 `k < phi_prefix_length pb.bb_instructions` >>
     `MEM (EL k pb.bb_instructions)
       (TAKE (phi_prefix_length pb.bb_instructions) pb.bb_instructions)` by
       (simp[MEM_EL] >> qexists `k` >>
        gvs[get_instruction_def, AllCaseEqs(), LENGTH_TAKE, EL_TAKE,
            phi_prefix_length_le]) >>
     `EL k pb.bb_instructions = src` by
       gvs[get_instruction_def, AllCaseEqs()] >>
     mp_tac (Q.SPEC `pb.bb_instructions`
       analysisSimProofsBaseTheory.phi_prefix_all_phi) >>
     rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `src` mp_tac) >>
     gvs[]) >>
 metis_tac[]
QED

Theorem cse_interval_definer_nonwriting[local]:
 wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\
 events = pre ++ [birth] ++ post /\
 MEM d (fn_insts fn) /\ MEM out d.inst_outputs /\
 d.inst_opcode <> PHI /\
 (d <> src ==> cse_path_preorder fn d.inst_id src.inst_id /\
               d.inst_id <> src.inst_id) /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 EVERY (\ev. ~cse_event_writes ev out) post
Proof
 strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
 `MEM ev events` by gvs[MEM_APPEND] >>
 drule_all cse_prefix_nonphi_writer_step >> strip_tac >>
 qpat_x_assum `ev = _` SUBST_ALL_TAC >>
 qpat_x_assum `MEM (CseStep _ _ _ _ _) post` mp_tac >>
 rewrite_tac[MEM_SPLIT] >> strip_tac >>
 rename1 `post = left ++ CseStep m sb d u v::right` >>
 `events = (pre ++ [birth] ++ left) ++ [CseStep m sb d u v] ++ right` by
   gvs[APPEND_ASSOC] >>
 drule_all cse_prefix_step_input_cut >> strip_tac >>
 `TAKE (LENGTH (pre ++ [birth] ++ left)) events = pre ++ [birth] ++ left` by
   gvs[TAKE_APPEND1, TAKE_APPEND2] >>
 `cse_phase_has_source fn (CseExec m sb u) e src` by
   (first_x_assum irule >>
    qexists `LENGTH (pre ++ [birth] ++ left)` >> simp[] >>
    gvs[]) >>
 `~cse_phase_has_source fn (CseExec m sb u) e src` by
   (Cases_on `d = src`
    >- (qpat_x_assum `d = src` SUBST_ALL_TAC >>
        irule cse_prefix_exec_self_source_barrier >> metis_tac[]) >>
    `cse_path_preorder fn d.inst_id src.inst_id /\ d.inst_id <> src.inst_id` by
      metis_tac[] >>
    irule cse_prefix_exec_predecessor_barrier >> metis_tac[]) >>
 simp[]
QED

Theorem cse_prefix_exec_avail_output_persistence:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx) e = SOME xs /\
 MEM src xs /\ src.inst_outputs = [out] ==>
 ?pre post m sb u v.
   events = pre ++ [CseStep m sb src u v] ++ post /\
   cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
   avail_source_birth (dfg_build_function fn) e src src /\
   EVERY (cse_event_survives e) post /\
   (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
      cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
      cse_phase_has_source fn ph e src) /\
   EVERY (\ev. ~cse_event_writes ev out) post /\
   lookup_var out s = lookup_var out v
Proof
 strip_tac >> drule_all cse_prefix_exec_avail_interval >> strip_tac >>
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 `src.inst_opcode <> PHI` by
   (strip_tac >> gvs[availExprProofsTheory.avail_source_birth_def, is_pseudo_def]) >>
 `MEM (CseStep m sb src u v) events` by gvs[MEM_APPEND] >>
 drule_all cse_prefix_event_provenance >> simp[] >> strip_tac >>
 `MEM sb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `MEM src sb.bb_instructions` by
   (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
 `MEM src (fn_insts fn)` by
   (simp[fn_insts_def] >>
    qpat_x_assum `MEM sb fn.fn_blocks` mp_tac >>
    qspec_tac (`fn.fn_blocks`, `bbs`) >>
    Induct >> simp[fn_insts_blocks_def] >> rpt strip_tac >> gvs[]) >>
 `MEM out src.inst_outputs` by simp[] >>
 `EVERY (\ev. ~cse_event_writes ev out) post` by
   (drule_all (SRULE [] (Q.INST [`d` |-> `src`]
      cse_interval_definer_nonwriting)) >> simp[]) >>
 qexistsl [`pre`, `post`, `m`, `sb`, `u`, `v`] >> simp[] >>
 `cse_event_writes (CseStep m sb src u v) out` by
   simp[cse_event_writes_def] >>
 drule_all cse_prefix_last_write_binding >>
 gvs[cse_phase_state_def, cse_event_output_def] >>
 strip_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem cse_source_interval_predecessor_nonwriting:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 MEM src (fn_insts fn) /\ MEM d (fn_insts fn) /\
 MEM x d.inst_outputs /\ d.inst_opcode <> PHI /\
 cse_path_preorder fn d.inst_id src.inst_id /\ d.inst_id <> src.inst_id /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 EVERY (\ev. ~cse_event_writes ev x) (CseStep m sb src u v :: post)
Proof
 strip_tac >>
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 `d <> src` by (strip_tac >> gvs[]) >>
 `(d <> src ==> cse_path_preorder fn d.inst_id src.inst_id /\
   d.inst_id <> src.inst_id)` by simp[] >>
 `EVERY (\ev. ~cse_event_writes ev x) post` by
   (drule_all cse_interval_definer_nonwriting >> simp[]) >>
 simp[cse_event_writes_def] >> strip_tac >>
 `src = d` by (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[]) >>
 gvs[]
QED

Theorem cse_source_interval_predecessor_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 MEM src (fn_insts fn) /\ MEM d (fn_insts fn) /\
 MEM x d.inst_outputs /\ d.inst_opcode <> PHI /\
 cse_path_preorder fn d.inst_id src.inst_id /\ d.inst_id <> src.inst_id /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 lookup_var x s = lookup_var x u
Proof
 strip_tac >> drule_all cse_source_interval_predecessor_nonwriting >> strip_tac >>
 qpat_assum `cse_prefix _ _ _ _ events _`
   (mp_then Any (qspec_then `x` mp_tac) cse_prefix_binding_fold) >>
 qpat_assum `cse_prefix _ _ _ _ pre _`
   (mp_then Any (qspec_then `x` mp_tac) cse_prefix_binding_fold) >>
 gvs[cse_phase_state_def, rich_listTheory.FOLDL_APPEND,
     cse_binding_fold_nonwriting]
QED

(* Interior PHI points below are syntactic analysis cuts, not runtime writes. *)
Theorem cse_static_trace_phi_predecessor_barrier:
 wf_function fn /\ fn_inst_wf fn /\ cse_static_trace fn ps /\
 LAST ps = (bb.bb_label,0) /\
 lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
 k < phi_prefix_length bb.bb_instructions /\
 cse_path_preorder fn (EL k bb.bb_instructions).inst_id src.inst_id /\
 (EL k bb.bb_instructions).inst_id <> src.inst_id ==>
 ~(?xs. FLOOKUP (ae_lookup_inst fn bb.bb_label 0) e = SOME xs /\ MEM src xs)
Proof
 strip_tac >>
 `k < LENGTH bb.bb_instructions` by
   (mp_tac phi_prefix_length_le >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
 `cse_static_trace fn (ps ++ GENLIST (\i. (bb.bb_label,SUC i)) k)` by
   (qspecl_then [`k`, `ps`, `bb.bb_label`, `0`] mp_tac cse_static_trace_advance >>
    simp[] >> disch_then irule >> simp[]) >>
 `LAST (ps ++ GENLIST (\i. (bb.bb_label,SUC i)) k) = (bb.bb_label,k)` by
   (Cases_on `k` >> simp[GENLIST]) >>
 `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
   (drule cse_static_trace_reachable >> simp[] >>
    metis_tac[cse_static_trace_nonempty, rich_listTheory.MEM_LAST, listTheory.list_CASES]) >>
 `ae_lookup_inst fn bb.bb_label k = ae_lookup_inst fn bb.bb_label 0` by
   (irule cse_avail_phi_prefix_unwrap >> simp[] >>
    rpt strip_tac >>
    qspec_then `bb.bb_instructions` mp_tac analysisSimProofsBaseTheory.phi_prefix_all_phi >>
    rewrite_tac[EVERY_EL] >> disch_then (qspec_then `j` mp_tac) >>
    `j < phi_prefix_length bb.bb_instructions` by decide_tac >>
    simp[LENGTH_TAKE, EL_TAKE, phi_prefix_length_le]) >>
 `cse_point_has_id fn
   (LAST (ps ++ GENLIST (\i. (bb.bb_label,SUC i)) k))
   (EL k bb.bb_instructions).inst_id` by
   simp[cse_point_has_id_def] >>
 drule_all cse_static_trace_predecessor_barrier >> simp[] >> metis_tac[]
QED

Theorem cse_prefix_run_phi_predecessor_barrier:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseRun n s) /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 k < phi_prefix_length bb.bb_instructions /\
 cse_path_preorder fn (EL k bb.bb_instructions).inst_id src.inst_id /\
 (EL k bb.bb_instructions).inst_id <> src.inst_id ==>
 ~cse_phase_has_source fn (CseRun n s) e src
Proof
 strip_tac >>
 `s.vs_current_bb = bb.bb_label` by metis_tac[lookup_block_label] >>
 drule_all cse_prefix_project_run >> strip_tac >>
 `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by metis_tac[] >>
 drule_all cse_static_trace_phi_predecessor_barrier >>
 simp[cse_phase_has_source_def] >> metis_tac[]
QED

Theorem cse_prefix_phi_input_cut[local]:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 !pre n bb s t post.
 events = pre ++ [CsePhi n bb s t] ++ post ==>
 cse_prefix ctx fn fuel0 s0 pre (CseRun (SUC n) s) /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 Cases_on `post` using SNOC_CASES >>
 gvs[GSYM rich_listTheory.SNOC_APPEND] >> metis_tac[]
QED

Theorem cse_source_interval_predecessor_nonwriting_all:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 MEM src (fn_insts fn) /\ MEM d (fn_insts fn) /\
 MEM x d.inst_outputs /\
 cse_path_preorder fn d.inst_id src.inst_id /\ d.inst_id <> src.inst_id /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 EVERY (\ev. ~cse_event_writes ev x) (CseStep m sb src u v :: post)
Proof
 strip_tac >> Cases_on `d.inst_opcode = PHI`
 >- suspend "phi"
 >> drule_all cse_source_interval_predecessor_nonwriting >> simp[]
QED

Resume cse_source_interval_predecessor_nonwriting_all[phi]:
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 `EVERY (\ev. ~cse_event_writes ev x) post` by
   (simp[EVERY_MEM] >> rpt strip_tac >>
    `MEM ev events` by gvs[MEM_APPEND] >>
    drule_all cse_prefix_writing_static_definer >> strip_tac >>
    qpat_x_assum `MEM ev post` mp_tac >> rewrite_tac[MEM_SPLIT] >> strip_tac >>
    rename1 `post = left ++ ev::right` >>
    `events = (pre ++ [CseStep m sb src u v] ++ left) ++ [ev] ++ right` by
      gvs[APPEND_ASSOC] >>
    Cases_on `ev`
    >- (qpat_x_assum `cse_event_covers _ _ _ _` mp_tac >>
        rewrite_tac[cse_event_covers_def] >> strip_tac >>
        rpt (qpat_x_assum `(_ :basic_block) = _` SUBST_ALL_TAC) >>
        suspend "phi_writer") >>
    qpat_x_assum `cse_event_covers _ _ _ _` mp_tac >>
    rewrite_tac[cse_event_covers_def] >> strip_tac >>
    rpt (qpat_x_assum `(_ :basic_block) = _` SUBST_ALL_TAC) >>
    rpt (qpat_x_assum `(_ :instruction) = _` SUBST_ALL_TAC) >>
    suspend "step_writer") >>
 simp[cse_event_writes_def] >> strip_tac >>
 `src = d` by (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[]) >>
 gvs[]
QED

Resume cse_source_interval_predecessor_nonwriting_all[phi_writer]:
 drule_all cse_prefix_phi_input_cut >> strip_tac >>
     `TAKE (LENGTH (pre ++ [CseStep m sb src u v] ++ left)) events =
        pre ++ [CseStep m sb src u v] ++ left` by
       gvs[TAKE_APPEND1, TAKE_APPEND2] >>
     rename1 `cse_prefix ctx fn fuel0 s0
       (pre ++ [CseStep m sb src u v] ++ left) (CseRun q w)` >>
     `cse_phase_has_source fn (CseRun q w) e src` by
       (first_x_assum irule >>
        qexists `LENGTH (pre ++ [CseStep m sb src u v] ++ left)` >> simp[] >> gvs[]) >>
     `EL k bb'.bb_instructions = d` by gvs[get_instruction_def, AllCaseEqs()] >>
     `~cse_phase_has_source fn (CseRun q w) e src` by
       (irule cse_prefix_run_phi_predecessor_barrier >> metis_tac[]) >> simp[]
QED

Resume cse_source_interval_predecessor_nonwriting_all[step_writer]:
 drule_all cse_prefix_step_input_cut >> strip_tac >>
 `TAKE (LENGTH (pre ++ [CseStep m sb src u v] ++ left)) events =
    pre ++ [CseStep m sb src u v] ++ left` by
   gvs[TAKE_APPEND1, TAKE_APPEND2] >>
 rename1 `cse_prefix ctx fn fuel0 s0
   (pre ++ [CseStep m sb src u v] ++ left) (CseExec q blk w)` >>
 `cse_phase_has_source fn (CseExec q blk w) e src` by
   (first_x_assum irule >>
    qexists `LENGTH (pre ++ [CseStep m sb src u v] ++ left)` >> simp[] >> gvs[]) >>
 `~cse_phase_has_source fn (CseExec q blk w) e src` by
   (irule cse_prefix_exec_predecessor_barrier >> metis_tac[]) >> simp[]
QED

Finalise cse_source_interval_predecessor_nonwriting_all

Theorem cse_source_interval_predecessor_binding_all:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 MEM src (fn_insts fn) /\ MEM d (fn_insts fn) /\
 MEM x d.inst_outputs /\
 cse_path_preorder fn d.inst_id src.inst_id /\ d.inst_id <> src.inst_id /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 lookup_var x s = lookup_var x u
Proof
 strip_tac >> drule_all cse_source_interval_predecessor_nonwriting_all >> strip_tac >>
 qpat_assum `cse_prefix _ _ _ _ events _`
   (mp_then Any (qspec_then `x` mp_tac) cse_prefix_binding_fold) >>
 qpat_assum `cse_prefix _ _ _ _ pre _`
   (mp_then Any (qspec_then `x` mp_tac) cse_prefix_binding_fold) >>
 gvs[cse_phase_state_def, rich_listTheory.FOLDL_APPEND,
     cse_binding_fold_nonwriting]
QED

(* An ASSIGN use rewinds to the input of its actual last writing visit,
   not to an evaluation of the source operand in the consumer state. *)
Theorem cse_prefix_assign_use_rewind:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM (Var x) use.inst_operands /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode = ASSIGN /\
 copy.inst_outputs = [x] /\ copy.inst_operands = [arg] ==>
 ?pre post m cb u t value.
   events = pre ++ [CseStep m cb copy u t] ++ post /\
   cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
   get_instruction cb u.vs_inst_idx = SOME copy /\
   eval_operand arg u = SOME value /\
   eval_operand (Var x) s = SOME value /\
   EVERY (\ev. ~cse_event_writes ev x) post /\
   LENGTH pre < LENGTH events
Proof
 strip_tac >> drule_all cse_prefix_ordinary_use_last_write >> strip_tac >>
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 `MEM ev events` by gvs[MEM_APPEND] >>
 `MEM x copy.inst_outputs /\ copy.inst_opcode <> PHI` by simp[] >>
 drule_all cse_prefix_nonphi_writer_step >> strip_tac >>
 qpat_x_assum `ev = _` SUBST_ALL_TAC >>
 drule_all cse_prefix_step_input_cut >> strip_tac >>
 drule_all cse_prefix_event_provenance >>
 simp[] >> strip_tac >>
 qexistsl [`pre`, `post`, `m`, `sb`, `u`, `v`] >>
 gvs[step_inst_def, step_inst_base_def, AllCaseEqs()] >>
 gvs[cse_event_output_def, eval_operand_def, lookup_var_def,
     update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem cse_prefix_assign_use_rewind_dfg:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM (Var x) use.inst_operands /\
 FLOOKUP (dfg_build_function fn).dfg_defs x = SOME copy /\
 copy.inst_opcode = ASSIGN /\ copy.inst_outputs = [x] /\
 copy.inst_operands = [arg] ==>
 ?pre post m cb u t value.
   events = pre ++ [CseStep m cb copy u t] ++ post /\
   cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
   get_instruction cb u.vs_inst_idx = SOME copy /\
   eval_operand arg u = SOME value /\
   eval_operand (Var x) s = SOME value /\
   EVERY (\ev. ~cse_event_writes ev x) post /\
   LENGTH pre < LENGTH events
Proof
 strip_tac >>
 `dfg_get_def (dfg_build_function fn) x = SOME copy` by
   simp[dfgDefsTheory.dfg_get_def_def] >>
 drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
 irule cse_prefix_assign_use_rewind >> metis_tac[]
QED

Theorem cse_dfg_assign_shape[local]:
 fn_inst_wf fn /\
 FLOOKUP (dfg_build_function fn).dfg_defs x = SOME inst /\
 inst.inst_opcode = ASSIGN ==>
 ?arg. inst.inst_operands = [arg] /\ inst.inst_outputs = [x]
Proof
 strip_tac >>
 `dfg_get_def (dfg_build_function fn) x = SOME inst` by
   simp[dfgDefsTheory.dfg_get_def_def] >>
 drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
 `!bbs. MEM inst (fn_insts_blocks bbs) ==>
    ?b. MEM b bbs /\ MEM inst b.bb_instructions` by
   (Induct >> simp[fn_insts_blocks_def] >> metis_tac[]) >>
 `?b. MEM b fn.fn_blocks /\ MEM inst b.bb_instructions` by
   metis_tac[fn_insts_def] >>
 `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
 gvs[inst_wf_def] >>
 Cases_on `inst.inst_operands` >> gvs[] >>
 Cases_on `inst.inst_outputs` >> gvs[]
QED

Theorem cse_prefix_operand_producer_rewind_aux[local]:
 !d seen op. !fn ctx fuel0 s0 events n bb s use k.
 d = dfg_build_function fn /\
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer d seen op = SOME k ==>
 ?pre post m cb u terminal_use v definer.
 events = pre ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 get_instruction cb u.vs_inst_idx = SOME terminal_use /\
 terminal_use.inst_opcode <> PHI /\
 MEM (Var v) terminal_use.inst_operands /\
 FLOOKUP (dfg_build_function fn).dfg_defs v = SOME definer /\
 definer.inst_opcode <> ASSIGN /\ definer.inst_id = k /\
 eval_operand op s = eval_operand (Var v) u
Proof
 recInduct cseDefsTheory.operand_producer_ind >> rpt strip_tac >>
 gvs[Once cseDefsTheory.operand_producer_def, AllCaseEqs()]
 >- (drule_all cse_dfg_assign_shape >> gvs[])
 >- suspend "copy"
 >- (drule_all cse_dfg_assign_shape >> gvs[]) >>
 qexistsl [`events`, `[]`, `n`, `bb`, `s`, `use`, `v`, `inst`] >> simp[]
QED

Resume cse_prefix_operand_producer_rewind_aux[copy]:
 drule_all cse_dfg_assign_shape >> strip_tac >> gvs[] >>
 drule_all cse_prefix_assign_use_rewind_dfg >> strip_tac >>
 `inst.inst_opcode <> PHI /\ MEM arg inst.inst_operands` by simp[] >>
 first_x_assum (qspec_then `fn` (mp_tac o SRULE [])) >>
 disch_then drule_all >> strip_tac >>
 qexistsl [`pre'`, `post' ++ [CseStep m cb inst u t] ++ post`,
   `m'`, `cb'`, `u'`, `terminal_use`, `v'`, `definer`] >>
 gvs[APPEND_ASSOC]
QED
Finalise cse_prefix_operand_producer_rewind_aux

Theorem cse_prefix_operand_producer_rewind:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) seen op = SOME k ==>
 ?pre post m cb u terminal_use v definer.
 events = pre ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 get_instruction cb u.vs_inst_idx = SOME terminal_use /\
 terminal_use.inst_opcode <> PHI /\
 MEM (Var v) terminal_use.inst_operands /\
 FLOOKUP (dfg_build_function fn).dfg_defs v = SOME definer /\
 definer.inst_opcode <> ASSIGN /\ definer.inst_id = k /\
 eval_operand op s = eval_operand (Var v) u
Proof
 strip_tac >> irule cse_prefix_operand_producer_rewind_aux >>
 metis_tac[]
QED

Theorem cse_prefix_use_dfg_def[local]:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM (Var x) use.inst_operands ==>
 ?inst. FLOOKUP (dfg_build_function fn).dfg_defs x = SOME inst
Proof
 strip_tac >> drule_all cse_prefix_ordinary_use_last_write >> strip_tac >>
 `MEM ev events` by gvs[MEM_APPEND] >>
 drule_all cse_prefix_writing_occurrence >> strip_tac >>
 `MEM inst (fn_insts_blocks fn.fn_blocks)` by
   (`MEM inst bb'.bb_instructions` by
      (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
    qpat_x_assum `MEM bb' fn.fn_blocks` mp_tac >>
    qspec_tac (`fn.fn_blocks`, `bbs`) >>
    Induct >> simp[fn_insts_blocks_def] >> metis_tac[]) >>
 `MEM inst (fn_insts fn)` by simp[fn_insts_def] >>
 drule_all dfgAnalysisPropsTheory.dfg_build_function_defs_complete >>
 simp[dfgDefsTheory.dfg_get_def_def]
QED

Theorem cse_prefix_copy_normal_form:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands ==>
 ?pre post m cb u terminal_use terminal.
 events = pre ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 get_instruction cb u.vs_inst_idx = SOME terminal_use /\
 terminal_use.inst_opcode <> PHI /\ MEM terminal terminal_use.inst_operands /\
 RTC (\a b. ?x copy. a = Var x /\
   FLOOKUP (dfg_build_function fn).dfg_defs x = SOME copy /\
   copy.inst_opcode = ASSIGN /\ copy.inst_operands = [b]) op terminal /\
 eval_operand op s = eval_operand terminal u /\
 ((?w. terminal = Lit w) \/ (?l. terminal = Label l) \/
  (?x definer. terminal = Var x /\
   FLOOKUP (dfg_build_function fn).dfg_defs x = SOME definer /\
   definer.inst_opcode <> ASSIGN))
Proof
 map_every qid_spec_tac [`op`, `use`, `s`, `bb`, `n`] >>
 measureInduct_on `LENGTH events` >> rpt strip_tac >>
 Cases_on `op`
 >- (rename1 `MEM (Lit w) use.inst_operands` >>
     qexistsl [`events`, `[]`, `n`, `bb`, `s`, `use`, `Lit w`] >>
     simp[relationTheory.RTC_REFL])
 >- suspend "var" >>
 qexistsl [`events`, `[]`, `n`, `bb`, `s`, `use`, `Label s'`] >>
 simp[relationTheory.RTC_REFL]
QED

Resume cse_prefix_copy_normal_form[var]:
 drule_all cse_prefix_use_dfg_def >> strip_tac >>
 Cases_on `inst.inst_opcode = ASSIGN`
 >- suspend "assign"
 >> qexistsl [`events`, `[]`, `n`, `bb`, `s`, `use`, `Var s'`] >>
 simp[relationTheory.RTC_REFL] >> metis_tac[]
QED

Resume cse_prefix_copy_normal_form[assign]:
 drule_all cse_dfg_assign_shape >> strip_tac >>
 drule_all cse_prefix_assign_use_rewind_dfg >> strip_tac >>
 `inst.inst_opcode <> PHI /\ MEM arg inst.inst_operands` by simp[] >>
 first_x_assum drule >>
 disch_then drule_all >> strip_tac >>
 qexistsl [`pre'`, `post' ++ [CseStep m cb inst u t] ++ post`,
   `m'`, `cb'`, `u'`, `terminal_use`, `terminal`] >>
 gvs[APPEND_ASSOC] >>
 irule relationTheory.RTC_TRANS >> qexists `arg` >>
 simp[] >> irule relationTheory.RTC_SINGLE >> simp[] >> metis_tac[]
QED
Finalise cse_prefix_copy_normal_form

Theorem cse_terminal_path_no_cycle[local]:
 !R x t. RTC R x t ==>
 (!a b c. R a b /\ R a c ==> b = c) ==>
 (!z. ~R t z) ==> !y. R x y ==> ~RTC R y x
Proof
 gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> conj_tac
 >- metis_tac[] >> rpt strip_tac >>
 `y = x'` by metis_tac[] >> gvs[] >>
 qpat_x_assum `RTC R x' x`
   (strip_assume_tac o PURE_ONCE_REWRITE_RULE [relationTheory.RTC_CASES1])
 >- (gvs[] >> metis_tac[relationTheory.RTC_REFL]) >>
 metis_tac[relationTheory.RTC_SINGLE, relationTheory.RTC_TRANS]
QED

Theorem cse_copy_path_interpret[local]:
 !op terminal.
 RTC (\a b. ?x copy. a = Var x /\
   FLOOKUP dfg.dfg_defs x = SOME copy /\
   copy.inst_opcode = ASSIGN /\ copy.inst_operands = [b]) op terminal ==>
 !visited.
 ((?w. terminal = Lit w) \/ (?l. terminal = Label l) \/
  (?x definer. terminal = Var x /\
    FLOOKUP dfg.dfg_defs x = SOME definer /\
    definer.inst_opcode <> ASSIGN)) /\
 (!v. MEM v visited ==> ~RTC (\a b. ?x copy. a = Var x /\
   FLOOKUP dfg.dfg_defs x = SOME copy /\
   copy.inst_opcode = ASSIGN /\ copy.inst_operands = [b]) op (Var v)) ==>
 operand_producer dfg (set visited) op = operand_producer dfg {} terminal /\
 ((!w. terminal = Lit w ==> mk_operand_expr dfg visited op = ExprLit w) /\
  (!l. terminal = Label l ==> mk_operand_expr dfg visited op = ExprLabel l))
Proof
 ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT >> conj_tac
 >- (rpt strip_tac >> gvs[] >>
     simp[cseDefsTheory.operand_producer_def,
          availExprDefsTheory.mk_operand_expr_def] >>
     `~MEM x visited` by metis_tac[relationTheory.RTC_REFL] >> simp[]) >>
 rpt gen_tac >> strip_tac >> gen_tac >>
 disch_then (CONJUNCTS_THEN assume_tac) >>
 qmatch_asmsub_abbrev_tac `RTC R op' terminal` >>
 `!a b c. R a b /\ R a c ==> b = c` by
   (simp[Abbr `R`] >> rpt strip_tac >> gvs[]) >>
 `!z. ~R terminal z` by
   (qpat_x_assum `!a b c. R a b /\ R a c ==> b = c` kall_tac >>
    qpat_x_assum `(?w. terminal = Lit w) \/ _` strip_assume_tac >>
    simp[Abbr `R`] >> rpt strip_tac >> gvs[]) >>
 `R op op'` by
   (qpat_x_assum `!a b c. R a b /\ R a c ==> b = c` kall_tac >>
    simp[Abbr `R`] >> metis_tac[]) >>
 `RTC R op terminal` by metis_tac[relationTheory.RTC_RULES] >>
 `~RTC R op' op` by metis_tac[cse_terminal_path_no_cycle] >>
 `~MEM x visited` by
   (gvs[] >> metis_tac[relationTheory.RTC_REFL]) >>
 first_x_assum (qspec_then `x::visited` mp_tac) >>
 impl_tac
 >- (simp[] >> rpt strip_tac >> gvs[] >>
     metis_tac[relationTheory.RTC_RULES]) >>
 strip_tac >> gvs[] >>
 simp[Once cseDefsTheory.operand_producer_def,
      Once availExprDefsTheory.mk_operand_expr_def,
      dfgDefsTheory.dfg_get_def_def, venomInstTheory.is_pseudo_def]
QED

Theorem cse_prefix_operand_producer_none_rewind:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) {} op = NONE ==>
 ?pre post m cb u terminal_use terminal.
 events = pre ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 get_instruction cb u.vs_inst_idx = SOME terminal_use /\
 terminal_use.inst_opcode <> PHI /\ MEM terminal terminal_use.inst_operands /\
 eval_operand op s = eval_operand terminal u /\
 ((?w. terminal = Lit w /\
       mk_operand_expr (dfg_build_function fn) [] op = ExprLit w) \/
  (?l. terminal = Label l /\
       mk_operand_expr (dfg_build_function fn) [] op = ExprLabel l))
Proof
 strip_tac >> drule_all cse_prefix_copy_normal_form >> strip_tac >>
 drule cse_copy_path_interpret >>
 disch_then (qspec_then `[]` mp_tac) >>
 (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
 qexistsl [`pre`, `post`, `m`, `cb`, `u`, `terminal_use`, `terminal`] >>
 simp[] >> gvs[cseDefsTheory.operand_producer_def]
QED

Theorem cse_prefix_labels_frame[local]:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 (cse_phase_state phase).vs_labels = s0.vs_labels
Proof
 ho_match_mp_tac cse_prefix_ind >> rpt conj_tac >>
 rpt gen_tac >> strip_tac >> gvs[cse_phase_state_def] >>
 metis_tac[venomExecPropsTheory.eval_phis_preserves_labels,
           venomExecPropsTheory.step_inst_preserves_labels_always]
QED

Theorem cse_prefix_exec_labels:
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) ==>
 s.vs_labels = s0.vs_labels
Proof
 strip_tac >> drule cse_prefix_labels_frame >> simp[cse_phase_state_def]
QED

Theorem cse_prefix_none_leaf_eval[local]:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) {} op = NONE ==>
 (?w. mk_operand_expr (dfg_build_function fn) [] op = ExprLit w /\
      eval_operand op s = eval_operand (Lit w) s0) \/
 (?l. mk_operand_expr (dfg_build_function fn) [] op = ExprLabel l /\
      eval_operand op s = eval_operand (Label l) s0)
Proof
 strip_tac >> drule_all cse_prefix_operand_producer_none_rewind >>
 strip_tac >> drule cse_prefix_exec_labels >>
 simp[eval_operand_def] >> metis_tac[]
QED

Theorem cse_prefix_none_operands_equal:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 cse_prefix ctx' fn fuel0' s0' events' (CseExec n' bb' s') /\
 s0.vs_labels = s0'.vs_labels /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 get_instruction bb' s'.vs_inst_idx = SOME use' /\
 use.inst_opcode <> PHI /\ use'.inst_opcode <> PHI /\
 MEM op use.inst_operands /\ MEM op' use'.inst_operands /\
 operand_producer (dfg_build_function fn) {} op = NONE /\
 operand_producer (dfg_build_function fn) {} op' = NONE /\
 mk_operand_expr (dfg_build_function fn) [] op =
 mk_operand_expr (dfg_build_function fn) [] op' ==>
 eval_operand op s = eval_operand op' s'
Proof
 strip_tac >>
 `(?w. mk_operand_expr (dfg_build_function fn) [] op = ExprLit w /\
       eval_operand op s = eval_operand (Lit w) s0) \/
  (?l. mk_operand_expr (dfg_build_function fn) [] op = ExprLabel l /\
       eval_operand op s = eval_operand (Label l) s0)` by
   (irule cse_prefix_none_leaf_eval >> metis_tac[]) >>
 `(?w. mk_operand_expr (dfg_build_function fn) [] op' = ExprLit w /\
       eval_operand op' s' = eval_operand (Lit w) s0') \/
  (?l. mk_operand_expr (dfg_build_function fn) [] op' = ExprLabel l /\
       eval_operand op' s' = eval_operand (Label l) s0')` by
   (irule cse_prefix_none_leaf_eval >> metis_tac[]) >>
 gvs[eval_operand_def]
QED

Theorem cse_prefix_some_operand_epoch:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) seen op = SOME producer ==>
 ?before ev middle tail m cb u terminal_use x d wb wi.
 events = before ++ [ev] ++ middle ++ tail /\
 cse_prefix ctx fn fuel0 s0 (before ++ [ev] ++ middle) (CseExec m cb u) /\
 get_instruction cb u.vs_inst_idx = SOME terminal_use /\
 terminal_use.inst_opcode <> PHI /\ MEM (Var x) terminal_use.inst_operands /\
 FLOOKUP (dfg_build_function fn).dfg_defs x = SOME d /\
 d.inst_opcode <> ASSIGN /\ d.inst_id = producer /\
 MEM wb fn.fn_blocks /\ get_instruction wb wi = SOME d /\
 MEM x d.inst_outputs /\ cse_event_covers ev wb wi d /\
 cse_event_writes ev x /\
 EVERY (\e. ~cse_event_writes e x) middle /\
 eval_operand op s = eval_operand (Var x) u /\
 eval_operand op s = lookup_var x (cse_event_output ev)
Proof
 strip_tac >> drule_all cse_prefix_operand_producer_rewind >> strip_tac >>
 `dfg_get_def (dfg_build_function fn) v = SOME definer` by
   simp[dfgDefsTheory.dfg_get_def_def] >>
 drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
 drule_all cse_prefix_ordinary_use_last_write >> strip_tac >>
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 `MEM ev pre` by gvs[MEM_APPEND] >>
 drule_all cse_prefix_writing_static_definer >> strip_tac >>
 qexistsl [`pre'`, `ev`, `post'`, `post`, `m`, `cb`, `u`,
           `terminal_use`, `v`, `definer`, `bb'`, `k`] >>
 gvs[APPEND_ASSOC, eval_operand_def]
QED

Theorem cse_prefix_nonwriting_cut_binding[local]:
 cse_prefix ctx fn fuel0 s0 pre phase0 /\
 cse_prefix ctx fn fuel0 s0 cut phase /\
 events = pre ++ suffix /\ events = cut ++ rest /\
 LENGTH pre <= LENGTH cut /\ EVERY (\ev. ~cse_event_writes ev x) suffix ==>
 lookup_var x (cse_phase_state phase) =
 lookup_var x (cse_phase_state phase0)
Proof
 strip_tac >>
 `cut = pre ++ TAKE (LENGTH cut - LENGTH pre) suffix` by
   (`TAKE (LENGTH cut) events = cut` by
      (qpat_assum `events = cut ++ rest` (fn th => pure_rewrite_tac[th]) >>
       simp[TAKE_APPEND1]) >>
    Cases_on `LENGTH pre = LENGTH cut`
    >- (gvs[TAKE_APPEND1] >> metis_tac[TAKE_LENGTH_TOO_LONG, arithmeticTheory.LESS_EQ_REFL]) >>
    `LENGTH pre < LENGTH cut` by decide_tac >>
    gvs[TAKE_APPEND2]) >>
 `EVERY (\ev. ~cse_event_writes ev x)
    (TAKE (LENGTH cut - LENGTH pre) suffix)` by
   metis_tac[rich_listTheory.EVERY_TAKE] >>
 qpat_assum `cse_prefix _ _ _ _ cut _`
   (mp_then Any (qspec_then `x` mp_tac) cse_prefix_binding_fold) >>
 qpat_assum `cse_prefix _ _ _ _ pre _`
   (mp_then Any (qspec_then `x` mp_tac) cse_prefix_binding_fold) >>
 qpat_assum `cut = pre ++ _` (fn th => once_rewrite_tac[th]) >>
 simp[rich_listTheory.FOLDL_APPEND, cse_binding_fold_nonwriting]
QED

Theorem cse_source_interval_terminal_epochs_equal:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 MEM src (fn_insts fn) /\ MEM d (fn_insts fn) /\
 MEM x d.inst_outputs /\
 cse_path_preorder fn d.inst_id src.inst_id /\ d.inst_id <> src.inst_id /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) /\
 events = cut1 ++ rest1 /\ LENGTH pre <= LENGTH cut1 /\
 cse_prefix ctx fn fuel0 s0 cut1 (CseExec n1 bb1 s1) /\
 cut1 = before1 ++ [ev1] ++ middle1 /\
 cse_event_writes ev1 x /\ EVERY (\ev. ~cse_event_writes ev x) middle1 /\
 events = cut2 ++ rest2 /\ LENGTH pre <= LENGTH cut2 /\
 cse_prefix ctx fn fuel0 s0 cut2 (CseExec n2 bb2 s2) /\
 cut2 = before2 ++ [ev2] ++ middle2 /\
 cse_event_writes ev2 x /\ EVERY (\ev. ~cse_event_writes ev x) middle2 ==>
 lookup_var x (cse_event_output ev1) = lookup_var x (cse_event_output ev2)
Proof
 strip_tac >>
 `EVERY (\ev. ~cse_event_writes ev x) (CseStep m sb src u v :: post)` by
   (drule_all cse_source_interval_predecessor_nonwriting_all >> simp[]) >>
 `lookup_var x s1 = lookup_var x u` by
   (`lookup_var x (cse_phase_state (CseExec n1 bb1 s1)) =
      lookup_var x (cse_phase_state (CseExec m sb u))` suffices_by
       simp[cse_phase_state_def] >>
    irule cse_prefix_nonwriting_cut_binding >>
    metis_tac[APPEND, APPEND_ASSOC]) >>
 `lookup_var x s2 = lookup_var x u` by
   (`lookup_var x (cse_phase_state (CseExec n2 bb2 s2)) =
      lookup_var x (cse_phase_state (CseExec m sb u))` suffices_by
       simp[cse_phase_state_def] >>
    irule cse_prefix_nonwriting_cut_binding >>
    metis_tac[APPEND, APPEND_ASSOC]) >>
 `lookup_var x s1 = lookup_var x (cse_event_output ev1)` by
   (`lookup_var x (cse_phase_state (CseExec n1 bb1 s1)) =
      lookup_var x (cse_event_output ev1)` suffices_by
       simp[cse_phase_state_def] >>
    irule cse_prefix_last_write_binding >> metis_tac[]) >>
 `lookup_var x s2 = lookup_var x (cse_event_output ev2)` by
   (`lookup_var x (cse_phase_state (CseExec n2 bb2 s2)) =
      lookup_var x (cse_event_output ev2)` suffices_by
       simp[cse_phase_state_def] >>
    irule cse_prefix_last_write_binding >> metis_tac[]) >>
 metis_tac[]
QED

Theorem cse_event_covers_points:
 cse_event_covers ev bb k inst ==>
 MEM ((bb.bb_label,k),SOME (j,k)) (cse_event_points j ev)
Proof
 Cases_on `ev` >>
 simp[cse_event_covers_def, cse_event_points_def, MEM_GENLIST] >>
 rpt strip_tac >> gvs[]
QED

Theorem cse_history_covers_points:
 !events start j bb k inst.
 j < LENGTH events /\ cse_event_covers (EL j events) bb k inst ==>
 MEM ((bb.bb_label,k),SOME (start+j,k)) (cse_history_points start events)
Proof
 Induct >> simp[cse_history_points_def] >> rpt gen_tac >>
 Cases_on `j`
 >- (simp[] >> metis_tac[cse_event_covers_points]) >>
 simp[cse_history_points_def] >> strip_tac >>
 first_x_assum drule >> disch_then (qspec_then `SUC start` mp_tac) >>
 simp[arithmeticTheory.ADD_CLAUSES] >> metis_tac[]
QED

Theorem cse_prefix_covered_point_has_id:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\
 MEM ev events /\ cse_event_covers ev bb k inst ==>
 cse_point_has_id fn (bb.bb_label,k) inst.inst_id
Proof
 strip_tac >> drule_all cse_prefix_event_provenance >>
 Cases_on `ev` >> gvs[cse_event_covers_def, cse_point_has_id_def,
                          get_instruction_def, AllCaseEqs()] >>
 metis_tac[lookup_block_label]
QED

Theorem cse_point_identifies_member[local]:
 wf_function fn /\ MEM inst (fn_insts fn) /\
 cse_point_has_id fn (lbl,k) inst.inst_id ==>
 ?bb. lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb k = SOME inst
Proof
 strip_tac >>
 `!bbs. MEM inst (fn_insts_blocks bbs) ==>
   ?b. MEM b bbs /\ MEM inst b.bb_instructions` by
   (Induct >> simp[fn_insts_blocks_def] >> metis_tac[]) >>
 `?b. MEM b fn.fn_blocks /\ MEM inst b.bb_instructions` by
   metis_tac[fn_insts_def] >>
 `?i. i < LENGTH b.bb_instructions /\ EL i b.bb_instructions = inst` by
   metis_tac[MEM_EL] >>
 `lookup_block b.bb_label fn.fn_blocks = SOME b` by
   (gvs[wf_function_def, fn_labels_def] >> metis_tac[MEM_lookup_block]) >>
 `cse_point_has_id fn (b.bb_label,i) inst.inst_id` by
   (simp[cse_point_has_id_def] >> metis_tac[]) >>
 `(lbl,k) = (b.bb_label,i)` by metis_tac[cse_point_has_id_injective] >>
 gvs[get_instruction_def]
QED

Theorem cse_prefix_event_point_instruction[local]:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\ MEM ev events /\
 MEM ((lbl,k),tag) (cse_event_points start ev) /\
 MEM inst (fn_insts fn) /\ cse_point_has_id fn (lbl,k) inst.inst_id ==>
 tag = SOME (start,k) /\ ?b. cse_event_covers ev b k inst
Proof
 strip_tac >> drule_all cse_point_identifies_member >> strip_tac >>
 drule_all cse_prefix_event_provenance >>
 Cases_on `ev` >> gvs[cse_event_points_def, MEM_GENLIST] >>
 rpt strip_tac >> gvs[]
 >- (`v.vs_current_bb = b.bb_label` by metis_tac[lookup_block_label] >>
     gvs[] >> simp[cse_event_covers_def] >> metis_tac[]) >>
 `v.vs_current_bb = b.bb_label` by metis_tac[lookup_block_label] >>
 gvs[] >> Cases_on `is_terminator i.inst_opcode` >>
 gvs[cse_event_covers_def, get_instruction_def]
QED

Theorem cse_event_ordinary_cover_unique[local]:
 cse_event_covers ev db dk definst /\
 cse_event_covers ev cb ck copy /\ copy.inst_opcode <> PHI ==>
 definst = copy
Proof
 Cases_on `ev` >> simp[cse_event_covers_def] >> strip_tac >> gvs[] >>
 qspec_then `b.bb_instructions` mp_tac
   analysisSimProofsBaseTheory.phi_prefix_all_phi >>
 rewrite_tac[EVERY_EL] >> disch_then (qspec_then `ck` mp_tac) >>
 gvs[get_instruction_def, LENGTH_TAKE, EL_TAKE, phi_prefix_length_le]
QED

Theorem cse_prefix_history_point_instruction[local]:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events phase /\ MEM inst (fn_insts fn) ==>
 !tail start lbl k tag.
 EVERY (\ev. MEM ev events) tail /\
 MEM ((lbl,k),tag) (cse_history_points start tail) /\
 cse_point_has_id fn (lbl,k) inst.inst_id ==>
 ?pre ev post b. tail = pre ++ ev::post /\
 tag = SOME (start + LENGTH pre,k) /\ cse_event_covers ev b k inst
Proof
 strip_tac >> Induct >> simp[cse_history_points_def] >>
 rpt gen_tac >> strip_tac
 >- (drule_all cse_prefix_event_point_instruction >> strip_tac >>
     qexistsl [`[]`, `h`, `tail`, `b`] >> simp[]) >>
 first_x_assum drule_all >> strip_tac >>
 qexistsl [`h::pre`, `ev`, `post`, `b`] >>
 simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem cse_prefix_ordinary_suffix_crossing:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode <> PHI /\
 copy.inst_id <> use.inst_id /\
 cse_path_preorder fn d copy.inst_id /\ d <> copy.inst_id /\
 cse_path_preorder fn copy.inst_id use.inst_id /\
 j < LENGTH events /\ cse_event_covers (EL j events) db dk definst /\
 definst.inst_id = d ==>
 ?i cb ck. j < i /\ i < LENGTH events /\
   cse_event_covers (EL i events) cb ck copy
Proof
 strip_tac >>
 `MEM (EL j events) events` by metis_tac[EL_MEM] >>
 `MEM ((db.bb_label,dk),SOME (j,dk)) (cse_history_points 0 events)` by
   (drule_all cse_history_covers_points >>
    disch_then (qspec_then `0` mp_tac) >> simp[]) >>
 drule cse_history_points_cut >> strip_tac >>
 `cse_point_has_id fn (db.bb_label,dk) d` by
   metis_tac[cse_prefix_covered_point_has_id] >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 `cse_point_has_id fn (bb.bb_label,s.vs_inst_idx) use.inst_id` by
   (gvs[cse_point_has_id_def, get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
 `cse_static_trace fn (cse_project_trace events (CseExec n bb s))` by
   metis_tac[cse_prefix_project_exec] >>
 qpat_x_assum `cse_static_trace fn _` mp_tac >>
 pure_rewrite_tac[cse_project_trace_def, cse_phase_point_def] >>
 qpat_assum `cse_history_points 0 events = _` (fn th => rewrite_tac[th]) >>
 rewrite_tac[MAP_APPEND, MAP, APPEND_ASSOC] >> strip_tac >>
 `?q. MEM q (MAP FST (right ++ cse_history_points (SUC j) post) ++
                [(bb.bb_label,s.vs_inst_idx)]) /\
       cse_point_has_id fn q copy.inst_id` by
   (irule cse_path_preorder_suffix_crossing >> simp[] >>
    qexistsl [`use.inst_id`, `d`, `(db.bb_label,dk)`,
              `MAP FST (cse_history_points 0 pre) ++ MAP FST left`] >>
    pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >> conj_tac
    >- (qpat_x_assum `cse_static_trace fn _` mp_tac >>
        pure_rewrite_tac[MAP_APPEND, GSYM APPEND_ASSOC, APPEND] >>
        metis_tac[]) >>
    once_rewrite_tac[GSYM APPEND] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.LAST_APPEND_NOT_NIL,
                     LAST_DEF, NOT_CONS_NIL] >>
    simp_tac bool_ss [rich_listTheory.LAST_APPEND_NOT_NIL, LAST_DEF,
                      NOT_CONS_NIL] >> metis_tac[]) >>
 suspend "extract"
QED

Resume cse_prefix_ordinary_suffix_crossing[extract]:
 `~cse_point_has_id fn (bb.bb_label,s.vs_inst_idx) copy.inst_id` by
   (gvs[cse_point_has_id_def] >> metis_tac[]) >>
 `MEM q (MAP FST (right ++ cse_history_points (SUC j) post))` by
   metis_tac[MEM_APPEND, MEM] >>
 qpat_x_assum `MEM q (MAP FST _)` mp_tac >>
 pure_rewrite_tac[MEM_MAP] >> strip_tac >>
 PairCases_on `y` >> rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST]) >>
 qpat_x_assum `q = _` SUBST_ALL_TAC >>
 Cases_on `MEM ((y0,y1),y2) right`
 >- (`MEM ((y0,y1),y2) (cse_event_points j ev)` by
       metis_tac[MEM_APPEND, MEM] >>
     `MEM ev events` by metis_tac[MEM_APPEND, MEM] >>
     `?b. cse_event_covers ev b y1 copy` by
       metis_tac[cse_prefix_event_point_instruction] >>
     `cse_event_covers ev db dk definst` by
       (qpat_x_assum `cse_event_covers (EL j events) _ _ _` mp_tac >>
        simp[EL_APPEND_EQN]) >>
     metis_tac[cse_event_ordinary_cover_unique]) >>
 `MEM ((y0,y1),y2) (cse_history_points (SUC j) post)` by
   metis_tac[MEM_APPEND] >>
 `EVERY (\e. MEM e events) post` by
   (simp[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
 drule_all cse_prefix_history_point_instruction >> strip_tac >>
 qexistsl [`SUC j + LENGTH pre'`, `b`, `y1`] >>
 conj_tac >- decide_tac >>
 conj_tac >- (gvs[] >> simp[] >> decide_tac) >>
 qpat_assum `events = pre ++ ev::post` (fn th => rewrite_tac[th]) >>
 qpat_assum `post = pre' ++ _` (fn th => rewrite_tac[th]) >>
 simp[EL_APPEND_EQN, arithmeticTheory.ADD1] >>
 pure_rewrite_tac[GSYM arithmeticTheory.ADD1, EL] >>
 simp[EL_APPEND_EQN]
QED
Finalise cse_prefix_ordinary_suffix_crossing

Theorem cse_prefix_live_ordinary_predecessor_nonwriting:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 events = pre ++ [CseStep m cb copy u t] ++ post /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode <> PHI /\
 copy.inst_outputs = [y] /\ EVERY (\ev. ~cse_event_writes ev y) post /\
 MEM d (fn_insts fn) /\ MEM x d.inst_outputs /\
 cse_path_preorder fn d.inst_id copy.inst_id /\ d.inst_id <> copy.inst_id /\
 cse_path_preorder fn copy.inst_id use.inst_id /\ copy.inst_id <> use.inst_id ==>
 EVERY (\ev. ~cse_event_writes ev x) (CseStep m cb copy u t :: post)
Proof
 strip_tac >>
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 `~MEM x copy.inst_outputs` by
   (strip_tac >> `d = copy` by
      (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[]) >>
    gvs[]) >>
 simp[cse_event_writes_def] >>
 rewrite_tac[EVERY_EL] >> qx_gen_tac `k` >> strip_tac >>
 BETA_TAC >> strip_tac >>
 `MEM (EL k post) events` by metis_tac[EL_MEM, MEM_APPEND] >>
 drule_all cse_prefix_writing_static_definer >> strip_tac >>
 `LENGTH pre + 1 + k < LENGTH events` by (gvs[] >> simp[] >> decide_tac) >>
 `EL (LENGTH pre + 1 + k) events = EL k post` by
   (qpat_assum `events = _` (fn th => rewrite_tac[th]) >>
    simp[EL_APPEND_EQN]) >>
 `?i b l. LENGTH pre + 1 + k < i /\ i < LENGTH events /\
    cse_event_covers (EL i events) b l copy` by
   (metis_tac[cse_prefix_ordinary_suffix_crossing]) >>
 `LENGTH pre + 1 <= i` by decide_tac >>
 `i - (LENGTH pre + 1) < LENGTH post` by
   (qpat_x_assum `i < LENGTH events` mp_tac >> simp[] >> decide_tac) >>
 `EL i events = EL (i - (LENGTH pre + 1)) post` by
   (qpat_assum `events = _` (fn th => rewrite_tac[th]) >>
    simp[EL_APPEND_EQN]) >>
 `MEM (EL i events) post` by metis_tac[EL_MEM] >>
 `cse_event_writes (EL i events) y` by
   (irule cse_prefix_covered_write >> metis_tac[MEM]) >>
 qpat_x_assum `EVERY _ post` mp_tac >> rewrite_tac[EVERY_MEM] >>
 metis_tac[]
QED

Theorem cse_prefix_live_ordinary_predecessor_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 events = pre ++ [CseStep m cb copy u t] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode <> PHI /\
 copy.inst_outputs = [y] /\ EVERY (\ev. ~cse_event_writes ev y) post /\
 MEM d (fn_insts fn) /\ MEM x d.inst_outputs /\
 cse_path_preorder fn d.inst_id copy.inst_id /\ d.inst_id <> copy.inst_id /\
 cse_path_preorder fn copy.inst_id use.inst_id /\ copy.inst_id <> use.inst_id ==>
 lookup_var x s = lookup_var x u
Proof
 strip_tac >>
 drule_all cse_prefix_live_ordinary_predecessor_nonwriting >> strip_tac >>
 `lookup_var x (cse_phase_state (CseExec n bb s)) =
  lookup_var x (cse_phase_state (CseExec m cb u))` suffices_by
   simp[cse_phase_state_def] >>
 irule cse_prefix_nonwriting_cut_binding >>
 goal_assum (drule_at Any) >>
 goal_assum (drule_at Any) >>
 qexistsl [`events`, `events`, `[]`] >> simp[]
QED

(* ASSIGN-specialized interfaces retained for existing copy consumers. *)
Theorem cse_prefix_copy_suffix_crossing:
 wf_function fn /\ fn_inst_wf fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode = ASSIGN /\
 copy.inst_id <> use.inst_id /\
 cse_path_preorder fn d copy.inst_id /\ d <> copy.inst_id /\
 cse_path_preorder fn copy.inst_id use.inst_id /\
 j < LENGTH events /\ cse_event_covers (EL j events) db dk definst /\
 definst.inst_id = d ==>
 ?i cb ck. j < i /\ i < LENGTH events /\
   cse_event_covers (EL i events) cb ck copy
Proof
 strip_tac >> `copy.inst_opcode <> PHI` by simp[] >>
 drule_all cse_prefix_ordinary_suffix_crossing >> simp[]
QED

Theorem cse_prefix_live_copy_predecessor_nonwriting:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 events = pre ++ [CseStep m cb copy u t] ++ post /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode = ASSIGN /\
 copy.inst_outputs = [y] /\ EVERY (\ev. ~cse_event_writes ev y) post /\
 MEM d (fn_insts fn) /\ MEM x d.inst_outputs /\
 cse_path_preorder fn d.inst_id copy.inst_id /\ d.inst_id <> copy.inst_id /\
 cse_path_preorder fn copy.inst_id use.inst_id /\ copy.inst_id <> use.inst_id ==>
 EVERY (\ev. ~cse_event_writes ev x) (CseStep m cb copy u t :: post)
Proof
 strip_tac >> `copy.inst_opcode <> PHI` by simp[] >>
 drule_all cse_prefix_live_ordinary_predecessor_nonwriting >> simp[]
QED

Theorem cse_prefix_live_copy_predecessor_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 events = pre ++ [CseStep m cb copy u t] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode = ASSIGN /\
 copy.inst_outputs = [y] /\ EVERY (\ev. ~cse_event_writes ev y) post /\
 MEM d (fn_insts fn) /\ MEM x d.inst_outputs /\
 cse_path_preorder fn d.inst_id copy.inst_id /\ d.inst_id <> copy.inst_id /\
 cse_path_preorder fn copy.inst_id use.inst_id /\ copy.inst_id <> use.inst_id ==>
 lookup_var x s = lookup_var x u
Proof
 strip_tac >> `copy.inst_opcode <> PHI` by simp[] >>
 drule_all cse_prefix_live_ordinary_predecessor_binding >> simp[]
QED

Theorem cse_prefix_def_use_distinct:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM (Var y) use.inst_operands /\
 MEM copy (fn_insts fn) /\ MEM y copy.inst_outputs ==>
 copy.inst_id <> use.inst_id
Proof
 strip_tac >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `MEM use bb.bb_instructions` by
   (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
 `def_available_at fn bb (SOME use) y` by
   (qpat_x_assum `cse_reachable_wf_ssa fn` mp_tac >>
    simp[cse_reachable_wf_ssa_def] >> strip_tac >>
    first_x_assum (qspecl_then [`bb`, `use`] mp_tac) >> simp[]) >>
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 qpat_x_assum `def_available_at fn bb (SOME use) y` mp_tac >>
 rewrite_tac[def_available_at_def] >> strip_tac >>
 `MEM def_inst (fn_insts fn)` by
   (simp[fn_insts_def] >>
    qpat_x_assum `MEM def_bb fn.fn_blocks` mp_tac >>
    qspec_tac (`fn.fn_blocks`, `bbs`) >>
    Induct >> simp[fn_insts_blocks_def] >> rpt strip_tac >> gvs[]) >>
 `def_inst = copy` by
   (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
 qpat_x_assum `def_inst = copy` SUBST_ALL_TAC >>
 `lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
   (conj_tac >> irule MEM_lookup_block >>
    gvs[wf_function_def, fn_labels_def]) >>
 strip_tac >>
     `?i. i < LENGTH def_bb.bb_instructions /\ EL i def_bb.bb_instructions = copy` by
       metis_tac[MEM_EL] >>
     `cse_point_has_id fn (def_bb.bb_label,i) copy.inst_id` by
       (simp[cse_point_has_id_def] >> metis_tac[]) >>
     `cse_point_has_id fn (bb.bb_label,s.vs_inst_idx) copy.inst_id` by
       (gvs[get_instruction_def, cse_point_has_id_def, AllCaseEqs()] >> metis_tac[]) >>
     `def_bb.bb_label = bb.bb_label` by metis_tac[cse_point_has_id_injective, pairTheory.PAIR_EQ] >>
     `def_bb = bb` by metis_tac[optionTheory.SOME_11] >>
     gvs[] >>
     `cse_point_has_id fn (bb.bb_label,i') (EL j bb.bb_instructions).inst_id /\
      cse_point_has_id fn (bb.bb_label,j) (EL j bb.bb_instructions).inst_id` by
       (gvs[cse_point_has_id_def] >> metis_tac[]) >>
     `i' = j` by metis_tac[cse_point_has_id_injective, pairTheory.PAIR_EQ] >> decide_tac
QED

Theorem cse_prefix_def_use_order:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM (Var y) use.inst_operands /\
 MEM copy (fn_insts fn) /\ MEM y copy.inst_outputs ==>
 cse_path_preorder fn copy.inst_id use.inst_id
Proof
 strip_tac >>
 drule_all cse_prefix_exec_control >> strip_tac >>
 `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `MEM use bb.bb_instructions` by
   (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
 `def_available_at fn bb (SOME use) y` by
   (qpat_x_assum `cse_reachable_wf_ssa fn` mp_tac >>
    simp[cse_reachable_wf_ssa_def] >> strip_tac >>
    first_x_assum (qspecl_then [`bb`, `use`] mp_tac) >> simp[]) >>
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 qpat_x_assum `def_available_at fn bb (SOME use) y` mp_tac >>
 rewrite_tac[def_available_at_def] >> strip_tac >>
 `MEM def_inst (fn_insts fn)` by
   (simp[fn_insts_def] >>
    qpat_x_assum `MEM def_bb fn.fn_blocks` mp_tac >>
    qspec_tac (`fn.fn_blocks`, `bbs`) >>
    Induct >> simp[fn_insts_blocks_def] >> rpt strip_tac >> gvs[]) >>
 `def_inst = copy` by
   (irule ssa_outputs_same_inst >> gvs[fn_insts_def] >> metis_tac[MEM]) >>
 qpat_x_assum `def_inst = copy` SUBST_ALL_TAC >>
 `lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
   (conj_tac >> irule MEM_lookup_block >>
    gvs[wf_function_def, fn_labels_def]) >>
 irule cse_dominates_local_order_preorder >> simp[] >>
 qexistsl_tac [`bb`, `def_bb`] >> simp[] >>
 qpat_x_assum `def_bb = bb ==> _` mp_tac >> simp[]
QED

Theorem cse_prefix_copy_use_distinct:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM (Var y) use.inst_operands /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode = ASSIGN /\
 copy.inst_outputs = [y] ==>
 copy.inst_id <> use.inst_id
Proof
 strip_tac >> irule cse_prefix_def_use_distinct >> metis_tac[MEM]
QED

Theorem cse_prefix_copy_use_order:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM (Var y) use.inst_operands /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode = ASSIGN /\
 copy.inst_outputs = [y] ==>
 cse_path_preorder fn copy.inst_id use.inst_id
Proof
 strip_tac >> irule cse_prefix_def_use_order >> metis_tac[MEM]
QED

Theorem cse_prefix_assign_use_rewind_predecessors:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM (Var y) use.inst_operands /\
 MEM copy (fn_insts fn) /\ copy.inst_opcode = ASSIGN /\
 copy.inst_outputs = [y] /\ copy.inst_operands = [arg] ==>
 ?pre post m cb u t value.
   events = pre ++ [CseStep m cb copy u t] ++ post /\
   cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
   get_instruction cb u.vs_inst_idx = SOME copy /\
   eval_operand arg u = SOME value /\
   eval_operand (Var y) s = SOME value /\
   EVERY (\ev. ~cse_event_writes ev y) post /\
   LENGTH pre < LENGTH events /\
   (!d x. MEM d (fn_insts fn) /\ MEM x d.inst_outputs /\
      cse_path_preorder fn d.inst_id copy.inst_id /\ d.inst_id <> copy.inst_id ==>
      lookup_var x s = lookup_var x u /\
      EVERY (\ev. ~cse_event_writes ev x) (CseStep m cb copy u t :: post))
Proof
 strip_tac >>
 `cse_path_preorder fn copy.inst_id use.inst_id` by
   metis_tac[cse_prefix_copy_use_order] >>
 `copy.inst_id <> use.inst_id` by metis_tac[cse_prefix_copy_use_distinct] >>
 drule_all cse_prefix_assign_use_rewind >> strip_tac >>
 `!d x. MEM d (fn_insts fn) /\ MEM x d.inst_outputs /\
    cse_path_preorder fn d.inst_id copy.inst_id /\ d.inst_id <> copy.inst_id ==>
    lookup_var x s = lookup_var x u /\
    EVERY (\ev. ~cse_event_writes ev x) (CseStep m cb copy u t :: post)` by
   (rpt gen_tac >> strip_tac >> conj_tac
    >- (drule_all cse_prefix_live_copy_predecessor_binding >> simp[]) >>
    drule_all cse_prefix_live_copy_predecessor_nonwriting >> simp[]) >>
 qexistsl_tac [`pre`, `post`, `m`, `cb`, `u`, `t`, `value`] >>
 gvs[EVERY_DEF] >> first_assum ACCEPT_TAC
QED

Theorem cse_prefix_some_operand_current_binding_aux[local]:
 !d seen op. !fn ctx fuel0 s0 events n bb s use k.
 d = dfg_build_function fn /\
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer d seen op = SOME k ==>
 ?v definer.
 FLOOKUP (dfg_build_function fn).dfg_defs v = SOME definer /\
 definer.inst_opcode <> ASSIGN /\ definer.inst_id = k /\
 MEM definer (fn_insts fn) /\ MEM v definer.inst_outputs /\
 eval_operand op s = lookup_var v s /\
 cse_path_preorder fn definer.inst_id use.inst_id /\
 definer.inst_id <> use.inst_id /\
 (!visited. set visited = seen ==>
   (is_pseudo definer.inst_opcode \/ 1 < LENGTH definer.inst_outputs) ==>
   availExprDefs$mk_operand_expr d visited op = ExprVar v)
Proof
 recInduct cseDefsTheory.operand_producer_ind >> rpt strip_tac >>
 gvs[Once cseDefsTheory.operand_producer_def, AllCaseEqs()]
 >- (drule_all cse_dfg_assign_shape >> gvs[])
 >- suspend "copy"
 >- (drule_all cse_dfg_assign_shape >> gvs[]) >>
 `dfg_get_def (dfg_build_function fn) v = SOME inst` by
   simp[dfgDefsTheory.dfg_get_def_def] >>
 drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
 `MEM inst (fn_insts fn)` by gvs[fn_insts_def] >>
 `cse_path_preorder fn inst.inst_id use.inst_id` by
   (drule_all cse_prefix_def_use_order >> simp[]) >>
 `inst.inst_id <> use.inst_id` by
   (drule_all cse_prefix_def_use_distinct >> simp[]) >>
 qexistsl_tac [`v`, `inst`] >> simp[eval_operand_def] >>
 rpt strip_tac >>
 simp[Once availExprDefsTheory.mk_operand_expr_def,
      dfgDefsTheory.dfg_get_def_def] >> gvs[]
QED

Resume cse_prefix_some_operand_current_binding_aux[copy]:
 drule_all cse_dfg_assign_shape >> strip_tac >> gvs[] >>
 `dfg_get_def (dfg_build_function fn) v = SOME inst` by
   simp[dfgDefsTheory.dfg_get_def_def] >>
 drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
 `MEM inst (fn_insts fn)` by gvs[fn_insts_def] >>
 drule_all cse_prefix_assign_use_rewind_predecessors >> strip_tac >>
 `inst.inst_opcode <> PHI /\ MEM arg inst.inst_operands` by simp[] >>
 first_x_assum (qspec_then `fn` (mp_tac o SRULE [])) >>
 disch_then drule_all >> strip_tac >>
 `definer.inst_id <> inst.inst_id` by
   (strip_tac >> `definer = inst` by
      (irule fn_inst_ids_distinct_inj >> fs[wf_function_def] >> metis_tac[]) >> gvs[]) >>
 `lookup_var v' s = lookup_var v' u` by metis_tac[] >>
 `cse_path_preorder fn inst.inst_id use.inst_id` by
   (drule_all cse_prefix_copy_use_order >> simp[]) >>
 `inst.inst_id <> use.inst_id` by
   (drule_all cse_prefix_copy_use_distinct >> simp[]) >>
 `cse_point_has_id fn (bb.bb_label,s.vs_inst_idx) use.inst_id` by
   (qpat_assum `cse_prefix _ _ _ _ _ (CseExec n bb s)`
      (mp_then Any mp_tac cse_prefix_exec_control) >>
    simp[] >> strip_tac >>
    gvs[cse_point_has_id_def, get_instruction_def, AllCaseEqs()]) >>
 qpat_assum `cse_prefix _ _ _ _ _ (CseExec n bb s)`
   (mp_then Any mp_tac cse_prefix_project_exec) >>
 simp[] >> strip_tac >>
 `cse_path_preorder fn definer.inst_id use.inst_id /\
  definer.inst_id <> use.inst_id` by
   (irule cse_path_preorder_reachable_strict_chain >> metis_tac[]) >>
 qexistsl_tac [`v'`, `definer`] >> simp[] >>
 conj_tac >- metis_tac[] >>
 rpt strip_tac >>
 simp[Once availExprDefsTheory.mk_operand_expr_def,
      dfgDefsTheory.dfg_get_def_def, venomInstTheory.is_pseudo_def] >>
 first_x_assum irule >> simp[]
QED
Finalise cse_prefix_some_operand_current_binding_aux

Theorem cse_prefix_some_operand_current_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) seen op = SOME k ==>
 ?v definer.
 FLOOKUP (dfg_build_function fn).dfg_defs v = SOME definer /\
 definer.inst_opcode <> ASSIGN /\ definer.inst_id = k /\
 MEM definer (fn_insts fn) /\ MEM v definer.inst_outputs /\
 eval_operand op s = lookup_var v s /\
 cse_path_preorder fn definer.inst_id use.inst_id /\
 definer.inst_id <> use.inst_id
Proof
 strip_tac >>
 drule_at (Pos hd) (SRULE [] cse_prefix_some_operand_current_binding_aux) >>
 disch_then drule_all >> metis_tac[]
QED

Theorem cse_prefix_opaque_operand_current_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) {} op = SOME d.inst_id /\
 MEM d (fn_insts fn) /\
 (is_pseudo d.inst_opcode \/ 1 < LENGTH d.inst_outputs) ==>
 ?x. MEM x d.inst_outputs /\
     availExprDefs$mk_operand_expr (dfg_build_function fn) [] op = ExprVar x /\
     eval_operand op s = lookup_var x s /\
     cse_path_preorder fn d.inst_id use.inst_id
Proof
 strip_tac >>
 drule_at (Pos hd) (SRULE [] cse_prefix_some_operand_current_binding_aux) >>
 disch_then drule_all >> strip_tac >>
 `definer = d` by (irule fn_inst_ids_distinct_inj >> fs[wf_function_def] >> metis_tac[]) >>
 gvs[] >> qexists_tac `v` >> simp[] >>
 first_x_assum irule >> simp[]
QED

Theorem cse_prefix_some_operand_single_output_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) seen op = SOME d.inst_id /\
 MEM d (fn_insts fn) /\ d.inst_outputs = [x] ==>
 eval_operand op s = lookup_var x s
Proof
 strip_tac >> drule_all cse_prefix_some_operand_current_binding >> strip_tac >>
 `definer = d` by (irule fn_inst_ids_distinct_inj >> fs[wf_function_def] >> metis_tac[]) >>
 gvs[]
QED

Theorem cse_source_interval_same_producer_operands_equal:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 src.inst_opcode <> PHI /\ MEM sop src.inst_operands /\
 MEM src (fn_insts fn) /\ MEM d (fn_insts fn) /\ d.inst_outputs = [x] /\
 operand_producer (dfg_build_function fn) {} op = SOME d.inst_id /\
 operand_producer (dfg_build_function fn) {} sop = SOME d.inst_id /\
 cse_path_preorder fn d.inst_id src.inst_id /\ d.inst_id <> src.inst_id /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 eval_operand op s = eval_operand sop u
Proof
 strip_tac >>
 `eval_operand op s = lookup_var x s` by
   (irule cse_prefix_some_operand_single_output_binding >> metis_tac[]) >>
 `eval_operand sop u = lookup_var x u` by
   (irule cse_prefix_some_operand_single_output_binding >> metis_tac[]) >>
 `MEM x d.inst_outputs` by simp[] >>
 drule_all cse_source_interval_predecessor_binding_all >> simp[]
QED

Theorem cse_source_interval_same_opaque_producer_operands_equal:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 src.inst_opcode <> PHI /\ MEM sop src.inst_operands /\
 MEM src (fn_insts fn) /\ MEM d (fn_insts fn) /\
 (is_pseudo d.inst_opcode \/ 1 < LENGTH d.inst_outputs) /\
 availExprDefs$mk_operand_expr (dfg_build_function fn) [] op =
 availExprDefs$mk_operand_expr (dfg_build_function fn) [] sop /\
 operand_producer (dfg_build_function fn) {} op = SOME d.inst_id /\
 operand_producer (dfg_build_function fn) {} sop = SOME d.inst_id /\
 cse_path_preorder fn d.inst_id src.inst_id /\ d.inst_id <> src.inst_id /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 eval_operand op s = eval_operand sop u
Proof
 strip_tac >>
 `?x. MEM x d.inst_outputs /\
   availExprDefs$mk_operand_expr (dfg_build_function fn) [] op = ExprVar x /\
   eval_operand op s = lookup_var x s` by
   (metis_tac[cse_prefix_opaque_operand_current_binding]) >>
 `?y. MEM y d.inst_outputs /\
   availExprDefs$mk_operand_expr (dfg_build_function fn) [] sop = ExprVar y /\
   eval_operand sop u = lookup_var y u` by
   (metis_tac[cse_prefix_opaque_operand_current_binding]) >>
 `x = y` by metis_tac[availExprDefsTheory.avail_expr_11] >>
 qpat_x_assum `x = y` SUBST_ALL_TAC >>
 drule_all cse_source_interval_predecessor_binding_all >> simp[]
QED

Theorem cse_prefix_some_operand_live_writer:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 operand_producer (dfg_build_function fn) seen op = SOME d.inst_id /\
 MEM d (fn_insts fn) /\ d.inst_outputs = [x] /\ d.inst_opcode <> PHI ==>
 ?pre post m db u t.
 events = pre ++ [CseStep m db d u t] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m db u) /\
 get_instruction db u.vs_inst_idx = SOME d /\
 EVERY (\ev. ~cse_event_writes ev x) post /\
 eval_operand op s = lookup_var x t /\
 lookup_var x s = lookup_var x t /\ LENGTH pre < LENGTH events
Proof
 strip_tac >>
 `?ev. MEM ev events /\ cse_event_writes ev x` by
   (drule_all cse_prefix_some_operand_epoch >> strip_tac >>
    `dfg_get_def (dfg_build_function fn) x' = SOME d'` by
      simp[dfgDefsTheory.dfg_get_def_def] >>
    drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
    `MEM d' (fn_insts fn)` by gvs[fn_insts_def] >>
    `d' = d` by (irule fn_inst_ids_distinct_inj >> fs[wf_function_def] >> metis_tac[]) >>
    gvs[] >> metis_tac[MEM_APPEND, MEM]) >>
 qspecl_then [`events`, `x`] strip_assume_tac cse_events_last_write
 >- (gvs[EVERY_MEM] >> metis_tac[]) >>
 `ssa_form fn` by gvs[cse_reachable_wf_ssa_def] >>
 `MEM ev' events` by gvs[MEM_APPEND] >>
 `MEM x d.inst_outputs` by simp[] >>
 drule_all cse_prefix_nonphi_writer_step >> strip_tac >>
 qpat_x_assum `ev' = CseStep _ _ _ _ _` SUBST_ALL_TAC >>
 drule_all cse_prefix_step_input_cut >> strip_tac >>
 `lookup_var x s = lookup_var x v` by
   (drule_all cse_prefix_last_write_binding >> simp[cse_phase_state_def, cse_event_output_def]) >>
 `eval_operand op s = lookup_var x s` by
   (irule cse_prefix_some_operand_single_output_binding >> metis_tac[]) >>
 qexistsl [`pre`, `post`, `m`, `sb`, `u`, `v`] >> simp[]
QED
