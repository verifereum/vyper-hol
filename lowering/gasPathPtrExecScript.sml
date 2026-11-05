(*
 * S3 piece: a counted pointer-checked path is a pointer-safe run.  The
 * pointer twin of fragGasPathMem's gas_path_mem_exec: a path that goes on
 * at t gives every run from t as a run from s, with the ghost carried
 * along and pointer safety back to s; one that stops gives the run from s
 * that stops there, pointer-safe, with the ghost where it stops.
 *
 * TOP-LEVEL:
 *   gas_path_ptr_exec -- the piece
 *)
Theory gasPathPtrExec
Ancestors
  fragGasPathPtr fragGasPath fragExec ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomInstProofs venomState
  arithmetic list

Theorem run_from_frame_run[local]:
  !fuel ctx fn s. run_from fuel ctx fn s = frame_run fuel ctx fn s
Proof
  simp[run_from_def, frame_run_def, block_run_def]
QED

(* A step inside a block: the run, the ghost and the check from the next
   instruction are those from s, with the step's fuel added. *)
Theorem ptr_within_step[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fe ctx inst s = OK t' /\ ~is_terminator inst.inst_opcode /\
  ptr_safe_step D lo fe ctx fn PG G tn inst s /\
  ghost_step fe ctx PG G tn inst s = (G1, tn1) /\
  (!e. run_from fuel ctx fn (t' with vs_inst_idx := SUC s.vs_inst_idx)
       <> Error e) ==>
  run_from (fe + fuel) ctx fn s =
    run_from fuel ctx fn (t' with vs_inst_idx := SUC s.vs_inst_idx) /\
  ghost_run (fe + fuel) ctx fn PG G tn s =
    ghost_run fuel ctx fn PG G1 tn1
      (t' with vs_inst_idx := SUC s.vs_inst_idx) /\
  (ptr_safe_run D lo fuel ctx fn PG G1 tn1
     (t' with vs_inst_idx := SUC s.vs_inst_idx) ==>
   ptr_safe_run D lo (fe + fuel) ctx fn PG G tn s)
Proof
  strip_tac >>
  `t'.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `step_inst (fe + fuel) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fe` >> simp[]) >>
  `!e. block_run fuel ctx fn bb (t' with vs_inst_idx := SUC s.vs_inst_idx)
       <> Error e` by gvs[run_from_frame_run, frame_run_def] >>
  `block_run (fe + fuel) ctx fn bb (t' with vs_inst_idx := SUC s.vs_inst_idx) =
   block_run fuel ctx fn bb (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule block_run_fuel_mono >> simp[]) >>
  `ghost_step (fe + fuel) ctx PG G tn inst s =
   ghost_step fe ctx PG G tn inst s` by
    (irule (cj 1 ghost_fuel_mono_up) >> simp[]) >>
  `ghost_block (fe + fuel) ctx fn PG G1 tn1 bb
     (t' with vs_inst_idx := SUC s.vs_inst_idx) =
   ghost_block fuel ctx fn PG G1 tn1 bb
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (cj 2 ghost_fuel_mono_up) >> simp[]) >>
  rpt conj_tac
  >- (simp[run_from_frame_run, frame_run_def] >>
      metis_tac[block_run_step])
  >- (qspecl_then [`fe + fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`, `s`,
                   `inst`, `t'`] mp_tac ghost_block_step >>
      simp[ghost_run_def]) >>
  strip_tac >>
  `ptr_safe_block D lo fuel ctx fn PG G1 tn1 bb
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by gvs[ptr_safe_run_def] >>
  `ptr_safe_block D lo (fe + fuel) ctx fn PG G1 tn1 bb
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (cj 2 ptr_safe_fuel_mono_up) >> qexists_tac `fuel` >> simp[]) >>
  `ptr_safe_step D lo (fe + fuel) ctx fn PG G tn inst s` by
    (irule (cj 1 ptr_safe_fuel_mono_up) >> qexists_tac `fe` >> simp[]) >>
  qspecl_then [`D`, `lo`, `fe + fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`,
               `s`, `inst`, `t'`] mp_tac ptr_safe_block_step >>
  simp[ptr_safe_run_def]
QED

(* A terminator that enters a block: the run, the ghost and the check from
   past the target's PHIs are those from s, one block later. *)
Theorem ptr_enter_step[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fe ctx inst s = OK t' /\ is_terminator inst.inst_opcode /\
  ~t'.vs_halted /\
  lookup_block t'.vs_current_bb fn.fn_blocks = SOME target /\
  eval_phis t' target.bb_instructions = OK entered /\
  ptr_safe_step D lo fe ctx fn PG G tn inst s /\
  (!e. run_from fuel ctx fn
         (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)
       <> Error e) ==>
  run_from (SUC (fe + fuel)) ctx fn s =
    run_from fuel ctx fn
      (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) /\
  ghost_run (SUC (fe + fuel)) ctx fn PG G tn s =
    ghost_run fuel ctx fn PG (entry_prov fn t' G) (entry_taint_vars fn t' tn)
      (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) /\
  (ptr_safe_run D lo fuel ctx fn PG (entry_prov fn t' G)
     (entry_taint_vars fn t' tn)
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) ==>
   ptr_safe_run D lo (SUC (fe + fuel)) ctx fn PG G tn s)
Proof
  strip_tac >>
  `entered.vs_current_bb = t'.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `step_inst (SUC (fe + fuel)) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fe` >> simp[]) >>
  `!e. block_run fuel ctx fn target
         (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)
       <> Error e` by gvs[run_from_frame_run, frame_run_def] >>
  `block_run (fe + fuel) ctx fn target
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
   block_run fuel ctx fn target
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule block_run_fuel_mono >> simp[]) >>
  `ghost_block (fe + fuel) ctx fn PG (entry_prov fn t' G)
     (entry_taint_vars fn t' tn) target
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
   ghost_block fuel ctx fn PG (entry_prov fn t' G)
     (entry_taint_vars fn t' tn) target
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule (cj 2 ghost_fuel_mono_up) >> simp[]) >>
  rpt conj_tac
  >- (simp[run_from_frame_run, frame_run_def] >>
      metis_tac[block_run_terminator, run_blocks_block_run])
  >- (simp[ghost_run_def] >>
      metis_tac[ghost_block_terminator, ghost_blocks_block]) >>
  strip_tac >>
  `ptr_safe_block D lo fuel ctx fn PG (entry_prov fn t' G)
     (entry_taint_vars fn t' tn) target
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    gvs[ptr_safe_run_def] >>
  `ptr_safe_block D lo (fe + fuel) ctx fn PG (entry_prov fn t' G)
     (entry_taint_vars fn t' tn) target
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule (cj 2 ptr_safe_fuel_mono_up) >> qexists_tac `fuel` >> simp[]) >>
  `ptr_safe_step D lo (SUC (fe + fuel)) ctx fn PG G tn inst s` by
    (irule (cj 1 ptr_safe_fuel_mono_up) >> qexists_tac `fe` >> simp[]) >>
  simp[ptr_safe_run_def] >>
  metis_tac[ptr_safe_block_terminator, ptr_safe_blocks_block]
QED

(* No PHIs at the block entered: the entry ghost is the ghost. *)
Theorem jump_entry_ghost[local]:
  !fn s bb G tn.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0 ==>
    entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  rpt strip_tac >> Cases_on `bb.bb_instructions` >>
  gvs[phi_prefix_length_def, entry_prov_def, entry_taint_vars_def,
      phis_prov_def, phis_taint_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def, phis_prov_def, phis_taint_def]
QED

(* A jump to the start of a block: the run from jump_to does not fail, so
   the block has no PHIs and the jump is an entry with nothing to evaluate. *)
Theorem ptr_jump_step[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ ~s.vs_halted /\
  step_inst fe ctx inst s = OK (jump_to lbl s) /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ptr_safe_step D lo fe ctx fn PG G tn inst s /\
  (!e. run_from fuel ctx fn (jump_to lbl s) <> Error e) ==>
  run_from (SUC (fe + fuel)) ctx fn s = run_from fuel ctx fn (jump_to lbl s) /\
  ghost_run (SUC (fe + fuel)) ctx fn PG G tn s =
    ghost_run fuel ctx fn PG G tn (jump_to lbl s) /\
  (ptr_safe_run D lo fuel ctx fn PG G tn (jump_to lbl s) ==>
   ptr_safe_run D lo (SUC (fe + fuel)) ctx fn PG G tn s)
Proof
  strip_tac >>
  `?target. lookup_block lbl fn.fn_blocks = SOME target /\
            phi_prefix_length target.bb_instructions = 0` by
    (irule run_from_jump_target >> metis_tac[]) >>
  `eval_phis (jump_to lbl s) target.bb_instructions = OK (jump_to lbl s)` by
    simp[eval_phis_no_phi] >>
  `(jump_to lbl s).vs_current_bb = lbl /\ ~(jump_to lbl s).vs_halted /\
   jump_to lbl s with vs_inst_idx := 0 = jump_to lbl s` by
    simp[jump_to_def] >>
  `entry_prov fn (jump_to lbl s) G = G /\
   entry_taint_vars fn (jump_to lbl s) tn = tn` by
    (irule jump_entry_ghost >> metis_tac[]) >>
  qspecl_then [`jump_to lbl s`, `jump_to lbl s`] mp_tac
    (Q.GENL [`t'`, `entered`] ptr_enter_step) >>
  simp[]
QED

Theorem ptr_edge_continue[local]:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G1 tn1 (OK t) /\
  (!e. run_from fuel ctx fn t <> Error e) ==>
  ?fuel'. run_from fuel' ctx fn s = run_from fuel ctx fn t /\
    ghost_run fuel' ctx fn PG G tn s = ghost_run fuel ctx fn PG G1 tn1 t /\
    (ptr_safe_run D lo fuel ctx fn PG G1 tn1 t ==>
     ptr_safe_run D lo fuel' ctx fn PG G tn s)
Proof
  simp[gas_path_ptr_edge_def] >> strip_tac >> gvs[exit_result_def]
  >~ [`exit_result (step_inst _ _ _ _)`]
  >- (Cases_on `step_inst fuel' ctx inst s` >> gvs[exit_result_def])
  >~ [`jump_to lbl s`]
  >- (qexists_tac `SUC (fuel' + fuel)` >> irule ptr_jump_step >>
      simp[] >> metis_tac[])
  >~ [`eval_phis t' target.bb_instructions = OK entered`]
  >- (qexists_tac `SUC (fuel' + fuel)` >> irule ptr_enter_step >>
      simp[] >> metis_tac[]) >>
  qexists_tac `fuel' + fuel` >> irule ptr_within_step >>
  simp[] >> metis_tac[]
QED

Theorem ptr_edge_exit[local]:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r /\
         ghost_run fuel ctx fn PG G tn s = (G', tn') /\
         ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  simp[gas_path_ptr_edge_def] >> strip_tac >> gvs[exit_result_def] >>
  qexists_tac `fuel` >>
  simp[run_from_def, ghost_run_def, ptr_safe_run_def] >>
  simp[Once exec_block_def, Once ghost_block_def, Once ptr_safe_block_def] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def]
QED

Theorem gas_path_ptr_exec:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    gas_path ctx fn s n r /\
    ((?t. r = OK t /\ ~t.vs_halted /\
          !fuel out.
            run_from fuel ctx fn t = out /\ (!e. out <> Error e) ==>
            ?fuel'. run_from fuel' ctx fn s = out /\
                    ghost_run fuel' ctx fn PG G tn s =
                      ghost_run fuel ctx fn PG G' tn' t /\
                    (ptr_safe_run D lo fuel ctx fn PG G' tn' t ==>
                     ptr_safe_run D lo fuel' ctx fn PG G tn s)) \/
     (exit_result r /\
      ?fuel. run_from fuel ctx fn s = r /\
             ghost_run fuel ctx fn PG G tn s = (G', tn') /\
             ptr_safe_run D lo fuel ctx fn PG G tn s))
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- (rpt strip_tac >- metis_tac[gas_path_rules] >>
      disj1_tac >> qexists_tac `s` >> simp[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      (conj_tac >- metis_tac[gas_path_ptr_edge_erase, gas_path_rules])
      >- (disj1_tac >> simp[] >> rpt strip_tac >>
          first_x_assum drule_all >> strip_tac >>
          metis_tac[ptr_edge_continue]) >>
      disj2_tac >> simp[] >>
      metis_tac[ptr_edge_continue, exit_result_not_error]) >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[gas_path_ptr_edge_erase, gas_path_rules] >>
  disj2_tac >> simp[] >> metis_tac[ptr_edge_exit]
QED
