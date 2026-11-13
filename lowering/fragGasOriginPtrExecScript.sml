(* The joint path lifts memory and pointer checks to one operational run. *)
Theory fragGasOriginPtrExec
Ancestors
  fragGasOriginPtr fragGasOrigin gasPathPtrExec fragGasPathPtr fragGasPathMem fragGasMode
  fragExec fragExecMem ptrSafeRun memSafeRun venomExecSemantics venomExecProofs
  venomState arithmetic list

Theorem gas_origin_ptr_path_exec:
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) marks (r, G', tn') ==>
  ((?t. r = OK t /\ ~t.vs_halted /\
        !fuel out.
          run_from fuel ctx func t = out /\ (!e. out <> Error e) ==>
          ?fuel'. run_from fuel' ctx func s = out /\
            ghost_run fuel' ctx func PG G tn s =
              ghost_run fuel ctx func PG G' tn' t /\
            (mem_safe_run fuel ctx func t ==>
             mem_safe_run fuel' ctx func s) /\
            (ptr_safe_run D lo fuel ctx func PG G' tn' t ==>
             ptr_safe_run D lo fuel' ctx func PG G tn s)) \/
   (exit_result r /\
    ?fuel. run_from fuel ctx func s = r /\
      ghost_run fuel ctx func PG G tn s = (G', tn') /\
      mem_safe_run fuel ctx func s /\
      ptr_safe_run D lo fuel ctx func PG G tn s))
Proof
  strip_tac >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >>
  disch_then (strip_assume_tac o MATCH_MP gas_path_mem_exec) >>
  drule gas_path_ptr_exec >> strip_tac >>
  gvs[exit_result_def]
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!fuel. _ ==> ?fuel'. _ /\ ghost_run _ _ _ _ _ _ _ = _ /\ _`
        (qspec_then `fuel` mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `fuel'` >> simp[] >> strip_tac >>
      metis_tac[mem_safe_run_all_fuel]) >>
  disj2_tac >>
  metis_tac[mem_safe_run_all_fuel, exit_result_not_error]
QED

Theorem ptr_edge_mem_continue[local]:
  gas_path_ptr_edge D lo ctx func PG G tn s n G1 tn1 (OK t) /\
  (!k. mem_safe_run k ctx func s) /\
  (?fuel. !e. run_from fuel ctx func t <> Error e) ==>
  !k. mem_safe_run k ctx func t
Proof
  simp[gas_path_ptr_edge_def] >> strip_tac >> gvs[exit_result_def]
  >~ [`exit_result (step_inst _ _ _ _)`]
  >- (Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def])
  >~ [`jump_to lbl s`]
  >- (`?target. lookup_block lbl func.fn_blocks = SOME target /\
                phi_prefix_length target.bb_instructions = 0` by
        (irule run_from_jump_target >> metis_tac[]) >>
      `eval_phis (jump_to lbl s) target.bb_instructions = OK (jump_to lbl s)` by
        simp[eval_phis_no_phi] >>
      gen_tac >>
      `step_inst (SUC (fuel + k)) ctx inst s = OK (jump_to lbl s)` by
        (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel` >> simp[]) >>
      `mem_safe_blocks (SUC (fuel + k)) ctx func (jump_to lbl s)` by
        (irule mem_safe_run_terminator >>
         `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >> metis_tac[]) >>
      `mem_safe_run (fuel + k) ctx func (jump_to lbl s)` by
        (`lookup_block (jump_to lbl s).vs_current_bb func.fn_blocks = SOME target /\
          (jump_to lbl s with vs_inst_idx := 0) = jump_to lbl s` by
           simp[jump_to_def] >>
         metis_tac[mem_safe_blocks_run]) >>
      metis_tac[mem_safe_run_fuel_mono_down, DECIDE ``k <= fuel + k``])
  >~ [`eval_phis t' target.bb_instructions = OK entered`]
  >- (gen_tac >>
      `step_inst (SUC (fuel + k)) ctx inst s = OK t'` by
        (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel` >> simp[]) >>
      `mem_safe_blocks (SUC (fuel + k)) ctx func t'` by
        (irule mem_safe_run_terminator >> metis_tac[]) >>
      `mem_safe_run (fuel + k) ctx func
         (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
        metis_tac[mem_safe_blocks_run] >>
      metis_tac[mem_safe_run_fuel_mono_down, DECIDE ``k <= fuel + k``]) >>
  gen_tac >>
  `step_inst (fuel + k) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `mem_safe_run (fuel + k) ctx func
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[mem_safe_run_step] >>
  metis_tac[mem_safe_run_fuel_mono_down, DECIDE ``k <= fuel + k``]
QED

Theorem ptr_zero_edge_mem_origin[local]:
  gas_path_ptr_edge D lo ctx func PG G tn s 0 G' tn' r /\
  (!fuel. mem_safe_run fuel ctx func s) ==>
  gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (r, G', tn')
Proof
  strip_tac >> simp[gas_origin_ptr_edge_def] >>
  irule gas_path_mem_edge_zero_origin >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_path_ptr_edge_def, gas_path_mem_edge_def] >>
  strip_tac >>
  `revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s` by
    metis_tac[mem_safe_run_head] >>
  metis_tac[]
QED

Theorem ptr_zero_path_mem_origin[local]:
  !D lo ctx func PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx func PG G tn s n G' tn' r ==>
    n = 0 /\ exit_result r /\ (!fuel. mem_safe_run fuel ctx func s) ==>
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) [] (r, G', tn')
Proof
  ho_match_mp_tac gas_path_ptr_strongind >> rpt conj_tac
  >- simp[exit_result_def]
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
      rename1 `gas_path_ptr_edge D lo ctx func PG G tn s 0 Gmid tnmid (OK t)` >>
      `?fuel. !e. run_from fuel ctx func t <> Error e` by
        (drule gas_path_ptr_exec >>
         metis_tac[exit_result_def, exit_result_not_error]) >>
      `!fuel. mem_safe_run fuel ctx func t` by
        (irule ptr_edge_mem_continue >> metis_tac[]) >>
      `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK t, Gmid, tnmid)` by
        (irule ptr_zero_edge_mem_origin >> simp[]) >>
      first_x_assum drule >> strip_tac >>
      metis_tac[cj 2 gas_origin_ptr_path_rules, APPEND]) >>
  rpt strip_tac >> gvs[] >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[] >>
  irule ptr_zero_edge_mem_origin >> simp[]
QED

(* Terminal zero-count paths have fixed empty marks. This claim keeps the
   pointer path's exact ghosts; zero GAS does not mean unchanged ghosts.
   A standalone entry prefix ending in OK is outside this statement. *)
Theorem gas_zero_paths_joint:
  gas_path_mem ctx func s 0 r /\
  gas_path_ptr D lo ctx func PG G tn s 0 G' tn' r /\
  exit_result r ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (r, G', tn')
Proof
  strip_tac >>
  `!fuel. mem_safe_run fuel ctx func s` by
    (drule gas_path_mem_exec >>
     metis_tac[exit_result_def, exit_result_not_error, mem_safe_run_all_fuel]) >>
  drule ptr_zero_path_mem_origin >> simp[]
QED
