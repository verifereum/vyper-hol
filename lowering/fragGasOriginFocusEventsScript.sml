(*
 * A GAS-origin focus marks a prefix of its run's recorded GAS sites.
 *
 * The focus may stop inside a callee or before the run ends, so it fixes
 * only a prefix of the events gas_events_blocks records at a large enough
 * fuel; gas_origin_path_events is the exit-run twin, which fixes all of them.
 *
 * TOP-LEVEL:
 *   gas_origin_focus_entry_events - from a block start, the focus marks are
 *                                   a prefix of the run's marked events
 *)
Theory fragGasOriginFocusEvents
Ancestors
  fragGasOrigin fragGasFocus gasEventsFuel gasEvents fragExec
  venomExecProofs venomExecSemantics venomInst venomState list arithmetic

(* ===== Events of a block suffix and its continuation ===== *)

(* Helper: more fuel only extends the recorded events. *)
Theorem gas_events_from_fuel_mono[local]:
  n <= m ==>
  ?extra.
    gas_events_block m ctx owner bb s ++
      (case exec_block m ctx bb s of
         OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
       | _ => []) =
    gas_events_block n ctx owner bb s ++
      (case exec_block n ctx bb s of
         OK u => if u.vs_halted then [] else gas_events_blocks n ctx func u
       | _ => []) ++ extra
Proof
  strip_tac >>
  qspecl_then [`n`, `ctx`, `owner`, `bb`, `s`, `m`] mp_tac
    (cj 2 gas_events_fuel_extension) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `exec_block n ctx bb s` >> gvs[] >>
  rename1 `_ = OK v` >> Cases_on `v.vs_halted` >> simp[] >>
  qspecl_then [`n`, `ctx`, `func`, `v`, `m`] mp_tac
    (cj 3 gas_events_fuel_extension) >>
  impl_tac >- simp[] >> strip_tac >> simp[]
QED

(* Helper: the events from an instruction start with its own. *)
Theorem gas_events_from_step[local]:
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  ?extra.
    gas_events_block m ctx owner bb s ++
      (case exec_block m ctx bb s of
         OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
       | _ => []) =
    gas_events_step m ctx owner inst s ++ extra
Proof
  strip_tac >> simp[Once gas_events_block_def]
QED

(* Helper: a non-terminator that steps OK passes the events on. *)
Theorem gas_events_from_istep[local]:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ step_inst m ctx inst s = OK u ==>
  gas_events_block m ctx owner bb s ++
    (case exec_block m ctx bb s of
       OK v => if v.vs_halted then [] else gas_events_blocks m ctx func v
     | _ => []) =
  gas_events_step m ctx owner inst s ++
    (gas_events_block m ctx owner bb (u with vs_inst_idx := SUC s.vs_inst_idx) ++
     (case exec_block m ctx bb (u with vs_inst_idx := SUC s.vs_inst_idx) of
        OK v => if v.vs_halted then [] else gas_events_blocks m ctx func v
      | _ => []))
Proof
  strip_tac >>
  CONV_TAC (LHS_CONV
    (ONCE_REWRITE_CONV [gas_events_block_def, exec_block_def])) >>
  simp[]
QED

(* Helper: at a block start, a PHI makes the events empty. *)
Theorem gas_events_from_phi_start[local]:
  s.vs_inst_idx = 0 /\ phi_prefix_length bb.bb_instructions <> 0 ==>
  gas_events_block m ctx owner bb s ++
    (case exec_block m ctx bb s of
       OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
     | _ => []) = []
Proof
  strip_tac >> Cases_on `bb.bb_instructions` >> fs[phi_prefix_length_def] >>
  rename1 `bb.bb_instructions = phi_inst :: _` >>
  Cases_on `phi_inst.inst_opcode = PHI` >> fs[] >>
  `get_instruction bb s.vs_inst_idx = SOME phi_inst` by
    simp[get_instruction_def] >>
  `step_inst m ctx phi_inst s = Error "phi outside prefix"` by
    simp[step_inst_phi_error] >>
  simp[Once gas_events_block_def, Once exec_block_def, gas_events_step_def]
QED

(* ===== One edge ===== *)

(* Helper: glue a prefix of the events past an edge to the edge's own. *)
Theorem map_glue[local]:
  X = A ++ (Z ++ e) /\ MAP g Z = right ++ extra ==>
  MAP g X = MAP g A ++ right ++ (extra ++ MAP g e)
Proof
  rw[] >> REWRITE_TAC [MAP_APPEND] >> asm_rewrite_tac[] >>
  REWRITE_TAC [APPEND_ASSOC]
QED

Theorem map_glue0[local]:
  X = A ++ Z /\ MAP g Z = right ++ extra ==>
  MAP g X = MAP g A ++ right ++ extra
Proof
  rw[] >> REWRITE_TAC [MAP_APPEND] >> asm_rewrite_tac[] >>
  REWRITE_TAC [APPEND_ASSOC]
QED

(* Helper: a terminator entering the next block passes the events on. *)
Theorem gas_events_from_enter[local]:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\
  step_inst (SUC M) ctx inst s = OK stepped /\ ~stepped.vs_halted /\
  lookup_block stepped.vs_current_bb func.fn_blocks = SOME target /\
  eval_phis stepped target.bb_instructions = OK entered ==>
  (gas_events_block (SUC M) ctx func.fn_name bb s ++
     (case exec_block (SUC M) ctx bb s of
        OK v => if v.vs_halted then [] else gas_events_blocks (SUC M) ctx func v
      | _ => [])) =
  gas_events_step (SUC M) ctx func.fn_name inst s ++
  (gas_events_block M ctx func.fn_name target (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) ++
     (case exec_block M ctx target (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) of
        OK v => if v.vs_halted then [] else gas_events_blocks M ctx func v
      | _ => []))
Proof
  strip_tac >>
  CONV_TAC (LHS_CONV
    (ONCE_REWRITE_CONV [gas_events_block_def, exec_block_def])) >>
  simp[] >> simp[Once gas_events_blocks_def]
QED

(* Helper: a raw jump to a PHI-free block passes the events on. *)
Theorem gas_events_from_jump[local]:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\
  step_inst (SUC n) ctx inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
  lookup_block lbl func.fn_blocks = SOME bt /\
  phi_prefix_length bt.bb_instructions = 0 ==>
  (gas_events_block (SUC n) ctx func.fn_name bb s ++
     (case exec_block (SUC n) ctx bb s of
        OK v => if v.vs_halted then [] else gas_events_blocks (SUC n) ctx func v
      | _ => [])) =
  gas_events_step (SUC n) ctx func.fn_name inst s ++
  (gas_events_block n ctx func.fn_name bt (jump_to lbl s) ++
     (case exec_block n ctx bt (jump_to lbl s) of
        OK v => if v.vs_halted then [] else gas_events_blocks n ctx func v
      | _ => []))
Proof
  strip_tac >>
  `(jump_to lbl s).vs_current_bb = lbl /\ ~(jump_to lbl s).vs_halted /\
   jump_to lbl s with vs_inst_idx := 0 = jump_to lbl s` by
    simp[jump_to_def] >>
  `eval_phis (jump_to lbl s) bt.bb_instructions = OK (jump_to lbl s)` by
    simp[eval_phis_no_phi] >>
  CONV_TAC (LHS_CONV
    (ONCE_REWRITE_CONV [gas_events_block_def, exec_block_def])) >>
  simp[] >> simp[Once gas_events_blocks_def]
QED

(* Helper: the run past an edge's jump or block entry, with its fuel. *)
Theorem gas_origin_edge_events_next[local]:
  gas_origin_edge memory explicit ctx func s left (OK t) /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bt /\
  MAP (\key. key IN explicit)
    (gas_events_block n ctx func.fn_name bt t ++
     case exec_block n ctx bt t of
       OK u => if u.vs_halted then [] else gas_events_blocks n ctx func u
     | _ => []) = right ++ extra /\ right <> [] ==>
  ?bb m extra'. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    MAP (\key. key IN explicit)
      (gas_events_block m ctx func.fn_name bb s ++
       case exec_block m ctx bb s of
         OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
       | _ => []) = left ++ right ++ extra'
Proof
  rw[gas_origin_edge_def] >> gvs[exit_result_def]
  >- suspend "within"
  >- suspend "enter"
  >- suspend "jump" >>
  qpat_x_assum `OK _ = _` (assume_tac o GSYM) >> gvs[exit_result_def]
QED

Resume gas_origin_edge_events_next[within]:
  rename1 `step_inst fuel ctx inst s = OK stepped` >>
  `stepped.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  gvs[] >>
  qpat_x_assum `MAP _ _ ++ MAP _ _ = right ++ extra`
    (assume_tac o REWRITE_RULE [GSYM MAP_APPEND]) >>
  qabbrev_tac `M = MAX fuel n` >>
  `fuel <= M /\ n <= M` by simp[Abbr `M`] >>
  `step_inst M ctx inst s = OK stepped /\
   gas_events_step M ctx func.fn_name inst s =
     gas_events_step fuel ctx func.fn_name inst s` by
    (qspecl_then [`fuel`, `ctx`, `func.fn_name`, `inst`, `s`, `M`]
       mp_tac (cj 1 gas_events_fuel_extension) >> simp[]) >>
  qspecl_then [`n`, `M`, `ctx`, `func.fn_name`, `bb`,
    `stepped with vs_inst_idx := SUC s.vs_inst_idx`, `func`]
    mp_tac (Q.GENL [`n`, `m`, `ctx`, `owner`, `bb`, `s`, `func`]
              gas_events_from_fuel_mono) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `e` assume_tac) >>
  mp_tac (Q.INST [`m` |-> `M`, `owner` |-> `func.fn_name`,
                  `u` |-> `stepped`] gas_events_from_istep) >>
  impl_tac >- simp[] >>
  disch_then (fn ist =>
    qpat_x_assum `gas_events_block M _ _ _ _ ++ _ = _ ++ _ ++ e` (fn mono =>
    qpat_x_assum `gas_events_step M _ _ _ _ = _` (fn st =>
      assume_tac (REWRITE_RULE [mono, st] ist)))) >>
  drule_all map_glue >> strip_tac >>
  qexistsl_tac [`M`, `extra ++ MAP (\key. key IN explicit) e`] >>
  fs[MAP_APPEND]
QED

Resume gas_origin_edge_events_next[enter]:
  rename1 `step_inst fuel ctx inst s = OK stepped` >>
  rename1 `eval_phis stepped target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = stepped.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `bt = target` by gvs[] >> gvs[] >>
  qpat_x_assum `MAP _ _ ++ MAP _ _ = right ++ extra`
    (assume_tac o REWRITE_RULE [GSYM MAP_APPEND]) >>
  qabbrev_tac `M = MAX fuel n` >>
  `fuel <= SUC M /\ n <= M` by simp[Abbr `M`, MAX_DEF] >>
  `step_inst (SUC M) ctx inst s = OK stepped /\
   gas_events_step (SUC M) ctx func.fn_name inst s =
     gas_events_step fuel ctx func.fn_name inst s` by
    (qspecl_then [`fuel`, `ctx`, `func.fn_name`, `inst`, `s`, `SUC M`]
       mp_tac (cj 1 gas_events_fuel_extension) >> simp[]) >>
  qspecl_then [`n`, `M`, `ctx`, `func.fn_name`, `bt`,
    `entered with vs_inst_idx := phi_prefix_length bt.bb_instructions`,
    `func`]
    mp_tac (Q.GENL [`n`, `m`, `ctx`, `owner`, `bb`, `s`, `func`]
              gas_events_from_fuel_mono) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `e` assume_tac) >>
  mp_tac (Q.INST [`target` |-> `bt`] gas_events_from_enter) >> impl_tac >- simp[] >>
  disch_then (fn ist =>
    qpat_x_assum `gas_events_block M _ _ _ _ ++ _ = _ ++ _ ++ e` (fn mono =>
    qpat_x_assum `gas_events_step (SUC M) _ _ _ _ = _` (fn st =>
      assume_tac (REWRITE_RULE [mono, st] ist)))) >>
  drule_all map_glue >> strip_tac >>
  qexistsl_tac [`SUC M`, `extra ++ MAP (\key. key IN explicit) e`] >>
  fs[MAP_APPEND]
QED

Resume gas_origin_edge_events_next[jump]:
  qpat_x_assum `MAP _ _ ++ MAP _ _ = right ++ extra`
    (assume_tac o REWRITE_RULE [GSYM MAP_APPEND]) >>
  `(jump_to lbl s).vs_inst_idx = 0 /\ (jump_to lbl s).vs_current_bb = lbl` by
    simp[jump_to_def] >>
  `phi_prefix_length bt.bb_instructions = 0` by
    (spose_not_then assume_tac >>
     drule_all gas_events_from_phi_start >>
     disch_then (qspecl_then [`func.fn_name`, `n`, `func`, `ctx`] mp_tac) >>
     strip_tac >> gvs[]) >>
  `step_inst (SUC n) ctx inst s = OK (jump_to lbl s)` by
    gvs[step_inst_non_invoke] >>
  `gas_events_step (SUC n) ctx func.fn_name inst s =
     gas_events_step fuel ctx func.fn_name inst s` by
    simp[gas_events_step_def] >>
  `lookup_block lbl func.fn_blocks = SOME bt` by gvs[] >>
  mp_tac gas_events_from_jump >> impl_tac >- simp[] >>
  disch_then (fn ist =>
    qpat_x_assum `gas_events_step (SUC n) _ _ _ _ = _` (fn st =>
      assume_tac (REWRITE_RULE [st] ist))) >>
  drule_all map_glue0 >> strip_tac >>
  qexistsl_tac [`SUC n`, `extra`] >> fs[MAP_APPEND]
QED

Finalise gas_origin_edge_events_next

(* Helper: an edge's marks, then any prefix of the run after it. *)
Theorem gas_origin_edge_events_prefix[local]:
  gas_origin_edge memory explicit ctx func s left (OK t) /\
  (right = [] \/
   ?bt n extra. lookup_block t.vs_current_bb func.fn_blocks = SOME bt /\
     MAP (\key. key IN explicit)
       (gas_events_block n ctx func.fn_name bt t ++
        case exec_block n ctx bt t of
          OK u => if u.vs_halted then [] else gas_events_blocks n ctx func u
        | _ => []) = right ++ extra) ==>
  ?bb m extra. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    MAP (\key. key IN explicit)
      (gas_events_block m ctx func.fn_name bb s ++
       case exec_block m ctx bb s of
         OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
       | _ => []) = left ++ right ++ extra
Proof
  Cases_on `right = []`
  >- (rw[] >> qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
      rw[gas_origin_edge_def] >> qexistsl_tac [`bb`, `fuel`] >> simp[] >>
      drule gas_events_from_step >>
      disch_then (qspecl_then [`func.fn_name`, `fuel`, `func`, `ctx`]
        (qx_choose_then `e`
           (assume_tac o Q.AP_TERM `MAP (\key. key IN explicit)`))) >>
      qexists_tac `MAP (\key. key IN explicit) e` >> fs[MAP_APPEND]) >>
  rw[] >> drule gas_origin_edge_events_next >> simp[MAP_APPEND] >>
  disch_then drule_all >> strip_tac >> metis_tac[]
QED

(* Helper: an edge then a path's marks, as one prefix. *)
Theorem gas_origin_path_step_events[local]:
  gas_origin_edge memory explicit ctx func s left (OK mid) /\
  (left2 ++ right = [] \/
   ?bt n extra. lookup_block mid.vs_current_bb func.fn_blocks = SOME bt /\
     MAP (\key. key IN explicit)
       (gas_events_block n ctx func.fn_name bt mid ++
        case exec_block n ctx bt mid of
          OK u => if u.vs_halted then [] else gas_events_blocks n ctx func u
        | _ => []) = left2 ++ right ++ extra) ==>
  ?bb m extra. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    MAP (\key. key IN explicit)
      (gas_events_block m ctx func.fn_name bb s ++
       case exec_block m ctx bb s of
         OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
       | _ => []) = left ++ left2 ++ right ++ extra
Proof
  strip_tac >> drule gas_origin_edge_events_prefix >>
  disch_then (qspec_then `left2 ++ right` mp_tac) >>
  (impl_tac >- (fs[] >> metis_tac[APPEND_ASSOC])) >>
  strip_tac >> qexistsl_tac [`bb`, `m`] >> fs[]
QED

(* ===== Paths and focuses ===== *)

Theorem gas_origin_path_events_prefix[local]:
  !memory explicit ctx func s left r.
    gas_origin_path memory explicit ctx func s left r ==>
    !mid right. r = OK mid /\
      (right = [] \/
       ?bt n extra. lookup_block mid.vs_current_bb func.fn_blocks = SOME bt /\
         MAP (\key. key IN explicit)
           (gas_events_block n ctx func.fn_name bt mid ++
            case exec_block n ctx bt mid of
              OK u => if u.vs_halted then [] else gas_events_blocks n ctx func u
            | _ => []) = right ++ extra) ==>
      left ++ right = [] \/
      ?bb m extra. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        MAP (\key. key IN explicit)
          (gas_events_block m ctx func.fn_name bb s ++
           case exec_block m ctx bb s of
             OK u => if u.vs_halted then [] else gas_events_blocks m ctx func u
           | _ => []) = left ++ right ++ extra
Proof
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac
  >- (rw[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
      first_x_assum (qspecl_then [`mid`, `right`] mp_tac) >>
      impl_tac >- (fs[] >> metis_tac[]) >> disch_tac >> disj2_tac >>
      irule gas_origin_path_step_events >> metis_tac[]) >>
  rw[] >> gvs[exit_result_def]
QED

Theorem gas_invoke_entry_events[local]:
  gas_invoke_entry (ctx, func) s callee entered /\
  lookup_block entered.vs_current_bb callee.fn_blocks = SOME cb ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    !n. ?extra.
      gas_events_block (SUC n) ctx func.fn_name bb s ++
        (case exec_block (SUC n) ctx bb s of
           OK u => if u.vs_halted then [] else gas_events_blocks (SUC n) ctx func u
         | _ => []) =
      gas_events_block n ctx callee.fn_name cb entered ++
        (case exec_block n ctx cb entered of
           OK u => if u.vs_halted then [] else gas_events_blocks n ctx callee u
         | _ => []) ++ extra
Proof
  rw[gas_invoke_entry_def] >>
  `phi_state.vs_current_bb = setup.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  gvs[] >> rw[] >>
  drule gas_events_from_step >>
  disch_then (qspecl_then [`func.fn_name`, `SUC n`, `func`, `ctx`]
                strip_assume_tac) >>
  simp[] >>
  simp[gas_events_step_def, Once gas_events_blocks_def]
QED

(* KEY LEMMA: a focus marks a prefix of its run's events at some fuel. *)
Theorem gas_origin_focus_events_prefix[local]:
  !memory explicit p s marks q.
    gas_origin_focus memory explicit p s marks q ==>
    marks = [] \/
    ?bb m extra.
      lookup_block s.vs_current_bb (SND p).fn_blocks = SOME bb /\
      MAP (\key. key IN explicit)
        (gas_events_block m (FST p) (SND p).fn_name bb s ++
         case exec_block m (FST p) bb s of
           OK u => if u.vs_halted then []
                   else gas_events_blocks m (FST p) (SND p) u
         | _ => []) = marks ++ extra
Proof
  ho_match_mp_tac gas_origin_focus_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule gas_origin_path_events_prefix >>
      disch_then (qspecl_then [`t`, `[]`] mp_tac) >> simp[])
  >- (rpt gen_tac >>
      PURE_REWRITE_TAC [pairTheory.FST, pairTheory.SND] >>
      rename1 `gas_origin_path _ _ _ _ _ _ (OK mm)` >>
      disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
      drule gas_origin_path_events_prefix >>
      disch_then (qspecl_then [`mm`, `marks`] mp_tac) >>
      impl_tac >- (conj_tac >- REFL_TAC >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >> rpt gen_tac >> strip_tac >> gvs[] >> disj2_tac >>
  drule_all gas_invoke_entry_events >> strip_tac >>
  first_x_assum (qspec_then `m` strip_assume_tac) >>
  qexistsl_tac [`bb'`, `SUC m`, `extra ++ MAP (\key. key IN explicit) extra'`] >>
  simp[] >>
  qpat_x_assum `gas_events_block (SUC _) _ _ _ _ ++ _ = _`
    (mp_tac o Q.AP_TERM `MAP (\key. key IN explicit)`) >>
  simp_tac std_ss [MAP_APPEND] >> disch_then SUBST1_TAC >>
  asm_rewrite_tac[]
QED

(* TOP-LEVEL: from a block start, a GAS-origin focus marks a prefix of the
   marked GAS sites the run records at some fuel. *)
Theorem gas_origin_focus_entry_events:
  gas_origin_focus memory explicit (ctx, func) s marks q /\
  s.vs_inst_idx = 0 ==>
  ?fuel extra.
    MAP (\key. key IN explicit) (gas_events_blocks fuel ctx func s) =
      marks ++ extra
Proof
  strip_tac >> Cases_on `marks = []`
  >- (qexistsl_tac [`0`,
        `MAP (\key. key IN explicit) (gas_events_blocks 0 ctx func s)`] >>
      simp[]) >>
  drule gas_origin_focus_events_prefix >> simp[] >> strip_tac >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (spose_not_then assume_tac >>
     drule_all gas_events_from_phi_start >>
     disch_then (qspecl_then [`func.fn_name`, `m`, `func`, `ctx`] mp_tac) >>
     strip_tac >> gvs[]) >>
  qexistsl_tac [`SUC m`, `extra`] >>
  simp[Once gas_events_blocks_def, eval_phis_no_phi] >>
  `s with vs_inst_idx := 0 = s` by
    simp[venom_state_component_equality] >>
  simp[]
QED
