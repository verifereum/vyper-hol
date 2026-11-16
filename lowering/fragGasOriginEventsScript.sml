(* A source focus may stop inside INVOKE, before a terminal result exists. *)
Theory fragGasOriginEvents
Ancestors
  fragGasOrigin fragGasFocus fragExec gasEvents gasEventsFuel
  venomExecSemantics venomExecProofs venomInst venomInstProofs
  venomState list rich_list arithmetic pred_set

Theorem gas_invoke_entry_events_prefix:
  gas_invoke_entry (ctx,func) s callee entered ==>
  ?extra.
    (case lookup_block s.vs_current_bb func.fn_blocks of
       NONE => []
     | SOME bb =>
         gas_events_block (SUC n) ctx func.fn_name bb s ++
         case exec_block (SUC n) ctx bb s of
           OK u => if u.vs_halted then []
                   else gas_events_blocks (SUC n) ctx func u
         | _ => []) =
    (case lookup_block entered.vs_current_bb callee.fn_blocks of
       NONE => []
     | SOME bb =>
         gas_events_block n ctx callee.fn_name bb entered ++
         case exec_block n ctx bb entered of
           OK u => if u.vs_halted then []
                   else gas_events_blocks n ctx callee u
         | _ => []) ++ extra
Proof
  rw[gas_invoke_entry_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  simp[] >>
  CONV_TAC (BINDER_CONV (LHS_CONV
    (ONCE_DEPTH_CONV (REWR_CONV gas_events_block_def)))) >>
  simp[gas_events_step_def, Once gas_events_blocks_def] >>
  simp[APPEND_ASSOC]
QED

(* Transport through paths depends only on the edge observation contract. *)
Theorem gas_origin_path_prefix_lift:
  (!ctx func s left t n.
     gas_origin_edge memory explicit ctx func s left (OK t) ==>
     ?m extra. observe ctx func s m = left ++ observe ctx func t n ++ extra) ==>
  !ctx func s left t n.
    gas_origin_path memory explicit ctx func s left (OK t) ==>
    ?m extra. observe ctx func s m = left ++ observe ctx func t n ++ extra
Proof
  qsuff_tac
       `!memory explicit ctx func s left r.
          gas_origin_path memory explicit ctx func s left r ==>
          !t n. r = OK t ==>
          (!ctx func s left t n.
             gas_origin_edge memory explicit ctx func s left (OK t) ==>
             ?m extra.
               observe ctx func s m = left ++ observe ctx func t n ++ extra) ==>
          ?m extra.
            observe ctx func s m = left ++ observe ctx func t n ++ extra`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> qexistsl [`n`, `[]`] >> simp[])
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `!n. ?m extra. _` (qspec_then `n` strip_assume_tac) >>
      qpat_x_assum `!ctx func s left t n. _` drule >>
      disch_then (qspec_then `m` strip_assume_tac) >>
      metis_tac[APPEND_ASSOC])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

Theorem gas_origin_focus_prefix_lift:
  (!ctx func s left t n.
     gas_origin_path memory explicit ctx func s left (OK t) ==>
     ?m extra. Obs ctx func s m = left ++ Obs ctx func t n ++ extra) /\
  (!ctx func s callee entered n.
     gas_invoke_entry (ctx,func) s callee entered ==>
     ?extra. Obs ctx func s (SUC n) = Obs ctx callee entered n ++ extra) ==>
  !ctx func s marks leaf t.
    gas_origin_focus memory explicit (ctx,func) s marks (leaf,t) ==>
    ?fuel extra. Obs ctx func s fuel = marks ++ extra
Proof
  qsuff_tac
    `!memory explicit p s marks q.
       gas_origin_focus memory explicit p s marks q ==>
       !Obs.
         (!ctx func s left t n.
            gas_origin_path memory explicit ctx func s left (OK t) ==>
            ?m extra. Obs ctx func s m = left ++ Obs ctx func t n ++ extra) /\
         (!ctx func s callee entered n.
            gas_invoke_entry (ctx,func) s callee entered ==>
            ?extra. Obs ctx func s (SUC n) = Obs ctx callee entered n ++ extra) ==>
         ?fuel extra. Obs (FST p) (SND p) s fuel = marks ++ extra`
  >- (rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac gas_origin_focus_ind >> conj_tac
  >- (rpt strip_tac >> simp[] >>
      first_x_assum drule >>
      disch_then (qspec_then `0` strip_assume_tac) >>
      metis_tac[APPEND_ASSOC]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      first_x_assum (qspec_then `Obs` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      first_x_assum drule >>
      disch_then (qspec_then `fuel` strip_assume_tac) >>
      gvs[] >> metis_tac[APPEND_ASSOC]) >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `Obs` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  first_x_assum drule >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  gvs[] >> metis_tac[APPEND_ASSOC]
QED

Theorem gas_origin_edge_events_prefix_continue:
  gas_origin_edge memory explicit ctx func s left (OK t) ==>
  !n. ?m extra.
    MAP (\key. key IN explicit)
      (case lookup_block s.vs_current_bb func.fn_blocks of
         NONE => []
       | SOME bb =>
           gas_events_block m ctx func.fn_name bb s ++
           case exec_block m ctx bb s of
             OK u => if u.vs_halted then []
                     else gas_events_blocks m ctx func u
           | _ => []) =
    left ++ MAP (\key. key IN explicit)
      (case lookup_block t.vs_current_bb func.fn_blocks of
         NONE => []
       | SOME bb =>
           gas_events_block n ctx func.fn_name bb t ++
           case exec_block n ctx bb t of
             OK u => if u.vs_halted then []
                     else gas_events_blocks n ctx func u
           | _ => []) ++ extra
Proof
  rw[gas_origin_edge_def] >> gvs[exit_result_def]
  >- suspend "within"
  >- suspend "enter"
  >- suspend "jump"
  >> (Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def])
QED

Resume gas_origin_edge_events_prefix_continue[within]:
  rename1 `step_inst fuel ctx inst s = OK stepped` >>
  `step_inst (MAX fuel n) ctx inst s = OK stepped /\
   gas_events_step (MAX fuel n) ctx func.fn_name inst s =
     gas_events_step fuel ctx func.fn_name inst s` by
    (mp_tac (cj 1 gas_events_fuel_extension) >>
     disch_then (qspecl_then [`fuel`, `ctx`, `func.fn_name`, `inst`, `s`,
                              `MAX fuel n`] mp_tac) >> simp[]) >>
  drule_all gas_events_current_nonterminator >> strip_tac >>
  `n <= MAX fuel n` by simp[] >>
  drule gas_events_current_fuel_prefix >>
  disch_then (qspecl_then [`stepped with vs_inst_idx := SUC s.vs_inst_idx`,
                         `func`, `ctx`] strip_assume_tac) >>
  gvs[] >>
  qexistsl [`MAX fuel n`, `MAP (\key. key IN explicit) extra`] >>
  rewrite_tac[GSYM MAP_APPEND] >> AP_TERM_TAC >>
  asm_rewrite_tac[APPEND_ASSOC]
QED

Resume gas_origin_edge_events_prefix_continue[enter]:
  rename1 `step_inst fuel ctx inst s = OK stepped` >>
  `step_inst (SUC (MAX fuel n)) ctx inst s = OK stepped /\
   gas_events_step (SUC (MAX fuel n)) ctx func.fn_name inst s =
     gas_events_step fuel ctx func.fn_name inst s` by
    (mp_tac (cj 1 gas_events_fuel_extension) >>
     disch_then (qspecl_then [`fuel`, `ctx`, `func.fn_name`, `inst`, `s`,
                              `SUC (MAX fuel n)`] mp_tac) >> simp[MAX_DEF]) >>
  drule_all gas_events_blocks_current_entry >>
  disch_then (qspecl_then [`MAX fuel n`, `ctx`] assume_tac) >>
  `n <= MAX fuel n` by simp[] >>
  drule gas_events_current_fuel_prefix >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `func`, `ctx`] strip_assume_tac) >>
  qexistsl [`SUC (MAX fuel n)`, `MAP (\key. key IN explicit) extra`] >>
  CONV_TAC (LHS_CONV
    (ONCE_DEPTH_CONV (REWR_CONV gas_events_block_def))) >>
  CONV_TAC (LHS_CONV
    (ONCE_DEPTH_CONV (REWR_CONV exec_block_def))) >>
  simp[MAP_APPEND] >>
  gvs[] >>
  rewrite_tac[GSYM MAP_APPEND] >> AP_TERM_TAC >>
  asm_rewrite_tac[APPEND_ASSOC]
QED

Resume gas_origin_edge_events_prefix_continue[jump]:
  `step_inst (SUC n) ctx inst s = OK (jump_to lbl s)` by
    gvs[step_inst_non_invoke] >>
  `gas_events_step (SUC n) ctx func.fn_name inst s =
   gas_events_step fuel ctx func.fn_name inst s` by
    simp[gas_events_step_def] >>
  `(jump_to lbl s).vs_halted = F` by simp[jump_to_def] >>
  strip_assume_tac gas_events_blocks_jump_prefix >>
  qexistsl [`SUC n`, `MAP (\key. key IN explicit) extra`] >>
  CONV_TAC (LHS_CONV
    (ONCE_DEPTH_CONV (REWR_CONV gas_events_block_def))) >>
  CONV_TAC (LHS_CONV
    (ONCE_DEPTH_CONV (REWR_CONV exec_block_def))) >>
  simp[MAP_APPEND, APPEND_ASSOC]
QED
Finalise gas_origin_edge_events_prefix_continue

Theorem gas_origin_path_events_prefix_continue:
  !ctx func s left t n.
    gas_origin_path memory explicit ctx func s left (OK t) ==>
    ?m extra.
      MAP (\key. key IN explicit)
        (case lookup_block s.vs_current_bb func.fn_blocks of
           NONE => []
         | SOME bb =>
             gas_events_block m ctx func.fn_name bb s ++
             case exec_block m ctx bb s of
               OK u => if u.vs_halted then []
                       else gas_events_blocks m ctx func u
             | _ => []) =
      left ++ MAP (\key. key IN explicit)
        (case lookup_block t.vs_current_bb func.fn_blocks of
           NONE => []
         | SOME bb =>
             gas_events_block n ctx func.fn_name bb t ++
             case exec_block n ctx bb t of
               OK u => if u.vs_halted then []
                       else gas_events_blocks n ctx func u
             | _ => []) ++ extra
Proof
  ho_match_mp_tac gas_origin_path_prefix_lift >>
  rpt strip_tac >>
  drule gas_origin_edge_events_prefix_continue >> simp[]
QED

Theorem gas_origin_focus_events_prefix:
  !memory explicit ctx func s marks leaf t.
    gas_origin_focus memory explicit (ctx,func) s marks (leaf,t) ==>
    ?fuel extra.
      MAP (\key. key IN explicit)
        (case lookup_block s.vs_current_bb func.fn_blocks of
           NONE => []
         | SOME bb =>
             gas_events_block fuel ctx func.fn_name bb s ++
             case exec_block fuel ctx bb s of
               OK u => if u.vs_halted then []
                       else gas_events_blocks fuel ctx func u
             | _ => []) = marks ++ extra
Proof
  map_every qx_gen_tac [`memory`, `explicit`] >>
  ho_match_mp_tac gas_origin_focus_prefix_lift >> conj_tac
  >- (rpt strip_tac >>
      drule gas_origin_path_events_prefix_continue >> simp[]) >>
  rpt strip_tac >>
  rename1 `gas_events_block (SUC k)` >>
  drule gas_invoke_entry_events_prefix >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  qexists_tac `MAP (\key. key IN explicit) extra` >>
  asm_rewrite_tac[GSYM MAP_APPEND]
QED
