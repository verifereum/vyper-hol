(* Fuel extension for ordinary reached instruction-site observations. *)
Theory gasEventsFuel
Ancestors gasEvents venomExecProofs venomExecSemantics list arithmetic

Theorem gas_events_fuel_extension:
  (!fuel ctx owner inst s. !larger. fuel <= larger ==>
    (?extra. gas_events_step larger ctx owner inst s =
       gas_events_step fuel ctx owner inst s ++ extra) /\
    ((!err. step_inst fuel ctx inst s <> Error err) ==>
      step_inst larger ctx inst s = step_inst fuel ctx inst s /\
      gas_events_step larger ctx owner inst s = gas_events_step fuel ctx owner inst s)) /\
  (!fuel ctx owner bb s. !larger. fuel <= larger ==>
    (?extra. gas_events_block larger ctx owner bb s =
       gas_events_block fuel ctx owner bb s ++ extra) /\
    ((!err. exec_block fuel ctx bb s <> Error err) ==>
      exec_block larger ctx bb s = exec_block fuel ctx bb s /\
      gas_events_block larger ctx owner bb s = gas_events_block fuel ctx owner bb s)) /\
  (!fuel ctx fn s. !larger. fuel <= larger ==>
    (?extra. gas_events_blocks larger ctx fn s =
       gas_events_blocks fuel ctx fn s ++ extra) /\
    ((!err. run_blocks fuel ctx fn s <> Error err) ==>
      run_blocks larger ctx fn s = run_blocks fuel ctx fn s /\
      gas_events_blocks larger ctx fn s = gas_events_blocks fuel ctx fn s))
Proof
  ho_match_mp_tac gas_events_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume gas_events_fuel_extension[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[gas_events_step_def, step_inst_def] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions`
      >- simp[gas_events_step_def, step_inst_def] >>
      Cases_on `eval_operands pair1 s`
      >- simp[gas_events_step_def, step_inst_def] >>
      rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
      rename1 `eval_operands pair1 s = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[gas_events_step_def, step_inst_def] >>
      gvs[] >> first_x_assum drule_all >> strip_tac >>
      simp[gas_events_step_def, Once step_inst_def] >>
      Cases_on `run_blocks fuel ctx callee x` >> gvs[] >> simp[step_inst_def]) >>
  simp[gas_events_step_def, step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[]
QED

Resume gas_events_fuel_extension[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[Once gas_events_block_def, Once exec_block_def] >>
      simp[Once gas_events_block_def, Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  gvs[] >>
  qpat_x_assum `!larger. _` (qspec_then `larger` mp_tac) >>
  simp[] >> strip_tac >>
  once_rewrite_tac[gas_events_block_def, exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  first_x_assum (qspec_then `larger` mp_tac) >> simp[]
QED

Resume gas_events_fuel_extension[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  namedCases_on `fuel` ["", "small"]
  >- (simp[Once run_blocks_def] >>
      qexists_tac `gas_events_blocks larger ctx fn s` >>
      simp[Once gas_events_blocks_def]) >>
  namedCases_on `larger` ["", "big"] >> gvs[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (gvs[] >>
      qpat_x_assum `!larger. _` (qspec_then `big` mp_tac) >>
      simp[] >> strip_tac >>
      once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[] >>
      rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
      qmatch_goalsub_abbrev_tac `exec_block small ctx bb entry` >>
      Cases_on `exec_block small ctx bb entry` >> gvs[] >>
      rename1 `exec_block small ctx bb entry = OK result` >>
      Cases_on `result.vs_halted` >> gvs[] >>
      first_x_assum (qspec_then `big` mp_tac) >> simp[]) >>
  once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[]
QED

Finalise gas_events_fuel_extension

Theorem gas_events_current_fuel_prefix:
  n <= m ==>
  ?extra.
    (case lookup_block s.vs_current_bb func.fn_blocks of
       NONE => []
     | SOME bb =>
         gas_events_block m ctx func.fn_name bb s ++
         (case exec_block m ctx bb s of
            OK u => if u.vs_halted then []
                    else gas_events_blocks m ctx func u
          | _ => [])) =
    (case lookup_block s.vs_current_bb func.fn_blocks of
       NONE => []
     | SOME bb =>
         gas_events_block n ctx func.fn_name bb s ++
         (case exec_block n ctx bb s of
            OK u => if u.vs_halted then []
                    else gas_events_blocks n ctx func u
          | _ => [])) ++ extra
Proof
  strip_tac >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` >>
  drule (cj 2 gas_events_fuel_extension) >>
  disch_then (qspecl_then [`ctx`, `func.fn_name`, `bb`, `s`]
    strip_assume_tac) >>
  Cases_on `exec_block n ctx bb s` >> gvs[]
  >- (Cases_on `v.vs_halted` >> simp[gas_events_fuel_extension]) >>
  simp[APPEND_ASSOC] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem gas_events_current_nonterminator:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst n ctx inst s = OK u /\
  ~is_terminator inst.inst_opcode ==>
  (case lookup_block s.vs_current_bb func.fn_blocks of
     NONE => []
   | SOME bb =>
       gas_events_block n ctx func.fn_name bb s ++
       (case exec_block n ctx bb s of
          OK v => if v.vs_halted then []
                  else gas_events_blocks n ctx func v
        | _ => [])) =
  gas_events_step n ctx func.fn_name inst s ++
  (case lookup_block (u with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
          func.fn_blocks of
     NONE => []
   | SOME bb =>
       gas_events_block n ctx func.fn_name bb
         (u with vs_inst_idx := SUC s.vs_inst_idx) ++
       (case exec_block n ctx bb
               (u with vs_inst_idx := SUC s.vs_inst_idx) of
          OK v => if v.vs_halted then []
                  else gas_events_blocks n ctx func v
        | _ => []))
Proof
  strip_tac >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >>
  strip_tac >>
  `gas_events_block n ctx func.fn_name bb s =
     gas_events_step n ctx func.fn_name inst s ++
     gas_events_block n ctx func.fn_name bb
       (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule gas_events_block_nonterminator >> simp[]) >>
  `exec_block n ctx bb s =
     exec_block n ctx bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (CONV_TAC (LHS_CONV (REWR_CONV exec_block_def)) >> simp[]) >>
  simp[APPEND_ASSOC]
QED
