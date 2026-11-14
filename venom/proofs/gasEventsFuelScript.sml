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

Theorem gas_events_block_silent:
  EVERY (\inst. inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE)
    bb.bb_instructions ==>
  gas_events_block fuel ctx owner bb st = []
Proof
  measureInduct_on `LENGTH bb.bb_instructions - st.vs_inst_idx` >>
  rpt strip_tac >> once_rewrite_tac[gas_events_block_def] >>
  Cases_on `st.vs_inst_idx < LENGTH bb.bb_instructions`
  >- (`(EL st.vs_inst_idx bb.bb_instructions).inst_opcode <> GAS /\
       (EL st.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE` by
        gvs[listTheory.EVERY_EL] >>
      simp[venomInstTheory.get_instruction_def, gas_events_step_def] >>
      Cases_on `step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st` >>
      simp[] >> IF_CASES_TAC >> simp[] >>
      first_x_assum irule >> simp[] >> decide_tac) >>
  simp[venomInstTheory.get_instruction_def]
QED

Theorem gas_events_blocks_unfold:
  gas_events_blocks (SUC n) ctx fn u =
    case lookup_block u.vs_current_bb fn.fn_blocks of
      NONE => []
    | SOME bb =>
        (case eval_phis u bb.bb_instructions of
           OK p => gas_events_block n ctx fn.fn_name bb
             (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)
         | _ => []) ++
        (case run_block_entry n ctx bb u of
           OK v => if v.vs_halted then [] else gas_events_blocks n ctx fn v
         | _ => [])
Proof
  simp[SimpLHS, Once gas_events_blocks_def] >>
  Cases_on `lookup_block u.vs_current_bb fn.fn_blocks` >> simp[] >>
  qspec_then `u` (qspec_then `x.bb_instructions` strip_assume_tac)
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs >>
  simp[venomExecSemanticsTheory.run_block_entry_def]
QED
