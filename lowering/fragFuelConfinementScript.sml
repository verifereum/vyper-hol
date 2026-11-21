(* A fuel bound that holds in every host function excludes an unlisted jump.
   Attach a longer jump chain at the putative destination and STOP at the
   fragment's ordinary continuation. A run taking the jump cannot have the
   required fuel stability. *)
Theory fragFuelConfinement
Ancestors
  cfgNormSim fragFuel venomInst venomState venomExecSemantics callLayoutDefs
  venomExecProofs fragExec arithmetic list pred_set string

val _ = Parse.hide "base";

Definition fuel_probe_blocks_def[local]:
  fuel_probe_blocks [] = [] /\
  fuel_probe_blocks [l] =
    [<|bb_label := l; bb_instructions := [mk_inst 0 STOP [] []]|>] /\
  fuel_probe_blocks (l::m::ls) =
    <|bb_label := l; bb_instructions := [mk_inst 0 JMP [Label m] []]|> ::
    fuel_probe_blocks (m::ls)
End

Theorem fuel_probe_block_labels[local]:
  !ls. MAP (\b. b.bb_label) (fuel_probe_blocks ls) = ls
Proof
  Induct >> simp[fuel_probe_blocks_def] >> Cases_on `ls` >>
  gvs[fuel_probe_blocks_def]
QED

Theorem fuel_probe_block_no_phi[local]:
  !ls. EVERY (\b. phi_prefix_length b.bb_instructions = 0) (fuel_probe_blocks ls)
Proof
  Induct >> simp[fuel_probe_blocks_def] >> Cases_on `ls` >>
  gvs[fuel_probe_blocks_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem fuel_probe_stops[local]:
  !ls fn ctx s.
    ls <> [] /\
    EVERY (\b. lookup_block b.bb_label fn.fn_blocks = SOME b) (fuel_probe_blocks ls) /\
    no_phi_fn fn /\ s.vs_current_bb = HD ls /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?t. run_from (PRE (LENGTH ls)) ctx fn s = Halt t
Proof
  Induct >> simp[] >> Cases_on `ls` >>
  simp[fuel_probe_blocks_def, get_instruction_def, mk_inst_def] >>
  rpt strip_tac
  >- (simp[run_from_def, Once exec_block_def, get_instruction_def,
           step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def] >>
      metis_tac[]) >>
  rename1 `EVERY _ (fuel_probe_blocks (next::rest))` >>
  `run_from (SUC (LENGTH rest)) ctx fn s = run_from (LENGTH rest) ctx fn (jump_to next s)` by
    (match_mp_tac run_from_jump_exact >>
     qexistsl_tac [`<|bb_label := s.vs_current_bb;
       bb_instructions := [mk_inst 0 JMP [Label next] []]|>`, `mk_inst 0 JMP [Label next] []`] >>
     simp[get_instruction_def, mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs]) >>
  first_x_assum (qspecl_then [`fn`,`ctx`,`jump_to next s`] mp_tac) >> simp[jump_to_def]
QED

Theorem fuel_probe_runs_out[local]:
  !ls fuel fn ctx s.
    fuel < PRE (LENGTH ls) /\
    EVERY (\b. lookup_block b.bb_label fn.fn_blocks = SOME b) (fuel_probe_blocks ls) /\
    no_phi_fn fn /\ s.vs_current_bb = HD ls /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?e. run_from fuel ctx fn s = Error e
Proof
  Induct >> simp[] >> Cases_on `ls` >> simp[fuel_probe_blocks_def] >>
  Cases_on `fuel` >> rpt strip_tac
  >- (simp[run_from_def, Once exec_block_def, get_instruction_def,
           step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def, jump_to_def,
           is_terminator_def] >>
      simp[Once run_blocks_def]) >>
  rename1 `EVERY _ (fuel_probe_blocks (next::rest))` >>
  `run_from (SUC n) ctx fn s = run_from n ctx fn (jump_to next s)` by
    (match_mp_tac run_from_jump_exact >>
     qexistsl_tac [`<|bb_label := s.vs_current_bb;
       bb_instructions := [mk_inst 0 JMP [Label next] []]|>`, `mk_inst 0 JMP [Label next] []`] >>
     simp[get_instruction_def, mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs]) >>
  first_x_assum (qspecl_then [`n`,`fn`,`ctx`,`jump_to next s`] mp_tac) >>
  simp[jump_to_def] >> decide_tac
QED

Theorem fuel_probe_fresh_labels[local]:
  !n (forbidden:string set). FINITE forbidden ==>
  ?ls. LENGTH ls = n /\ ALL_DISTINCT ls /\ DISJOINT (set ls) forbidden
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `?fresh:string. fresh NOTIN forbidden` by
    metis_tac[INFINITE_STR_UNIV, IN_INFINITE_NOT_FINITE] >>
  `FINITE (fresh INSERT forbidden)` by simp[] >>
  first_x_assum drule >> disch_then (qx_choose_then `ls` strip_assume_tac) >>
  qexists_tac `fresh::ls` >> fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem fuel_probe_attach[local]:
  lookup_block s.vs_current_bb base.fn_blocks = NONE /\ no_phi_fn base /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  ?host. no_phi_fn host /\
    (!l b. lookup_block l base.fn_blocks = SOME b ==> lookup_block l host.fn_blocks = SOME b) /\
    (!ctx. (?e. run_from fuel ctx host s = Error e) /\
           (?t. run_from (SUC fuel) ctx host s = Halt t))
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`SUC fuel`,`s.vs_current_bb INSERT set (MAP (\b. b.bb_label) base.fn_blocks)`]
    fuel_probe_fresh_labels) >> simp[] >>
  disch_then (qx_choose_then `tail` strip_assume_tac) >>
  qabbrev_tac `ls = s.vs_current_bb::tail` >>
  qabbrev_tac `blocks = fuel_probe_blocks ls` >>
  qabbrev_tac `host = base with fn_blocks updated_by (\bs. bs ++ blocks)` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) blocks)` by
    fs[Abbr `blocks`, Abbr `ls`, fuel_probe_block_labels, DISJOINT_DEF, EXTENSION] >>
  `!l. MEM l (MAP (\b. b.bb_label) blocks) ==> lookup_block l base.fn_blocks = NONE` by
    (simp[Abbr `blocks`, fuel_probe_block_labels, Abbr `ls`] >> rpt strip_tac >> gvs[] >>
     fs[cfgNormSimTheory.lookup_block_NONE, DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `!b. MEM b blocks ==> lookup_block b.bb_label host.fn_blocks = SOME b` by
    (rpt strip_tac >>
     `lookup_block b.bb_label base.fn_blocks = NONE` by metis_tac[MEM_MAP] >>
     `lookup_block b.bb_label blocks = SOME b` by metis_tac[MEM_lookup_block] >>
     fs[Abbr `host`, lookup_block_def, FIND_APPEND_CASE]) >>
  `no_phi_fn host` by
    fs[Abbr `host`, Abbr `blocks`, no_phi_fn_def, EVERY_APPEND, fuel_probe_block_no_phi] >>
  `EVERY (\b. lookup_block b.bb_label host.fn_blocks = SOME b) (fuel_probe_blocks ls)` by
    fs[Abbr `blocks`, EVERY_MEM] >>
  `PRE (LENGTH ls) = SUC fuel /\ HD ls = s.vs_current_bb /\ ls <> []` by simp[Abbr `ls`] >>
  qexists_tac `host` >> simp[] >> conj_tac
  >- (simp[Abbr `host`, lookup_block_def, FIND_APPEND_CASE] >> rpt strip_tac >> simp[]) >>
  gen_tac >> conj_tac
  >- (irule fuel_probe_runs_out >> simp[] >> qexists_tac `ls` >> simp[]) >>
  mp_tac (Q.SPECL [`ls`,`host`,`ctx`,`s`] fuel_probe_stops) >> simp[]
QED

Theorem frag_fuel_excludes_unlisted_jump:
  frag_fuel Wv {} {} sa sb Kb /\ at_point sa s /\
  fn_has_code sa sb observer /\ no_phi_fn observer /\
  lookup_block sb.cs_current_bb observer.fn_blocks = SOME cut /\
  get_instruction cut (LENGTH sb.cs_current_insts) = SOME (mk_inst id STOP [] []) /\
  s'.vs_inst_idx = 0 /\ ~s'.vs_halted /\
  (!host. no_phi_fn host /\
    (!l b. lookup_block l observer.fn_blocks = SOME b ==> lookup_block l host.fn_blocks = SOME b) ==>
    ?cost. !fuel ctx. run_from (fuel + cost) ctx host s = run_from fuel ctx host s') ==>
  IS_SOME (lookup_block s'.vs_current_bb observer.fn_blocks)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `lookup_block s'.vs_current_bb observer.fn_blocks` >> simp[] >>
  mp_tac (Q.INST [`base` |-> `observer`, `s` |-> `s'`, `fuel` |-> `Kb`]
    fuel_probe_attach) >>
  asm_rewrite_tac[] >> disch_then (qx_choose_then `host` strip_assume_tac) >>
  `fn_has_code sa sb host` by
    (fs[fn_has_code_def] >> qexists_tac `cut` >> simp[]) >>
  `lookup_block sb.cs_current_bb host.fn_blocks = SOME cut` by metis_tac[] >>
  `?cost. !fuel ctx. run_from (fuel + cost) ctx host s = run_from fuel ctx host s'` by
    metis_tac[] >>
  qabbrev_tac `ctx = <|ctx_functions := []|>` >>
  `callees_stable 0 ctx host` by simp[callees_stable_def, Abbr `ctx`, lookup_function_def, FIND_thm] >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` (mp_tac o REWRITE_RULE [frag_fuel_def]) >>
  disch_then (qspecl_then [`0`,`0`,`ctx`,`host`,`s`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[ZERO_LESS_EQ]) >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  `!u f. at_point sb u ==> run_from f ctx host u =
          Halt (halt_state (u with vs_returndata := []))` by
    simp[at_point_def, run_from_def, Once exec_block_def, step_inst_non_invoke,
         mk_inst_def, step_inst_base_opcode_eqs] >>
  `!f g. run_from (f + j) ctx host s = run_from (g + j) ctx host s` by
    (fs[fuel_outcome_def] >> metis_tac[]) >>
  `run_from (Kb + cost) ctx host s = run_from (SUC Kb + cost) ctx host s` by
    (`Kb + cost - j + j = Kb + cost /\ SUC Kb + cost - j + j = SUC Kb + cost` by decide_tac >>
     qpat_x_assum `_ = SUC Kb + cost` (fn hi =>
       qpat_x_assum `_ = Kb + cost` (fn lo =>
         qpat_assum `!f g. run_from _ _ _ _ = _`
           (qspecl_then [`Kb + cost - j`, `SUC Kb + cost - j`]
             (ACCEPT_TAC o REWRITE_RULE [lo,hi]))))) >>
  `run_from Kb ctx host s' = run_from (SUC Kb) ctx host s'` by
    metis_tac[] >>
  qpat_x_assum `!ctx. (∃e. _) /\ ∃t. _` (qspec_then `ctx` strip_assume_tac) >>
  metis_tac[exec_result_distinct]
QED
