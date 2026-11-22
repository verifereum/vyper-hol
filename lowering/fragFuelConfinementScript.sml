(* A fuel bound that holds in every host function excludes an unlisted jump.
   Attach a longer jump chain at the putative destination and STOP at the
   fragment's ordinary continuation. A run taking the jump cannot have the
   required fuel stability. *)
Theory fragFuelConfinement
Ancestors
  fragFuel venomInst venomState venomExecSemantics callLayoutDefs
  venomExecProofs venomFnInstsProofs fragExec fragGasPath relation
  arithmetic list pred_set string

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

Theorem fuel_probe_blocks_do_not_invoke[local]:
  !ls bb i. MEM bb (fuel_probe_blocks ls) /\ MEM i bb.bb_instructions ==>
  i.inst_opcode <> INVOKE
Proof
  Induct >- simp[fuel_probe_blocks_def] >>
  Cases_on `ls` >> simp[fuel_probe_blocks_def, mk_inst_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fuel_probe_attach[local]:
  lookup_block s.vs_current_bb base.fn_blocks = NONE /\ no_phi_fn base /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  ?host. no_phi_fn host /\
    (!l b. lookup_block l base.fn_blocks = SOME b ==> lookup_block l host.fn_blocks = SOME b) /\
    (!i. MEM i (fn_insts host) /\ i.inst_opcode = INVOKE ==>
      MEM i (fn_insts base)) /\
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
     Cases_on `lookup_block l base.fn_blocks` >> simp[] >>
     fs[DISJOINT_DEF, EXTENSION, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `!b. MEM b blocks ==> lookup_block b.bb_label host.fn_blocks = SOME b` by
    (rpt strip_tac >>
     `lookup_block b.bb_label base.fn_blocks = NONE` by metis_tac[MEM_MAP] >>
     `lookup_block b.bb_label blocks = SOME b` by
       metis_tac[MEM_lookup_block] >>
     fs[Abbr `host`, lookup_block_def, FIND_APPEND_CASE]) >>
  `no_phi_fn host` by
    fs[Abbr `host`, Abbr `blocks`, no_phi_fn_def, EVERY_APPEND, fuel_probe_block_no_phi] >>
  `EVERY (\b. lookup_block b.bb_label host.fn_blocks = SOME b) (fuel_probe_blocks ls)` by
    fs[Abbr `blocks`, EVERY_MEM] >>
  `PRE (LENGTH ls) = SUC fuel /\ HD ls = s.vs_current_bb /\ ls <> []` by simp[Abbr `ls`] >>
  qexists_tac `host` >> simp[] >> conj_tac
  >- (simp[Abbr `host`, lookup_block_def, FIND_APPEND_CASE] >> rpt strip_tac >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule fn_insts_mem_block >> strip_tac >>
      fs[Abbr `host`, MEM_APPEND] >>
      metis_tac[MEM_fn_insts, fuel_probe_blocks_do_not_invoke]) >>
  gen_tac >> conj_tac
  >- (irule fuel_probe_runs_out >> simp[] >> qexists_tac `ls` >> simp[]) >>
  mp_tac (Q.SPECL [`ls`,`host`,`ctx`,`s`] fuel_probe_stops) >> simp[]
QED

(* The probe is executed in the original context when the fragment calls
   internal functions. The added blocks themselves contain no calls. *)
Theorem frag_fuel_excludes_unlisted_jump_stable:
  frag_fuel Wv {} {} sa sb Kb /\ at_point sa s /\
  fn_has_code sa sb observer /\ no_phi_fn observer /\
  lookup_block sb.cs_current_bb observer.fn_blocks = SOME cut /\
  get_instruction cut (LENGTH sb.cs_current_insts) = SOME (mk_inst id STOP [] []) /\
  s'.vs_inst_idx = 0 /\ ~s'.vs_halted /\ callees_stable G ctx observer /\
  (!host. no_phi_fn host /\ callees_stable G ctx host /\
    (!l b. lookup_block l observer.fn_blocks = SOME b ==> lookup_block l host.fn_blocks = SOME b) ==>
    ?cost. !fuel. G <= fuel ==> run_from (fuel + cost) ctx host s = run_from fuel ctx host s') ==>
  IS_SOME (lookup_block s'.vs_current_bb observer.fn_blocks)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `lookup_block s'.vs_current_bb observer.fn_blocks` >> simp[] >>
  mp_tac (Q.INST [`base` |-> `observer`, `s` |-> `s'`, `fuel` |-> `G + Kb`]
    fuel_probe_attach) >>
  asm_rewrite_tac[] >> disch_then (qx_choose_then `host` strip_assume_tac) >>
  `fn_has_code sa sb host` by
    (fs[fn_has_code_def] >> qexists_tac `cut` >> simp[]) >>
  `lookup_block sb.cs_current_bb host.fn_blocks = SOME cut` by metis_tac[] >>
  `callees_stable G ctx host` by (fs[callees_stable_def] >> metis_tac[]) >>
  `?cost. !fuel. G <= fuel ==> run_from (fuel + cost) ctx host s = run_from fuel ctx host s'` by
    metis_tac[] >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` (mp_tac o REWRITE_RULE [frag_fuel_def]) >>
  disch_then (qspecl_then [`G`,`0`,`ctx`,`host`,`s`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[ZERO_LESS_EQ] >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  `!u f. at_point sb u ==> run_from f ctx host u =
        Halt (halt_state (u with vs_returndata := []))` by
    simp[at_point_def, run_from_def, Once exec_block_def, step_inst_non_invoke,
         mk_inst_def, step_inst_base_opcode_eqs] >>
  `!f g. G <= f /\ G <= g ==> run_from (f + j) ctx host s = run_from (g + j) ctx host s` by
    (fs[fuel_outcome_def] >> metis_tac[]) >>
  `G <= G + Kb + cost - j /\ G <= SUC (G + Kb) + cost - j /\
    G + Kb + cost - j + j = G + Kb + cost /\
    SUC (G + Kb) + cost - j + j = SUC (G + Kb) + cost` by decide_tac >>
  `run_from (G + Kb + cost) ctx host s = run_from (SUC (G + Kb) + cost) ctx host s` by
    (qpat_assum `!f g. G <= f /\ G <= g ==> run_from (f+j) ctx host s = _`
       (fn th =>
         qpat_assum `G <= G + Kb + cost - j` (fn lo =>
           qpat_assum `G <= SUC (G + Kb) + cost - j` (fn hi =>
             mp_tac (MATCH_MP (Q.SPECL [`G + Kb + cost - j`,
                `SUC (G + Kb) + cost - j`] th) (CONJ lo hi))))) >>
     pure_asm_rewrite_tac[] >> DISCH_TAC >> FIRST_ASSUM ACCEPT_TAC) >>
  `G <= G + Kb /\ G <= SUC (G + Kb)` by decide_tac >>
  `run_from (G + Kb) ctx host s' = run_from (SUC (G + Kb)) ctx host s'` by
    (qpat_assum `!fuel. G <= fuel ==> run_from (fuel + cost) _ _ _ = _`
       (qspecl_then [`G + Kb`] mp_tac) >>
     qpat_assum `!fuel. G <= fuel ==> run_from (fuel + cost) _ _ _ = _`
       (qspecl_then [`SUC (G + Kb)`] mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `!ctx. (∃e. _) /\ ∃t. _` (qspec_then `ctx` strip_assume_tac) >>
  metis_tac[exec_result_distinct]
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
  strip_tac >>
  match_mp_tac (Q.INST [`G` |-> `0`, `ctx` |-> `<|ctx_functions := []|>`,
    `Wv` |-> `Wv`, `sa` |-> `sa`, `sb` |-> `sb`, `Kb` |-> `Kb`,
    `s` |-> `s`, `cut` |-> `cut`, `id` |-> `id`]
    frag_fuel_excludes_unlisted_jump_stable) >>
  asm_simp_tac (srw_ss()) [callees_stable_def, lookup_function_def, FIND_thm] >>
  metis_tac[]
QED

Theorem frag_observed_edge_fuel:
  gas_path_edge ctx fn s n (OK t) /\ no_phi_fn fn /\
  no_phi_fn host /\ callees_stable G ctx host /\
  (!bb i. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb s.vs_inst_idx = SOME i ==>
          ?b. lookup_block s.vs_current_bb host.fn_blocks = SOME b /\
              get_instruction b s.vs_inst_idx = SOME i) ==>
  ?cost. !f. G <= f ==> run_from (f + cost) ctx host s = run_from f ctx host t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_path_edge _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_path_edge_def]) >>
  gvs[exit_result_def]
  >~ [`~is_terminator inst.inst_opcode`] >-
    (`MEM inst (fn_insts host)` by metis_tac[lookup_block_get_instruction_fn_insts] >>
     rename1 `step_inst k ctx inst s = OK u` >>
     `step_inst (G + k) ctx inst s = OK u` by
       (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
     `step_inst G ctx inst s = OK u` by
       metis_tac[step_inst_fuel_stable, arithmeticTheory.LESS_EQ_ADD] >>
     qexists_tac `0` >> simp[] >> rpt strip_tac >>
     `step_inst f ctx inst s = OK u` by metis_tac[step_inst_fuel_stable] >>
     mp_tac (Q.SPECL [`f`,`ctx`,`host`,`s`,`b`,`inst`] run_from_nonterm) >>
     simp[])
  >~ [`exit_result (step_inst fuel ctx inst s)`] >-
    (qpat_x_assum `OK t = step_inst fuel ctx inst s`
      (fn eq => fs[GSYM eq, exit_result_def])) >>
  `inst.inst_opcode <> INVOKE` by (qpat_assum `is_terminator inst.inst_opcode` mp_tac >>
      Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  `?lbl. u = jump_to lbl s` by
    (drule_all step_inst_ok_terminator_jump >> strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(), LET_THM] >>
     metis_tac[]) >>
  `step_inst_base inst s = OK (jump_to lbl s)` by fs[step_inst_non_invoke] >>
  `!f. run_from (SUC f) ctx host s = run_from f ctx host (jump_to lbl s)` by
    (gen_tac >> irule run_from_jump_exact >> asm_rewrite_tac[] >>
     qexistsl_tac [`b`,`inst`] >> simp[]) >>
  qexists_tac `1` >> rpt strip_tac >> simp[GSYM arithmeticTheory.ADD1]
  >~ [`eval_phis _ _ = OK _`] >-
    (`phi_prefix_length target.bb_instructions = 0` by
       (drule lookup_block_MEM >> fs[no_phi_fn_def, EVERY_MEM]) >>
     drule_then assume_tac eval_phis_no_phi >> gvs[jump_to_def]) >>
  gvs[jump_to_def]
QED

Theorem frag_observed_prefix_fuel:
  !ctx fn G host s t.
    no_phi_fn fn /\ no_phi_fn host /\ callees_stable G ctx host /\
    RTC (\u v. (?n. gas_path_edge ctx fn u n (OK v)) /\
      (!bb i. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
              get_instruction bb u.vs_inst_idx = SOME i ==>
              ?b. lookup_block u.vs_current_bb host.fn_blocks = SOME b /\
                  get_instruction b u.vs_inst_idx = SOME i)) s t ==>
    ?cost. !f. G <= f ==> run_from (f + cost) ctx host s = run_from f ctx host t
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `RTC _ s t` mp_tac >>
  MAP_EVERY qid_spec_tac [`t`,`s`] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >> conj_tac
  >- (gen_tac >> qexists_tac `0` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all frag_observed_edge_fuel >> strip_tac >>
  qexists_tac `cost + cost'` >> rpt strip_tac >>
  `G <= cost + f` by decide_tac >>
  qpat_assum `!f. G <= f ==> run_from (f + cost') _ _ _ = _`
    (qspec_then `cost + f` mp_tac) >>
  qpat_assum `!f. G <= f ==> run_from (cost + f) _ _ _ = _`
    (qspec_then `f` mp_tac) >>
  `cost + f + cost' = cost + cost' + f` by decide_tac >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem gas_path_first_outside:
  !ctx fn s n r. gas_path ctx fn s n r ==>
    !t P. r = OK t /\ P s ==>
    (P t /\ RTC (\a b. P a /\ ?j. gas_path_edge ctx fn a j (OK b)) s t) \/
    ?u v k m.
      RTC (\a b. P a /\ ?j. gas_path_edge ctx fn a j (OK b)) s u /\
      P u /\ ~P v /\ gas_path_edge ctx fn u k (OK v) /\
      gas_path ctx fn v m (OK t)
Proof
  ho_match_mp_tac gas_path_strongind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac
  >- gvs[RTC_REFL]
  >~ [`exit_result r`] >- gvs[exit_result_def] >>
  rename1 `gas_path_edge ctx fn s k (OK mid)` >>
  Cases_on `P mid`
  >- (qpat_x_assum `!t P. _ ==> _ \/ _`
        (qspecl_then [`t`,`P`] mp_tac) >> simp[] >>
      strip_tac
      >- (disj1_tac >> asm_rewrite_tac[] >> irule (cj 2 RTC_RULES) >>
          qexists_tac `mid` >> simp[] >> qexists_tac `k` >> simp[]) >>
      disj2_tac >> qexistsl_tac [`u`,`v`,`k'`,`m`] >>
      asm_rewrite_tac[] >> irule (cj 2 RTC_RULES) >>
      qexists_tac `mid` >> simp[] >> qexists_tac `k` >> simp[]) >>
  rename1 `gas_path ctx fn mid m _` >>
  disj2_tac >> qexistsl_tac [`s`,`mid`,`k`,`m`] >> gvs[RTC_REFL]
QED

(* In a normal executable path, the first step out of the fragment reaches
   its compiler cut. The observer is only used to certify that step. *)
Theorem frag_fuel_path_reaches_cut:
  frag_fuel Wv {} {} sa sb Kb /\ at_point sa s /\ P s /\
  gas_path ctx fn s n (OK t) /\ no_phi_fn fn /\
  fn_has_code sa sb observer /\ no_phi_fn observer /\ callees_stable G ctx observer /\
  lookup_block sb.cs_current_bb observer.fn_blocks = SOME cut /\
  get_instruction cut (LENGTH sb.cs_current_insts) = SOME (mk_inst id STOP [] []) /\
  (!u bb i. P u /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
                  get_instruction bb u.vs_inst_idx = SOME i ==>
       ?b. lookup_block u.vs_current_bb observer.fn_blocks = SOME b /\
           get_instruction b u.vs_inst_idx = SOME i) /\
  (!u k v. P u /\ gas_path_edge ctx fn u k (OK v) /\ ~P v /\ ~at_point sb v ==>
       v.vs_inst_idx = 0 /\ lookup_block v.vs_current_bb observer.fn_blocks = NONE) ==>
  (P t /\ RTC (\a b. P a /\ ?j. gas_path_edge ctx fn a j (OK b)) s t) \/
  ?u v k m.
      RTC (\a b. P a /\ ?j. gas_path_edge ctx fn a j (OK b)) s u /\
      P u /\ at_point sb v /\ gas_path_edge ctx fn u k (OK v) /\
      gas_path ctx fn v m (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `gas_path ctx fn s n (OK t)`
    (mp_tac o MATCH_MP gas_path_first_outside) >>
  disch_then (qspecl_then [`t`,`P`] mp_tac) >> simp[] >>
  disch_then DISJ_CASES_TAC >- simp[] >> disj2_tac >>
  qpat_x_assum `?u v k m. _` (qx_choosel_then [`u`,`v`,`k`,`m`] strip_assume_tac) >>
  qexistsl_tac [`u`,`v`,`k`,`m`] >> asm_rewrite_tac[] >>
  CCONTR_TAC >>
  `v.vs_inst_idx = 0 /\ lookup_block v.vs_current_bb observer.fn_blocks = NONE` by
    metis_tac[] >>
  `~v.vs_halted` by metis_tac[gas_path_edge_normal] >>
  `RTC (\a b. P a /\ ?j. gas_path_edge ctx fn a j (OK b)) s v` by
    (irule (cj 2 RTC_RULES_RIGHT1) >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `!host. no_phi_fn host /\ callees_stable G ctx host /\
     (!l b. lookup_block l observer.fn_blocks = SOME b ==> lookup_block l host.fn_blocks = SOME b) ==>
     ?cost. !f. G <= f ==> run_from (f + cost) ctx host s = run_from f ctx host v` by
    (gen_tac >> strip_tac >> irule frag_observed_prefix_fuel >> simp[] >>
     qexists_tac `fn` >> simp[] >>
     irule RTC_MONOTONE >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all frag_fuel_excludes_unlisted_jump_stable >> simp[]
QED
