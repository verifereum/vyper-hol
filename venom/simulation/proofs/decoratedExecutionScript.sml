Theory decoratedExecution
Ancestors
  venomExecSemantics venomExecProps venomExecProofs venomInstProps venomInst venomState list

(* A finite non-Error evaluation, decorated at each executed instruction.
   Calls are atomic step_inst premises at exactly the semantic fuel. *)
val (decorated_block_rules, decorated_block_ind, decorated_block_cases) =
  Hol_reln `
  (!Q fuel ctx bb s inst s1 r.
    get_instruction bb s.vs_inst_idx = SOME inst /\ Q inst s /\
    step_inst fuel ctx inst s = OK s1 /\
    ~is_terminator inst.inst_opcode /\
    decorated_block Q fuel ctx bb
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) r ==>
    decorated_block Q fuel ctx bb s r) /\
  (!Q fuel ctx bb s inst s1.
    get_instruction bb s.vs_inst_idx = SOME inst /\ Q inst s /\
    step_inst fuel ctx inst s = OK s1 /\
    is_terminator inst.inst_opcode ==>
    decorated_block Q fuel ctx bb s
      (if s1.vs_halted then Halt s1 else OK s1)) /\
  (!Q fuel ctx bb s inst s1.
    get_instruction bb s.vs_inst_idx = SOME inst /\ Q inst s /\
    step_inst fuel ctx inst s = Halt s1 ==>
    decorated_block Q fuel ctx bb s (Halt s1)) /\
  (!Q fuel ctx bb s inst s1 a.
    get_instruction bb s.vs_inst_idx = SOME inst /\ Q inst s /\
    step_inst fuel ctx inst s = Abort a s1 ==>
    decorated_block Q fuel ctx bb s (Abort a s1)) /\
  (!Q fuel ctx bb s inst s1 vals.
    get_instruction bb s.vs_inst_idx = SOME inst /\ Q inst s /\
    step_inst fuel ctx inst s = IntRet vals s1 ==>
    decorated_block Q fuel ctx bb s (IntRet vals s1))`;

val (decorated_run_rules, decorated_run_ind, decorated_run_cases) =
  Hol_reln `
  (!Q fuel ctx fn s bb s_phi s1 r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    decorated_block Q fuel ctx bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK s1) /\
    ~s1.vs_halted /\ decorated_run Q fuel ctx fn s1 r ==>
    decorated_run Q (SUC fuel) ctx fn s r) /\
  (!Q fuel ctx fn s bb s_phi s1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    decorated_block Q fuel ctx bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK s1) /\
    s1.vs_halted ==>
    decorated_run Q (SUC fuel) ctx fn s (Halt s1)) /\
  (!Q fuel ctx fn s bb s_phi s1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    decorated_block Q fuel ctx bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (Halt s1) ==>
    decorated_run Q (SUC fuel) ctx fn s (Halt s1)) /\
  (!Q fuel ctx fn s bb s_phi s1 a.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    decorated_block Q fuel ctx bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (Abort a s1) ==>
    decorated_run Q (SUC fuel) ctx fn s (Abort a s1)) /\
  (!Q fuel ctx fn s bb s_phi s1 vals.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    decorated_block Q fuel ctx bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) (IntRet vals s1) ==>
    decorated_run Q (SUC fuel) ctx fn s (IntRet vals s1))`;

Theorem decorated_block_erase:
  !Q fuel ctx bb s r. decorated_block Q fuel ctx bb s r ==>
    exec_block fuel ctx bb s = r
Proof
  ho_match_mp_tac decorated_block_ind >> rpt strip_tac >>
  simp[Once exec_block_def]
QED

Theorem decorated_run_erase:
  !Q fuel ctx fn s r. decorated_run Q fuel ctx fn s r ==>
    run_blocks fuel ctx fn s = r
Proof
  ho_match_mp_tac decorated_run_ind >> rpt strip_tac >>
  drule decorated_block_erase >> strip_tac >>
  simp[Once run_blocks_def]
QED

Theorem decorated_block_nonerror:
  !Q fuel ctx bb s r. decorated_block Q fuel ctx bb s r ==>
    ~(?e. r = Error e)
Proof
  ho_match_mp_tac decorated_block_ind >> rpt strip_tac >> gvs[] >>
  Cases_on `s1.vs_halted` >> gvs[]
QED

Theorem decorated_run_nonerror:
  !Q fuel ctx fn s r. decorated_run Q fuel ctx fn s r ==>
    ~(?e. r = Error e)
Proof
  ho_match_mp_tac decorated_run_ind >> rpt strip_tac >> gvs[]
QED

Theorem decorated_block_mono:
  !Q fuel ctx bb s r. decorated_block Q fuel ctx bb s r ==>
    !Q'. (!inst u. Q inst u ==> Q' inst u) ==>
      decorated_block Q' fuel ctx bb s r
Proof
  ho_match_mp_tac decorated_block_ind >> rpt strip_tac
  >- (irule (cj 1 decorated_block_rules) >>
      qexistsl_tac [`inst`, `s1`] >> simp[] >> metis_tac[])
  >- (irule (cj 2 decorated_block_rules) >> simp[] >> metis_tac[])
  >- (irule (cj 3 decorated_block_rules) >> simp[] >> metis_tac[])
  >- (irule (cj 4 decorated_block_rules) >> simp[] >> metis_tac[])
  >> irule (cj 5 decorated_block_rules) >> simp[] >> metis_tac[]
QED

Theorem decorated_run_mono:
  !Q fuel ctx fn s r. decorated_run Q fuel ctx fn s r ==>
    !Q'. (!inst u. Q inst u ==> Q' inst u) ==>
      decorated_run Q' fuel ctx fn s r
Proof
  ho_match_mp_tac decorated_run_ind >> rpt strip_tac
  >- (rename1 `decorated_block Q fuel ctx bb _ (OK next)` >>
      irule (cj 1 decorated_run_rules) >>
      qexistsl_tac [`bb`, `next`, `s_phi`] >> simp[] >>
      drule decorated_block_mono >>
      disch_then (qspec_then `Q'` irule) >> first_assum ACCEPT_TAC)
  >- (irule (cj 2 decorated_run_rules) >> simp[] >>
      drule decorated_block_mono >>
      disch_then (qspec_then `Q'` irule) >> first_assum ACCEPT_TAC)
  >- (irule (cj 3 decorated_run_rules) >> simp[] >>
      drule decorated_block_mono >>
      disch_then (qspec_then `Q'` irule) >> first_assum ACCEPT_TAC)
  >- (irule (cj 4 decorated_run_rules) >> simp[] >>
      drule decorated_block_mono >>
      disch_then (qspec_then `Q'` irule) >> first_assum ACCEPT_TAC)
  >> irule (cj 5 decorated_run_rules) >> simp[] >>
     drule decorated_block_mono >>
     disch_then (qspec_then `Q'` irule) >> first_assum ACCEPT_TAC
QED

(* Construction from a local invariant. Only OK transitions preserve I;
   no safety obligation is introduced after an Error or terminal result. *)
Theorem decorated_block_construct:
  !fuel ctx bb s Inv Post Q.
    Inv s /\
    (!u inst. Inv u /\ get_instruction bb u.vs_inst_idx = SOME inst ==>
      Q inst u) /\
    (!u inst v. Inv u /\ get_instruction bb u.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst u = OK v ==>
      (if is_terminator inst.inst_opcode then Post v
       else Inv (v with vs_inst_idx := SUC u.vs_inst_idx))) /\
    ~(?e. exec_block fuel ctx bb s = Error e) ==>
    decorated_block Q fuel ctx bb s (exec_block fuel ctx bb s) /\
    (!v. exec_block fuel ctx bb s = OK v ==> Post v)
Proof
  rpt gen_tac >> map_every qid_spec_tac [`Q`, `Post`, `Inv`] >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!y. _` (mk_asm "ih") >>
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `~(?e. exec_block _ _ _ _ = Error e)` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `SOME inst` >>
  qpat_x_assum `~(?e. exec_block _ _ _ _ = Error e)` mp_tac >>
  simp[Once exec_block_def] >> disch_tac >>
  simp[Once exec_block_def] >>
  `Q inst s` by metis_tac[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[]
  >- suspend "ok"
  >- (conj_tac >- metis_tac[cj 3 decorated_block_rules] >>
      simp[Once exec_block_def])
  >- (conj_tac >- metis_tac[cj 4 decorated_block_rules] >>
      simp[Once exec_block_def])
  >> conj_tac >- metis_tac[cj 5 decorated_block_rules] >>
     simp[Once exec_block_def]
QED

Resume decorated_block_construct[ok]:
  rename1 `step_inst fuel ctx inst s = OK next` >>
  `(if is_terminator inst.inst_opcode then Post next
    else Inv (next with vs_inst_idx := SUC s.vs_inst_idx))` by metis_tac[] >>
  Cases_on `is_terminator inst.inst_opcode` >> fs[]
  >- (conj_tac
      >- (irule (cj 2 decorated_block_rules) >> metis_tac[]) >>
      simp[Once exec_block_def] >> Cases_on `next.vs_halted` >> simp[]) >>
  `LENGTH bb.bb_instructions - SUC s.vs_inst_idx <
   LENGTH bb.bb_instructions - s.vs_inst_idx` by
    (fs[get_instruction_def, AllCaseEqs()] >> decide_tac) >>
  asm_x "ih" (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[] >>
  disch_then (qspec_then `next with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`Inv`, `Post`, `Q`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac
  >- (irule (cj 1 decorated_block_rules) >> metis_tac[]) >>
  simp[Once exec_block_def]
QED
Finalise decorated_block_construct

Theorem decorated_run_construct:
  !fuel ctx fn s Inv Q.
    Inv s /\ s.vs_inst_idx = 0 /\
    (!bb u v. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      u.vs_inst_idx = 0 /\ Inv u /\ eval_phis u bb.bb_instructions = OK v ==>
      Inv (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
    (!fuel bb u. Inv u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      ~(?e. exec_block fuel ctx bb u = Error e) ==>
      decorated_block Q fuel ctx bb u (exec_block fuel ctx bb u) /\
      (!v. exec_block fuel ctx bb u = OK v ==> Inv v)) /\
    ~(?e. run_blocks fuel ctx fn s = Error e) ==>
    decorated_run Q fuel ctx fn s (run_blocks fuel ctx fn s)
Proof
  Induct_on `fuel`
  >- simp[Once run_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ctx fn s Inv Q. _` (mk_asm "ih") >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `~(?e. run_blocks _ _ _ _ = Error e)` mp_tac >>
      simp[Once run_blocks_def]) >> rename1 `SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- suspend "phis_ok" >>
  qpat_x_assum `~(?e. run_blocks _ _ _ _ = Error e)` mp_tac >>
  simp[Once run_blocks_def]
QED

Resume decorated_run_construct[phis_ok]:
  rename1 `eval_phis s bb.bb_instructions = OK phi` >>
  qpat_x_assum `~(?e. run_blocks _ _ _ _ = Error e)` mp_tac >>
  simp[Once run_blocks_def] >> disch_tac >>
  `Inv (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[] >>
  `lookup_block
     (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
     fn.fn_blocks = SOME bb` by
    (drule eval_phis_preserves_current_bb >> simp[]) >>
  qmatch_asmsub_abbrev_tac `exec_block fuel ctx bb entry` >>
  `~(?e. exec_block fuel ctx bb entry = Error e)` by
    (Cases_on `exec_block fuel ctx bb entry` >> gvs[]) >>
  `decorated_block Q fuel ctx bb entry (exec_block fuel ctx bb entry) /\
   (!v. exec_block fuel ctx bb entry = OK v ==> Inv v)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[Once run_blocks_def] >>
  Cases_on `exec_block fuel ctx bb entry` >> fs[]
  >- suspend "block_ok"
  >- (irule (cj 3 decorated_run_rules) >>
      simp[] >> metis_tac[])
  >- (irule (cj 4 decorated_run_rules) >>
      simp[] >> metis_tac[])
  >> irule (cj 5 decorated_run_rules) >> simp[] >> metis_tac[]
QED
Resume decorated_run_construct[block_ok]:
  rename1 `exec_block fuel ctx bb entry = OK next` >>
  Cases_on `next.vs_halted` >> fs[]
  >- (irule (cj 2 decorated_run_rules) >> simp[] >> metis_tac[]) >>
  `next.vs_inst_idx = 0` by metis_tac[exec_block_OK_inst_idx_0] >>
  irule (cj 1 decorated_run_rules) >>
  qexistsl_tac [`bb`, `next`, `phi`] >> simp[] >>
  asm_x "ih" irule >> simp[] >> qexists_tac `Inv` >>
  simp[] >> metis_tac[]
QED
Finalise decorated_run_construct

Theorem decorated_block_invariant:
  Inv s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!bb inst u. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\ Inv u ==> Q inst u) /\
  (!bb inst fuel u v. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\ Inv u /\
    step_inst fuel ctx inst u = OK v ==>
    Inv (if is_terminator inst.inst_opcode then v
         else v with vs_inst_idx := SUC u.vs_inst_idx)) /\
  ~(?e. exec_block fuel ctx bb s = Error e) ==>
  decorated_block Q fuel ctx bb s (exec_block fuel ctx bb s) /\
  (!v. exec_block fuel ctx bb s = OK v ==> Inv v)
Proof
  strip_tac >> irule decorated_block_construct >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `\u. Inv u /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `Inv (if is_terminator inst.inst_opcode then v
        else v with vs_inst_idx := SUC u.vs_inst_idx)` by metis_tac[] >>
  Cases_on `is_terminator inst.inst_opcode` >> fs[] >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem decorated_run_invariant:
  Inv s /\ s.vs_inst_idx = 0 /\
  (!bb u v. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    u.vs_inst_idx = 0 /\ Inv u /\ eval_phis u bb.bb_instructions = OK v ==>
    Inv (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!bb inst fuel u v. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\ Inv u /\
    step_inst fuel ctx inst u = OK v ==>
    Inv (if is_terminator inst.inst_opcode then v
         else v with vs_inst_idx := SUC u.vs_inst_idx)) /\
  (!bb inst u. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\ Inv u ==> Q inst u) /\
  ~(?e. run_blocks fuel ctx fn s = Error e) ==>
  decorated_run Q fuel ctx fn s (run_blocks fuel ctx fn s)
Proof
  strip_tac >> irule decorated_run_construct >>
  reverse conj_tac >- metis_tac[] >> qexists_tac `Inv` >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  irule decorated_block_invariant >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  qexists_tac `fn` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
