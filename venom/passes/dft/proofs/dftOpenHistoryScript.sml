(* Provenance of live caller frames in finite open execution prefixes. *)
Theory dftOpenHistory
Ancestors
  dftOpenAdequacy dftOpenMachine venomExecSemantics arithmetic list

Definition dft_history_counter_def:
  dft_history_counter (DftOpen ctl stack n) = n
End

Theorem dft_history_deliver_counter[simp]:
  dft_history_counter (dft_open_deliver fn b bb inst s stack n r) = n
Proof
  Cases_on `r` >> simp[dft_open_deliver_def, dft_history_counter_def]
QED

Theorem dft_history_return_counter[simp]:
  dft_history_counter (dft_open_return r stack n) = n
Proof
  Cases_on `r` >> Cases_on `stack` >>
  simp[dft_open_return_def, dft_history_counter_def] >>
  Cases_on `h` >>
  simp[dft_open_return_def] >>
  CASE_TAC >> simp[dft_history_counter_def]
QED

Theorem dft_history_next_counter:
  dft_history_counter c <= dft_history_counter (dft_open_next a ctx c)
Proof
  Cases_on `c` >> rename1 `DftOpen ctl stack n` >> Cases_on `ctl`
  >- (simp[dft_open_next_def, dft_history_counter_def] >>
      CASE_TAC >> simp[dft_history_counter_def] >>
      CASE_TAC >> simp[dft_history_counter_def] >>
      CASE_TAC >> simp[dft_history_counter_def])
  >- (simp[dft_open_next_def, dft_history_counter_def] >>
      CASE_TAC >> simp[dft_history_counter_def] >>
      IF_CASES_TAC
      >- (simp[dft_open_invoke_def] >>
          CASE_TAC >> simp[dft_history_counter_def] >>
          rename1 `decode_invoke _ = SOME pair` >> PairCases_on `pair` >>
          simp[] >> CASE_TAC >> simp[dft_history_counter_def] >>
          CASE_TAC >> simp[dft_history_counter_def] >>
          CASE_TAC >> simp[dft_history_counter_def]) >>
      IF_CASES_TAC >> simp[] >>
      CASE_TAC >> simp[dft_history_counter_def] >>
      CASE_TAC >> simp[dft_history_counter_def]) >>
  simp[dft_open_next_def, dft_history_counter_def]
QED

Theorem dft_history_iter_counter:
  !j c. dft_history_counter c <=
    dft_history_counter (FUNPOW (dft_open_next a ctx) j c)
Proof
  Induct_on `j` >- simp[] >> gen_tac >>
  simp[FUNPOW_SUC] >>
  irule LESS_EQ_TRANS >>
  qexists_tac `dft_history_counter (FUNPOW (dft_open_next a ctx) j c)` >>
  simp[dft_history_next_counter]
QED

Definition dft_history_push_def:
  dft_history_push ctx c frame rest callee cs n <=>
    ?fn budget bb inst caller nm ops args.
      frame = DftCaller fn budget bb inst caller /\
      c = DftOpen (DftAt fn budget bb caller) rest n /\
      get_instruction bb caller.vs_inst_idx = SOME inst /\
      inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
      lookup_function nm ctx.ctx_functions = SOME callee /\
      eval_operands ops caller = SOME args /\ setup_callee callee args caller = SOME cs
End

(* Each nonempty suffix of a successor stack is either inherited without
   exiting its scope, or is precisely the frame just pushed by this step. *)
Theorem dft_history_step_suffix:
  dft_open_next a ctx c = DftOpen ctl (prefix ++ frame::rest) n ==>
  (dft_open_stack_extends (frame::rest) c /\
   ~dft_open_stack_exit (frame::rest) c) \/
  (?callee cs. prefix = [] /\ dft_history_push ctx c frame rest callee cs n)
Proof
  Cases_on `c` >> rename1 `DftOpen control stack m` >> Cases_on `control`
  >- suspend "enter"
  >- suspend "at"
  >- suspend "done"
QED

Resume dft_history_step_suffix[enter]:
  simp[dft_open_next_def] >>
  CASE_TAC >> simp[] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[] >>
  strip_tac >> gvs[dft_open_stack_extends_def, dft_open_stack_exit_def] >>
  metis_tac[]
QED

Resume dft_history_step_suffix[at]:
  simp[dft_open_next_def] >>
  CASE_TAC >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "push" >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[] >> Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >> simp[] >>
      simp[dft_open_deliver_def] >> strip_tac >>
      gvs[dft_open_stack_extends_def, dft_open_stack_exit_def] >> metis_tac[]) >>
  simp[] >> Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def] >> strip_tac >>
  gvs[dft_open_stack_extends_def, dft_open_stack_exit_def] >> metis_tac[]
QED

Resume dft_history_step_suffix[push]:
  simp[dft_open_invoke_def] >>
  CASE_TAC >> simp[] >> rename1 `decode_invoke inst = SOME pair` >>
  PairCases_on `pair` >> simp[] >>
  CASE_TAC >> simp[] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[] >>
  Cases_on `prefix` >> simp[] >> strip_tac >> gvs[]
  >- (disj2_tac >> simp[dft_history_push_def] >> metis_tac[]) >>
  simp[dft_open_stack_extends_def, dft_open_stack_exit_def] >>
  metis_tac[]
QED

Resume dft_history_step_suffix[done]:
  simp[dft_open_next_def] >> Cases_on `e` >> Cases_on `stack` >>
  simp[dft_open_return_def] >>
  Cases_on `h` >> simp[] >> CASE_TAC >> simp[dft_open_deliver_def] >>
  strip_tac >> gvs[] >> disj1_tac >>
  simp[dft_open_stack_extends_def, dft_open_stack_exit_def]
QED

Finalise dft_history_step_suffix

Definition dft_live_origin_def:
  dft_live_origin ctx q j frame rest <=>
    ?p callee budget cs n0.
      p < j /\ dft_history_push ctx (q p) frame rest callee cs n0 /\
      q (SUC p) = DftOpen (DftEnter callee budget cs) (frame::rest) n0 /\
      !t. SUC p <= t /\ t < j ==> ~dft_open_stack_exit (frame::rest) (q t)
End

Theorem dft_live_origin_extend:
  dft_live_origin ctx q j frame rest /\
  ~dft_open_stack_exit (frame::rest) (q j) ==>
  dft_live_origin ctx q (SUC j) frame rest
Proof
  simp[dft_live_origin_def] >> rpt strip_tac >>
  qexistsl_tac [`p`, `callee`, `budget`, `cs`, `n0`] >> simp[] >>
  rpt strip_tac >> Cases_on `t = j` >- gvs[] >>
  `t < j` by decide_tac >> metis_tac[]
QED

Theorem dft_live_origin_push:
  dft_history_push ctx (q j) frame rest callee cs n0 /\
  q (SUC j) = dft_open_next a ctx (q j) ==>
  dft_live_origin ctx q (SUC j) frame rest
Proof
  simp[dft_history_push_def] >> rpt strip_tac >> gvs[] >>
  simp[dft_live_origin_def] >> qexists_tac `j` >>
  simp[dft_open_next_def, dft_open_invoke_def, dft_history_push_def] >>
  metis_tac[]
QED

Theorem dft_history_all_origins:
  !j ctl stack n.
    FUNPOW (dft_open_next a ctx) j (DftOpen initial [] nstart) =
      DftOpen ctl stack n ==>
    !prefix frame rest. stack = prefix ++ frame::rest ==>
      dft_live_origin ctx
        (\t. FUNPOW (dft_open_next a ctx) t (DftOpen initial [] nstart))
        j frame rest
Proof
  Induct_on `j` >- simp[] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `dft_live_origin ctx q` >>
  `q (SUC j) = dft_open_next a ctx (q j)` by (simp[Abbr `q`] >> metis_tac[FUNPOW_SUC]) >>
  `dft_open_next a ctx (q j) = DftOpen ctl (prefix ++ frame::rest) n`
    by gvs[Abbr `q`] >>
  drule dft_history_step_suffix >> strip_tac
  >- (irule dft_live_origin_extend >> simp[] >>
      Cases_on `q j` >>
      gvs[dft_open_stack_extends_def] >>
      first_x_assum irule >> simp[Abbr `q`] >> metis_tac[]) >>
  irule dft_live_origin_push >> metis_tac[]
QED

Theorem dft_history_counter_between:
  p <= j ==>
  dft_history_counter (FUNPOW (dft_open_next a ctx) p c) <=
  dft_history_counter (FUNPOW (dft_open_next a ctx) j c)
Proof
  strip_tac >> `j = (j - p) + p` by decide_tac >>
  qpat_x_assum `j = _` SUBST1_TAC >>
  simp[FUNPOW_ADD, dft_history_iter_counter]
QED

Theorem dft_history_top_origin:
  FUNPOW (dft_open_next a ctx) j (DftOpen initial [] nstart) =
    DftOpen ctl (DftCaller fn budget bb inst caller::rest) n ==>
  ?p callee cs n0 nm ops args.
    p < j /\
    FUNPOW (dft_open_next a ctx) p (DftOpen initial [] nstart) =
      DftOpen (DftAt fn budget bb caller) rest n0 /\
    get_instruction bb caller.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops caller = SOME args /\ setup_callee callee args caller = SOME cs /\
    FUNPOW (dft_open_next a ctx) (SUC p) (DftOpen initial [] nstart) =
      DftOpen (DftEnter callee budget cs) (DftCaller fn budget bb inst caller::rest) n0 /\
    (!t. SUC p <= t /\ t < j ==> ~dft_open_stack_exit
      (DftCaller fn budget bb inst caller::rest)
      (FUNPOW (dft_open_next a ctx) t (DftOpen initial [] nstart))) /\ n0 <= n
Proof
  strip_tac >> drule dft_history_all_origins >>
  disch_then (qspecl_then [`[]`, `DftCaller fn budget bb inst caller`, `rest`] mp_tac) >>
  simp[dft_live_origin_def, dft_history_push_def] >> rpt strip_tac >> gvs[] >>
  rename1 `p < j` >>
  `dft_history_counter (FUNPOW (dft_open_next a ctx) p (DftOpen initial [] nstart)) <=
   dft_history_counter (FUNPOW (dft_open_next a ctx) j (DftOpen initial [] nstart))` by
    (irule dft_history_counter_between >> decide_tac) >>
  gvs[dft_history_counter_def] >>
  qexistsl_tac [`p`, `n0`] >> simp[] >>
  qpat_x_assum `FUNPOW _ (SUC p) _ = _` mp_tac >>
  simp[FUNPOW_SUC, dft_open_next_def, dft_open_invoke_def]
QED
