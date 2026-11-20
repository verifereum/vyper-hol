Theory staticAbortOptStackShuffleCut
Ancestors combin[qualified,ignore_grammar]
  staticAbortProtectedFetch staticAbortProtectedTraceCoverage asmSymPcOwn asmSymOwnCode
  staticAbortOptStackStopped
  stackOpSim asmOptPeephole asmOptimizer asmSplice asmSymSem asmWf asmSem
  codegenSymRel staticAbortStraight planExec alist
  staticAbortProtectedActualPrefix asmDataEnv asmSymBridge
  list rich_list arithmetic finite_map pred_set words

(* Only symbolic slot identity is used at the pending cut.  In particular
   no label is decoded using the intermediate program's concrete offsets. *)
val cut_just = ``
  \(height:(num#num)->num) (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) x stk.
    LENGTH stk = height x /\
    (!k l o'. tag x k = SOME(l,o') ==> k < height x /\ EL k stk = Lab l 0) /\
    (!k. boolean x k ==> k < height x /\ (EL k stk = Val 0w \/ EL k stk = Val 1w))``;

val cut_shuffle = ``
  \opn (stk:sval list). case opn of NONE => TL stk
    | SOME n => LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk)``;

val cut_fetch = ``\opn. AsmOp (case opn of NONE => "POP" | SOME n => swap_name n)``;

val cut_height = ``\(opn:num option) (h:num). case opn of NONE => h-1 | SOME n => h``;

val cut_src = ``\opn (k:num). case opn of NONE => k+1
    | SOME n => if k=0 then n else if k=n then 0 else k``;

val cut_size = ``\(opn:num option) (h:num). case opn of NONE => 0<h | SOME n => 0<n /\ n<h``;

val cut_pull = ``
  \(height:(num#num)->num) (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) x y opn.
    (!k l o'. tag y k = SOME(l,o') ==> k < height y /\
       ^cut_src opn k < height x /\ tag x (^cut_src opn k) = SOME(l,o')) /\
    (!k. boolean y k ==> k < height y /\
       ^cut_src opn k < height x /\ boolean x (^cut_src opn k))``;

(* Slot transport does not require evaluating an old pending sym_step. *)
Theorem strict_shuffle_just[local]:
  ^cut_just height tag boolean x stk /\ ^cut_size opn (height x) /\
  height y = ^cut_height opn (height x) /\ ^cut_pull height tag boolean x y opn ==>
  ^cut_just height tag boolean y (^cut_shuffle opn stk)
Proof
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "source")
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "pull")))) >>
  qmatch_goalsub_abbrev_tac `LENGTH out` >>
  `LENGTH stk = height x` by (asm "source" (ACCEPT_TAC o CONJUNCT1)) >>
  `LENGTH out = height y /\ !k. k < height y ==> EL k out = EL (^cut_src opn k) stk` by (
    namedCases_on `opn` ["", "n"]
    >- (Cases_on `stk` >> gvs[Abbr `out`, GSYM ADD1, EL]) >>
    gvs[Abbr `out`, LENGTH_LUPDATE] >> rpt strip_tac >>
    Cases_on `k=0` >> Cases_on `k=n` >> gvs[EL_LUPDATE, EL] >>
    Cases_on `stk` >> gvs[listTheory.LUPDATE_DEF]) >>
  conj_tac >- simp[] >> conj_tac
  >- (map_every qx_gen_tac [`k`,`l`,`origin`] >> disch_tac >>
      asm "pull" (qspecl_then [`k`,`l`,`origin`] (drule_then strip_assume_tac) o CONJUNCT1) >>
      simp[] >> asm "source" (drule_then strip_assume_tac o cj 2) >> simp[]) >>
  qx_gen_tac `k` >> disch_tac >>
  asm "pull" (qspec_then `k` (drule_then strip_assume_tac) o CONJUNCT2) >>
  simp[] >> asm "source" (drule_then strip_assume_tac o cj 3) >> simp[]
QED

val cut_hop = ``
  \p (V:(num#num)->bool) (rank:(num#num)->num) pc height tag boolean edge.
    !x opn. x IN V /\ EL (pc x) p = ^cut_fetch opn /\
            (case opn of NONE => T | SOME n => 0<n /\ n<=16) ==>
      ^cut_size opn (height x) /\
      ?y. edge x y /\ y IN V /\ rank y < rank x /\ pc y = pc x+1 /\
          height y = ^cut_height opn (height x) /\ ^cut_pull height tag boolean x y opn``;

val strict_path = ``
  \(V:(num#num)->bool) (rank:(num#num)->num) pc height edge path x z (ops:num option list).
    path 0 = x /\ path (LENGTH ops) = z /\
    (!i. i <= LENGTH ops ==> path i IN V /\ pc (path i) = pc x + i) /\
    (!i. i < LENGTH ops ==> edge (path i) (path (SUC i)) /\
       rank (path (SUC i)) < rank (path i) /\
       ^cut_size (EL i ops) (height (path i)) /\
       height (path (SUC i)) = ^cut_height (EL i ops) (height (path i)))``;

Theorem strict_shuffle_walk[local]:
  ^cut_hop p V rank pc height tag boolean edge ==>
  !ops x stk. x IN V /\ ^cut_just height tag boolean x stk /\
     (!i. i < LENGTH ops ==> EL (pc x+i) p = ^cut_fetch (EL i ops) /\
         (case EL i ops of NONE => T | SOME n => 0<n /\ n<=16)) ==>
    ?z path. ^strict_path V rank pc height edge path x z ops /\
      (ops <> [] ==> rank z < rank x) /\
      ^cut_just height tag boolean z (FOLDL (\stk opn. ^cut_shuffle opn stk) stk ops)
Proof
  BETA_TAC >> disch_then (mk_asm "hop") >> Induct
  >- (simp[] >> rpt strip_tac >> qexists `\i. x` >> simp[]) >>
  qx_gen_tac `opn` >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (mk_asm "root") (mk_asm "fetch"))) >>
  asm "hop" (qspecl_then [`x`,`opn`] mp_tac) >>
  impl_tac >- (asm "fetch" (qspec_then `0:num` mp_tac) >> simp[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `y` strip_assume_tac)) >>
  first_x_assum (qspecl_then [`y`,`^cut_shuffle opn stk`] mp_tac) >>
  impl_tac >- (
    conj_tac >- simp[] >> conj_tac >-
      (BETA_TAC >> MATCH_MP_TAC (BETA_RULE strict_shuffle_just) >>
       asm "root" assume_tac >> asm_rewrite_tac[]) >>
    qx_gen_tac `i` >> strip_tac >> asm "fetch" (qspec_then `SUC i` mp_tac) >>
    simp[ADD1, AC ADD_ASSOC ADD_COMM]) >>
  disch_then (qx_choose_then `z` (qx_choose_then `path` strip_assume_tac)) >>
  qexistsl [`z`,`\i. if i=0 then x else path (PRE i)`] >>
  conj_tac >- (
    simp[] >> conj_tac >-
      (gen_tac >> Cases_on `i` >> simp[ADD1, AC ADD_ASSOC ADD_COMM]) >>
    gen_tac >> Cases_on `i` >> simp[]) >>
  conj_tac >- (Cases_on `ops` >> gvs[] >> metis_tac[LESS_TRANS]) >>
  simp[] >> metis_tac[]
QED

(* Only the literal AsmOp arm of Rows needs to be opened here. *)
val cut_op_check = ``
  \p cc pc h (tg:num->(string#num)option) arm legal dead name.
    !next. next = (\n. arm (\c:num. c = pc+1) n /\ legal (\c. c = pc+1) n) ==>
    !target. target = (\c. ?l o' off. tg 0 = SOME(l,o') /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME c) ==>
    !untagged. untagged = (\a. !k. k<a ==> tg k=NONE) ==>
    !stop. stop = (\a. a<=h /\ untagged a /\ dead) ==>
    if name="INVALID" then stop 0
    else if name="REVERT" then stop 2
    else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
         then cc.cc_static /\ stop (asm_op_arity name)
    else case ALOOKUP dup_table name of
      SOME n => n<h /\ next (h+1)
    | NONE => case ALOOKUP swap_table name of
        SOME n => 0<n /\ n<h /\ next h
      | NONE =>
          if name="JUMP" then 1<=h /\ arm target (h-1) /\ legal target (h-1)
          else if name="JUMPI" then
            2<=h /\ tg 1=NONE /\ arm (\c. c=pc+1) (h-2) /\ arm target (h-2) /\
            legal (\c. c=pc+1 \/ target c) (h-2)
          else ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                 untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m)``;

val cut_op_flow = ``
  \p (height:(num#num)->num) (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) x y name.
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !inherit. inherit = (\(src:num->num option) (fresh:num->(string#num)option) (bnew:num->bool).
      (!k l origin. tag y k = SOME(l,origin) ==> k < hj /\
          (fresh k = SOME(l,origin) \/ ?a. src k = SOME a /\ a < hi /\
                                            tag x a = SOME(l,origin))) /\
      (!k. boolean y k ==> k < hj /\ (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
    case ALOOKUP dup_table name of
      SOME n => n < hi /\ hj = hi+1 /\
        inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
    | NONE => case ALOOKUP swap_table name of
        SOME n => 0<n /\ n<hi /\ hj=hi /\
          inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
      | NONE => !a. a = asm_op_arity name ==> !m. m = hj + a - hi ==>
          a <= hi /\ hj = m+(hi-a) /\ ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
          inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
            (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one (AsmOp name) /\
              !t u. LENGTH t.as_stack=hi /\
                asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                  (AsmOp name) t = AsmOK u ==> (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))``;

val cut_op_rows = ``
  \p cc (V:(num#num)->bool) (rank:(num#num)->num) pc height tag boolean edge.
    (!x name. x IN V /\ EL (pc x) p = AsmOp name ==>
      ^cut_op_check p cc (pc x) (height x) (tag x)
        (\P n. ?y. edge x y /\ P (pc y) /\ height y=n)
        (\P n. !y. edge x y ==> P (pc y) /\ height y=n)
        (!y. ~edge x y) name) /\
    (!x y name. edge x y /\ EL (pc x) p = AsmOp name ==>
      y IN V /\ rank y < rank x /\ ^cut_op_flow p height tag boolean x y name)``;

Theorem cut_swap_name_facts[local]:
  !n. n < 17 ==> 0 < n ==>
    ALOOKUP dup_table (swap_name n) = NONE /\
    ALOOKUP swap_table (swap_name n) = SOME n /\
    ~MEM (swap_name n) ["INVALID";"REVERT";"SSTORE";"TSTORE";
                        "LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
Proof
  CONV_TAC (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV EVAL)) >> EVAL_TAC >> simp[]
QED

Theorem cut_pop_name_facts[local]:
  ALOOKUP dup_table "POP" = NONE /\ ALOOKUP swap_table "POP" = NONE /\
  asm_op_arity "POP" = 1 /\ (!m. static_abort_straight "POP" m <=> m=0)
Proof
  simp[static_abort_straight_def] >> EVAL_TAC
QED

Theorem strict_shuffle_hop[local]:
  ^cut_op_rows p cc V rank pc height tag boolean edge ==>
  ^cut_hop p V rank pc height tag boolean edge
Proof
  simp[LET_THM] >> disch_then (CONJUNCTS_THEN2 (mk_asm "rows") (mk_asm "edges")) >>
  qx_gen_tac `x` >> namedCases_on `opn` ["", "n"]
  >- (simp[] >> strip_tac >> asm "rows" (qspecl_then [`x`,`"POP"`] mp_tac) >>
      simp[cut_pop_name_facts] >> strip_tac >>
      rename1 `edge x y` >> asm "edges" (qspecl_then [`x`,`y`,`"POP"`] mp_tac) >>
      simp[cut_pop_name_facts] >> strip_tac >> qexists `y` >> simp[] >>
      `height y + 1 - height x = 0` by decide_tac >> gvs[ADD_COMM]) >>
  simp[] >> strip_tac >> `n < 17` by decide_tac >>
  drule_all cut_swap_name_facts >> simp[] >> strip_tac >>
  asm "rows" (qspecl_then [`x`,`swap_name n`] mp_tac) >> simp[] >> strip_tac >>
  rename1 `edge x y` >> asm "edges" (qspecl_then [`x`,`y`,`swap_name n`] mp_tac) >>
  simp[] >> strip_tac >> qexists `y` >> simp[]
QED

val cut_fold = ``FOLDL (\stk opn. ^cut_shuffle opn stk)``;

Theorem cut_shuffle_length[local]:
  ^cut_size opn (LENGTH stk) ==>
  LENGTH (^cut_shuffle opn stk) = ^cut_height opn (LENGTH stk)
Proof
  Cases_on `opn` >> simp[] >> Cases_on `stk` >> simp[]
QED

Theorem strict_path_sizes[local]:
  ^strict_path V rank pc height edge path x z ops /\
  LENGTH stk = height x ==>
  !i. i < LENGTH ops ==> ^cut_size (EL i ops) (LENGTH (^cut_fold stk (TAKE i ops)))
Proof
  BETA_TAC >> strip_tac >>
  `!i. i <= LENGTH ops ==> LENGTH (^cut_fold stk (TAKE i ops)) = height (path i)` by (
    Induct >- simp[] >> strip_tac >>
    `i < LENGTH ops` by decide_tac >>
    qpat_assum `!j. j < LENGTH ops ==> edge _ _ /\ _`
      (qspec_then `i` strip_assume_tac) >>
    `LENGTH (^cut_fold stk (TAKE i ops)) = height (path i)` by simp[] >>
    simp[TAKE_SUC, FOLDL_APPEND] >> gvs[BETA_RULE cut_shuffle_length]) >>
  rpt strip_tac >>
  qpat_assum `!j. j <= LENGTH ops ==> LENGTH _ = _`
    (qspec_then `i` mp_tac) >>
  qpat_x_assum `!j. j < LENGTH ops ==> edge _ _ /\ _`
    (qspec_then `i` mp_tac) >> simp[] >> gvs[]
QED

val fixed_cut_cases = ``
  [(1:num,[AsmOp "DUP1";AsmOp "SWAP2";AsmOp "SWAP1"],[AsmOp "SWAP1";AsmOp "DUP2"],
      [SOME (2:num);SOME 1]);
   (2,[AsmOp "DUP1";AsmOp "SWAP2";AsmOp "SWAP1"],[AsmOp "SWAP1";AsmOp "DUP2"],
      [SOME 1]);
   (1,[AsmOp "DUP1";AsmOp "SWAP1";AsmOp "POP"],[],[SOME 1;NONE]);
   (2,[AsmOp "DUP1";AsmOp "SWAP1";AsmOp "POP"],[],[NONE]);
   (1,[AsmOp "SWAP1";AsmOp "POP";AsmOp "POP"],[AsmOp "POP";AsmOp "POP"],[NONE;NONE]);
   (2,[AsmOp "SWAP1";AsmOp "POP";AsmOp "POP"],[AsmOp "POP";AsmOp "POP"],[NONE]);
   (1,[AsmOp "DUP1";AsmOp "SWAP1"],[AsmOp "DUP1"],[SOME 1])]``;

val cut_fit = ``\(opn:num option). case opn of NONE => T | SOME n => 0<n /\ n<=16``;

Theorem fixed_cut_case_fetch[local]:
  MEM (c,pat,repl,ops) ^fixed_cut_cases ==>
  MAP ^cut_fetch ops = DROP c pat /\ EVERY ^cut_fit ops /\ ops <> []
Proof
  simp[] >> strip_tac >> gvs[swap_name_def]
QED

val cut_visit_result = ``
  \allow_own own q env u ss (repl:asm_inst list) (ops:num option list).
    ?out. sym_steps_mode allow_own q env own (LENGTH repl) u = SymOK out /\
      out.sym_base.as_pc = u.sym_base.as_pc + LENGTH repl /\
      out.sym_base.as_call_ctx = ss.sym_base.as_call_ctx /\
      out.sym_base.as_requests = ss.sym_base.as_requests /\
      out.sym_stack = ^cut_fold ss.sym_stack ops``;

Theorem fixed_cut_visit_mode[local]:
  MEM (c,pat,repl,ops) ^fixed_cut_cases /\
  u.sym_base.as_pc = LENGTH pre /\
  sym_steps_mode allow_own (pre++pat++tail) env own c u = SymOK ss /\
  (!i. i < LENGTH ops ==> ^cut_size (EL i ops) (LENGTH (^cut_fold ss.sym_stack (TAKE i ops)))) ==>
  ^cut_visit_result allow_own own (pre++repl++tail) env u ss repl ops
Proof
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (fn th => qspec_then `0:num` assume_tac th >> qspec_then `1:num` assume_tac th)))) >>
  gvs[] >>
  qpat_x_assum `sym_steps_mode allow_own _ _ _ _ _ = SymOK _` mp_tac >>
  Cases_on `u.sym_stack` >>
  simp[protected_mode_fetch_one, protected_mode_fetch_two, protected_mode_fetch_three, sym_steps_mode_zero, EL_APPEND_EQN] >>
  simp[literal_stack_dispatch, sym_dup_def, sym_swap_def, sym_set_stack_def, asm_next_def, LUPDATE_compute] >>
  rename1 `u.sym_stack = _ :: stk` >> Cases_on `stk` >>
  simp[protected_mode_fetch_one, protected_mode_fetch_two, protected_mode_fetch_three,
       sym_steps_mode_zero, EL_APPEND_EQN, literal_stack_dispatch, sym_dup_def, sym_swap_def,
       sym_set_stack_def, asm_next_def, LUPDATE_compute] >> strip_tac >> gvs[LUPDATE_compute]
QED

(* The first, protected SWAP rules out a mere prefix match without a
   dispatch-table entry.  The pending second SWAP is a slot permutation. *)
Theorem guarded_cut_visit_mode[local]:
  asm_swap_op a /\ u.sym_base.as_pc = LENGTH pre /\
  sym_steps_mode allow_own (pre++[a;a]++tail) env own 1 u = SymOK ss ==>
  ?n. 0 < n /\ n <= 16 /\ a = ^cut_fetch (SOME n) /\
      ^cut_visit_result allow_own own (pre++tail) env u ss [] [SOME n]
Proof
  Cases_on `a` >> simp[Excl "isPREFIX", asm_swap_op_def] >> strip_tac >>
  rename1 `sym_steps_mode allow_own (_ ++ [AsmOp name; AsmOp name] ++ _) _ _ _ _ = _` >>
  `isPREFIX "SWAP" name` by fs[] >>
  `name <> "CODESIZE" /\ name <> "CODECOPY"` by
    (conj_tac >> disch_then SUBST_ALL_TAC >> fs[]) >>
  qpat_x_assum `sym_steps_mode allow_own _ _ _ _ _ = SymOK _` mp_tac >>
  simp[protected_mode_fetch_one, protected_mode_fetch_two, protected_mode_fetch_three, sym_steps_mode_zero, EL_APPEND_EQN] >>
  Cases_on `ALOOKUP swap_table name`
  >- (drule_all swap_prefix_unknown >> strip_tac >>
      drule_all sym_step_unknown_op >>
      disch_then (qspecl_then [`u`,`pre++[AsmOp name;AsmOp name]++tail`,`env`] assume_tac) >>
      gvs[]) >>
  rename1 `ALOOKUP swap_table name = SOME n` >>
  drule sym_step_swap_table >> strip_tac >>
  `0 < n /\ n <= 16 /\ name = swap_name n` by (
    `EVERY (\(a,k). 0<k /\ k<=16 /\ a=swap_name k) swap_table` by EVAL_TAC >>
    drule ALOOKUP_MEM >> strip_tac >>
    qpat_x_assum `EVERY _ swap_table`
      (mp_tac o Q.SPEC `(name,n)` o REWRITE_RULE[EVERY_MEM]) >> simp[]) >>
  qpat_x_assum `!ss p env. sym_step p env (AsmOp name) ss = sym_swap n ss`
    (pure_rewrite_tac o single) >>
  Cases_on `n < LENGTH u.sym_stack` >>
  simp[sym_swap_def, sym_set_stack_def, asm_next_def] >>
  strip_tac >> qexists `n` >> gvs[swap_swap_id]
QED

(* Normalize both literal and guarded windows to a list of residual
   permutations and pops, with a replay obligation only on the replacement. *)
val cut_families = ``
  \(pat:asm_inst list) repl.
    (?c ops. MEM (c,pat,repl,ops) ^fixed_cut_cases) \/
    (?a. asm_swap_op a /\ pat=[a;a] /\ repl=[])``;

Theorem cut_residual_visit_mode[local]:
  ^cut_families pat repl /\
  0 < c /\ c < LENGTH pat /\ u.sym_base.as_pc=LENGTH pre /\
  sym_steps_mode allow_own (pre++pat++tail) env own c u = SymOK ss ==>
  ?ops. MAP ^cut_fetch ops = DROP c pat /\ EVERY ^cut_fit ops /\
    ((!i. i < LENGTH ops ==> ^cut_size (EL i ops) (LENGTH (^cut_fold ss.sym_stack (TAKE i ops)))) ==>
     ^cut_visit_result allow_own own (pre++repl++tail) env u ss repl ops)
Proof
  BETA_TAC >> strip_tac
  >- (`?ops. MEM (c,pat,repl,ops) ^fixed_cut_cases` by (
        qpat_x_assum `MEM (_,pat,repl,_) _` mp_tac >> simp[] >>
        strip_tac >> gvs[] >>
        `c=1 \/ c=2` by decide_tac >> gvs[]) >>
      drule fixed_cut_case_fetch >> strip_tac >> qexists `ops'` >>
      simp[] >> strip_tac >>
      mp_tac (Q.INST [`u` |-> `u`, `ss` |-> `ss`, `env` |-> `env`, `ops` |-> `ops'`]
        (BETA_RULE fixed_cut_visit_mode)) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      qpat_assum `u.sym_base.as_pc = LENGTH pre` (pure_rewrite_tac o single) >>
      disch_then ACCEPT_TAC) >>
  `c=1` by gvs[] >> gvs[] >>
  drule_all (BETA_RULE guarded_cut_visit_mode) >> strip_tac >> qexists `[SOME n]` >> gvs[]
QED

Theorem cut_family_stopped_mode[local]:
  ^cut_families pat repl /\
  asm_static_wf (pre++pat++tail) /\ s.as_pc=0 /\
  sym_steps_mode allow_own (pre++pat++tail) env own n (sym_init s)=SymOK ss /\
  LENGTH pre < ss.sym_base.as_pc /\ ss.sym_base.as_pc < LENGTH pre+LENGTH pat ==>
  ?j u. u.sym_base.as_pc=LENGTH pre /\
     sym_steps_mode allow_own (pre++pat++tail) env own (ss.sym_base.as_pc-LENGTH pre) u=SymOK ss /\
     sym_steps_mode allow_own (pre++repl++tail) env own j (sym_init s)=SymOK u
Proof
  BETA_TAC >> strip_tac >>
  qspecl_then [`pre`,`pat`,`repl`,`tail`,`env`,`s`,`n`,`ss`] mp_tac
    (REWRITE_RULE[LET_THM] stack_peephole_one_stopped_prefix_mode) >>
  gvs[] >> metis_tac[]
QED

Theorem cut_suffix_fetch[local]:
  MAP ^cut_fetch ops = DROP c pat /\ EVERY ^cut_fit ops /\
  c < LENGTH pat /\ pc e = LENGTH pre+c ==>
  LENGTH ops=LENGTH pat-c /\
  !i. i<LENGTH ops ==>
      EL (pc e+i) (pre++pat++tail) = ^cut_fetch (EL i ops) /\ ^cut_fit (EL i ops)
Proof
  BETA_TAC >> strip_tac >>
  `LENGTH ops=LENGTH pat-c` by (
    qpat_assum `MAP _ _ = DROP _ _` (mp_tac o AP_TERM ``LENGTH:asm_inst list->num``) >>
    simp[]) >> simp[] >> rpt strip_tac
  >- (qpat_assum `MAP _ _ = DROP _ _` (mp_tac o AP_TERM ``EL (i:num):asm_inst list->asm_inst``) >>
      `i+c<LENGTH pat` by decide_tac >>
      simp[listTheory.EL_DROP, EL_MAP, EL_APPEND_EQN, ADD_COMM]) >>
  qpat_assum `EVERY _ ops` (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  metis_tac[EL_MEM]
QED

Theorem strict_shuffle_symbolic_mode[local]:
  !p. p = pre++pat++tail ==>
  !q. q = pre++repl++tail ==>
  !b. b = LENGTH pre ==>
  ^cut_families pat repl /\ asm_static_wf p /\ s.as_pc=0 /\
  sym_steps_mode allow_own p env own n (sym_init s) = SymOK ss /\
  e IN V /\ pc e=ss.sym_base.as_pc /\ b < pc e /\ pc e < b+LENGTH pat /\
  ^cut_just height tag boolean e ss.sym_stack /\ ^cut_hop p V rank pc height tag boolean edge ==>
  ?z j u ops path.
    ^strict_path V rank pc height edge path e z ops /\ LENGTH ops=b+LENGTH pat-pc e /\
    z IN V /\ pc z=b+LENGTH pat /\ rank z < rank e /\
    sym_steps_mode allow_own q env own j (sym_init s)=SymOK u /\
    u.sym_base.as_pc=splice_pc b (LENGTH pat) (LENGTH repl) (pc z) /\
    u.sym_base.as_call_ctx=ss.sym_base.as_call_ctx /\ u.sym_base.as_requests=ss.sym_base.as_requests /\
    ^cut_just height tag boolean z u.sym_stack
Proof
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH pre < ss.sym_base.as_pc /\ ss.sym_base.as_pc < LENGTH pre + LENGTH pat` by simp[] >>
  drule_all_then strip_assume_tac (BETA_RULE cut_family_stopped_mode) >>
  qabbrev_tac `c = ss.sym_base.as_pc - LENGTH (pre:asm_inst list)` >>
  `0 < c /\ c < LENGTH pat /\ pc e=LENGTH pre+c` by simp[Abbr `c`] >>
  drule_all_then strip_assume_tac (BETA_RULE cut_residual_visit_mode) >>
  drule_all_then strip_assume_tac (BETA_RULE cut_suffix_fetch) >>
  drule (BETA_RULE strict_shuffle_walk) >>
  disch_then (qspecl_then [`ops`,`e`,`ss.sym_stack`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  Q.SUBGOAL_THEN `^strict_path V rank pc height edge path e z ops /\ LENGTH ss.sym_stack = height e`
    (mp_tac o MATCH_MP (BETA_RULE strict_path_sizes) o BETA_RULE)
  >- (BETA_TAC >> asm_rewrite_tac[]) >> strip_tac >>
  qpat_assum `_ ==> ?out. sym_steps_mode allow_own _ _ _ _ _ = SymOK out /\ _` drule >> strip_tac >>
  qpat_assum `!tail. LENGTH ops = _ /\ _` (qspec_then `tail` strip_assume_tac) >>
  qexistsl [`z`,`j+LENGTH repl`,`out`,`ops`,`path`] >>
  `pc z=pc e+LENGTH ops /\ z IN V` by metis_tac[LESS_EQ_REFL] >>
  `pc z = LENGTH pre+LENGTH pat /\ ops <> []` by (Cases_on `ops` >> gvs[]) >>
  simp[sym_steps_mode_add, splice_pc_def]
QED

val cut_origin = ``\p l origin.
  EL origin p = AsmPushLabel l \/
  (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l``;

val cut_hit = ``\p l off dest.
  FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
  off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest``;

val cut_shape = ``
  \p cc req (pc:(num#num)->num) height need tag boolean x (t:asm_state).
  t.as_pc=pc x /\ LENGTH t.as_stack=height x /\ t.as_call_ctx=cc /\ t.as_requests=req /\
  (need x ==> t.as_call_ctx.cc_static) /\
  (!k l o'. tag x k=SOME(l,o') ==>
     k<height x /\ o'<LENGTH p /\ ^cut_origin p l o' /\
     ?off dest. ^cut_hit p l off dest /\ EL k t.as_stack=(n2w off:bytes32)) /\
  (!k. boolean x k ==> k<height x /\ (EL k t.as_stack=0w \/ EL k t.as_stack=1w))``;

val cut_slots = ``
  \p cc (height:(num#num)->num) need tag boolean x.
  (need x ==> cc.cc_static) /\
  (!k. boolean x k ==> k<height x /\ tag x k=NONE) /\
  (!k l o'. tag x k=SOME(l,o') ==>
     k<height x /\ o'<LENGTH p /\
     (EL o' p=AsmPushLabel l \/ EL o' p=AsmPushOfst l 0) /\
     ?off dest. ^cut_hit p l off dest)``;

(* The AsmOp projection below is sufficient for the residual walk.  Rows is
   kept whole at the public boundary so clients can use their actual table. *)
val cut_rows = ``
  \p cc (V:(num#num)->bool) (rank:(num#num)->num) pc height need tag boolean edge.
  (!x. x IN V ==> ^cut_slots p cc height need tag boolean x) /\
  (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\
   (!hi. hi = height x ==>
    !hj. hj = height y ==>
    !inherit. inherit = (\(src:num->num option) (fresh:num->(string#num)option) (bnew:num->bool).
      (!k l o'. tag y k=SOME(l,o') ==> k<hj /\
        (fresh k=SOME(l,o') \/ ?a. src k=SOME a /\ a<hi /\ tag x a=SOME(l,o'))) /\
      (!k. boolean y k ==> k<hj /\ (bnew k \/ ?a. src k=SOME a /\ a<hi /\ boolean x a))) ==>
    case EL (pc x) p of
      AsmLabel l => hj=hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj=hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
        (\k. k=0 /\ !t u. asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
                                (AsmPush bs) t = AsmOK u ==>
                          (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))
    | AsmPushLabel l => hj=hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
        (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmPushOfst l d => hj=hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
        (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmOp name => ^cut_op_flow p height tag boolean x y name
    | _ => F)) /\
  (!x. x IN V ==> pc x<LENGTH p /\
   (!h. h = height x ==>
    !arm. arm = (\P n. ?y. edge x y /\ P (pc y) /\ height y=n) ==>
    !legal. legal = (\P n. !y. edge x y ==> P (pc y) /\ height y=n) ==>
    !next. next = (\n. arm (\c. c=pc x+1) n /\ legal (\c. c=pc x+1) n) ==>
    case EL (pc x) p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
    | AsmOp name => ^cut_op_check p cc (pc x) h (tag x) arm legal (!y. ~edge x y) name
    | _ => F))``;

Theorem cut_rows_hop[local]:
  ^cut_rows p cc V rank pc height need tag boolean edge ==>
  ^cut_hop p V rank pc height tag boolean edge
Proof
  CONV_TAC (REDEPTH_CONV (FIRST_CONV [BETA_CONV, HO_REWR_CONV UNWIND_FORALL_THM2])) >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 (mk_asm "edges") (mk_asm "dispatch"))) >>
  MATCH_MP_TAC (BETA_RULE (REWRITE_RULE[LET_THM] strict_shuffle_hop)) >>
  BETA_TAC >> conj_tac
  >- (rpt gen_tac >> strip_tac >> asm "dispatch" (qspec_then `x` mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >> asm "edges" (qspecl_then [`x`,`y`] mp_tac) >> simp[]
QED

val cut_translate = ``\(f:num->num) (tag:(num#num)->num->(string#num)option) x k.
  OPTION_MAP (\(l,o'). (l,f o')) (tag x k)``;

Theorem cut_translate_just[local]:
  ^cut_just height tag boolean x stk ==> ^cut_just height (^cut_translate f tag) boolean x stk
Proof
  simp[optionTheory.OPTION_MAP_EQ_SOME] >> strip_tac >>
  rpt gen_tac >> disch_then (qx_choose_then `a` strip_assume_tac) >>
  PairCases_on `a` >> gvs[] >> metis_tac[]
QED

Theorem cut_endpoint_shape_mode[local]:
  (if allow_own then asm_sym_rel_own (lo_reloc q orig) q env own else asm_sym_rel q plain_env) t u /\
  (allow_own ==> asm_static_wf q) /\
  t.as_pc=pc x /\ t.as_call_ctx=cc /\ t.as_requests=req /\
  ^cut_just height tag boolean x u.sym_stack /\ ^cut_slots q cc height need tag boolean x ==>
  ^cut_shape q cc req pc height need tag boolean x t
Proof
  BETA_TAC >> disch_then (CONJUNCTS_THEN2 (mk_asm "rel") (map_every assume_tac o CONJUNCTS)) >>
  asm "rel" (strip_assume_tac o MATCH_MP protected_cut_relation_pc) >>
  asm "rel" (mk_asm "slots" o MATCH_MP protected_cut_relation_slots) >>
  simp[] >> conj_tac >- (
    rpt gen_tac >> disch_tac >>
    qpat_assum `!k l o'. tag x k=SOME(l,o') ==> k<height x /\ o'<LENGTH q /\ _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!k l o'. tag x k=SOME(l,o') ==> k<height x /\ EL k u.sym_stack=Lab l 0`
      (drule_then strip_assume_tac) >>
    `EL k t.as_stack = (n2w off:bytes32)` by (
      `k < LENGTH u.sym_stack` by simp[] >>
      asm "slots" (fn th =>
        qpat_assum `k < LENGTH u.sym_stack` (fn lt =>
          qspecl_then [`l`,`off`,`dest`] mp_tac
            (CONJUNCT2 (MATCH_MP (Q.SPEC `k:num` th) lt)))) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
    simp[] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!k. boolean x k ==> k<height x /\ (_=Val 0w \/ _=Val 1w)`
    (drule_then strip_assume_tac) >>
  `k < LENGTH u.sym_stack` by simp[] >>
  asm "slots" (fn th => qpat_assum `k < LENGTH u.sym_stack`
    (mp_tac o CONJUNCT1 o MATCH_MP (Q.SPEC `k:num` th))) >>
  simp[]
QED

(* The selected exit and the actual run do not depend on any destination
   table. Only the last Shape projection uses the destination's Slots. *)
Theorem stack_shuffle_strict_endpoint_mode:
  !p. p = pre++pat++tail ==>
  !q. q = pre++repl++tail ==>
  !b. b = LENGTH pre ==>
  !env. env = asm_data_env orig (assemble orig ++ data) ==>
  !f. f = splice_pc b (LENGTH pat) (LENGTH repl) ==>
  ^cut_families pat repl /\
  asm_static_wf orig /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  FILTER is_data_inst q = FILTER is_data_inst orig /\
  s.as_pc=0 /\ s.as_code=assemble orig ++ data /\
  sym_steps_mode allow_own p env s.as_code n (sym_init s)=SymOK ss /\
  (if allow_own then asm_sym_rel_own (lo_reloc p orig) p (asm_data_env orig s.as_code) s.as_code
   else asm_sym_rel p (asm_data_env p (assemble p ++ data))) t ss /\
  e IN V /\ pc e=ss.sym_base.as_pc /\ b<pc e /\ pc e<b+LENGTH pat /\
  ^cut_shape p cc req pc height need tag boolean e t /\
  ^cut_just height tag boolean e ss.sym_stack /\
  ^cut_rows p cc V rank pc height need tag boolean edge ==>
  ?z j u t' ops path.
    ^strict_path V rank pc height edge path e z ops /\ LENGTH ops=b+LENGTH pat-pc e /\
    z IN V /\ pc z=b+LENGTH pat /\ rank z<rank e /\
    sym_steps_mode allow_own q env s.as_code j (sym_init s)=SymOK u /\
    u.sym_base.as_pc=f (pc z) /\ LENGTH u.sym_stack=height z /\
    u.sym_base.as_call_ctx=cc /\ u.sym_base.as_requests=req /\
    ^cut_just height (^cut_translate f tag) boolean z u.sym_stack /\
    asm_steps (if allow_own then lo_reloc q orig else SND (compute_label_offsets q))
      (build_offset_to_pc q) q j (if allow_own then s else (s with as_code := assemble q ++ data)) = AsmOK t' /\
    (if allow_own then asm_sym_rel_own (lo_reloc q orig) q (asm_data_env orig s.as_code) s.as_code
     else asm_sym_rel q (asm_data_env q (assemble q ++ data))) t' u /\
    t'.as_pc=u.sym_base.as_pc /\ LENGTH t'.as_stack=LENGTH u.sym_stack /\
    t'.as_call_ctx=cc /\ t'.as_requests=req /\
    (^cut_slots q cc height need (^cut_translate f tag) boolean z ==>
     ^cut_shape q cc req (f o pc) height need (^cut_translate f tag) boolean z t')
Proof
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac cut_rows_hop >>
  rule_assum_tac BETA_RULE >> BETA_TAC >>
  qabbrev_tac `env = asm_data_env orig (assemble orig ++ data)` >>
  `?z j u ops path.
     ^strict_path V rank pc height edge path e z ops /\
     LENGTH ops=LENGTH pre+LENGTH pat-pc e /\
     z IN V /\ pc z=LENGTH pre+LENGTH pat /\ rank z<rank e /\
     sym_steps_mode allow_own (pre++repl++tail) env s.as_code j (sym_init s)=SymOK u /\
     u.sym_base.as_pc=splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) (pc z) /\
     u.sym_base.as_call_ctx=ss.sym_base.as_call_ctx /\
     u.sym_base.as_requests=ss.sym_base.as_requests /\
     ^cut_just height tag boolean z u.sym_stack` by (
    BETA_TAC >>
    irule (BETA_RULE (CONV_RULE (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) strict_shuffle_symbolic_mode)) >>
    qpat_x_assum `s.as_code = _` kall_tac >>
    asm_rewrite_tac[] >> qexists `n` >> asm_rewrite_tac[]) >>
  rule_assum_tac BETA_RULE >> unabbrev_all_tac >>
  drule_all_then (qx_choose_then `out` strip_assume_tac) stopped_symbolic_prefix_mode >>
  `^cut_just height (^cut_translate (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)) tag)
     boolean z u.sym_stack` by (
    BETA_TAC >> irule (BETA_RULE cut_translate_just) >> asm_rewrite_tac[]) >>
  `ss.sym_base.as_call_ctx=cc /\ ss.sym_base.as_requests=req` by (
    qpat_assum `(if allow_own then asm_sym_rel_own _ _ _ _ else asm_sym_rel _ _) t ss`
      (strip_assume_tac o MATCH_MP protected_cut_relation_context) >>
    qpat_assum `t.as_pc = pc e /\ _` (map_every assume_tac o CONJUNCTS) >>
    simp[]) >>
  qabbrev_tac `f = splice_pc (LENGTH (pre:asm_inst list)) (LENGTH pat) (LENGTH repl)` >>
  qabbrev_tac `tg = \x k. OPTION_MAP (\(l,o'). (l,f o')) (tag x k)` >>
  rule_assum_tac BETA_RULE >>
  `^cut_slots (pre++repl++tail) cc height need tg boolean z ==>
   ^cut_shape (pre++repl++tail) cc req (f o pc) height need tg boolean z out` by (
    (BETA_TAC >> disch_tac >>
     `^cut_just height tg boolean z u.sym_stack` by
       (qpat_assum `Abbrev (tg = _)`
          (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        BETA_TAC >> first_assum ACCEPT_TAC) >>
     pop_assum (assume_tac o BETA_RULE) >>
     `out.as_pc = (f o pc) z /\ out.as_call_ctx = cc /\ out.as_requests = req` by
       simp[combinTheory.o_THM] >>
     pop_assum (map_every assume_tac o CONJUNCTS) >>
     `allow_own ==> asm_static_wf (pre++repl++tail)` by
       (strip_tac >> first_assum ACCEPT_TAC) >>
     mp_tac (BETA_RULE (Q.INST [`q` |-> `pre++repl++tail`,
       `env` |-> `asm_data_env orig s.as_code`, `own` |-> `s.as_code`,
       `plain_env` |-> `asm_data_env (pre++repl++tail) (assemble (pre++repl++tail) ++ data)`,
       `t` |-> `out`, `x` |-> `z`, `pc` |-> `f o pc`, `tag` |-> `tg`]
       cut_endpoint_shape_mode)) >>
     (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
     disch_then ACCEPT_TAC)) >>
  qexistsl [`z`,`j`,`u`,`out`,`ops`,`path`] >>
  BETA_TAC >> rule_assum_tac BETA_RULE >>
  asm_rewrite_tac[] >>
  qpat_assum `Abbrev (tg = _)`
    (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  BETA_TAC >>
  qpat_assum `LENGTH u.sym_stack = height z /\
              (!k l o'. OPTION_MAP _ (tag z k) = SOME (l,o') ==> _) /\ _`
    (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)
QED


Theorem stack_shuffle_strict_endpoint:
  !p. p = pre++pat++tail ==>
  !q. q = pre++repl++tail ==>
  !b. b = LENGTH pre ==>
  !env. env = asm_data_env orig (assemble orig ++ data) ==>
  !f. f = splice_pc b (LENGTH pat) (LENGTH repl) ==>
  ^cut_families pat repl /\
  asm_static_wf orig /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  FILTER is_data_inst q = FILTER is_data_inst orig /\
  s.as_pc=0 /\ s.as_code=assemble orig ++ data /\
  sym_steps p env n (sym_init s)=SymOK ss /\
  asm_sym_rel p (asm_data_env p (assemble p ++ data)) t ss /\
  e IN V /\ pc e=ss.sym_base.as_pc /\ b<pc e /\ pc e<b+LENGTH pat /\
  ^cut_shape p cc req pc height need tag boolean e t /\
  ^cut_just height tag boolean e ss.sym_stack /\
  ^cut_rows p cc V rank pc height need tag boolean edge ==>
  ?z j u t' ops path.
    ^strict_path V rank pc height edge path e z ops /\ LENGTH ops=b+LENGTH pat-pc e /\
    z IN V /\ pc z=b+LENGTH pat /\ rank z<rank e /\
    sym_steps q env j (sym_init s)=SymOK u /\
    u.sym_base.as_pc=f (pc z) /\ LENGTH u.sym_stack=height z /\
    u.sym_base.as_call_ctx=cc /\ u.sym_base.as_requests=req /\
    ^cut_just height (^cut_translate f tag) boolean z u.sym_stack /\
    asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q j
      (s with as_code := assemble q ++ data) = AsmOK t' /\
    asm_sym_rel q (asm_data_env q (assemble q ++ data)) t' u /\
    t'.as_pc=u.sym_base.as_pc /\ LENGTH t'.as_stack=LENGTH u.sym_stack /\
    t'.as_call_ctx=cc /\ t'.as_requests=req /\
    (^cut_slots q cc height need (^cut_translate f tag) boolean z ==>
     ^cut_shape q cc req (f o pc) height need (^cut_translate f tag) boolean z t')
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`]
    stack_shuffle_strict_endpoint_mode |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
