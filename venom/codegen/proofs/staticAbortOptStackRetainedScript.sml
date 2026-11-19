Theory staticAbortOptStackRetained
Ancestors
  staticAbortStraight stackOpAsmSim asmSem asmIR asmOptimizer
  alist arithmetic finite_map list option pair words

(* A retained instruction keeps its incoming interface. Each outgoing port
   may keep fewer demands, but only at the very same output slots. *)
Theorem stack_splice_retained_arms:
  !Inherit. Inherit = (\hi hj (tx:num->(string#num)option) ty bx by
              (src:num->num option) (fresh:num->(string#num)option) bnew.
    (!k l o'. ty k = SOME(l,o') ==>
       k < hj /\ (fresh k = SOME(l,o') \/
         ?a. src k = SOME a /\ a < hi /\ tx a = SOME(l,o'))) /\
    (!k. by k ==> k < hj /\
       (bnew k \/ ?a. src k = SOME a /\ a < hi /\ bx a))) ==>
  !Flow. Flow = (\p i ins hi hj tx ty bx by.
    !inherit. inherit = Inherit hi hj tx ty bx by ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
    | AsmPushLabel l =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,i) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,i) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
             !a. a = asm_op_arity name ==>
             !m. m = hj + a - hi ==>
             a <= hi /\ hj = m+(hi-a) /\
             ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
             inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
               (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                 !t u. LENGTH t.as_stack=hi /\
                   asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                     ins t = AsmOK u ==>
                   (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !Canon. Canon = (\p l j. ?off. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
                off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME j) ==>
  !Slots. Slots = (\p cc height need tag boolean (x:num#num).
    (need x ==> cc.cc_static) /\
    (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
    (!k l i. tag x k = SOME(l,i) ==>
      k < height x /\ i < LENGTH p /\
      (EL i p = AsmPushLabel l \/ EL i p = AsmPushOfst l 0) /\ ?j. Canon p l j)) ==>
  !Role. Role = (\p cc pc height tag edge (x:num#num).
    !h. h = height x ==>
    !fall. fall = (\y. pc y = pc x + 1) ==>
    !target. target = (\y. ?l i. tag x 0 = SOME(l,i) /\ Canon p l (pc y)) ==>
    !arm. arm = (\A n. ?y. edge x y /\ A y /\ height y = n) ==>
    !legal. legal = (\A n. !y. edge x y ==> A y /\ height y = n) ==>
    !next. next = (\n. arm fall n /\ legal fall n) ==>
    !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
    !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
    case EL (pc x) p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmOp name =>
        if name="INVALID" then stop 0
        else if name="REVERT" then stop 2
        else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
             then cc.cc_static /\ stop (asm_op_arity name)
        else
          (case ALOOKUP dup_table name of
             SOME n => n<h /\ next (h+1)
           | NONE => case ALOOKUP swap_table name of
               SOME n => 0<n /\ n<h /\ next h
             | NONE =>
                 if name="JUMP" then
                    1<=h /\ arm target (h-1) /\ legal target (h-1)
                 else if name="JUMPI" then
                    2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm target (h-2) /\
                    legal (\y. fall y \/ target y) (h-2)
                 else
                    ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                        untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F) ==>
  !p q cc f pc height rank need tag boolean edge x P H R N Tag Bool E c g.
    !ins. ins = EL (pc x) p ==>
    P c = f (pc x) /\ P c < LENGTH q /\ EL (P c) q = ins /\
    H c = height x /\ R c = rank x /\ N c = need x /\ Bool c = boolean x /\
    (!k. Tag c k = OPTION_MAP (\(l,i). (l,f i)) (tag x k)) /\
    (!z. E c z <=> ?y. edge x y /\ z = g y) /\
    (!y. edge x y ==>
      rank y < rank x /\ Flow p (pc x) ins (height x) (height y)
                             (tag x) (tag y) (boolean x) (boolean y) /\
      Slots p cc height need tag boolean y /\
      P (g y) = f (pc y) /\ H (g y) = height y /\ R (g y) <= rank y /\
      (N (g y) ==> cc.cc_static) /\
      (!k l j. Tag (g y) k = SOME(l,j) ==>
         ?i. tag y k = SOME(l,i) /\ j = f i) /\
      (!k. Bool (g y) k ==> boolean y k)) /\
    (!y. edge x y /\ pc y = pc x + 1 ==> f (pc y) = f (pc x) + 1) /\
    (!l i. Canon p l i ==> Canon q l (f i)) /\
    (!l. IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) ==>
         IS_SOME (FLOOKUP (SND(compute_label_offsets q)) l)) /\
    (!l i. i < LENGTH p /\ (EL i p = AsmPushLabel l \/ EL i p = AsmPushOfst l 0) ==>
       f i < LENGTH q /\ EL (f i) q = EL i p) /\
    Slots p cc height need tag boolean x /\ Role p cc pc height tag edge x ==>
    P c < LENGTH q /\ Slots q cc H N Tag Bool c /\ Role q cc P H Tag E c /\
    !z. E c z ==> R z < R c /\ Slots q cc H N Tag Bool z /\
                  Flow q (P c) (EL (P c) q) (H c) (H z) (Tag c) (Tag z) (Bool c) (Bool z)
Proof
  map_every (fn name => qx_gen_tac name >>
    disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`Inherit`, `Flow`, `Canon`, `Slots`, `Role`] >>
  `!p q i f ins hi hj tx ty bx by ty' by'.
      (!k l j. ty' k = SOME(l,j) ==> ?o'. ty k = SOME(l,o') /\ j = f o') /\
      (!k. by' k ==> by k) /\ Flow p i ins hi hj tx ty bx by ==>
      Flow q (f i) ins hi hj (\k. OPTION_MAP (\(l,j). (l,f j)) (tx k)) ty' bx by'`
    by suspend "flow" >>
  ntac 21 gen_tac >>
  qx_gen_tac `ins` >>
  disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qabbrev_tac `tr = \(l:string,i:num). (l,f i)` >>
  strip_tac >>
  `!y z. H z = height y /\ (N z ==> cc.cc_static) /\ Slots p cc height need tag boolean y /\
         (!k l j. Tag z k = SOME(l,j) ==> ?i. tag y k = SOME(l,i) /\ j = f i) /\
         (!k. Bool z k ==> boolean y k) ==> Slots q cc H N Tag Bool z`
    by suspend "slot_transfer" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "source_slots" >>
  conj_tac >- suspend "role" >>
  suspend "edges"
QED

Resume stack_splice_retained_arms[flow]:
  rpt gen_tac >> strip_tac >>
  `!src fresh fresh' bnew bnew'. Inherit hi hj tx ty bx by src fresh bnew /\
       (!k. fresh' k = OPTION_MAP (\(l,j). (l,f j)) (fresh k)) /\
       (!k. bnew k ==> bnew' k) ==>
     Inherit hi hj (\k. OPTION_MAP (\(l,j). (l,f j)) (tx k)) ty' bx by' src fresh' bnew'` by
    suspend "inherit" >>
  pop_assum (mk_asm "inherit") >>
  qpat_x_assum `Flow p i ins hi hj tx ty bx by` mp_tac >>
  simp_tac bool_ss [Abbr `Flow`, UNWIND_FORALL_THM2] >>
  Cases_on `ins` >> simp_tac bool_ss [asm_inst_case_def] >>
  TRY (qmatch_goalsub_rename_tac `ALOOKUP dup_table name` >>
       Cases_on `ALOOKUP dup_table name` >> simp_tac bool_ss [option_case_def] >>
       TRY (Cases_on `ALOOKUP swap_table name` >> simp_tac bool_ss [option_case_def])) >>
  strip_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (* The final two arguments of the goal are the new fresh-tag and
     Boolean predicates. The source Inherit fact fixes the other ports. *)
  goal_term (fn g =>
    asm "inherit" (fn th => pop_assum
      (mp_then Any (mp_tac o BETA_RULE o SPECL [rand (rator g), rand g]) th))) >>
  (impl_tac >- (simp[asm_step_push_ok, COND_RAND] >> suspend "op_boolean")) >>
  simp[]
QED

Resume stack_splice_retained_arms[inherit]:
  simp_tac bool_ss [Abbr `Inherit`] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!k l j. ty' k = SOME(l,j) ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!k l j. ty k = SOME(l,j) ==> _` (drule_then strip_assume_tac) >>
      simp[] >> metis_tac[OPTION_MAP_DEF]) >>
  metis_tac[]
QED

Resume stack_splice_retained_arms[op_boolean]:
  rpt strip_tac >>
  `name <> "JUMP" /\ name <> "JUMPI"` by
    (qpat_assum `_ \/ _ ==> hj + asm_op_arity name - hi = 0` mp_tac >> simp[]) >>
  `asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) (AsmOp name) t =
   asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q) (AsmOp name) t` by
    (pure_rewrite_tac [asm_step_def, asm_inst_case_def, asm_step_op_def, asm_step_control_def] >>
     simp[]) >>
  qpat_assum `!t u. LENGTH t.as_stack = hi /\ _ ==> _`
    (qspecl_then [`t`,`u`] mp_tac) >> simp[]
QED

Resume stack_splice_retained_arms[slot_transfer]:
  simp[Abbr `Slots`] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `boolean y k` by metis_tac[] >>
      `k < height y /\ tag y k = NONE` by metis_tac[] >>
      Cases_on `Tag z k` >> simp[] >>
      rename1 `Tag z k = SOME a` >> PairCases_on `a` >>
      qpat_assum `!k l j. Tag z k = SOME(l,j) ==> _` (drule_then mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!k l j. Tag z k = SOME(l,j) ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!k l i. tag y k = SOME(l,i) ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!l i. i < LENGTH p /\ _ ==> _` (qspecl_then [`l`,`i`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >> metis_tac[]
QED

Resume stack_splice_retained_arms[source_slots]:
  `N c ==> cc.cc_static` by
    (qpat_assum `Slots p cc height need tag boolean x` mp_tac >>
     simp_tac bool_ss [Abbr `Slots`] >> strip_tac >> simp[]) >>
  qpat_assum `!y z. H z = height y /\ _ ==> Slots q cc H N Tag Bool z`
    (qspecl_then [`x`,`c`] mp_tac) >>
  simp[Abbr `tr`, pairTheory.EXISTS_PROD]
QED

Resume stack_splice_retained_arms[role]:
  `!y. edge x y ==> E c (g y) /\ H (g y) = height y /\
    (pc y = pc x + 1 ==> P (g y) = P c + 1) /\
    ((?l i. tag x 0 = SOME(l,i) /\ Canon p l (pc y)) ==>
     (?l i. Tag c 0 = SOME(l,i) /\ Canon q l (P (g y))))` by
    suspend "role_ports" >>
  `!k. Tag c k = NONE <=> tag x k = NONE` by simp[] >>
  `EL (pc x) p = ins` by simp[Abbr `ins`] >>
  Cases_on `ins = AsmOp "JUMPI"` >- suspend "role_jumpi" >>
  qpat_x_assum `Role p cc pc height tag edge x` mp_tac >>
  simp_tac bool_ss [Abbr `Role`, UNWIND_FORALL_THM2] >>
  qpat_x_assum `!y. edge x y ==> rank y < rank x /\ _` kall_tac >>
  rpt (qpat_x_assum `!k. Tag c k = OPTION_MAP tr (tag x k)` kall_tac ORELSE
       qpat_x_assum `!l i. Canon p l i ==> Canon q l (f i)` kall_tac ORELSE
       qpat_x_assum `!y. edge x y /\ pc y = pc x + 1 ==> _` kall_tac) >>
  rpt (qpat_x_assum `Abbrev (Slots = _)` kall_tac ORELSE
       qpat_x_assum `Abbrev (Flow = _)` kall_tac ORELSE
       qpat_x_assum `Abbrev (Inherit = _)` kall_tac ORELSE
       qpat_x_assum `Slots p cc height need tag boolean x` kall_tac ORELSE
       qpat_x_assum `!y z. H z = height y /\ _ ==> Slots q cc H N Tag Bool z` kall_tac ORELSE
       qpat_x_assum `!p q i f ins hi hj tx ty bx by ty' by'. _ ==> Flow q _ _ _ _ _ _ _ _` kall_tac) >>
  Cases_on `ins` >>
  simp[IgnAsm `!z. E c z <=> _`, IgnAsm `!k. Tag c k = OPTION_MAP _ _`,
       IgnAsm `P c = f (pc x)`] >>
  suspend "role_dispatch"
QED

Resume stack_splice_retained_arms[role_jumpi]:
  qabbrev_tac `F0 = \u. pc u = pc x + 1` >>
  qabbrev_tac `F1 = \z. P z = P c + 1` >>
  qabbrev_tac `T0 = \u. ?l i. tag x 0 = SOME(l,i) /\ Canon p l (pc u)` >>
  qabbrev_tac `T1 = \z. ?l i. Tag c 0 = SOME(l,i) /\ Canon q l (P z)` >>
  `!u. edge x u ==> E c (g u) /\ H (g u) = height u /\
    (F0 u ==> F1 (g u)) /\ (T0 u ==> T1 (g u))` by
    (simp_tac bool_ss [Abbr `F0`, Abbr `F1`, Abbr `T0`, Abbr `T1`] >>
     first_assum ACCEPT_TAC) >>
  `!A B. (!u. edge x u /\ A u ==> B (g u)) ==>
     (((?u. edge x u /\ A u /\ height u = height x - 2) ==>
        (?z. E c z /\ B z /\ H z = height x - 2)) /\
      ((!u. edge x u ==> A u /\ height u = height x - 2) ==>
        (!z. E c z ==> B z /\ H z = height x - 2)))` by
    suspend "jumpi_arms" >>
  `((?u. edge x u /\ F0 u /\ height u = height x - 2) ==>
    (?z. E c z /\ F1 z /\ H z = height x - 2)) /\
   ((?u. edge x u /\ T0 u /\ height u = height x - 2) ==>
    (?z. E c z /\ T1 z /\ H z = height x - 2)) /\
   ((!u. edge x u ==> (F0 u \/ T0 u) /\ height u = height x - 2) ==>
    (!z. E c z ==> (F1 z \/ T1 z) /\ H z = height x - 2))` by
    suspend "jumpi_use_arms" >>
  qpat_x_assum `!z. E c z <=> _` kall_tac >>
  qpat_x_assum `!k. Tag c k = OPTION_MAP _ _` kall_tac >>
  qpat_x_assum `Role p cc pc height tag edge x` mp_tac >>
  simp_tac bool_ss [Abbr `Role`, UNWIND_FORALL_THM2] >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac [th]))
    [`EL (pc x) p = ins`, `EL (P c) q = ins`, `ins = AsmOp "JUMPI"`,
     `H c = height x`, `!k. Tag c k = NONE <=> tag x k = NONE`] >>
  simp_tac (srw_ss()) [asm_inst_case_def, option_case_def, MEM,
    EVAL ``ALOOKUP dup_table "JUMPI"``, EVAL ``ALOOKUP swap_table "JUMPI"``] >>
  qpat_x_assum `(?u. edge x u /\ F0 u /\ _) ==> _` mp_tac >>
  qpat_x_assum `(?u. edge x u /\ T0 u /\ _) ==> _` mp_tac >>
  qpat_x_assum `(!u. edge x u ==> (F0 u \/ T0 u) /\ _) ==> _` mp_tac >>
  simp_tac bool_ss [Abbr `F0`, Abbr `F1`, Abbr `T0`, Abbr `T1`] >>
  tautLib.TAUT_TAC
QED

Resume stack_splice_retained_arms[jumpi_arms]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >> qexists `g u` >>
      qpat_assum `!v. edge x v ==> E c (g v) /\ H (g v) = height v /\ _`
        (qspec_then `u` mp_tac) >> simp[]) >>
  strip_tac >> gen_tac >> disch_tac >>
  qpat_assum `!z. E c z <=> _` (qspec_then `z` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v. edge x v ==> E c (g v) /\ H (g v) = height v /\ _`
    (qspec_then `y` mp_tac) >>
  qpat_assum `!v. edge x v ==> A v /\ _` (qspec_then `y` mp_tac) >>
  simp[]
QED

Resume stack_splice_retained_arms[jumpi_use_arms]:
  rpt conj_tac
  >- (qpat_assum `!A B. _` (qspecl_then [`F0`,`F1`] mp_tac) >>
      (impl_tac >- suspend "jumpi_map") >> tautLib.TAUT_TAC)
  >- (qpat_assum `!A B. _` (qspecl_then [`T0`,`T1`] mp_tac) >>
      (impl_tac >- suspend "jumpi_map") >> tautLib.TAUT_TAC) >>
  qpat_assum `!A B. _`
    (qspecl_then [`\u. F0 u \/ T0 u`,`\z. F1 z \/ T1 z`] mp_tac) >>
  BETA_TAC >> (impl_tac >- suspend "jumpi_map") >> tautLib.TAUT_TAC
QED

Resume stack_splice_retained_arms[jumpi_map]:
  markerLib.RESUME_TAC >> gen_tac >>
  qpat_assum `!v. edge x v ==> E c (g v) /\ H (g v) = height v /\ _`
    (qspec_then `u` mp_tac) >> tautLib.TAUT_TAC
QED

Resume stack_splice_retained_arms[role_ports]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!y. edge x y ==> rank y < rank x /\ _` (drule_then strip_assume_tac) >>
  conj_tac >- (simp[] >> qexists `y` >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- (strip_tac >> simp[]) >>
  strip_tac >> qexistsl [`l`,`f i`] >> simp[Abbr `tr`]
QED

Resume stack_splice_retained_arms[role_dispatch]:
  markerLib.RESUME_TAC >>
  TRY (qmatch_asmsub_rename_tac `EL (pc x) p = AsmOp name` >>
       Cases_on `ALOOKUP dup_table name` >> gvs[IgnAsm `!z. E c z <=> _`] >>
       Cases_on `ALOOKUP swap_table name` >> gvs[IgnAsm `!z. E c z <=> _`] >>
       rpt IF_CASES_TAC) >>
  simp[] >> rpt strip_tac >>
  TRY (rename1 `static_abort_straight _ m` >> qexists `m` >> rpt strip_tac) >>
  TRY (qmatch_goalsub_rename_tac `?z. _ /\ (?l i. Tag c 0 = SOME(l,i) /\ Canon q l (P z)) /\ _` >>
       rename1 `Canon p _ (pc yt)` >> qexists `g yt`) >>
  TRY (rename1 `edge x y` >> qexists `g y`) >>
  gvs[] >>
  TRY (qmatch_goalsub_rename_tac `P (g u)` >>
       qpat_assum `!y. edge x y ==> _ /\ H (g y) = _ /\ _`
         (qspec_then `u` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Resume stack_splice_retained_arms[edges]:
  gen_tac >> disch_tac >>
  qpat_assum `!z. E c z <=> _` (qspec_then `z` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `!y. edge x y ==> rank y < rank x /\ _` (drule_then strip_assume_tac) >>
  conj_tac >- (simp[] >> irule ratTheory.RAT_LEQ_LES_TRANS >>
               qexists `rank y` >> simp[]) >>
  conj_tac
  >- (qpat_assum `!y z. H z = height y /\ _ ==> Slots q cc H N Tag Bool z`
        (qspecl_then [`y`,`g y`] mp_tac) >> simp[]) >>
  `Tag c = (\k. OPTION_MAP tr (tag x k))` by simp[FUN_EQ_THM] >>
  simp[] >> simp_tac bool_ss [Abbr `tr`] >>
  qpat_assum `!p q i f ins hi hj tx ty bx by ty' by'. _ ==> Flow q _ _ _ _ _ _ _ _`
    irule >>
  qexistsl [`boolean y`, `p`, `tag y`] >> simp[]
QED

Finalise stack_splice_retained_arms
