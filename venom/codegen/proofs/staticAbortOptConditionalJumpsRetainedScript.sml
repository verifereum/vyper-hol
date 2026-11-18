Theory staticAbortOptConditionalJumpsRetained
Ancestors
  asmSplice asmOptimizer staticAbortStraight stackOpAsmSim asmSem
  asmIR alist arithmetic finite_map list option pair words

Theorem conditional_jump_retained_row:
  !p q b i cc h tx bx (edge:(num#num)->bool) pc height tag boolean.
  let r = splice_pc b 4 3 in
  let C = \p l d. ?off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME d in
  let Target = \p tx j. ?l origin. tx 0 = SOME(l,origin) /\ C p l j in
  let arm = \P n. ?y. edge y /\ P y /\ height y = n in
  let legal = \P n. !y. edge y ==> P y /\ height y = n in
  let Row = \p i tx pc.
    let fall = \y. pc y = i+1 in
    let taken = \y. Target p tx (pc y) in
    let next = \n. arm fall n /\ legal fall n in
    let untagged = \a. !k. k<a ==> tx k=NONE in
    let stop = \a. a<=h /\ untagged a /\ !y. ~edge y in
    case EL i p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
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
                 if name="JUMP" then 1<=h /\ arm taken (h-1) /\ legal taken (h-1)
                 else if name="JUMPI" then
                   2<=h /\ tx 1=NONE /\ arm fall (h-2) /\ arm taken (h-2) /\
                   legal (\y. fall y \/ taken y) (h-2)
                 else
                   ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                       untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F in
  let Inherit = \tx ty bx by' hj src fresh bnew.
    (!k l origin. ty k = SOME(l,origin) ==>
       k < hj /\ (fresh k = SOME(l,origin) \/
       ?a. src k = SOME a /\ a < h /\ tx a = SOME(l,origin))) /\
    (!k. by' k ==> k < hj /\ (bnew k \/ ?a. src k = SOME a /\ a < h /\ bx a)) in
  let Flow = \p i tx ty by' hj.
    let ins = EL i p in
    let inherit = Inherit tx ty bx by' hj in
    case ins of
      AsmLabel l => hj=h /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj=h+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !s u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) s = AsmOK u ==> (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))
    | AsmPushLabel l => hj=h+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,i) else NONE) (\k. F)
    | AsmPushOfst l d => hj=h+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,i) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n<h /\ hj=h+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<h /\ hj=h /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
               let a = asm_op_arity name; m = hj + asm_op_arity name - h in
               a<=h /\ hj=m+(h-a) /\ ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !s u. LENGTH s.as_stack=h /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins s = AsmOK u ==> (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F in
  let Legal = \p i tx j.
    if EL i p = AsmOp "JUMP" then Target p tx j
    else if EL i p = AsmOp "JUMPI" then j=i+1 \/ Target p tx j
    else j=i+1 in
  (i<b \/ b+4<=i) /\ r i < LENGTH q /\ EL (r i) q = EL i p /\
  (!l j. C p l j ==> (j<b \/ b+4<=j) /\ C q l (r j)) /\
  (!l. IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) ==>
       IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l)) /\
  Row p i tx pc /\
  (!y. edge y ==> Flow p i tx (tag y) (boolean y) (height y) /\ Legal p i tx (pc y)) ==>
  (!y. edge y ==> pc y<=b \/ b+4<=pc y) /\
  !rho raw boolQ.
    let tr = OPTION_MAP (\(l,j). (l,rho l j)) in
    (!l. EL i p = AsmPushLabel l \/ EL i p = AsmPushOfst l 0 ==> rho l i = r i) /\
    (!y k l j. edge y /\ raw y k = SOME(l,j) ==> tag y k = SOME(l,j)) /\
    (!y k. edge y /\ boolQ y k ==> boolean y k) ==>
    r i < LENGTH q /\ EL (r i) q = EL i p /\
    Row q (r i) (tr o tx) (r o pc) /\
    (!y. edge y ==>
       (pc y=i+1 ==> r (pc y)=r i+1) /\
       (Target p tx (pc y) ==> Target q (tr o tx) (r (pc y))) /\
       Legal q (r i) (tr o tx) (r (pc y)) /\
       Flow q (r i) (tr o tx) (tr o raw y) (boolQ y) (height y) /\
       (!k l. raw y k = SOME(l,b) ==> ?a. a < h /\ tx a = SOME(l,b)))
Proof
  rpt gen_tac >>
  map_every (fn p => qmatch_goalsub_abbrev_tac p >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ r`,`LET _ C`,`LET _ Target`,`LET _ arm`,`LET _ legal`,`LET _ Row`,
     `LET _ Inherit`,`LET _ Flow`,`LET _ Legal`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!j. j=i+1 ==> (j<=b \/ b+4<=j) /\ r j=r i+1` by
    (qunabbrev_tac `r` >> metis_tac[splice_pc_next, DECIDE ``0 < (4:num)``]) >>
  conj_tac >- suspend "successors" >>
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `LET _ tr` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >> strip_tac >>
  `!j. Target p tx j ==> Target q (tr o tx) (r j)` by
    (simp[Abbr `Target`, Abbr `tr`, combinTheory.o_THM] >> rpt strip_tac >>
     rename1 `tx 0 = SOME(l,origin)` >> qexistsl [`l`,`rho' l origin`] >>
     simp[] >> qpat_assum `!l j. C p l j ==> _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "row" >>
  gen_tac >> disch_tac >>
  qpat_assum `!y. edge y ==> Flow _ _ _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  conj_tac >- simp[] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >-
    (qpat_x_assum `Legal p i tx (pc y)` mp_tac >> simp[Abbr `Legal`] >>
     Cases_on `EL i p = AsmOp "JUMP"` >> simp[] >>
     Cases_on `EL i p = AsmOp "JUMPI"` >> simp[] >> metis_tac[]) >>
  suspend "flow"
QED

Resume conditional_jump_retained_row[successors]:
  rpt strip_tac >>
  qpat_assum `!y. edge y ==> Flow _ _ _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  qpat_x_assum `Legal _ _ _ _` mp_tac >>
  simp[Abbr `Legal`,Abbr `Target`] >>
  Cases_on `EL i p = AsmOp "JUMP"` >> simp[] >>
  Cases_on `EL i p = AsmOp "JUMPI"` >> simp[] >> metis_tac[LESS_IMP_LESS_OR_EQ]
QED

Resume conditional_jump_retained_row[row]:
  `!P Q. (!y. P y ==> Q y) ==> !n.
       (arm P n ==> arm Q n) /\ (legal P n ==> legal Q n)` by
    (simp[Abbr `arm`, Abbr `legal`] >> metis_tac[]) >>
  `tr NONE = NONE` by simp[Abbr `tr`] >>
  qmatch_goalsub_abbrev_tac `Row _ _ txQ pcQ` >>
  `!y. pc y = i+1 ==> pcQ y = r i+1` by simp[Abbr `pcQ`,combinTheory.o_THM] >>
  `!y. Target p tx (pc y) ==> Target q txQ (pcQ y)` by
    simp[Abbr `pcQ`, Abbr `txQ`,combinTheory.o_THM] >>
  `!y. pc y=i+1 \/ Target p tx (pc y) ==>
       pcQ y=r i+1 \/ Target q txQ (pcQ y)` by metis_tac[] >>
  qpat_x_assum `!P Q. _ ==> !n. _` (fn th =>
    map_every (fn (P,Q) => qspecl_then [P,Q] (mp_tac o BETA_RULE) th >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      simp[FORALL_AND_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS))
      [(`\y. pc y=i+1`,`\y. pcQ y=r i+1`),
       (`\y. Target p tx (pc y)`,`\y. Target q txQ (pcQ y)`),
       (`\y. pc y=i+1 \/ Target p tx (pc y)`,
        `\y. pcQ y=r i+1 \/ Target q txQ (pcQ y)`)]) >>
  qpat_x_assum `Row p i tx pc` mp_tac >> simp[Abbr `Row`] >>
  Cases_on `EL i p` >> simp[] >>
  TRY (rename1 `AsmOp name` >>
       Cases_on `ALOOKUP dup_table name` >> simp[] >>
       TRY (Cases_on `ALOOKUP swap_table name` >> simp[]) >>
       rpt (COND_CASES_TAC >> simp[])) >>
  rpt strip_tac >>
  fs[Abbr `txQ`,combinTheory.o_THM] >>
  qmatch_asmsub_rename_tac `static_abort_straight name out` >>
  TRY (qexists `out` >>
       `h + out - asm_op_arity name = h - asm_op_arity name + out` by decide_tac >>
       pop_assum SUBST1_TAC >> rpt conj_tac >>
       (first_assum ACCEPT_TAC ORELSE (first_assum irule >> first_assum ACCEPT_TAC)) >> NO_TAC) >>
  gvs[]
QED

Resume conditional_jump_retained_row[flow]:
  `i <> b` by decide_tac >>
  `!k l j. raw y k = SOME(l,j) ==> tag y k = SOME(l,j)` by metis_tac[] >>
  `!k. boolQ y k ==> boolean y k` by metis_tac[] >>
  `!src fresh bnew fq bnewQ.
      Inherit tx (tag y) bx (boolean y) (height y) src fresh bnew ==>
      (!k. fq k = tr (fresh k)) /\ (!k. bnew k ==> bnewQ k) /\
      (!k l. fresh k <> SOME(l,b)) ==>
      Inherit (tr o tx) (tr o raw y) bx (boolQ y) (height y) src fq bnewQ /\
      (!k l. raw y k = SOME(l,b) ==> ?a. a < h /\ tx a = SOME(l,b))` by
    (qunabbrev_tac `Inherit` >> qunabbrev_tac `tr` >> BETA_TAC >>
     pure_rewrite_tac[combinTheory.o_THM] >>
     rpt gen_tac >> rpt (disch_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
     conj_tac >-
       (conj_tac >-
         (rpt gen_tac >> Cases_on `raw y k` >> simp[] >>
          rename1 `raw y k = SOME v` >> PairCases_on `v` >> simp[] >>
          disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
          qpat_assum `!k l j. raw y k = _ ==> _` (drule_then assume_tac) >>
          qpat_assum `!k l j. tag y k = _ ==> _` (drule_then strip_assume_tac) >-
            simp[] >>
          rename1 `src k = SOME a` >> simp[] >>
          disj2_tac >> qexists `a` >> simp[]) >>
        rpt strip_tac >> qpat_assum `!k. boolQ y k ==> _` (drule_then assume_tac) >>
        qpat_assum `!k. boolean y k ==> _` (drule_then strip_assume_tac) >>
        simp[] >> metis_tac[]) >>
     rpt strip_tac >>
     qpat_assum `!k l j. raw y k = _ ==> _` (drule_then assume_tac) >>
     qpat_assum `!k l j. tag y k = _ ==> _` (drule_then strip_assume_tac) >>
     metis_tac[]) >>
  pop_assum (mk_asm "transfer") >>
  qpat_x_assum `!y. edge y ==> Flow p i _ _ _ _ /\ _` kall_tac >>
  qpat_x_assum `Flow p i _ _ _ _` mp_tac >>
  qunabbrev_tac `Flow` >>
  Cases_on `EL i p` >>
  TRY (rename1 `EL i p = AsmOp name` >>
       Cases_on `ALOOKUP dup_table name` >>
       TRY (qpat_assum `ALOOKUP dup_table name = NONE` (K all_tac) >>
            Cases_on `ALOOKUP swap_table name`)) >>
  ASM_SIMP_TAC (bool_ss ++ boolSimps.LET_ss)
    [asm_inst_case_def, option_case_def, GSYM CONJ_ASSOC] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  TRY (qpat_assum `F` CONTR_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >-
    (qpat_assum `Inherit tx (tag y) bx (boolean y) (height y) _ _ _`
       (fn old => asm "transfer" (fn transfer => MATCH_MP_TAC (MATCH_MP transfer old))) >>
     simp[Abbr `tr`] >> rpt strip_tac >>
     `name <> "JUMP" /\ name <> "JUMPI"` by
       (conj_tac >> strip_tac >> fs[asm_returns_zero_or_one_def]) >>
     rename1 `asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
                      (AsmOp name) st = AsmOK u` >>
     `asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
               (AsmOp name) st = AsmOK u` by
       (qpat_x_assum `asm_step (SND (compute_label_offsets q)) _ _ _ = _` mp_tac >>
        simp[asm_step_def, asm_step_op_def, asm_step_control_def]) >>
     metis_tac[]) >>
  (* Align the source and destination height indices before moving demands. *)
  qpat_assum `height y = _` SUBST_ALL_TAC >>
  qpat_assum `Inherit tx (tag y) bx (boolean y) _ _ _ _`
    (fn old => asm "transfer" (fn transfer => MATCH_MP_TAC (MATCH_MP transfer old))) >>
  simp[Abbr `tr`, asm_step_push_ok] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
QED

Finalise conditional_jump_retained_row
