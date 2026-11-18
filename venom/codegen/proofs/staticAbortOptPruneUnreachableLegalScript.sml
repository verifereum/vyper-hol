(* Transfer control-flow legality, keeping the fall and taken arms separate. *)
Theory staticAbortOptPruneUnreachableLegal
Ancestors
  asmOptimizer asmSem asmSymSem finite_map words arithmetic list pred_set combin

Theorem prune_one_relocated_legal:
  !pre t x tail (V:(num#num)->bool) pc
    (tag:(num#num)->num->(string#num)option) edge.
    let p = pre ++ [t;x] ++ tail in
    let q = pre ++ [t] ++ tail in
    let d = LENGTH pre+1 in
    let r = \i. if i < d then i else i-1 in
    let Z = \l j. j < LENGTH q /\
      (EL j q = AsmPushLabel l \/ EL j q = AsmPushOfst l 0) in
    let pick = \l. @j. Z l j in
    let tagQ = \v k. OPTION_MAP (\(l,i). (l,if i=d then pick l else r i))
      (tag v k) in
    let Hit = \p l j.
      ?off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME j in
    let Target = \p pc tag (a:num#num) (b:num#num).
      ?l i. tag a 0 = SOME(l,i) /\ Hit p l (pc b) in
    let Legal = \p pc tag a b.
      if EL (pc a) p = AsmOp "JUMP" then Target p pc tag a b
      else if EL (pc a) p = AsmOp "JUMPI" then pc b = pc a+1 \/ Target p pc tag a b
      else pc b = pc a+1 in
    let fall = \a b. edge a b /\ ~asm_terminal_op (EL (pc a) p) /\ pc b = pc a+1 in
    let taken = \a l b. edge a b /\
      (EL (pc a) p = AsmOp "JUMP" \/ EL (pc a) p = AsmOp "JUMPI") /\
      (?i. tag a 0 = SOME(l,i)) /\ Hit p l (pc b) in
    (!v. v IN V ==> pc v <> d /\ r (pc v) < LENGTH q /\
      EL (r (pc v)) q = EL (pc v) p) /\
    (!a b. edge a b <=> fall a b \/ ?l. taken a l b) /\
    (!a b. fall a b ==> r (pc b) = r (pc a)+1) /\
    (!a l b. taken a l b ==> Hit q l (r (pc b))) /\
    (!a b. edge a b ==> a IN V /\ b IN V) /\
    (!a b. edge a b ==> Legal p pc tag a b) /\
    (!a b. edge a b /\ EL (pc a) p <> AsmOp "JUMP" ==>
      ~asm_terminal_op (EL (pc a) p)) ==>
    (!a b. edge a b /\ EL (pc a) p <> AsmOp "JUMP" /\ pc b = pc a+1 ==>
      r (pc b) = r (pc a)+1) /\
    (!a b. edge a b /\
      (EL (pc a) p = AsmOp "JUMP" \/ EL (pc a) p = AsmOp "JUMPI") /\
      Target p pc tag a b ==> Target q (r o pc) tagQ a b) /\
    (!a b. edge a b ==> Legal q (r o pc) tagQ a b)
Proof
  rpt gen_tac >>
  map_every (fn selector =>
    qmatch_goalsub_abbrev_tac selector >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ p`, `LET _ q`, `LET _ d`, `LET _ r`, `LET _ Z`, `LET _ pick`,
     `LET _ tagQ`, `LET _ Hit`, `LET _ Target`, `LET _ Legal`,
     `LET _ fall`, `LET _ taken`] >>
  strip_tac >>
  qpat_x_assum `!a b. edge a b <=> _` kall_tac >>
  conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a b. fall a b ==> _` irule >>
      simp[Abbr `fall`] >> metis_tac[]) >>
  conj_asm1_tac
  >- (rpt gen_tac >> disch_tac >>
      `?l i. tag a 0 = SOME(l,i) /\ Hit p l (pc b)` by fs[Abbr `Target`] >>
      `taken a l b` by (fs[Abbr `taken`] >> metis_tac[]) >>
      qpat_assum `!a l b. taken a l b ==> _` (drule_then assume_tac) >>
      simp[Abbr `Target`, o_THM] >>
      qexistsl [`l`, `if i=d then pick l else r i`] >>
      simp[Abbr `tagQ`]) >>
  rpt gen_tac >> disch_tac >>
  `a IN V` by (qpat_assum `!a b. edge a b ==> a IN V /\ _` drule >> simp[]) >>
  qpat_assum `!v. v IN V ==> pc v <> d /\ _`
    (qspec_then `a:num#num` (fn th =>
       qpat_assum `a IN V` (strip_assume_tac o MP th))) >>
  qpat_x_assum `!a b. edge a b ==> Legal p pc tag a b`
    (qspecl_then [`a`, `b`] (fn th => qpat_assum `edge a b` (mp_tac o MP th))) >>
  qpat_x_assum `!a b. edge a b /\ _ /\ Target p pc tag a b ==> _`
    (qspecl_then [`a`, `b`] mp_tac) >>
  qpat_x_assum `!a b. edge a b /\ _ /\ pc b = pc a+1 ==> _`
    (qspecl_then [`a`, `b`] mp_tac) >>
  Cases_on `EL (pc a) p = AsmOp "JUMP"` >>
  Cases_on `EL (pc a) p = AsmOp "JUMPI"` >>
  simp[Abbr `Legal`, o_THM] >>
  POP_ASSUM_LIST kall_tac >> metis_tac[]
QED
