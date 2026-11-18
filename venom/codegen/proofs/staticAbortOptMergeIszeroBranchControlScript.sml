Theory staticAbortOptMergeIszeroBranchControl
Ancestors
  staticAbortOptMergeIszeroLayout asmSymSem asmIR asmSem finite_map words
  pred_set arithmetic list rich_list option

(* Only the control-relevant projections of the source certificate are used:
   an outgoing taken arm at JUMPI, tag freshness at a label push, and
   the root's symbolic top slot when the cut is after that push. *)
Theorem merge_iszero_branch_control:
  !(V:(num#num)->bool) e (rank:(num#num)->num) pc (height:(num#num)->num)
    tag boolean edge next v.
  let b = LENGTH pre in
  let c = ss.sym_base.as_pc in
  let keep = \i. i < b \/ b+2 <= i in
  let f = \i. if i < b then i else i-2 in
  let fresh = (c=b+3) in
  let Vq = {x | x IN V /\ keep (pc x)} UNION (if fresh then {v} else {}) in
  let pcq = \x. if x=v then b else f (pc x) in
  let rq = \x. if x=v then SUC (rank e) else rank x in
  let M = OPTION_MAP (\(nm,org). (nm,f org)) in
  let tq = \x k.
    if x=v then (if k=0 then NONE else M (tag e (k+1)))
    else if (pc x=b+2 /\ k=0) \/ (pc x=b+3 /\ k=1) then NONE
    else if pc x=b+3 /\ k=0 then SOME(l,b) else M (tag x k)
  in
  let eqr = \x y. (x=v /\ fresh /\ y=e) \/
              (x IN V /\ keep (pc x) /\ ?z. edge x z /\ y=next z) in
  let Target = \prog pcs tags (x:num#num) (y:num#num).
    ?nm org off. tags x 0 = SOME(nm,org) /\
      FLOOKUP (SND (compute_label_offsets prog)) nm = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc prog) off = SOME (pcs y)
  in
  let Control = \prog pcs tags x y.
    if EL (pcs x) prog = AsmOp "JUMP" then Target prog pcs tags x y
    else if EL (pcs x) prog = AsmOp "JUMPI" then
      pcs y = pcs x+1 \/ Target prog pcs tags x y
    else pcs y = pcs x+1
  in
  p = pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] ++ tail /\
  q = pre ++ [AsmPushLabel l; AsmOp "JUMPI"] ++ tail /\
  asm_static_wf p /\ e IN V /\ pc e=c /\ v NOTIN V /\
  (!x. x IN V ==> pc x < LENGTH p) /\
  (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Control p pc tag x y) /\
  (!x. x IN V /\ EL (pc x) p = AsmOp "JUMPI" ==>
       ?y. edge x y /\ Target p pc tag x y) /\
  (!x y nm name org. edge x y /\ EL (pc x) p = AsmPushLabel nm /\
       tag y 0 = SOME(name,org) ==> name=nm) /\
  (!nm org. tag e 0=SOME(nm,org) ==> EL 0 ss.sym_stack=Lab nm 0) /\
  (fresh ==> ?stk. ss.sym_stack=Lab l 0::stk) /\
  (!x. x IN V ==> next x IN V /\ keep (pc (next x)) /\ height (next x)=height x /\
       (if keep (pc x) then next x=x else pc (next x)=b+2 /\ rank (next x)<rank x) /\
       (!k nm org. 0<k /\ tag (next x) k=SOME(nm,org) ==> tag x k=SOME(nm,org)) /\
       (!k. 0<k /\ boolean (next x) k ==> boolean x k)) /\
  (!x. x IN V /\ x<>e ==> ?w. edge w x) /\
  (!x z. x IN V /\ keep (pc x) /\ edge x z /\ pc z=pc x+1 ==>
         f (pc (next z))=f (pc x)+1) ==>
  (!x. x IN V /\ pc x=b+3 ==> ?i. tag x 0=SOME(l,i)) /\
  (!x z. x IN V /\ keep (pc x) /\ edge x z ==>
     (pc z=pc x+1 ==> pcq (next z)=pcq x+1) /\
     ((EL (pc x) p=AsmOp "JUMP" \/ EL (pc x) p=AsmOp "JUMPI") /\
        Target p pc tag x z ==> Target q pcq tq x (next z)) /\
     (pc (next z)=b+3 ==> next z=z /\ pc x=b+2)) /\
  (!x y. eqr x y ==> x IN Vq /\ y IN Vq /\ rq y<rq x /\ Control q pcq tq x y)
Proof
  rpt gen_tac >>
  map_every (fn name =>
    CONV_TAC (REWR_CONV combinTheory.LET_FORALL_ELIM THENC
      TOP_DEPTH_CONV (FIRST_CONV [BETA_CONV, REWR_CONV combinTheory.S_DEF,
                        REWR_CONV combinTheory.o_THM, REWR_CONV combinTheory.C_DEF])) >>
    qx_gen_tac name >> disch_tac)
    [`b`,`c`,`keep`,`f`,`fresh`,`Vq`,`pcq`,`rq`,`M`,`tq`,`eqr`,`Target`,`Control`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EL (b+2) p = AsmPushLabel l /\ EL (b+3) p = AsmOp "JUMPI" /\
   EL b q = AsmPushLabel l` by
    simp[Abbr `b`, EL_APPEND_EQN] >>
  `(!nm old dest. FLOOKUP (SND (compute_label_offsets p)) nm = SOME old /\
       FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
       keep dest /\ EL dest p = AsmLabel nm /\
       ?off. FLOOKUP (SND (compute_label_offsets q)) nm = SOME off /\
             off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME (f dest)) /\
   (!i. keep i /\ i < LENGTH p ==> EL (f i) q = EL i p)` by (
     mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"]`,
                     `repl` |-> `[AsmPushLabel l; AsmOp "JUMPI"]`]
       (BETA_RULE (REWRITE_RULE [LET_THM] merge_iszero_one_canonical_layout))) >>
     (impl_tac >- (simp[] >> metis_tac[])) >>
     disch_then (fn th =>
       let val packet = BETA_RULE (PURE_REWRITE_RULE
             [EVAL ``LENGTH [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] = 3``,
              COND_CLAUSES] th)
       in map_every assume_tac [cj 3 packet, cj 4 packet] end) >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!a old dest. FLOOKUP (SND (compute_label_offsets p)) a = SOME old /\ _ ==> _`
           (drule_all_then mp_tac) >>
         simp[Abbr `keep`, Abbr `f`, Abbr `b`] >> strip_tac >>
         simp[] >> metis_tac[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!i. _ ==> _ < LENGTH q /\ _` (qspec_then `i` mp_tac) >>
     simp[Abbr `keep`, Abbr `f`, Abbr `b`] >> gvs[]) >>
  `!x. x IN V ==> next x IN V /\ keep (pc (next x)) /\ rank (next x)<=rank x /\
       (keep (pc x) ==> next x=x) /\ (next x<>x ==> pc (next x)=b+2)` by (
    gen_tac >> disch_tac >>
    qpat_x_assum `!a. a IN V ==> next a IN V /\ _`
      (qspec_then `x` (drule_then (map_every assume_tac o CONJUNCTS))) >>
    Cases_on `keep (pc x)` >> gvs[] >> decide_tac) >>
  `!x. x IN V ==> x<>v /\ pcq x=f (pc x) /\ rq x=rank x /\
       (keep (pc x) ==> x IN Vq)` by (
    gen_tac >> disch_tac >> `x<>v` by metis_tac[] >>
    simp[Abbr `pcq`, Abbr `rq`, Abbr `Vq`] >> Cases_on `fresh` >> simp[]) >>
  `!x y. Target p pc tag x y ==> keep (pc y) /\
       (?nm. EL (pc y) p=AsmLabel nm) /\
       ?nm org off. tag x 0=SOME(nm,org) /\
         FLOOKUP (SND (compute_label_offsets q)) nm = SOME off /\
         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME (f (pc y))` by
    suspend "target_layout" >>
  `!prog pcs tags a d. Control prog pcs tags a d <=>
     ((EL (pcs a) prog <> AsmOp "JUMP" /\ pcs d=pcs a+1) \/
      ((EL (pcs a) prog = AsmOp "JUMP" \/ EL (pcs a) prog = AsmOp "JUMPI") /\
       Target prog pcs tags a d))` by (
    qpat_assum `Abbrev (Control = _)`
      (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    BETA_TAC >> POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
    Cases_on `EL (pcs a) prog = AsmOp "JUMP"` >>
    Cases_on `EL (pcs a) prog = AsmOp "JUMPI"` >> simp[]) >>
  pop_assum (mk_asm "control_arms") >>
  `!x y. edge x y /\ pc y=b+3 ==> pc x=b+2` by suspend "predecessor" >>
  `!x. x IN V /\ pc x=b+3 ==> ?i. tag x 0=SOME(l,i)` by suspend "top_tag" >>
  `!x z. x IN V /\ keep (pc x) /\ edge x z ==>
     (pc z=pc x+1 ==> pcq (next z)=pcq x+1) /\
     ((EL (pc x) p=AsmOp "JUMP" \/ EL (pc x) p=AsmOp "JUMPI") /\
        Target p pc tag x z ==> Target q pcq tq x (next z)) /\
     (pc (next z)=b+3 ==> next z=z /\ pc x=b+2)` by suspend "arms" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `Abbrev (eqr = _)`
    (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
  >- suspend "fresh_edge" >>
  suspend "kept_edge"
QED

Resume merge_iszero_branch_control[target_layout]:
  rpt gen_tac >>
  qpat_assum `Abbrev (Target = _)`
    (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  BETA_TAC >> strip_tac >>
  qpat_assum `!nm old dest. FLOOKUP (SND (compute_label_offsets p)) nm = SOME old /\ _ ==> _`
    (drule_all_then strip_assume_tac) >> metis_tac[]
QED

Resume merge_iszero_branch_control[predecessor]:
  rpt gen_tac >> strip_tac >>
  `~Target p pc tag x y` by (
    strip_tac >> `?nm. EL (pc y) p = AsmLabel nm` by metis_tac[] >> gvs[]) >>
  `Control p pc tag x y` by metis_tac[] >>
  `pc y=pc x+1` by (
    asm "control_arms" (qspecl_then [`p`,`pc`,`tag`,`x`,`y`] (mp_tac o iffLR)) >>
    simp[]) >>
  decide_tac
QED

Resume merge_iszero_branch_control[top_tag]:
  gen_tac >> strip_tac >>
  `?y. edge x y /\ Target p pc tag x y` by metis_tac[] >>
  qpat_x_assum `Target p pc tag x y` mp_tac >> simp[Abbr `Target`] >>
  disch_then (qx_choose_then `nm` (qx_choose_then `org` (qx_choose_then `off` strip_assume_tac))) >>
  qexists `org` >> `nm=l` suffices_by simp[] >>
  Cases_on `x=e`
  >- (`c=b+3` by metis_tac[] >> `fresh` by simp[Abbr `fresh`] >>
      `?stk. ss.sym_stack=Lab l 0::stk` by metis_tac[] >>
      `EL 0 ss.sym_stack=Lab nm 0` by metis_tac[] >>
      qpat_x_assum `EL 0 ss.sym_stack = Lab nm 0` mp_tac >> simp[]) >>
  `?w. edge w x` by metis_tac[] >> `pc w=b+2` by metis_tac[] >>
  `EL (pc w) p=AsmPushLabel l` by metis_tac[] >> metis_tac[]
QED

Resume merge_iszero_branch_control[arms]:
  rpt gen_tac >> strip_tac >>
  `z IN V` by metis_tac[] >> `next z IN V` by metis_tac[] >>
  `pcq x=f (pc x) /\ pcq (next z)=f (pc (next z))` by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac
  >- (strip_tac >> `next z=z` by (spose_not_then assume_tac >>
         `pc (next z)=b+2` by metis_tac[] >> decide_tac) >>
      `pc z=b+3` by metis_tac[] >> metis_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!a d. Target p pc tag a d ==> _`
    (qspecl_then [`x`,`z`] (drule_then (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (K ALL_TAC)
        (qx_choose_then `lab` (qx_choose_then `org`
          (qx_choose_then `off` strip_assume_tac))))))) >>
  `next z=z` by metis_tac[] >>
  `x<>v` by metis_tac[] >>
  `pc x<>b+2` by (strip_tac >> gvs[]) >>
  `?origin. tq x 0 = SOME(lab,origin)` by (
    Cases_on `pc x=b+3`
    >- (`?i. tag x 0=SOME(l,i)` by metis_tac[] >>
        `lab=l` by metis_tac[SOME_11,pairTheory.PAIR_EQ] >> simp[Abbr `tq`]) >>
    simp[Abbr `tq`, Abbr `M`]) >>
  qpat_assum `Abbrev (Target = _)`
    (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  BETA_TAC >> qexistsl [`lab`,`origin`,`off`] >> metis_tac[]
QED

Resume merge_iszero_branch_control[fresh_edge]:
  `pc e=b+3` by gvs[Abbr `fresh`] >>
  `keep (pc e)` by simp[Abbr `keep`] >>
  `e <> v /\ e IN Vq` by metis_tac[] >>
  `pcq e=b+1` by (simp[Abbr `pcq`, Abbr `f`] >> decide_tac) >>
  `v IN Vq` by simp[Abbr `Vq`] >>
  `rq v=SUC (rank e) /\ rq e=rank e` by simp[Abbr `rq`] >>
  `pcq v=b` by simp[Abbr `pcq`] >>
  `EL (pcq v) q=AsmPushLabel l` by metis_tac[] >>
  `Control q pcq tq v e` by (
    asm "control_arms" (qspecl_then [`q`,`pcq`,`tq`,`v`,`e`] (irule o iffRL)) >>
    disj1_tac >> conj_tac
    >- (qpat_x_assum `EL (pcq v) q = AsmPushLabel l` SUBST1_TAC >> simp[]) >>
    simp[]) >>
  `rq e < rq v` by decide_tac >> metis_tac[]
QED

Resume merge_iszero_branch_control[kept_edge]:
  qpat_x_assum `?z. edge x z /\ _` strip_assume_tac >>
  `z IN V /\ rank z<rank x /\ Control p pc tag x z` by metis_tac[] >>
  `next z IN V /\ keep (pc (next z)) /\ rank (next z)<=rank z` by metis_tac[] >>
  `x IN Vq /\ next z IN Vq /\ rq x=rank x /\ rq (next z)=rank (next z) /\ pcq x=f (pc x)` by
    metis_tac[] >>
  `rq (next z)<rq x` by decide_tac >>
  `EL (pcq x) q=EL (pc x) p` by metis_tac[] >>
  qpat_x_assum `y = next z` SUBST1_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!a d. a IN V /\ keep (pc a) /\ edge a d ==>
                   (pc d=pc a+1 ==> _) /\ _`
    (qspecl_then [`x`,`z`] (drule_all_then (map_every assume_tac o CONJUNCTS))) >>
  asm "control_arms" (qspecl_then [`q`,`pcq`,`tq`,`x`,`next z`] (irule o iffRL)) >>
  qpat_assum `EL (pcq x) q=EL (pc x) p` SUBST1_TAC >>
  asm "control_arms" (qspecl_then [`p`,`pc`,`tag`,`x`,`z`] (drule_then mp_tac o iffLR)) >>
  disch_then (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

Finalise merge_iszero_branch_control
