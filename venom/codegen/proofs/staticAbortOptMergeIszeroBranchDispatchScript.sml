Theory staticAbortOptMergeIszeroBranchDispatch
Ancestors
  staticAbortOptMergeIszeroLayout asmSymSem asmSymBridge asmToBytecodeProofs
  asmIR asmSem asmOptimizer staticAbortStraight finite_map words list pred_set arithmetic alist

Theorem merge_iszero_branch_dispatch:
  !p q pre l tail (ss:sym_state) (a:asm_state) (t:asm_state)
    (V:(num#num)->bool) e rank pc height tag boolean edge next v.
  let b = LENGTH pre; c = ss.sym_base.as_pc in
  let Target = \prog P T x y.
    ?nm org off. T x 0 = SOME(nm,org) /\
      FLOOKUP (SND (compute_label_offsets prog)) nm = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc prog) off = SOME(P y) in
  let Row = \cc h cond lookup fall taken out consumed terminal ins.
    case ins of
      AsmOp name =>
        name = "INVALID" /\ terminal \/
        name = "REVERT" /\ 2 <= h /\ consumed 2 /\ terminal \/
        MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] /\
          cc.cc_static /\ asm_op_arity name <= h /\ consumed (asm_op_arity name) /\ terminal \/
        (case ALOOKUP dup_table name of
           SOME n => n < h /\ fall /\ out (h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < h /\ fall /\ out h
           | NONE =>
             name = "JUMP" /\ 1 <= h /\ taken /\ out (h-1) \/
             name = "JUMPI" /\ 2 <= h /\ cond /\ fall /\ taken /\ out (h-2) \/
             ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                 consumed (asm_op_arity name) /\ fall /\ out (h-asm_op_arity name+m))
    | AsmPush bs => fall /\ out (h+1)
    | AsmPushLabel nm => lookup nm /\ fall /\ out (h+1)
    | AsmPushOfst nm d => lookup nm /\ fall /\ out (h+1)
    | AsmLabel nm => fall /\ out h
    | _ => F in
  let Rows = \prog cc A P H T E.
    !x. x IN A ==> P x < LENGTH prog /\
      Row cc (H x) (T x 1 = NONE)
        (\nm. IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) nm))
        (?y. E x y /\ P y = P x+1)
        (?y. E x y /\ Target prog P T x y)
        (\n. !y. E x y ==> H y = n)
        (\n. !k. k<n ==> T x k=NONE)
        (!y. ~E x y) (EL (P x) prog) in
  let keep = \i. i < b \/ b+2 <= i in
  let f = \i. if i < b then i else i-2 in
  let fresh = (c=b+3) in
  let Vq = {x | x IN V /\ keep(pc x)} UNION (if fresh then {v} else {}) in
  let pcq = \x. if x=v then b else f(pc x) in
  let hq = \x. if x=v then height e-1 else height x in
  let M = OPTION_MAP (\(nm,org). (nm,f org)) in
  let tq = \x k.
    if x=v then if k=0 then NONE else M(tag e (k+1))
    else if (pc x=b+2 /\ k=0) \/ (pc x=b+3 /\ k=1) then NONE
    else if pc x=b+3 /\ k=0 then SOME(l,b) else M(tag x k) in
  let eqr = \x y. (x=v /\ fresh /\ y=e) \/
    (x IN V /\ keep(pc x) /\ ?z. edge x z /\ y=next z) in
  p = pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] ++ tail /\
  q = pre ++ [AsmPushLabel l; AsmOp "JUMPI"] ++ tail /\ asm_static_wf p /\
  e IN V /\ pc e = c /\ t.as_call_ctx = a.as_call_ctx /\
  Rows p a.as_call_ctx V pc height tag edge /\
  (!x z. edge x z ==> z IN V) /\
  (!x. x IN V ==> next x IN V /\ keep (pc (next x)) /\
    height (next x) = height x /\
    (if keep (pc x) then next x=x else pc (next x)=b+2 /\ rank (next x)<rank x) /\
    (!k nm org. 0<k /\ tag (next x) k=SOME(nm,org) ==> tag x k=SOME(nm,org)) /\
    (!k. 0<k /\ boolean (next x) k ==> boolean x k)) /\ v NOTIN V /\
  (!x z. x IN V /\ keep(pc x) /\ edge x z ==>
    (pc z=pc x+1 ==> pcq (next z)=pcq x+1) /\
    (((EL (pc x) p=AsmOp "JUMP" \/ EL (pc x) p=AsmOp "JUMPI") /\
      Target p pc tag x z) ==> Target q pcq tq x (next z))) ==>
  Rows q t.as_call_ctx Vq pcq hq tq eqr
Proof
  rpt gen_tac >>
  map_every (fn name =>
    CONV_TAC (REWR_CONV combinTheory.LET_FORALL_ELIM THENC
      SIMP_CONV bool_ss [combinTheory.S_DEF, combinTheory.o_THM, combinTheory.C_DEF]) >>
    qx_gen_tac name >> disch_tac)
    [`b`,`c`,`Target`,`Row`,`Rows`,`keep`,`f`,`fresh`,`Vq`,`pcq`,`hq`,`M`,`tq`,`eqr`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `q = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `t.as_call_ctx = _` (fn th => once_rewrite_tac[GSYM th]) >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"]`,
                    `repl` |-> `[AsmPushLabel l; AsmOp "JUMPI"]`]
    (BETA_RULE (REWRITE_RULE [LET_THM] merge_iszero_one_canonical_layout))) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
                conj_tac >- first_assum ACCEPT_TAC >>
                conj_tac >- first_assum ACCEPT_TAC >> simp[])) >>
  qpat_assum `Abbrev (b = _)` (fn th =>
    simp[NoAsms, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. keep i /\ i < LENGTH p ==> f i < LENGTH q /\ EL (f i) q = EL i p` by
    (simp[Abbr `keep`, Abbr `f`] >> (gvs[])) >>
  `!i. i IN Vq <=> (i IN V /\ keep (pc i)) \/ (i=v /\ fresh)` by
    (simp[Abbr `Vq`] >> Cases_on `fresh` >> simp[]) >>
  `EL (b+3) p = AsmOp "JUMPI" /\ EL b q = AsmPushLabel l /\ b < LENGTH q` by
    (qpat_assum `p = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `q = _` (fn th => rewrite_tac[th]) >>
     simp[Abbr `b`, EL_APPEND_EQN]) >>
  `!nm. (MEM (AsmPushLabel nm) q \/ (?d. MEM (AsmPushOfst nm d) q)) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets q)) nm)` by suspend "lookup" >>
  qpat_assum `Abbrev (Rows = _)` (fn th =>
    qpat_x_assum `Rows p _ _ _ _ _ _`
      (assume_tac o BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
    rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> qx_gen_tac `x` >> disch_tac >> Cases_on `x=v`
  >- suspend "fresh_row" >> suspend "retained_row"
QED

Resume merge_iszero_branch_dispatch[lookup]:
  qx_gen_tac `nm` >> disch_tac >>
  `MEM nm (asm_label_refs q)` by
    (simp[NoAsms, asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     qpat_x_assum `MEM (AsmPushLabel nm) q \/ _` strip_assume_tac
     >- (qexists `AsmPushLabel nm` >> simp[]) >>
     qexists `AsmPushOfst nm d` >> simp[]) >>
  `MEM (AsmLabel nm) q \/ MEM (AsmDataHeader nm) q` by
    (qpat_assum `asm_static_wf q`
       (fn th => drule (cj 3 (REWRITE_RULE [asm_static_wf_def] th))) >>
     disch_then ACCEPT_TAC) >>
  `nm IN FDOM (SND (compute_label_offsets q))` by
    (rewrite_tac[symbolResolveTheory.compute_label_offsets_def, clo_step_eq] >>
     irule clo_FDOM >> simp[IgnAsm `q = _`]) >>
  simp[IgnAsm `q = _`, FLOOKUP_DEF]
QED

Resume merge_iszero_branch_dispatch[fresh_row]:
  `fresh` by metis_tac[] >>
  `pc e=b+3` by fs[Abbr `fresh`] >>
  `e<>v` by metis_tac[] >>
  `!y. eqr x y <=> y=e` by
    (simp[Abbr `eqr`] >> metis_tac[]) >>
  `2 <= height e` by (
    first_x_assum (qspec_then `e` (drule_then (mp_tac o CONJUNCT2))) >>
    `EL (pc e) p = AsmOp "JUMPI"` by metis_tac[] >>
    simp[Abbr `Row`, EVAL ``ALOOKUP dup_table "JUMPI"``,
      EVAL ``ALOOKUP swap_table "JUMPI"``, EVAL ``MEM "JUMPI" ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]``,
      static_abort_straight_def]) >>
  `pcq x=b /\ pcq e=b+1 /\ hq x=height e-1 /\ hq e=height e` by
    (simp[Abbr `pcq`, Abbr `hq`, Abbr `f`] >> decide_tac) >>
  `IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l)` by
    (first_x_assum irule >> qpat_assum `q = _` (fn th => simp[th])) >>
  simp[IgnAsm `q = _`, Abbr `Row`] >> decide_tac
QED

Resume merge_iszero_branch_dispatch[retained_row]:
  `x IN V /\ keep (pc x)` by metis_tac[] >>
  `pcq x=f (pc x) /\ hq x=height x` by simp[Abbr `pcq`, Abbr `hq`] >>
  first_x_assum (qspec_then `x` (drule_then strip_assume_tac)) >>
  `pcq x < LENGTH q /\ EL (pcq x) q = EL (pc x) p` by metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!y. eqr x y <=> ?z. edge x z /\ y=next z` by simp[Abbr `eqr`] >>
  `!z. edge x z ==> hq (next z) = height z` by (
    qx_gen_tac `z` >> disch_tac >>
    `z IN V` by metis_tac[] >>
    `next z IN V /\ height (next z) = height z` by metis_tac[] >>
    `next z <> v` by metis_tac[] >> simp[Abbr `hq`]) >>
  `!z. edge x z ==>
    (pc z = pc x+1 ==> pcq (next z)=pcq x+1) /\
    ((EL (pc x) p=AsmOp "JUMP" \/ EL (pc x) p=AsmOp "JUMPI") /\
     Target p pc tag x z ==> Target q pcq tq x (next z))` by metis_tac[] >>
  suspend "retained_arms"
QED

Resume merge_iszero_branch_dispatch[retained_arms]:
  `(?z. edge x z /\ pc z=pc x+1) ==> (?y. eqr x y /\ pcq y=pcq x+1)` by (
    strip_tac >> qexists `next z` >> simp[] >> qexists `z` >> simp[]) >>
  `(EL (pc x) p=AsmOp "JUMP" \/ EL (pc x) p=AsmOp "JUMPI") /\
    (?z. edge x z /\ Target p pc tag x z) ==> (?y. eqr x y /\ Target q pcq tq x y)` by (
    disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `z` strip_assume_tac)) >>
    qexists `next z` >> conj_tac
    >- (simp[] >> qexists `z` >> simp[]) >>
    qpat_assum `!z. edge x z ==> (_ ==> _) /\ _`
      (qspec_then `z` (drule_then (irule o CONJUNCT2))) >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  `!n. (!z. edge x z ==> height z=n) ==> (!y. eqr x y ==> hq y=n)` by
    (simp[] >> rpt strip_tac >> gvs[]) >>
  `(!z. ~edge x z) ==> (!y. ~eqr x y)` by simp[] >>
  `tag x 1 = NONE ==> tq x 1 = NONE` by simp[Abbr `tq`, Abbr `M`] >>
  `EL (pc x) p <> AsmOp "JUMPI" ==> !n.
    (!k. k<n ==> tag x k=NONE) ==> (!k. k<n ==> tq x k=NONE)` by (
    strip_tac >> `pc x <> b+3` by metis_tac[] >>
    simp[Abbr `tq`, Abbr `M`]) >>
  qpat_x_assum `Row _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `EL (pcq x) q = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `hq x = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `t.as_call_ctx = _` (fn th => rewrite_tac[th]) >>
  Cases_on `EL (pc x) p` >> simp[IgnAsm `p = _`, IgnAsm `q = _`, Abbr `Row`, Excl "MEM"]
  >~ [`AsmOp name`] >- suspend "opcode"
  >~ [`AsmPushLabel nm`] >- suspend "label_push"
  >~ [`AsmPushOfst nm d`] >- suspend "ofst_push" >>
  metis_tac[]
QED

Resume merge_iszero_branch_dispatch[label_push]:
  rename1 `EL (pcq x) q = AsmPushLabel nm'` >>
  disch_tac >> first_assum irule >> disj1_tac >>
  rewrite_tac[MEM_EL] >> qexists `pcq x` >> simp[IgnAsm `q = _`]
QED

Resume merge_iszero_branch_dispatch[ofst_push]:
  rename1 `EL (pcq x) q = AsmPushOfst nm' d` >>
  disch_tac >> first_assum irule >> disj2_tac >> qexists `d` >>
  rewrite_tac[MEM_EL] >> qexists `pcq x` >> simp[IgnAsm `q = _`]
QED

Resume merge_iszero_branch_dispatch[opcode]:
  rename1 `EL (pc x) p = AsmOp name` >>
  qpat_assum `(_ ==> ?y. eqr x y /\ pcq y = _)` mp_tac >>
  qpat_assum `(_ ==> ?y. eqr x y /\ Target q pcq tq x y)` mp_tac >>
  qpat_assum `!n. (!z. edge x z ==> height z=n) ==> _` mp_tac >>
  qpat_assum `(!z. ~edge x z) ==> _` mp_tac >>
  qpat_assum `tag x 1 = NONE ==> _` mp_tac >>
  qpat_assum `AsmOp name <> AsmOp "JUMPI" ==> _` mp_tac >>
  qpat_assum `!y. eqr x y <=> ?z. edge x z /\ y = next z`
    (fn th => rewrite_tac[th]) >>
  qpat_assum `pcq x = f (pc x)` (fn th => rewrite_tac[th]) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `ALOOKUP dup_table name` >> pop_assum (fn th => simp[NoAsms, th])
  >- (Cases_on `ALOOKUP swap_table name` >> pop_assum (fn th => simp[NoAsms, th])
      >- (Cases_on `name = "JUMPI"`
          >- (simp[static_abort_straight_def] >> metis_tac[]) >>
          simp[] >> rpt disch_tac >> pop_assum strip_assume_tac >>
          gvs[] >> metis_tac[]) >>
      rpt disch_tac >> pop_assum strip_assume_tac >> gvs[] >> metis_tac[]) >>
  rpt disch_tac >> pop_assum strip_assume_tac >> gvs[] >> metis_tac[]
QED

Finalise merge_iszero_branch_dispatch
