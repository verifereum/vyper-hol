Theory staticAbortOptMergeIszeroBranchSlots
Ancestors
  staticAbortOptMergeIszeroLayout asmIR asmSem asmSymSem asmWf
  finite_map words list pred_set arithmetic option pair

Theorem merge_iszero_branch_slots:
  !(pre:asm_inst list) tail p q l (ss:sym_state) (t:asm_state)
    (V:(num#num)->bool) e pc (height:(num#num)->num) need tag boolean v.
  let b = LENGTH pre in
  let keep = \i. i < b \/ b+2 <= i in
  let f = \i. if i < b then i else i-2 in
  let M = OPTION_MAP (\(nm,org). (nm,f org)) in
  let fresh = (ss.sym_base.as_pc = b+3) in
  let Vq = {x | x IN V /\ keep (pc x)} UNION (if fresh then {v} else {}) in
  let hq = \x. if x=v then height e-1 else height x in
  let nq = \x. x<>v /\ need x in
  let tq = \x k. if x=v then (if k=0 then NONE else M (tag e (k+1)))
    else if (pc x=b+2 /\ k=0) \/ (pc x=b+3 /\ k=1) then NONE
    else if pc x=b+3 /\ k=0 then SOME(l,b) else M (tag x k) in
  let Bq = \x k. if x=v then 0<k /\ boolean e (k+1)
    else boolean x k /\ ~(pc x=b+2 /\ k=0) /\ ~(pc x=b+3 /\ k<=1) in
  let LabelOK = \code nm org.
    org < LENGTH code /\
    (EL org code = AsmPushLabel nm \/ EL org code = AsmPushOfst nm 0) /\
    ?off dest. FLOOKUP (SND (compute_label_offsets code)) nm = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc code) off = SOME dest in
  let Slots = \code cc A h n g B.
    !x. x IN A ==>
      (n x ==> cc.cc_static) /\
      (!k. B x k ==> k < h x /\ g x k=NONE) /\
      (!k nm org. g x k=SOME(nm,org) ==> k < h x /\ LabelOK code nm org) in
  p=pre++[AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"]++tail /\
  q=pre++[AsmPushLabel l; AsmOp "JUMPI"]++tail /\ asm_static_wf p /\
  e IN V /\ v NOTIN V /\ Slots p t.as_call_ctx V height need tag boolean /\
  (!x. x IN V /\ pc x=b+3 ==> ?i. tag x 0=SOME(l,i)) ==>
  Slots q t.as_call_ctx Vq hq nq tq Bq
Proof
  rpt gen_tac >>
  map_every (fn name =>
    CONV_TAC (REWR_CONV combinTheory.LET_FORALL_ELIM THENC
      SIMP_CONV bool_ss [combinTheory.S_DEF, combinTheory.o_THM, combinTheory.C_DEF]) >>
    qx_gen_tac name >> disch_tac)
    [`b`,`keep`,`f`,`M`,`fresh`,`Vq`,`hq`,`nq`,`tq`,`Bq`,`LabelOK`,`Slots`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"]`,
                   `repl` |-> `[AsmPushLabel l; AsmOp "JUMPI"]`]
                 merge_iszero_one_canonical_layout) >>
  CONV_TAC (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM, BETA_CONV])) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => EVERY [mk_asm "layout-target" (cj 3 th),
    mk_asm "layout-fetch" (cj 4 th), mk_asm "layout-origin" (cj 5 th)]) >>
  `!nm old dest. FLOOKUP (SND (compute_label_offsets p)) nm = SOME old /\
      FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
      ?off dest'. FLOOKUP (SND (compute_label_offsets q)) nm = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME dest'` by
    suspend "canonical" >>
  `!nm org. LabelOK p nm org ==> LabelOK q nm (f org)` by suspend "producer" >>
  `b < LENGTH q /\ EL b q = AsmPushLabel l` by
    (qpat_assum `q = _` SUBST1_TAC >> simp[Abbr `b`, EL_APPEND_EQN]) >>
  map_every (fn name => asm_x name kall_tac) ["layout-target","layout-fetch","layout-origin"] >>
  qpat_x_assum `p = _` kall_tac >>
  qunabbrev_tac `Slots` >> BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `q = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qx_gen_tac `x` >> disch_tac >>
  Cases_on `x=v`
  >- suspend "fresh_slots" >>
  `x IN V` by (qpat_x_assum `x IN Vq` mp_tac >> Cases_on `fresh` >> simp[Abbr `Vq`]) >>
  qpat_assum `!x. x IN V ==> _` (qspec_then `x` (drule_then strip_assume_tac)) >>
  simp[Abbr `nq`,Abbr `hq`] >>
  conj_tac >- suspend "kept_boolean" >>
  suspend "kept_tag"
QED

Resume merge_iszero_branch_slots[canonical]:
  rpt gen_tac >> strip_tac >>
  asm "layout-target" (drule_all_then strip_assume_tac) >>
  rename1 `FLOOKUP (SND (compute_label_offsets q)) nm = SOME off` >>
  qexists `off` >> simp[]
QED

Resume merge_iszero_branch_slots[producer]:
  map_every qx_gen_tac [`nm`,`org`] >> simp[NoAsms, Abbr `LabelOK`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `f org < LENGTH q /\ EL (f org) q = EL org p` by (
    `org < LENGTH pre \/ LENGTH pre+2 <= org` by (
      asm "layout-origin" (qspecl_then [`nm`,`org`] mp_tac) >>
      simp[NoAsms] >> metis_tac[]) >>
    asm "layout-fetch" (qspec_then `org` mp_tac) >> simp[Abbr `f`, Abbr `b`]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `EL (f org) q = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `!nm old dest. FLOOKUP _ nm = SOME old /\ _ ==> _`
    (drule_all_then ACCEPT_TAC)
QED

Resume merge_iszero_branch_slots[fresh_slots]:
  qpat_assum `!x. x IN V ==> _` (qspec_then `e` (drule_then strip_assume_tac)) >>
  simp[Abbr `nq`, Abbr `hq`, Abbr `tq`, Abbr `Bq`] >>
  conj_tac
  >- (qx_gen_tac `k` >> strip_tac >>
      `k+1 < height e /\ tag e (k+1) = NONE` by metis_tac[] >>
      simp[Abbr `M`] >> simp[SUB_LEFT_LESS]) >>
  map_every qx_gen_tac [`k`,`nm`,`org`] >> Cases_on `k=0` >>
  simp[Abbr `M`, EXISTS_PROD] >> strip_tac >>
  rename1 `tag e (k+1)=SOME(nm,i)` >>
  `k+1 < height e /\ LabelOK p nm i` by metis_tac[] >>
  `k < height e-1` by (simp[SUB_LEFT_LESS]) >>
  gvs[]
QED

Resume merge_iszero_branch_slots[kept_boolean]:
  qx_gen_tac `k` >> simp[Abbr `Bq`, Abbr `tq`, Abbr `M`] >> strip_tac >>
  `k < height x /\ tag x k=NONE` by metis_tac[] >>
  `~(pc x = b+3 /\ k=0)` by decide_tac >> simp[]
QED

Resume merge_iszero_branch_slots[kept_tag]:
  map_every qx_gen_tac [`k`,`nm`,`org`] >> simp[Abbr `tq`] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[] >>
      `?i. tag x 0 = SOME(l,i)` by metis_tac[] >>
      `0 < height x /\ LabelOK p l i` by metis_tac[] >>
      qpat_assum `LabelOK p l i` mp_tac >> simp[Abbr `LabelOK`] >> metis_tac[]) >>
  simp[Abbr `M`, EXISTS_PROD] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Finalise merge_iszero_branch_slots
