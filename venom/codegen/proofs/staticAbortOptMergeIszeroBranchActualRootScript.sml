Theory staticAbortOptMergeIszeroBranchActualRoot
Ancestors
  asmSplice asmSymPc asmSymBridge asmDataEnv asmSem words list rich_list
  finite_map pred_set arithmetic pair

Theorem merge_iszero_branch_actual_root:
  let b = LENGTH pre; c = ss.sym_base.as_pc in
  let B = \w:bytes32. (b2w (w=0w):bytes32) in
  let Shape = \p cc req pc height need tag boolean (i:num#num) (s:asm_state).
    s.as_pc = pc i /\ LENGTH s.as_stack = height i /\
    s.as_call_ctx = cc /\ s.as_requests = req /\
    (need i ==> s.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest /\
         EL k s.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k s.as_stack = 0w \/ EL k s.as_stack = 1w)) in
  let Just = \ss tag boolean (e:num#num).
    (!k l origin. tag e k=SOME(l,origin) ==>
       k<LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
    (!k. boolean e k ==>
       k<LENGTH ss.sym_stack /\ (EL k ss.sym_stack=Val 0w \/ EL k ss.sym_stack=Val 1w)) in
  let Slots = \p cc V height need tag boolean.
    !x:num#num. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest) in
  let keep = \i. i<b \/ b+2<=i;
      f = \i. if i<b then i else i-2;
      fresh = (c=b+3) in
  let M = OPTION_MAP (\(nm,org). (nm,f org)) in
  let Vq = {x | x IN V /\ keep (pc x)} UNION (if fresh then {v} else {});
      root = if fresh then v else next e;
      pcq = \x. if x=v then b else f (pc x);
      hq = \x. if x=v then height e-1 else height x;
      nq = \x. x<>v /\ need x;
      tq = \x k. if x=v then (if k=0 then NONE else M (tag e (k+1)))
        else if (pc x=b+2 /\ k=0) \/ (pc x=b+3 /\ k=1) then NONE
        else if pc x=b+3 /\ k=0 then SOME(l,b) else M (tag x k);
      Bq = \x k. if x=v then 0<k /\ boolean e (k+1)
        else ~((pc x=b+2 /\ k=0) \/ (pc x=b+3 /\ k<=1)) /\ boolean x k in
  asm_sym_rel p (asm_data_env p (assemble p ++ data)) a ss /\
  asm_sym_rel q (asm_data_env q (assemble q ++ data)) t u /\
  e IN V /\ Shape p a.as_call_ctx a.as_requests pc height need tag boolean e a /\
  Just ss tag boolean e /\
  (if b < c /\ c < b+4 then u.sym_base.as_pc=b /\ ?w stk.
     u.sym_stack=Val w::stk /\
     ss.sym_stack=(if c-b=3 then [Lab l 0] else []) ++
        (Val (FUNPOW B (MIN (c-b) 2) w)::stk)
   else u=sym_with_pc (splice_pc b 4 2 c) ss) /\
  (!x. x IN V ==> next x IN V /\ keep (pc (next x)) /\ height (next x)=height x /\
     (if keep (pc x) then next x=x else pc (next x)=b+2 /\ rank (next x)<(rank:num#num->num) x) /\
     (!k nm org. 0<k /\ tag (next x) k=SOME(nm,org) ==> tag x k=SOME(nm,org)) /\
     (!k. 0<k /\ boolean (next x) k ==> boolean x k)) /\
  v NOTIN V /\ Slots q t.as_call_ctx Vq hq nq tq Bq ==>
  Shape q t.as_call_ctx t.as_requests pcq hq nq tq Bq root t /\ Just u tq Bq root
Proof
  map_every (fn name =>
    CONV_TAC (REWR_CONV combinTheory.LET_FORALL_ELIM THENC
      SIMP_CONV bool_ss [combinTheory.S_DEF, combinTheory.o_THM, combinTheory.C_DEF]) >>
    qx_gen_tac name >> disch_tac)
    [`b`,`c`,`B`,`Shape`,`Just`,`Slots`,`keep`,`f`,`fresh`,`M`,`Vq`,`root`,
     `pcq`,`hq`,`nq`,`tq`,`Bq`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `pc e=c /\ height e=LENGTH ss.sym_stack` by
    (qpat_assum `asm_sym_rel p _ a ss` (mp_tac o MATCH_MP asm_sym_rel_pc) >>
     qpat_x_assum `Shape p _ _ _ _ _ _ _ e a` mp_tac >>
     simp[Abbr `Shape`, Abbr `c`] >> metis_tac[]) >>
  qpat_x_assum `!x. x IN V ==> next x IN V /\ _` (qspec_then `e` mp_tac) >>
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `next e <> v` by metis_tac[] >>
  `root IN Vq` by (Cases_on `fresh` >> simp[Abbr `root`, Abbr `Vq`]) >>
  qabbrev_tac `on = \k:num. 0<k \/ (~fresh /\ pc (next e) <> b+2)` >>
  qabbrev_tac `src = \k:num. if fresh then k+1 else k` >>
  `u.sym_base.as_pc = pcq root /\ LENGTH u.sym_stack = hq root /\
   (!k. on k ==> EL k u.sym_stack = EL (src k) ss.sym_stack)` by
    suspend "align" >>
  `Just u tq Bq root` by suspend "justify" >>
  conj_tac >- suspend "concrete" >>
  first_assum ACCEPT_TAC
QED

Resume merge_iszero_branch_actual_root[align]:
  qpat_x_assum `Abbrev (fresh <=> _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  Cases_on `fresh` >> simp[Abbr `root`, Abbr `pcq`, Abbr `hq`, Abbr `on`, Abbr `src`]
  >- (`c=b+3` by fs[] >>
      `b<c /\ c<b+4 /\ c-b=3` by decide_tac >>
      qpat_x_assum `(if b<c /\ c<b+4 then _ else _)` mp_tac >>
      simp[] >> rpt strip_tac >>
      gvs[GSYM ADD1, EL_CONS, PRE_SUB1]) >>
  `c <> b+3` by fs[] >>
  Cases_on `c < b \/ b+4 <= c`
  >- (`keep c` by (simp[Abbr `keep`] >> decide_tac) >>
      `next e=e` by fs[] >>
      `~(b<c /\ c<b+4)` by decide_tac >>
      qpat_x_assum `(if b<c /\ c<b+4 then _ else _)` mp_tac >>
      simp[] >> disch_tac >>
      gvs[sym_with_pc_def, splice_pc_def, Abbr `f`] >> decide_tac) >>
  `pc (next e)=b+2` by
    (Cases_on `keep c` >> fs[] >>
     qpat_x_assum `keep c` mp_tac >> simp[Abbr `keep`] >> decide_tac) >>
  `f (pc (next e)) = b` by simp[Abbr `f`] >>
  Cases_on `c=b`
  >- (qpat_x_assum `(if b<c /\ c<b+4 then _ else _)` mp_tac >>
      simp[] >> disch_tac >> gvs[sym_with_pc_def, splice_pc_def]) >>
  `b<c /\ c<b+4 /\ c-b<>3` by decide_tac >>
  qpat_x_assum `(if b<c /\ c<b+4 then _ else _)` mp_tac >>
  simp[] >> rpt strip_tac >>
  gvs[EL_CONS, PRE_SUB1]
QED

Resume merge_iszero_branch_actual_root[justify]:
  `~fresh ==> pc (next e) <> b+3` by
    (simp[Abbr `fresh`] >> disch_tac >>
     qpat_assum `(if keep c then _ else _)` mp_tac >> IF_CASES_TAC >> simp[]) >>
  `pc (next e) <> b+2 ==> next e=e` by
    (qpat_assum `(if keep c then _ else _)` mp_tac >> IF_CASES_TAC >> simp[]) >>
  `!k nm org. tq root k=SOME(nm,org) ==>
      on k /\ ?old. tag e (src k)=SOME(nm,old)` by
    (Cases_on `fresh` >>
     simp[Abbr `root`, Abbr `tq`, Abbr `M`, Abbr `src`, Abbr `on`, EXISTS_PROD]
     >- (rpt strip_tac >> goal_assum drule) >>
     map_every qx_gen_tac [`k`,`nm`,`org`] >> strip_tac >>
     rename1 `tag (next e) k = SOME (nm,old)` >>
     qexists `old` >>
     Cases_on `k=0`
     >- (`next e=e` by fs[] >> gvs[]) >>
     `0<k` by decide_tac >>
     qpat_assum `!k nm org. 0<k /\ tag (next e) k = _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `!k. Bq root k ==> on k /\ boolean e (src k)` by
    (Cases_on `fresh` >> simp[Abbr `root`, Abbr `Bq`, Abbr `src`, Abbr `on`] >>
     qx_gen_tac `k` >> strip_tac >>
     Cases_on `k=0`
     >- (`next e=e` by fs[] >> gvs[]) >>
     `0<k` by decide_tac >>
     qpat_assum `!k. 0<k /\ boolean (next e) k ==> _` (drule_all_then ACCEPT_TAC)) >>
  qpat_x_assum `Slots q _ Vq hq nq tq Bq` mp_tac >>
  simp[Abbr `Slots`] >> disch_then (qspec_then `root` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Just ss tag boolean e` mp_tac >>
  simp[Abbr `Just`, NoAsms] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "old_tags") (mk_asm "old_booleans")) >>
  conj_tac
  >- (map_every qx_gen_tac [`k`,`nm`,`org`] >> disch_tac >>
      qpat_assum `!k l origin. tq root k = SOME(l,origin) ==> k < _ /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!k nm org. tq root k = SOME(nm,org) ==> on k /\ _`
        (drule_then strip_assume_tac) >>
      asm "old_tags" (drule_then strip_assume_tac) >>
      qpat_assum `!k. on k ==> _` (drule_then (fn th => simp[th]))) >>
  qx_gen_tac `k` >> disch_tac >>
  qpat_assum `!k. Bq root k ==> k < _ /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!k. Bq root k ==> on k /\ _` (drule_then strip_assume_tac) >>
  asm "old_booleans" (drule_then strip_assume_tac) >>
  qpat_assum `!k. on k ==> _` (drule_then (fn th => simp[th]))
QED

Resume merge_iszero_branch_actual_root[concrete]:
  `t.as_pc = pcq root /\ LENGTH t.as_stack = hq root` by
    (drule asm_sym_rel_pc >> simp[]) >>
  qpat_x_assum `Slots q _ Vq hq nq tq Bq` mp_tac >>
  simp[Abbr `Slots`] >> disch_then (qspec_then `root` mp_tac) >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `asm_sym_rel q _ t u` (mp_tac o CONJUNCT1 o REWRITE_RULE [asm_sym_rel_def]) >>
  simp[LIST_REL_EL_EQN] >> disch_tac >>
  qpat_x_assum `Just u tq Bq root` mp_tac >>
  simp[Abbr `Just`, Abbr `Shape`] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "tags") (mk_asm "booleans")) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      first_x_assum (drule_then strip_assume_tac) >>
      asm "tags" (drule_then strip_assume_tac) >>
      first_x_assum (qspec_then `k` mp_tac) >> simp[sval_conc_def] >>
      rpt strip_tac >> metis_tac[]) >>
  qx_gen_tac `k` >> disch_tac >>
  asm "booleans" (drule_then strip_assume_tac) >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[sval_conc_def]
QED

Finalise merge_iszero_branch_actual_root
