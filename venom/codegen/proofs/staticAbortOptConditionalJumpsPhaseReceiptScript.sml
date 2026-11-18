Theory staticAbortOptConditionalJumpsPhaseReceipt
Ancestors
  staticAbortOptConditionalJumpsArms staticAbortOptConditionalJumpsTable
  staticAbortStraight asmSplice asmIR asmSem finite_map pred_set list
  arithmetic words pair

Theorem conditional_jump_phase_receipt:
  let b = LENGTH pre in
  let r = splice_pc b 4 3 in
  let C = \p l d. ?off. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
                       off<dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME d in
  let Producer = \p l i. i<LENGTH p /\
       (EL i p=AsmPushLabel l \/ EL i p=AsmPushOfst l 0) /\ ?d. C p l d in
  let Slots = \p h n tg bl.
    (n ==> cc.cc_static) /\ (!k. bl k ==> k<h /\ tg k=NONE) /\
    (!k l i. tg k=SOME(l,i) ==> k<h /\ Producer p l i) in
  let Flow = \p pc height tag boolean (u:num#num) (v:num#num).
    let hi=height u; hj=height v; ins=EL (pc u) p in
    let inherit = \(src:num->num option) (fresh:num->(string#num)option) bnew.
      (!k l i. tag v k=SOME(l,i) ==> k<hj /\
        (fresh k=SOME(l,i) \/ ?a. src k=SOME a /\ a<hi /\ tag u a=SOME(l,i))) /\
      (!k. boolean v k ==> k<hj /\ (bnew k \/ ?a. src k=SOME a /\ a<hi /\ boolean u a)) in
    case ins of
      AsmLabel l => hj=hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t s. asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                     (AsmPush bs) t=AsmOK s ==> EL 0 s.as_stack=0w \/ EL 0 s.as_stack=1w)
    | AsmPushLabel l => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmPushOfst l d => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n<hi /\ hj=hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<hi /\ hj=hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
           | NONE => let a=asm_op_arity name; m=hj+asm_op_arity name-hi in
               a<=hi /\ hj=m+(hi-a) /\ ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t s. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p) ins t=AsmOK s ==>
                       EL 0 s.as_stack=0w \/ EL 0 s.as_stack=1w))
    | _ => F in
  let Target = \p tg d. ?l i. tg 0=SOME(l,i) /\ C p l d in
  let Legal = \p i tg j.
    if EL i p=AsmOp "JUMP" then Target p tg j else
    if EL i p=AsmOp "JUMPI" then j=i+1 \/ Target p tg j else j=i+1 in
  let Row = \p i h tg (edge:(num#num)->bool) pc height.
    let arm = \P n. ?v. edge v /\ P (pc v) /\ height v=n in
    let legal = \P n. !v. edge v ==> P (pc v) /\ height v=n in
    let fall = \d. d=i+1; taken = Target p tg in
    let next = \n. arm fall n /\ legal fall n in
    let untagged = \a. !k. k<a ==> tg k=NONE in
    let stop = \a. a<=h /\ untagged a /\ !v. ~edge v in
    case EL i p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmOp name =>
        if name="INVALID" then stop 0 else if name="REVERT" then stop 2 else
        if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] then
          cc.cc_static /\ stop (asm_op_arity name) else
        (case ALOOKUP dup_table name of
           SOME n => n<h /\ next (h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<h /\ next h
           | NONE => if name="JUMP" then 1<=h /\ arm taken (h-1) /\ legal taken (h-1) else
                     if name="JUMPI" then 2<=h /\ tg 1=NONE /\ arm fall (h-2) /\
                       arm taken (h-2) /\ legal (\d. fall d \/ taken d) (h-2) else
                     ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                       untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F in
  let raw = \k. case tag z0 k of NONE => tag z1 k | SOME u => SOME u in
  let UB = \k. boolean z0 k \/ boolean z1 k in
  let Ii = (0:num,0:num) in
  let Ip = (1:num,0:num) in
  let Ij = (2:num,0:num) in
  let L = (3:num,0:num) in
  let E0 = (4:num,0:num) in
  let E1 = (5:num,0:num) in
  let W = {Ii;Ip;Ij;L;E0;E1} in
  let pcq = \u. if u=Ii then b else if u=Ip then b+1 else
          if u=Ij then b+2 else if u=L then b+3 else
          if u=E0 then r (pc z0) else r (pc z1) in
  let hq = \u. if u=Ii \/ u=Ip then H else if u=Ij then H+1 else H-1 in
  let nq = \u. (u=E0 /\ need z0) \/ (u=E1 /\ need z1) in
  let tq = \(rho:string->num->num) u k.
    let translate = OPTION_MAP (\(l,i). (l,rho l i)) in
    let U = \k. translate (raw k) in
    if u=Ii \/ u=Ip then (if k=0 then NONE else U (k-1)) else
    if u=Ij then (if k=0 then SOME(x,b+1) else
                 if k=1 then NONE else U (k-2)) else
    if u=E0 then translate (tag z0 k) else translate (tag z1 k) in
  let bq = \u k. if u=Ii then k<>0 /\ UB (k-1) else
          if u=Ip then k=0 \/ UB (k-1) else
          if u=Ij then k=1 \/ (2<=k /\ UB (k-2)) else
          if u=E0 then boolean z0 k else boolean z1 k in
  let edges = \u y. (u=Ii /\ y=Ip) \/ (u=Ip /\ y=Ij) \/
          (u=Ij /\ y=E0) \/ (u=Ij /\ y=L) \/ (u=L /\ y=E1) in
  let Named = \rho:string->num->num.
    (!u. u IN W ==> (nq u ==> cc.cc_static) /\
       (!k. bq u k ==> k<hq u /\ tq rho u k=NONE) /\
       (!k l i. tq rho u k=SOME(l,i) ==> k<hq u)) /\
    (!u. u IN {Ii;Ip;Ij;L} ==> pcq u < LENGTH q) /\
    EL (pcq Ii) q = AsmOp "ISZERO" /\ static_abort_straight "ISZERO" 1 /\
    EL (pcq Ip) q = AsmPushLabel x /\ EL (pcq Ij) q = AsmOp "JUMPI" /\
    EL (pcq L) q = AsmLabel c /\
    (!u y. edges u y ==> Flow q pcq hq (tq rho) bq u y) /\
    (C q x (r (pc z0)) /\
     (!z k l i. (z=z0 \/ z=z1) /\ tag z k=SOME(l,i) ==> Producer q l (rho l i)) ==>
     (!u k l i. u IN W /\ tq rho u k=SOME(l,i) ==> Producer q l i) /\
     IS_SOME (FLOOKUP (SND(compute_label_offsets q)) x) /\
     edges Ii Ip /\ pcq Ip = pcq Ii+1 /\ edges Ip Ij /\ pcq Ij = pcq Ip+1 /\
     edges Ij E0 /\ tq rho Ij 0=SOME(x,pcq Ip) /\ C q x (pcq E0) /\
     edges Ij L /\ pcq L = pcq Ij+1 /\
     edges L E1 /\ pcq E1 = pcq L+1 /\ pcq E1 = b+4) in
  let vp = \(i:num). if i<4 then b+i else if i=4 then r(pc z0) else r(pc z1) in
  let vh = \(i:num). if i<2 then H else if i=2 then H+1 else H-1 in
  let vn = \(i:num). (i=4 /\ need z0) \/ (i=5 /\ need z1) in
  let vraw = \(i:num) k.
    if i<2 then (if k=0 then NONE else raw (k-1)) else
    if i=2 then (if k=0 then SOME(x,b+2) else if k=1 then NONE else raw (k-2))
    else if i=4 then tag z0 k else tag z1 k in
  let vb = \(i:num) k.
    if i=0 then k<>0 /\ UB (k-1) else if i=1 then k=0 \/ UB (k-1) else
    if i=2 then k=1 \/ (2<=k /\ UB (k-2)) else
    if i=4 then boolean z0 k else boolean z1 k in
  let VE = \(i:num) j. (i<3 /\ j=i+1) \/ (i=2 /\ j=4) \/ (i=3 /\ j=5) in
  let P = \v:num#num. vp (FST v) in
  let J = \v:num#num. vh (FST v) in
  let Tags = \rho (v:num#num) k. if FST v=2 /\ k=0 then SOME(x,b+1) else
                            OPTION_MAP (\(l,i). (l,rho l i)) (vraw (FST v) k) in
  let B = \v:num#num. vb (FST v) in
  let Phase = \rho.
    (!i j. VE i j ==> Flow q P J (Tags rho) B (i,0) (j,0)) /\
    (C q x (r(pc z0)) /\
     (!v k l i. (v=z0 \/ v=z1) /\ tag v k=SOME(l,i) ==> Producer q l (rho l i)) ==>
     (!i. i<4 ==> Slots q (vh i) (vn i) (Tags rho (i,0)) (B (i,0))) /\
     (!i. i<4 ==> vp i<LENGTH q /\ Row q (vp i) (vh i) (Tags rho (i,0))
                           (\v. VE i (FST v)) P J) /\
     (!i j. VE i j ==> Legal q (vp i) (Tags rho (i,0)) (vp j))) in
  0<H /\ (!rho. Named rho) ==> !phase_rho. Phase phase_rho
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `!rho. Named rho` (qspec_then `phase_rho` mp_tac) >>
  simp[Abbr `Named`] >> strip_tac >>
  `!i. pcq (i,0) = P (i,0) /\ hq (i,0) = J (i,0) /\
       nq (i,0) = vn i /\ tq phase_rho (i,0) = Tags phase_rho (i,0) /\ bq (i,0) = B (i,0)` by
    (gen_tac >>
     `i=0 \/ i=1 \/ i=2 \/ i=3 \/ i=4 \/ i=5 \/ 5<i` by decide_tac >>
     simp[Abbr `pcq`, Abbr `hq`, Abbr `nq`, Abbr `tq`, Abbr `bq`,
          Abbr `P`, Abbr `J`, Abbr `Tags`, Abbr `B`, Abbr `vp`, Abbr `vh`,
          Abbr `vn`, Abbr `vb`, Abbr `vraw`, Abbr `Ii`, Abbr `Ip`,
          Abbr `Ij`, Abbr `L`, Abbr `E0`, Abbr `E1`, FUN_EQ_THM] >>
     rpt gen_tac >> IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> simp[]) >>
  `!i j. VE i j ==> edges (i,0) (j,0)` by
    (simp[Abbr `VE`, Abbr `edges`, Abbr `Ii`, Abbr `Ip`, Abbr `Ij`,
          Abbr `L`, Abbr `E0`, Abbr `E1`] >> decide_tac) >>
  simp[Abbr `Phase`] >> conj_tac
  >- (rpt strip_tac >> `edges (i,0) (j,0)` by metis_tac[] >>
      qpat_x_assum `!u y. edges u y ==> Flow q pcq hq (tq phase_rho) bq u y`
        (qspecl_then [`(i,0)`, `(j,0)`] mp_tac) >>
      simp[Abbr `Flow`, markerTheory.Abbrev_def]) >>
  disch_tac >> qpat_x_assum `C q x _ /\ _ ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!i. i<4 ==> (i,0) IN W'` by
    (simp[Abbr `W'`, Abbr `Ii`, Abbr `Ip`, Abbr `Ij`, Abbr `L`, Abbr `E0`, Abbr `E1`] >>
     decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> `(i,0) IN W'` by metis_tac[] >>
      qpat_x_assum `!u. u IN W' ==> _` (qspec_then `(i,0)` mp_tac) >>
      simp[Abbr `Slots`, Abbr `J`] >> metis_tac[]) >>
  `!i. i<4 ==> pcq (i,0) < LENGTH q` by
    (rpt strip_tac >>
     qpat_assum `!u. u=Ii \/ u=Ip \/ u=Ij \/ u=L ==> pcq u < LENGTH q` irule >>
     simp[Abbr `Ii`, Abbr `Ip`, Abbr `Ij`, Abbr `L`] >> decide_tac) >>
  `!i. i<4 ==> vp i < LENGTH q` by
    (rpt strip_tac >>
     qpat_assum `!i. i<4 ==> pcq (i,0) < LENGTH q` (qspec_then `i` mp_tac) >>
     gvs[Abbr `P`]) >>
  `EL b q=AsmOp "ISZERO" /\ EL (b+1) q=AsmPushLabel x /\
   EL (b+2) q=AsmOp "JUMPI" /\ EL (b+3) q=AsmLabel c /\
   C q x (r(pc z0)) /\ r(pc z1)=b+4` by
    fs[Abbr `pcq`, Abbr `Ii`, Abbr `Ip`, Abbr `Ij`, Abbr `L`, Abbr `E0`, Abbr `E1`] >>
  `ALOOKUP dup_table "ISZERO"=NONE /\ ALOOKUP swap_table "ISZERO"=NONE /\
   ALOOKUP dup_table "JUMPI"=NONE /\ ALOOKUP swap_table "JUMPI"=NONE /\
   asm_op_arity "ISZERO"=1` by EVAL_TAC >>
  `Tags phase_rho (0,0) 0=NONE /\ Tags phase_rho (2,0) 1=NONE /\
   Tags phase_rho (2,0) 0=SOME (x,b+1)` by simp[NoAsms, Abbr `Tags`, Abbr `vraw`] >>
  `!i j. VE i j ==> (i=0 /\ j=1) \/ (i=1 /\ j=2) \/
                   (i=2 /\ (j=3 \/ j=4)) \/ (i=3 /\ j=5)` by
    (simp[Abbr `VE`] >> decide_tac) >>
  reverse conj_tac
  >- (rpt gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
      simp[Abbr `vp`, Abbr `Legal`, Abbr `Target`] >>
      gvs[]) >>
  rpt strip_tac
  >- metis_tac[] >>
  `i=0 \/ i=1 \/ i=2 \/ i=3` by decide_tac >>
  pop_assum SUBST1_TAC >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`r (pc z1) = b+4`, `C q x (r (pc z0))`,
     `asm_op_arity "ISZERO" = 1`, `static_abort_straight "ISZERO" 1`,
     `IS_SOME (FLOOKUP (SND (compute_label_offsets q)) x)`,
     `EL b q = AsmOp "ISZERO"`, `EL (b+1) q = AsmPushLabel x`,
     `EL (b+2) q = AsmOp "JUMPI"`, `EL (b+3) q = AsmLabel c`,
     `ALOOKUP dup_table "ISZERO" = NONE`, `ALOOKUP swap_table "ISZERO" = NONE`,
     `ALOOKUP dup_table "JUMPI" = NONE`, `ALOOKUP swap_table "JUMPI" = NONE`,
     `Tags phase_rho (0,0) 0 = NONE`, `Tags phase_rho (2,0) 1 = NONE`,
     `Tags phase_rho (2,0) 0 = SOME (x,b+1)`, `0 < H`] >>
  SIMP_TAC bool_ss [Abbr `Row`, Abbr `vp`, Abbr `vh`] >>
  simp[NoAsms, Abbr `P`, Abbr `J`, Abbr `VE`, Abbr `Target`, EXISTS_PROD, FORALL_PROD] >>
  SIMP_TAC bool_ss [markerTheory.Abbrev_def] >>
  rpt disch_tac
  >- (qexists `1` >> conj_tac >- first_assum ACCEPT_TAC >>
      reverse conj_tac >- rewrite_tac[arithmeticTheory.ADD_SUB] >> rpt strip_tac >>
      `k=0` by simp[] >> asm_rewrite_tac[]) >>
  conj_tac >- (qexists `3` >> simp[]) >>
  conj_tac >- (qexists `4` >> simp[]) >>
  rpt strip_tac >> simp[]
QED
