(* A continuation link preserves the complete instruction interfaces. *)
Theory staticAbortRowsSplice
Ancestors
  staticAbortOpenFragmentSplice staticAbortLinkedArmInterfaces
  staticAbortStraight asmSem asmIR asmSymSem alist finite_map words list
  arithmetic pred_set pair

val structural_splice =
  Q.SPECL [`\i:'a. \t:asm_state. T`, `\i:'a. T`, `\i j:'a. T`,
           `\t u:asm_state. T`, `\t:asm_state. T`] open_fragment_splice
  |> SIMP_RULE bool_ss [LET_THM];

Theorem bounded_static_rows_splice:
!p cc f V1 X2 e1 e2 z r1 r2
 (I1:(num#num)->(num#num#bool#(num->(string#num)option)#(num->bool))) I2 R1 R2.
let Flow =
  \p pc height tag boolean (x:num#num) (y:num#num).
  let hi = height x; hj = height y; ins = EL (pc x) p in
  let inherit =
    \(src:num -> num option)
      (fresh:num -> (string#num)option) (bnew:num -> bool).
      (!k l origin. tag y k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
         ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
      (!k. boolean y k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))
  in
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
        (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
  | AsmPushOfst l d =>
      hj = hi+1 /\
      inherit (\k. if k=0 then NONE else SOME(k-1))
        (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
  | AsmOp name =>
      (case ALOOKUP dup_table name of
         SOME n =>
           n < hi /\ hj = hi+1 /\
           inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
       | NONE =>
         case ALOOKUP swap_table name of
           SOME n =>
             0 < n /\ n < hi /\ hj = hi /\
             inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
               (\k. NONE) (\k. F)
         | NONE =>
           let a = asm_op_arity name; m = hj + asm_op_arity name - hi in
           a <= hi /\ hj = m+(hi-a) /\
           ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
           inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
             (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
               !t u. LENGTH t.as_stack=hi /\
                 asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                   ins t = AsmOK u ==>
                 (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
  | _ => F
in
let Reach = \(edge:(num#num)->(num#num)->bool) e x.
  ?n (path:num->num#num).
    path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))
in
let lo = SND(compute_label_offsets p); invmap = build_offset_to_pc p in
let Check = \pc h tag arm legal dead.
  let fall = \c. c = pc + 1 in
  let target = \c.
    ?l origin off. tag 0 = SOME(l,origin) /\ FLOOKUP lo l = SOME off /\
      off < dimword(:256) /\ FLOOKUP invmap off = SOME c in
  let next = \n. arm fall n /\ legal fall n in
  let untagged = \a. !k. k<a ==> tag k=NONE in
  let stop = \a. a<=h /\ untagged a /\ dead in
  pc < LENGTH p /\
  case EL pc p of
    AsmLabel l => next h
  | AsmPush bs => next (h+1)
  | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ next (h+1)
  | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ next (h+1)
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
                  2<=h /\ tag 1=NONE /\ arm fall (h-2) /\ arm target (h-2) /\
                  legal (\c. fall c \/ target c) (h-2)
               else
                  ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                      untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
  | _ => F
in
let Valid = \h need tag boolean.
  (need ==> cc.cc_static) /\
  (!k. boolean k ==> k < h /\ tag k=NONE) /\
  (!k l origin. tag k = SOME(l,origin) ==>
     k < h /\ origin < LENGTH p /\
     (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
     ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                FLOOKUP invmap off = SOME dest)
in
let Rows = \V X (rank:num#num->num) pc height need tag boolean edge.
  (!x. x IN V ==> Valid (height x) (need x) (tag x) (boolean x)) /\
  (!x y. edge x y ==>
    x IN V DIFF X /\ y IN V /\ rank y < rank x /\
    Flow p pc height tag boolean x y) /\
  (!x. x IN V DIFF X ==>
    Check (pc x) (height x) (tag x)
      (\P n. ?y. edge x y /\ P (pc y) /\ height y = n)
      (\P n. !y. edge x y ==> P (pc y) /\ height y = n)
      (!y. ~edge x y))
in
let B = \V X e r I R.
  FINITE V /\ X SUBSET V /\ e IN V /\
  (!x. x IN V ==> FST x=f /\ Reach R e x) /\
  Rows V X r (\x. FST (I x)) (\x. FST (SND (I x)))
    (\x. FST (SND (SND (I x)))) (\x. FST (SND (SND (SND (I x)))))
    (\x. SND (SND (SND (SND (I x))))) R
in
let L = \x:num#num. (f,2*SND x); D = \x:num#num. (f,2*SND x+1) in
let d = \x. if x=z then D e2 else L x in
let U = IMAGE L (V1 DELETE z) UNION IMAGE D V2;
    Y = IMAGE D X2;
    e = d e1;
    E = \a b. (?x y. R1 x y /\ a=L x /\ b=d y) \/
              (?x y. R2 x y /\ a=D x /\ b=D y)
in
B V1 {z} e1 r1 I1 R1 /\ B V2 X2 e2 r2 I2 R2 /\ I1 z=I2 e2 ==>
?r I. B U Y e r I E /\ I e=I1 e1 /\
  (!x. x IN V1 DELETE z ==> I(L x)=I1 x) /\
  (!x. x IN V2 ==> I(D x)=I2 x)
Proof
  rpt gen_tac >> rpt BasicProvers.LET_ELIM_TAC >>
  fs[Abbr `B`, Abbr `Rows`] >> rpt strip_tac >>
  `?(r:(num#num)->num) I. (FINITE U /\ Y SUBSET U /\
    (!x y. E x y ==> x IN U DIFF Y /\ y IN U /\ r y < r x)) /\
    e IN U /\ I e=I1 e1 /\
    (!x. x IN V1 DELETE z ==> I(L x)=I1 x) /\
    (!x. x IN V2 ==> I(D x)=I2 x) /\
    (!x. x IN U ==> FST x=f /\ Reach E e x)` by suspend "geometry" >>
  rename1 `iface e = I1 e1` >> qexistsl [`r`,`iface`] >> simp[] >>
  suspend "transport"
QED

Resume bounded_static_rows_splice[geometry]:
  Q.ISPECL_THEN [`V1`,`V2`,`X2`,`e1`,`e2`,`z`,`r1`,`r2`,
                 `I1`,`I2`,`R1`,`R2`,`f`] mp_tac structural_splice >>
  (impl_tac >-
    (fs[Abbr `Reach`] >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
     FIRST [qpat_assum `!x y. R1 x y ==> _` drule,
            qpat_assum `!x y. R2 x y ==> _` drule] >> simp[])) >>
  disch_then (qx_choose_then `rr` (qx_choose_then `iface`
    (EVERY o map assume_tac o CONJUNCTS))) >>
  qexistsl [`rr`,`iface`] >>
  gns[Abbr `U`, Abbr `Y`, Abbr `e`, Abbr `E`, Abbr `d`, Abbr `L`, Abbr `D`, Abbr `Reach`] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume bounded_static_rows_splice[transport]:
  `!x y. L x <> D y` by
    (simp[Abbr `L`, Abbr `D`] >> POP_ASSUM_LIST (K all_tac) >>
     rpt gen_tac >> strip_tac >>
     pop_assum (mp_tac o AP_TERM ``EVEN``) >> simp[EVEN_MULT, EVEN_ADD]) >>
  `!x y. FST x=f /\ FST y=f ==>
     ((L x=L y <=> x=y) /\ (D x=D y <=> x=y))` by
    (rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >>
     simp[Abbr `L`, Abbr `D`]) >>
  `!x y. R1 x y ==> x IN V1 DELETE z /\ y IN V1` by
    (qpat_assum `!x y. R1 x y ==> _` mp_tac >> simp[] >> metis_tac[]) >>
  `!x y. R2 x y ==> x IN V2 DIFF X2 /\ y IN V2` by
    (qpat_assum `!x y. R2 x y ==> _` mp_tac >> simp[] >> metis_tac[]) >>
  `!x. x IN V1 ==> iface (d x) = I1 x` by
    (rpt strip_tac >> Cases_on `x=z` >> simp[Abbr `d`]) >>
  `!x. x IN U DIFF Y ==>
    (?a. a IN V1 DELETE z /\ x=L a) \/ (?a. a IN V2 DIFF X2 /\ x=D a)` by
    (simp[Abbr `U`, Abbr `Y`, IN_IMAGE] >> metis_tac[]) >>
  conj_tac >- suspend "valid" >>
  conj_tac >- suspend "flow" >>
  suspend "rows"
QED

Resume bounded_static_rows_splice[valid]:
  simp[Abbr `U`, IN_IMAGE] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume bounded_static_rows_splice[flow]:
  rpt gen_tac >> disch_tac >>
  `x IN U DIFF Y /\ y IN U /\ r y<r x` by metis_tac[] >> simp[] >>
  qpat_x_assum `E x y` mp_tac >> simp[Abbr `E`] >> strip_tac >> gvs[IN_DIFF] >>
  (FIRST
    [rename1 `R1 a b` >>
     qpat_assum `!x y. R1 x y ==> _ /\ _ /\ _ /\ Flow _ _ _ _ _ x y` drule >>
     strip_tac >>
     `iface (L a) = I1 a /\ iface (d b) = I1 b` by simp[],
     rename1 `R2 a b` >>
     qpat_assum `!x y. R2 x y ==> _ /\ _ /\ _ /\ Flow _ _ _ _ _ x y` drule >>
     strip_tac >>
     `iface (D a) = I2 a /\ iface (D b) = I2 b` by simp[]]) >>
  qpat_x_assum `Flow _ _ _ _ _ a b` EQ_MP_TAC >>
  qunabbrev_tac `Flow` >> BETA_TAC >>
  qpat_assum `iface _ = _ a` SUBST1_TAC >>
  qpat_assum `iface _ = _ b` SUBST1_TAC >> (simp[])
QED

Resume bounded_static_rows_splice[rows]:
  rpt (qpat_x_assum `!a b. _ a b ==> _ /\ _ /\ _ /\ Flow _ _ _ _ _ a b` kall_tac) >>
  `L z NOTIN U` by (simp[Abbr `U`, IN_IMAGE] >> metis_tac[]) >>
  qabbrev_tac `pre = \a b. (?x y. R1 x y /\ a=L x /\ b=L y) \/
                            (?x y. R2 x y /\ a=D x /\ b=D y)` >>
  qabbrev_tac `J = \a. if a=L z then I1 z else iface a` >>
  qabbrev_tac `dest = \a. if a=L z then D e2 else a` >>
  `!a b. pre a b ==> a IN U /\ b IN (U UNION {L z})` by suspend "pre_geom" >>
  `!a b. R1 a b ==> dest (L b) = d b` by
    (rpt strip_tac >> Cases_on `b=z` >> simp[Abbr `dest`, Abbr `d`] >> metis_tac[]) >>
  `!b. dest (D b) = D b` by (simp[Abbr `dest`] >> metis_tac[]) >>
  `!a b. E a b <=> a IN U /\ ?c. pre a c /\ b=dest c` by suspend "redirect" >>
  suspend "arm_images"
QED

Resume bounded_static_rows_splice[pre_geom]:
  rpt gen_tac >> simp[Abbr `pre`] >> strip_tac
  >- (rename1 `R1 x y` >>
      qpat_assum `!a b. R1 a b ==> _` drule >>
      strip_tac >>
      `L x IN IMAGE L (V1 DELETE z)` by ((simp[IN_IMAGE] >> qexists `x` >> simp[] >> (gvs[IN_IMAGE]))) >>
      conj_tac >- (asm_rewrite_tac[] >> simp_tac bool_ss [Abbr `U`, IN_UNION] >>
                  asm_rewrite_tac[]) >>
      Cases_on `y=z` >- simp[IN_UNION] >>
      `L y IN IMAGE L (V1 DELETE z)` by (simp[IN_IMAGE] >> qexists `y` >> simp[]) >>
      asm_rewrite_tac[] >> simp_tac bool_ss [Abbr `U`, IN_UNION, IN_SING] >>
      asm_rewrite_tac[]) >>
  rename1 `R2 x y` >> qpat_assum `!a b. R2 a b ==> _` drule >>
  simp[IN_DIFF] >> strip_tac >>
  `D x IN IMAGE D V2` by (simp[IN_IMAGE] >> qexists `x` >> simp[]) >>
  `D y IN IMAGE D V2` by (simp[IN_IMAGE] >> qexists `y` >> simp[]) >>
  simp[Abbr `U`]
QED

Resume bounded_static_rows_splice[redirect]:
  rpt gen_tac >> eq_tac
  >- (strip_tac >> conj_tac
      >- (qpat_assum `!x y. E x y ==> _` drule >> simp[IN_DIFF]) >>
      qpat_x_assum `E a b` mp_tac >> simp[Abbr `E`] >> strip_tac >> gvs[]
      >- (rename1 `R1 x y` >> qexists `L y` >> simp[Abbr `pre`] >> metis_tac[]) >>
      rename1 `R2 x y` >> qexists `D y` >> simp[Abbr `pre`] >> metis_tac[]) >>
  simp[Abbr `pre`] >> strip_tac >> gvs[Abbr `E`] >> metis_tac[]
QED

Resume bounded_static_rows_splice[arm_images]:
  `!x. x IN U ==> J x = iface x` by
    (rpt strip_tac >> `x <> L z` by (strip_tac >> fs[]) >> simp[Abbr `J`]) >>
  `!x v. x IN U ==> ((?y. pre x y /\ J y = v) <=> (?y. E x y /\ iface y = v))`
    by suspend "relink" >>
  suspend "check_transport"
QED

Resume bounded_static_rows_splice[relink]:
  `(U UNION {L z}) DIFF {L z} = U` by (simp[EXTENSION, IN_DIFF] >> metis_tac[]) >>
  `D e2 IN U` by (simp[Abbr `U`, IN_IMAGE] >> metis_tac[]) >>
  `D e2 <> L z` by metis_tac[] >>
  `J (D e2) = J (L z)` by simp[Abbr `J`] >>
  `{x | x IN U /\ ?n (path:num->num#num). path 0=e /\ path n=x /\
                   !k. k<n ==> E (path k) (path (SUC k))} = U` by
    (qpat_x_assum `!a b. E a b <=> _` kall_tac >>
     simp[EXTENSION] >> gen_tac >> eq_tac >> simp[] >> strip_tac >>
     qpat_assum `!x. x IN U ==> FST x=f /\ _` drule >> simp[Abbr `Reach`]) >>
  Q.ISPECL_THEN [`U UNION {L z}`, `{L z}`, `e`, `pre`, `\a:num#num. D e2`, `J`]
    mp_tac linked_reachable_arm_interfaces >>
  simp_tac bool_ss [LET_THM, IN_SING] >>
  qpat_assum `(U UNION {L z}) DIFF {L z} = U` (rewrite_tac o single) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!a b. (a IN U /\ ?c. pre a c /\ b = if c=L z then D e2 else c) <=> E a b` by
    ((qpat_x_assum `!a b. E a b <=> _` mp_tac >> simp[Abbr `dest`, EQ_IMP_THM] >> (metis_tac[Abbr `dest`, EQ_IMP_THM]))) >>
  qpat_x_assum `!a b. E a b <=> _` kall_tac >>
  qpat_x_assum `!a b. (a IN U /\ _) <=> E a b` (rewrite_tac o single) >>
  qpat_assum `{x | x IN U /\ ?n path. _} = U` (rewrite_tac o single) >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!x v. x IN U ==> _` (qspecl_then [`x`,`v`] mp_tac) >>
  csimp[] >>
  `!y. E x y ==> y IN U` by (rpt strip_tac >>
     qpat_assum `!a b. E a b ==> _` drule >> simp[]) >>
  metis_tac[]
QED

Resume bounded_static_rows_splice[check_transport]:
  `!x P. x IN U ==>
     ((?y. pre x y /\ P (J y)) <=> (?y. E x y /\ P (iface y)))` by
    (qpat_x_assum `!x v. x IN U ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qabbrev_tac `C = \(K:(num#num)->(num#num#bool#(num->(string#num)option)#(num->bool))) R x.
    Check (FST (K x)) (FST (SND (K x)))
      (FST (SND (SND (SND (K x)))))
      (\P n. ?y. R x y /\ P (FST (K y)) /\ FST (SND (K y)) = n)
      (\P n. !y. R x y ==> P (FST (K y)) /\ FST (SND (K y)) = n)
      (!y. ~R x y)` >>
  `!K K' R R' a a'. K a = K' a' /\
     (!P. (?y. R a y /\ P (K y)) <=> (?y. R' a' y /\ P (K' y))) ==>
     (C K R a <=> C K' R' a')` by suspend "check_congruence" >>
  rpt gen_tac >> disch_tac >>
  `x IN U` by fs[IN_DIFF] >>
  `C J pre x` by suspend "check_pre" >>
  `C iface E x` suffices_by simp[Abbr `C`] >>
  qpat_assum `!K K' R R' a a'. _ ==> (C K R a <=> C K' R' a')`
    (qspecl_then [`J`,`iface`,`pre`,`E`,`x`,`x`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- simp[] >>
     qpat_assum `!a P. a IN U ==> _` (qspec_then `x` mp_tac) >> simp[])) >>
  disch_then (irule o iffLR) >> first_assum ACCEPT_TAC
QED

Resume bounded_static_rows_splice[check_congruence]:
  map_every qx_gen_tac [`iL`,`iR`,`R`,`R'`,`a`,`a'`] >> strip_tac >>
  `!P n. (?y. R a y /\ P (FST (iL y)) /\ FST (SND (iL y)) = n) <=>
         (?y. R' a' y /\ P (FST (iR y)) /\ FST (SND (iR y)) = n)` by
    (rpt gen_tac >> first_x_assum (qspec_then `\v. P (FST v) /\ FST (SND v) = n` mp_tac) >>
     simp[CONJ_ASSOC]) >>
  `!P n. (!y. R a y ==> P (FST (iL y)) /\ FST (SND (iL y)) = n) <=>
         (!y. R' a' y ==> P (FST (iR y)) /\ FST (SND (iR y)) = n)` by
    (rpt gen_tac >> qpat_assum `!P. (?y. R a y /\ P (iL y)) <=> _`
       (qspec_then `\v. ~(P (FST v) /\ FST (SND v) = n)` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> BETA_TAC >> metis_tac[]) >>
  `(!y. ~R a y) <=> (!y. ~R' a' y)` by
    (qpat_assum `!P. (?y. R a y /\ P (iL y)) <=> _` (qspec_then `\v. T` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> BETA_TAC >> metis_tac[]) >>
  simp[Abbr `C`] >>
  ` (\P n. ?y. R a y /\ P (FST (iL y)) /\ FST (SND (iL y)) = n) =
    (\P n. ?y. R' a' y /\ P (FST (iR y)) /\ FST (SND (iR y)) = n)` by
    simp[FUN_EQ_THM] >>
  ` (\P n. !y. R a y ==> P (FST (iL y)) /\ FST (SND (iL y)) = n) =
    (\P n. !y. R' a' y ==> P (FST (iR y)) /\ FST (SND (iR y)) = n)` by
    simp[FUN_EQ_THM] >> simp[]
QED

Resume bounded_static_rows_splice[check_pre]:
  `!b. b IN V1 ==> J (L b) = I1 b` by
    (rpt strip_tac >> Cases_on `b=z` >- simp[Abbr `J`] >>
     `L b <> L z` by metis_tac[] >> simp[Abbr `J`]) >>
  `!b. b IN V2 ==> J (D b) = I2 b` by
    (rpt strip_tac >> `D b <> L z` by metis_tac[] >> simp[Abbr `J`]) >>
  `!a y. a IN V1 ==> (pre (L a) y <=> ?b. R1 a b /\ y=L b)` by suspend "pre_left" >>
  `!a y. a IN V2 ==> (pre (D a) y <=> ?b. R2 a b /\ y=D b)` by suspend "pre_right" >>
  `!a P. a IN V1 ==>
     ((?y. R1 a y /\ P (I1 y)) <=> (?y. pre (L a) y /\ P (J y)))` by
    (rpt gen_tac >> strip_tac >> simp[] >> metis_tac[]) >>
  `!a P. a IN V2 ==>
     ((?y. R2 a y /\ P (I2 y)) <=> (?y. pre (D a) y /\ P (J y)))` by
    (rpt gen_tac >> strip_tac >> simp[] >> metis_tac[]) >>
  `x IN U DIFF Y` by simp[IN_DIFF] >>
  qpat_assum `!a. a IN U DIFF Y ==> _` (drule_then strip_assume_tac) >>
  FIRST [qpat_x_assum `x = L a` SUBST_ALL_TAC,
         qpat_x_assum `x = D a` SUBST_ALL_TAC] >>
  RULE_ASSUM_TAC (REWRITE_RULE [IN_DELETE, IN_DIFF]) >>
  rpt (qpat_x_assum `_ /\ _` strip_assume_tac)
  >- (`C I1 R1 a` by simp[Abbr `C`] >>
      qpat_assum `!K K' R R' a a'. _ ==> (C K R a <=> C K' R' a')`
        (qspecl_then [`I1`,`J`,`R1`,`pre`,`a`,`L a`] mp_tac) >>
      (impl_tac >-
        (conj_tac >- simp[] >>
         qpat_assum `!b P. b IN V1 ==> ((?y. R1 b y /\ P (I1 y)) <=> _)`
           (qspec_then `a` mp_tac) >> simp[])) >>
      disch_then (irule o iffLR) >> first_assum ACCEPT_TAC) >>
  `C I2 R2 a` by simp[Abbr `C`] >>
  qpat_assum `!K K' R R' a a'. _ ==> (C K R a <=> C K' R' a')`
    (qspecl_then [`I2`,`J`,`R2`,`pre`,`a`,`D a`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- simp[] >>
     qpat_assum `!b P. b IN V2 ==> ((?y. R2 b y /\ P (I2 y)) <=> _)`
       (qspec_then `a` mp_tac) >> simp[])) >>
  disch_then (irule o iffLR) >> first_assum ACCEPT_TAC
QED

Resume bounded_static_rows_splice[pre_left]:
  rpt gen_tac >> strip_tac >> simp[Abbr `pre`] >>
  reverse eq_tac >- metis_tac[] >>
  strip_tac >> rename1 `R1 b c` >>
  qpat_assum `!u v. R1 u v ==> u IN V1 DELETE z /\ v IN V1`
    (drule_then strip_assume_tac o REWRITE_RULE [IN_DELETE]) >>
  `FST a = f` by simp[] >>
  `FST b = f` by simp[] >>
  `a = b` by (qpat_x_assum `L a = L b` mp_tac >> simp[]) >>
  qpat_x_assum `a = b` SUBST_ALL_TAC >> qexists `c` >> simp[]
QED

Resume bounded_static_rows_splice[pre_right]:
  rpt gen_tac >> strip_tac >> simp[Abbr `pre`] >>
  reverse eq_tac >- metis_tac[] >>
  strip_tac >> rename1 `R2 b c` >>
  qpat_assum `!u v. R2 u v ==> u IN V2 DIFF X2 /\ v IN V2`
    (drule_then strip_assume_tac o REWRITE_RULE [IN_DIFF]) >>
  `FST a = f` by simp[] >>
  `FST b = f` by simp[] >>
  `a = b` by (qpat_x_assum `D a = D b` mp_tac >> simp[]) >>
  qpat_x_assum `a = b` SUBST_ALL_TAC >> qexists `c` >> simp[]
QED

Finalise bounded_static_rows_splice
