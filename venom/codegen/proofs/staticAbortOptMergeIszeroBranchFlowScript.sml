(* Flow is checked against the fixed relinked table, one edge at a time. *)
Theory staticAbortOptMergeIszeroBranchFlow
Ancestors
  staticAbortOptMergeIszeroLayout stackOpAsmSim asmOptimizer asmSem
  alist arithmetic finite_map list option pair pred_set words

(* Open one lexical binding in the conclusion without rewriting assumptions. *)
local
  fun use_binding name ttac = FIRST_ASSUM (fn th =>
    let
      val eq = CONV_RULE (REWR_CONV markerTheory.Abbrev_def) th
      val _ = Lib.assert (fn s => s = name) (fst (dest_var (lhs (concl eq))))
    in
      ttac eq
    end)
in
  fun expose_binding name = use_binding name SUBST1_TAC >> BETA_TAC
  fun intro_binding conv name = qx_gen_tac name >>
    disch_then (assume_tac o CONV_RULE
      (RAND_CONV conv THENC REWR_CONV (GSYM markerTheory.Abbrev_def)))
end

Theorem merge_iszero_branch_flow:
  !Inherit. Inherit = (\hi hj (ta:num->(string#num)option) tb ba bb
       (src:num->num option) (newtag:num->(string#num)option) newbool.
    (!k nm org. tb k = SOME(nm,org) ==>
       k < hj /\ (newtag k = SOME(nm,org) \/
          ?j. src k = SOME j /\ j < hi /\ ta j = SOME(nm,org))) /\
    (!k. bb k ==> k < hj /\
       (newbool k \/ ?j. src k = SOME j /\ j < hi /\ ba j))) ==>
  !Flow. Flow = (\p pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==> !hj. hj = height y ==> !ins. ins = EL (pc x) p ==>
    !inherit. inherit = Inherit hi hj (tag x) (tag y) (boolean x) (boolean y) ==>
    case ins of
      AsmLabel nm => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !s u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) s = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
    | AsmPushLabel nm => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(nm,pc x) else NONE) (\k. F)
    | AsmPushOfst nm d => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(nm,pc x) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE =>
           case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==> !m. m = hj + a - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !s u. LENGTH s.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins s = AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !p q pre tail l (V:(num#num)->bool) e c (rank:(num#num)->num)
     pc height tag boolean edge next v.
  !b. b = LENGTH pre ==>
  !keep. keep = (\i. i < b \/ b+2 <= i) ==>
  !f. f = (\i. if i < b then i else i-2) ==>
  !M. M = OPTION_MAP (\(nm,org). (nm,f org)) ==>
  p = pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] ++ tail /\
  q = pre ++ [AsmPushLabel l; AsmOp "JUMPI"] ++ tail /\ asm_static_wf p /\
  e IN V /\ pc e=c /\ v NOTIN V /\
  (!x. x IN V ==> pc x < LENGTH p) /\
  (!x. x IN V /\ pc x=b+3 ==> 2 <= height x) /\
  (!x. x IN V ==>
    (!k nm org. tag x k = SOME(nm,org) ==> k < height x) /\
    (!k. boolean x k ==> k < height x)) /\
  (!x z. edge x z ==> z IN V /\ Flow p pc height tag boolean x z /\
    ((EL (pc x) p <> AsmOp "JUMP" /\ EL (pc x) p <> AsmOp "JUMPI") ==>
       pc z=pc x+1)) /\
  (!x. x IN V ==> next x IN V /\ keep (pc (next x)) /\ height (next x)=height x /\
    (if keep (pc x) then next x=x else pc (next x)=b+2 /\ rank (next x)<rank x) /\
    (!k nm org. 0<k /\ tag (next x) k=SOME(nm,org) ==> tag x k=SOME(nm,org)) /\
    (!k. 0<k /\ boolean (next x) k ==> boolean x k)) /\
  (!x z. x IN V /\ keep(pc x) /\ edge x z /\ pc(next z)=b+3 ==>
    next z=z /\ pc x=b+2) ==>
  !x y. (x=v /\ c=b+3 /\ y=e) \/
        (x IN V /\ keep(pc x) /\ ?z. edge x z /\ y=next z) ==>
    Flow q
      (\x. if x=v then b else f (pc x))
      (\x. if x=v then height e-1 else height x)
      (\x k. if x=v then (if k=0 then NONE else M(tag e (k+1)))
        else if (pc x=b+2 /\ k=0) \/ (pc x=b+3 /\ k=1) then NONE
        else if pc x=b+3 /\ k=0 then SOME(l,b) else M(tag x k))
      (\x k. if x=v then 0<k /\ boolean e (k+1)
        else ~((pc x=b+2 /\ k=0) \/ (pc x=b+3 /\ k<=1)) /\ boolean x k) x y
Proof
  intro_binding ALL_CONV `Inherit` >>
  intro_binding (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) `Flow` >>
  ntac 16 gen_tac >> map_every (intro_binding ALL_CONV) [`b`, `keep`, `f`, `M`] >>
  qmatch_goalsub_abbrev_tac `Flow q pcq _ _ _ _ _` >>
  qmatch_goalsub_abbrev_tac `Flow q pcq hq _ _ _ _` >>
  qmatch_goalsub_abbrev_tac `Flow q pcq hq tq _ _ _` >>
  qmatch_goalsub_abbrev_tac `Flow q pcq hq tq Bq _ _` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EL (b+2) p = AsmPushLabel l /\ EL (b+3) p = AsmOp "JUMPI" /\
   EL b q = AsmPushLabel l` by
    simp[Abbr `b`, EL_APPEND_EQN] >>
  `!i. keep i /\ i < LENGTH p ==> EL (f i) q = EL i p` by suspend "fetch" >>
  `!nm r rpc rh rt rb u w. EL (rpc u) r = AsmPushLabel nm ==>
     (Flow r rpc rh rt rb u w <=> rh w = rh u + 1 /\
       Inherit (rh u) (rh w) (rt u) (rt w) (rb u) (rb w)
         (\k. if k=0 then NONE else SOME(k-1))
         (\k. if k=0 then SOME(nm,rpc u) else NONE) (\k. F))` by suspend "pushrow" >>
  rpt gen_tac >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac)))
  >- suspend "fresh" >>
  `z IN V /\ Flow p pc height tag boolean x z /\
   (pc x=b+2 ==> pc z=b+3)` by
    (qpat_assum `!x z. edge x z ==> _` (qspecl_then [`x`,`z`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
     disch_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> disch_tac >>
     `EL (pc x) p = AsmPushLabel l` by
       (qpat_assum `pc x=b+2` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `(_ /\ _) ==> pc z=pc x+1` mp_tac >> simp[] >> decide_tac) >>
  `y IN V /\ hq x=height x /\ hq y=height z /\
   pcq x=f(pc x) /\ EL (pcq x) q=EL (pc x) p` by
    (qpat_assum `!x. x IN V ==> next x IN V /\ _` (qspec_then `z` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `y IN V /\ x<>v /\ y<>v /\ pc x<LENGTH p` by metis_tac[] >>
     simp[Abbr `pcq`, Abbr `hq`, IgnAsm `p = _`, IgnAsm `q = _`]) >>
  Cases_on `pc x=b+2` >- suspend "push" >>
  suspend "retained"
QED

Resume merge_iszero_branch_flow[fetch]:
  mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"]`,
                  `repl` |-> `[AsmPushLabel l; AsmOp "JUMPI"]`]
      (CONV_RULE (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2))
        merge_iszero_one_canonical_layout)) >>
  simp[NoAsms] >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[Abbr `keep`, Abbr `f`, Abbr `b`] >> first_assum ACCEPT_TAC
QED

Resume merge_iszero_branch_flow[pushrow]:
  rpt gen_tac >> expose_binding "Flow" >>
  disch_then (fn th => simp[NoAsms, LET_THM, th])
QED

Resume merge_iszero_branch_flow[fresh]:
  `pc e=b+3 /\ e<>v /\ 2<=height e` by metis_tac[] >>
  `EL (pcq v) q = AsmPushLabel l /\ pcq v=b /\
   hq v=height e-1 /\ hq e=height e` by
    simp[Abbr `pcq`, Abbr `hq`, IgnAsm `q = _`] >>
  `(!k nm org. tag e k=SOME(nm,org) ==> k<height e) /\
   (!k. boolean e k ==> k<height e)` by
    (qpat_assum `!x. x IN V ==> (!k nm org. _ ==> _) /\ _`
      (qspec_then `e` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  qpat_assum `x = v` SUBST1_TAC >> qpat_assum `y = e` SUBST1_TAC >>
  expose_binding "Flow" >>
  qpat_assum `EL (pcq v) q = AsmPushLabel l`
    (fn th => simp[NoAsms, LET_THM, th]) >>
  expose_binding "Inherit" >>
  simp[Abbr `tq`, Abbr `Bq`, IgnAsm `q = _`, IgnAsm `p = _`] >>
  rpt gen_tac >> Cases_on `k=0` >- simp[] >>
  strip_tac >>
  `k < height e` by
    (Cases_on `tag e k` >> fs[Abbr `M`] >> Cases_on `x'` >> fs[] >> metis_tac[]) >>
  `k-1+1=k /\ 1<k` by decide_tac >>
  fs[]
QED

Resume merge_iszero_branch_flow[push]:
  `pc z=b+3` by simp[] >>
  `keep (pc z)` by simp[Abbr `keep`] >>
  `next z=z` by
    (qpat_assum `!x. x IN V ==> next x IN V /\ _` (qspec_then `z` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (mp_tac o el 4 o CONJUNCTS) >> asm_rewrite_tac[]) >>
  `y=z` by metis_tac[] >> qpat_assum `y=z` SUBST1_TAC >>
  `x<>v /\ z<>v /\ 2<=height z` by metis_tac[] >>
  `pcq x=b` by simp[Abbr `f`] >>
  `EL (pc x) p = AsmPushLabel l` by
    (qpat_assum `pc x=b+2` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `EL (pcq x) q = AsmPushLabel l` by metis_tac[] >>
  qpat_x_assum `Flow p pc height tag boolean x z` mp_tac >>
  expose_binding "Flow" >>
  qpat_assum `EL (pc x) p = AsmPushLabel l` (fn hp =>
    qpat_assum `EL (pcq x) q = AsmPushLabel l` (fn hq =>
      simp[NoAsms, LET_THM, hp, hq])) >>
  expose_binding "Inherit" >>
  `hq z=height z` by simp[Abbr `hq`] >>
  simp[Abbr `tq`, Abbr `Bq`, IgnAsm `p = _`, IgnAsm `q = _`] >>
  strip_tac >> rpt gen_tac >> Cases_on `k=0` >- simp[] >>
  strip_tac >>
  `1<k` by decide_tac >>
  `?nm0 org0. tag z k=SOME(nm0,org0)` by
    (Cases_on `tag z k` >> fs[Abbr `M`] >> Cases_on `x'` >> metis_tac[]) >>
  `k<height x+1 /\ tag x (k-1)=SOME(nm0,org0)` by
    metis_tac[] >>
  fs[]
QED

Resume merge_iszero_branch_flow[retained]:
  `x<>v /\ y<>v` by metis_tac[] >>
  `pc y<>b+3` by metis_tac[] >>
  `!a nm org. M a=SOME(nm,org) ==>
    ?org0. a=SOME(nm,org0) /\ org=f org0` by
    (rpt gen_tac >> Cases_on `a` >> simp[Abbr `M`] >>
     PairCases_on `x'` >> simp[]) >>
  `(!k nm org. tq y k=SOME(nm,org) ==>
     ?org0. tag z k=SOME(nm,org0) /\ org=f org0) /\
   (!k. Bq y k ==> boolean z k)` by suspend "demands" >>
  `!src ft ftq fb fbq.
     (pc x=b+3 ==> !k j. src k=SOME j ==> 1<j) /\
     (!k. ftq k=M (ft k)) /\ (!k. fb k ==> fbq k) /\
     Inherit (height x) (height z) (tag x) (tag z) (boolean x) (boolean z) src ft fb ==>
     Inherit (height x) (height z) (tq x) (tq y) (Bq x) (Bq y) src ftq fbq`
    by suspend "inherit" >>
  pop_assum $ mk_asm "inherit_transport" >>
  suspend "dispatch"
QED

Resume merge_iszero_branch_flow[demands]:
  qpat_assum `!x. x IN V ==> next x IN V /\ _` (qspec_then `z` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `y=z \/ pc y=b+2` by (Cases_on `keep(pc z)` >> fs[] >> metis_tac[]) >>
  simp[Abbr `tq`, Abbr `Bq`] >>
  rpt strip_tac >> `0<k` by decide_tac >> metis_tac[]
QED

Resume merge_iszero_branch_flow[inherit]:
  rpt gen_tac >> expose_binding "Inherit" >> strip_tac >>
  `!k j. src k=SOME j ==> (tq x j=M (tag x j) /\ (Bq x j <=> boolean x j))` by
    (rpt strip_tac >> Cases_on `pc x=b+3` >> simp[Abbr `tq`, Abbr `Bq`] >>
     `1<j` by metis_tac[] >> `j<>0 /\ j<>1 /\ ~(j<=1)` by decide_tac >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `?org0. tag z k=SOME(nm,org0) /\ org=f org0` by metis_tac[] >>
      conj_tac >- metis_tac[] >>
      `ft k=SOME(nm,org0) \/
         (?j. src k=SOME j /\ j<height x /\ tag x j=SOME(nm,org0))` by metis_tac[]
      >- (disj1_tac >> simp[Abbr `M`]) >>
      disj2_tac >> qexists `j` >>
      `tq x j = M (tag x j)` by metis_tac[] >> simp[Abbr `M`]) >>
  rpt strip_tac >>
  `boolean z k` by metis_tac[] >>
  metis_tac[]
QED

Resume merge_iszero_branch_flow[dispatch]:
  `pc x=b+3 ==> EL (pc x) p=AsmOp "JUMPI"` by metis_tac[] >>
  qpat_x_assum `Flow p pc height tag boolean x z` mp_tac >>
  expose_binding "Flow" >>
  qpat_assum `EL (pcq x) q = EL (pc x) p` (fn hf =>
    qpat_assum `hq x=height x` (fn hx =>
      qpat_assum `hq y=height z` (fn hy => simp[NoAsms, LET_THM, hf, hx, hy]))) >>
  Cases_on `EL (pc x) p` >>
  pure_rewrite_tac[TypeBase.case_def_of ``:asm_inst``] >> BETA_TAC >>
  TRY (qmatch_goalsub_rename_tac `F ==> F` >> simp[] >> NO_TAC)
  >- suspend "operator" >>
  qpat_x_assum `pc x=b+3 ==> _` (assume_tac o SRULE []) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  asm "inherit_transport" irule >>
  qpat_assum `Inherit (height x) (height z) (tag x) (tag z) _ _ _ _ _`
    (irule_at Any) >>
  simp[Abbr `M`, COND_RAND] >>
  simp[NoAsms, asm_step_def]
QED

(* With no masked position, inherit the unchanged permutation. *)
val permutation_flow_tac =
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  asm "inherit_transport" irule >>
  qpat_assum `Inherit (height x) (height z) (tag x) (tag z) _ _ _ _ _`
    (irule_at Any) >> simp[Abbr `M`]

Resume merge_iszero_branch_flow[operator]:
  rename1 `EL (pc x) p = AsmOp name` >>
  `pc x=b+3 ==> name="JUMPI"` by
    (qpat_assum `pc x=b+3 ==> AsmOp name = _` mp_tac >> simp[NoAsms]) >>
  `ALOOKUP dup_table "JUMPI" = NONE /\
   ALOOKUP swap_table "JUMPI" = NONE /\ asm_op_arity "JUMPI" = 2` by EVAL_TAC >>
  Cases_on `pc x=b+3`
  >- (qpat_assum `pc x=b+3 ==> name="JUMPI"` drule >>
      disch_then (fn hn =>
        qpat_assum `ALOOKUP dup_table "JUMPI" = NONE` (fn hd =>
          qpat_assum `ALOOKUP swap_table "JUMPI" = NONE` (fn hs =>
            qpat_assum `asm_op_arity "JUMPI" = 2` (fn ha =>
              pure_rewrite_tac[hn, hd, hs, ha,
                TypeBase.case_def_of ``:num option``, LET_THM])))) >>
      BETA_TAC >> suspend "masked_oprow") >>
  Cases_on `ALOOKUP dup_table name` >>
  pure_rewrite_tac[TypeBase.case_def_of ``:num option``, LET_THM] >> BETA_TAC
  >- (Cases_on `ALOOKUP swap_table name` >>
      pure_rewrite_tac[TypeBase.case_def_of ``:num option``, LET_THM] >> BETA_TAC
      >- suspend "oprow" >> permutation_flow_tac) >>
  permutation_flow_tac
QED

Resume merge_iszero_branch_flow[masked_oprow]:
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  asm "inherit_transport" irule >>
  qpat_assum `Inherit (height x) (height z) (tag x) (tag z) _ _ _ _ _`
    (irule_at Any) >> simp[Abbr `M`] >>
  `height z + 2 <= height x` by
    (qpat_assum `_ ==> height z + 2 <= height x` mp_tac >> simp[NoAsms]) >>
  simp[]
QED

Resume merge_iszero_branch_flow[oprow]:
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  asm "inherit_transport" irule >>
  qpat_assum `Inherit (height x) (height z) (tag x) (tag z) _ _ _ _ _`
    (irule_at Any) >> simp[Abbr `M`, IgnAsm `p = _`, IgnAsm `q = _`] >>
  strip_tac >>
  `name <> "JUMP" /\ name <> "JUMPI"` by
    (`~(height z + asm_op_arity name <= height x)` by decide_tac >>
     qpat_assum `_ ==> height z + asm_op_arity name <= height x` mp_tac >>
     simp[DE_MORGAN_THM]) >>
  `!s. asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
         (AsmOp name) s =
       asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
         (AsmOp name) s` by
    (qpat_assum `name <> "JUMP"` (fn hj =>
       qpat_assum `name <> "JUMPI"` (fn hji =>
         simp[NoAsms, asm_step_def, asm_step_op_def, asm_step_control_def, hj, hji]))) >>
  qpat_x_assum `!s. asm_step _ _ _ s = asm_step _ _ _ s` (fn h =>
    qpat_x_assum `!s u. LENGTH s.as_stack = _ /\ _ ==> _` mp_tac >>
    simp[h, IgnAsm `p = _`, IgnAsm `q = _`])
QED

Finalise merge_iszero_branch_flow
