(* Uniform source continuation through the erased ISZERO instructions. *)
Theory staticAbortOptMergeIszeroLive
Ancestors
  stackOpAsmSim stackOpSim asmSem asmSymSem asmOptimizer alist pred_set rich_list

Triviality fetched_iszero:
  t.as_pc < LENGTH p /\ EL t.as_pc p = AsmOp "ISZERO" ==>
  asm_steps lo o2pc p 1 t =
    case t.as_stack of
      [] => AsmError "stack underflow"
    | w::stk => AsmOK
        (t with <|as_pc := t.as_pc+1; as_stack := b2w (w=0w)::stk|>)
Proof
  strip_tac >> Cases_on `t.as_stack` >>
  rewrite_tac[numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_iszero, asm_unop_def, asm_next_def,
       asm_state_fupdcanon]
QED

Triviality iszero_flow_table:
  ALOOKUP dup_table "ISZERO" = NONE /\ ALOOKUP swap_table "ISZERO" = NONE /\
  asm_op_arity "ISZERO" = 1
Proof
  EVAL_TAC
QED

Triviality fetch_iszero_tail:
  0 < k ==> EL k (a::stk) = EL k (b::stk)
Proof
  simp[rich_listTheory.EL_CONS]
QED

Theorem merge_iszero_pending_root_contraction:
!p cc req V rank pc height need tag boolean edge v d.
!Shape. Shape =
  (\p cc req pc height need tag boolean i (t:asm_state).
    t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need i ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest.
         FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\
         FLOOKUP (build_offset_to_pc p) off = SOME dest /\
         EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
!Flow. Flow =
  (\p pc height tag boolean (x:num#num) (y:num#num).
  !hi. hi = height x ==>
  !hj. hj = height y ==>
  !ins. ins = EL (pc x) p ==>
  !inherit. inherit =
    (\(src:num -> num option)
      (fresh:num -> (string#num)option) (bnew:num -> bool).
      (!k l origin. tag y k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
         ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
      (!k. boolean y k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
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
!Open. Open =
  (\p cc req (V:(num#num)->bool) X rank pc height need
    (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) edge.
  !S. S = Shape p cc req pc height need tag boolean ==>
  !target. target = (\x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ target x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF X /\ S x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ S y u))) ==>
!Reach. Reach = (\(edge:(num#num)->(num#num)->bool) e x.
  ?n (path:num->num#num).
    path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) ==>
!LiveShape. LiveShape = Shape p cc req pc height need tag boolean ==>
Open p cc req V {} rank pc height need tag boolean edge /\ v IN V /\
(d=1 \/ d=2) /\ asm_block_at p (pc v) (REPLICATE d (AsmOp "ISZERO")) ==>
?z. z IN V /\ Reach edge v z /\ rank z < rank v /\
    pc z=pc v+d /\ height z=height v /\ tag z 0=NONE /\
    (!k l o'. tag z k=SOME(l,o') ==> 0<k /\ tag v k=SOME(l,o')) /\
    (!k. 0<k /\ boolean z k ==> boolean v k) /\
    (!t. LiveShape v t ==> ?w stk. t.as_stack=w::stk /\
      !u. u = t with <|as_pc := pc v+d;
                      as_stack := FUNPOW (\a. b2w (a=0w)) d w :: stk|> ==>
      asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p d t = AsmOK u /\ LiveShape z u) /\
    (!live_set. live_set = {a | a IN V /\ Reach edge z a} ==>
     !live_edge. live_edge = (\a b. a IN live_set /\ edge a b) ==>
     z IN live_set /\ Open p cc req live_set {} rank pc height need tag boolean live_edge /\
     (!a. a IN live_set ==> Reach live_edge z a))
Proof
  ntac 13 gen_tac >>
  map_every (fn q => qx_gen_tac q >>
    disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]))
    [`Shape`,`Flow`,`Open`,`Reach`,`LiveShape`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  qpat_assum `Abbrev (Open = _)` (fn openth =>
    qpat_assum `Abbrev (LiveShape = _)` (fn shth =>
      qpat_assum `Open p cc req V {} rank pc height need tag boolean edge`
        (strip_assume_tac o SRULE[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] shth)] o
          CONV_RULE (REDEPTH_CONV (BETA_CONV ORELSEC HO_REWR_CONV UNWIND_FORALL_THM2)) o
          PURE_REWRITE_RULE[REWRITE_RULE[markerTheory.Abbrev_def] openth]))) >>
  `!x. x IN V /\ EL (pc x) p = AsmOp "ISZERO" ==>
     ?y. edge x y /\ y IN V /\ rank y < rank x /\
         pc y = pc x+1 /\ height y = height x /\ tag y 0 = NONE /\
         (!k l o'. tag y k = SOME(l,o') ==> 0<k /\ tag x k = SOME(l,o')) /\
         (!k. 0<k /\ boolean y k ==> boolean x k) /\
         (!t. LiveShape x t ==> ?w stk. t.as_stack = w::stk /\
           let u = t with <|as_pc := pc x+1; as_stack := b2w (w=0w)::stk|> in
           asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u /\ LiveShape y u)`
    by (suspend "hop") >>
  `?z. z IN V /\ Reach edge v z /\ rank z < rank v /\
       pc z=pc v+d /\ height z=height v /\ tag z 0=NONE /\
       (!k l o'. tag z k=SOME(l,o') ==> 0<k /\ tag v k=SOME(l,o')) /\
       (!k. 0<k /\ boolean z k ==> boolean v k) /\
       (!t. LiveShape v t ==> ?w stk. t.as_stack=w::stk /\
         !u. u = t with <|as_pc := pc v+d;
                         as_stack := FUNPOW (\a. b2w (a=0w)) d w :: stk|> ==>
         asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p d t = AsmOK u /\ LiveShape z u)`
    by (suspend "contract") >>
  qexists `z` >> rpt (conj_tac >- (first_assum ACCEPT_TAC)) >>
  suspend "restrict"
QED

Resume merge_iszero_pending_root_contraction[hop]:
  qx_gen_tac `x` >> strip_tac >>
  `pc x < LENGTH p` by metis_tac[] >>
  `?s. LiveShape x s` by metis_tac[] >>
  `s.as_pc = pc x /\ LENGTH s.as_stack = height x` by fs[Abbr `LiveShape`, Abbr `Shape`] >>
  qpat_x_assum `!x t. x IN V /\ _ ==> _` (qspecl_then [`x`,`s`] mp_tac) >>
  Cases_on `s.as_stack` >- simp[fetched_iszero] >>
  simp[fetched_iszero] >> strip_tac >>
  rename1 `edge x y` >>
  `height y = height x /\ (need y ==> cc.cc_static)` by
    (qpat_assum `LiveShape y _` mp_tac >>
     qpat_assum `LiveShape x s` mp_tac >>
     simp[Abbr `LiveShape`, Abbr `Shape`] >> rpt strip_tac >> gvs[]) >>
  qpat_assum `!x y. edge x y ==> _`
    (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >>
  `pc y = pc x+1` by
    (qpat_assum `LiveShape y _` mp_tac >>
     simp[Abbr `LiveShape`, Abbr `Shape`] >> gvs[]) >>
  `0 < height x` by fs[] >>
  `(!k l o'. tag y k = SOME(l,o') ==> 0<k /\ tag x k = SOME(l,o')) /\
   (!k. 0<k /\ boolean y k ==> boolean x k)` by
    (qpat_assum `Abbrev (Flow = _)` (fn flow =>
       qpat_assum `EL (pc x) p = AsmOp "ISZERO"` (fn inst =>
         qpat_assum `height y = height x` (fn height_eq =>
           qpat_x_assum `Flow p pc height tag boolean x y`
             (strip_assume_tac o SRULE[inst, height_eq, iszero_flow_table,
                DECIDE ``!h:num. h+1-h=1``] o
              CONV_RULE (REDEPTH_CONV (BETA_CONV ORELSEC HO_REWR_CONV UNWIND_FORALL_THM2)) o
              PURE_REWRITE_RULE[REWRITE_RULE[markerTheory.Abbrev_def] flow])))) >>
     conj_tac
     >- (map_every qx_gen_tac [`k`,`l`,`orig`] >> disch_tac >>
         qpat_x_assum `!k l origin. tag y k = SOME(l,origin) ==> _ /\ _`
           (qspecl_then [`k`,`l`,`orig`] mp_tac) >>
         Cases_on `k=0` >> simp[DECIDE ``!k:num. k<>0 ==> k-1+1=k``]) >>
     qx_gen_tac `k` >> strip_tac >>
     qpat_x_assum `!k. boolean y k ==> _ /\ _` (qspec_then `k` mp_tac) >>
     simp[DECIDE ``!k:num. 0<k ==> ~(k<1) /\ k-1+1=k``,
          DECIDE ``!k:num. k<>0 ==> 0<k``]) >>
  `tag y 0 = NONE` by
    (Cases_on `tag y 0` >> simp[] >> rename1 `tag y 0 = SOME lab` >>
     Cases_on `lab` >> metis_tac[DECIDE ``~(0n<0)``]) >>
  qexists `y` >> simp[] >>
  suspend "uniform"
QED

Resume merge_iszero_pending_root_contraction[uniform]:
  qx_gen_tac `st` >> disch_tac >>
  qpat_x_assum `LiveShape x st` mp_tac >>
  simp[Abbr `LiveShape`, Abbr `Shape`] >> strip_tac >>
  Cases_on `st.as_stack` >- gvs[] >>
  rename1 `st.as_stack = w::stk` >>
  `SUC (LENGTH stk) = height x` by fs[] >>
  qexistsl [`w`,`stk`] >> simp[fetched_iszero] >>
  conj_tac
  >- (map_every qx_gen_tac [`k`,`l`,`orig`] >> disch_tac >>
      qpat_assum `!k l o'. tag y k = SOME(l,o') ==> _`
        (qspecl_then [`k`,`l`,`orig`] (drule_then strip_assume_tac)) >>
      `EL k (b2w (w=0w)::stk) = EL k (w::stk)` by
        (irule fetch_iszero_tail >> simp[]) >>
      pop_assum SUBST1_TAC >>
      qpat_assum `!k l origin. tag x k = SOME(l,origin) ==> _`
        (qspecl_then [`k`,`l`,`orig`] (drule_then mp_tac)) >>
      simp[]) >>
  qx_gen_tac `k` >> disch_tac >> Cases_on `k=0`
  >- (gvs[] >> Cases_on `w=0w` >> simp[]) >>
  `0<k` by decide_tac >>
  qpat_assum `!k. 0<k /\ boolean y k ==> boolean x k`
    (qspec_then `k` (fn th => `boolean x k` by (irule th >> simp[]))) >>
  `EL k (b2w (w=0w)::stk) = EL k (w::stk)` by
    (irule fetch_iszero_tail >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qpat_assum `!k. boolean x k ==> _` (qspec_then `k` (drule_then mp_tac)) >>
  simp[]
QED

Resume merge_iszero_pending_root_contraction[contract]:
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  `EL (pc v) p = AsmOp "ISZERO" /\
   (d=2 ==> EL (pc v+1) p = AsmOp "ISZERO")` by
    ((qpat_x_assum `d = 1 \/ d = 2` strip_assume_tac >>
     qpat_assum `asm_block_at p (pc v) _` mp_tac >>
     simp[EVAL ``REPLICATE 1 (AsmOp "ISZERO")``,
          EVAL ``REPLICATE 2 (AsmOp "ISZERO")``, asm_block_at_cons] >> (gvs[EVAL ``REPLICATE 1 (AsmOp "ISZERO")``, EVAL ``REPLICATE 2 (AsmOp "ISZERO")``, asm_block_at_cons]))) >>
  qpat_assum `!x. x IN V /\ EL (pc x) p = _ ==> _`
    (qspec_then `v` mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `y` strip_assume_tac) >>
  qpat_x_assum `d = 1 \/ d = 2` strip_assume_tac
  >- (qexists `y` >> simp[] >>
      `Reach edge v y` by
        (simp[Abbr `Reach`] >> qexistsl [`1`,`\k. if k=0 then v else y`] >>
         simp[DECIDE ``!k:num. k<1 <=> k=0``]) >>
      simp[] >>
      qpat_assum `!t. LiveShape v t ==> _`
        (ACCEPT_TAC o SRULE[LET_THM, asm_state_fupdcanon])) >>
  qpat_x_assum `!x. x IN V /\ EL (pc x) p = _ ==> _`
    (qspec_then `y` mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `z` strip_assume_tac) >>
  `Reach edge v z` by
    (simp[Abbr `Reach`] >> qexistsl [`2`,`\k. if k=0 then v else if k=1 then y else z`] >>
     simp[] >> rpt strip_tac >> `k=0 \/ k=1` by decide_tac >> fs[]) >>
  `rank z < rank v` by
    (irule ratTheory.RAT_LES_TRANS >> qexists `rank y` >> simp[]) >>
  qexists `z` >> simp[arithmeticTheory.ADD_ASSOC, arithmeticTheory.FUNPOW_2] >>
  qx_gen_tac `st` >> disch_tac >>
  qpat_assum `!t. LiveShape v t ==> _`
    (qspec_then `st` (drule_then (strip_assume_tac o SRULE[LET_THM, asm_state_fupdcanon]))) >>
  rename1 `st.as_stack = w::stk` >>
  qmatch_asmsub_abbrev_tac `LiveShape y mid` >>
  `mid.as_stack = b2w (w=0w)::stk` by simp[Abbr `mid`] >>
  qpat_assum `!t. LiveShape y t ==> _`
    (qspec_then `mid` (drule_then (strip_assume_tac o SRULE[LET_THM, asm_state_fupdcanon]))) >>
  qexistsl [`w`,`stk`] >>
  qpat_assum `asm_steps _ _ p 1 st = AsmOK mid`
    (mp_then Any (qspec_then `1` mp_tac) asm_steps_add_ok) >>
  gvs[Abbr `mid`, asm_state_fupdcanon_comp, arithmeticTheory.ADD_ASSOC]
QED

Resume merge_iszero_pending_root_contraction[restrict]:
  map_every (fn q => qx_gen_tac q >>
    disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]))
    [`live_set`,`live_edge`] >>
  `!a. a IN live_set <=> a IN V /\ Reach edge z a` by simp[Abbr `live_set`] >>
  `live_set SUBSET V` by simp[SUBSET_DEF] >>
  `!a b. a IN live_set /\ edge a b ==> b IN live_set` by
    (map_every qx_gen_tac [`a`,`b`] >> strip_tac >>
     `b IN V` by
       (qpat_assum `!x y. edge x y ==> _`
          (qspecl_then [`a`,`b`] (drule_then strip_assume_tac)) >> simp[]) >>
     `Reach edge z a` by metis_tac[] >>
     qpat_assum `Abbrev (Reach = _)` (fn rth =>
       qpat_x_assum `Reach edge z a`
         (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac) o
          SRULE [REWRITE_RULE [markerTheory.Abbrev_def] rth])) >>
     simp[Abbr `Reach`] >>
     qexistsl [`SUC n`,`\k. if k = SUC n then b else path k`] >>
     simp[] >> qx_gen_tac `k` >> disch_tac >> Cases_on `k=n`
     >- (`n <> SUC n` by decide_tac >> simp[]) >>
     `k < n /\ k <> SUC n` by decide_tac >> simp[]) >>
  conj_tac >- (simp[Abbr `Reach`] >> qexistsl [`0`,`\k. z`] >> simp[]) >>
  conj_tac
  >- (qpat_assum `Abbrev (Open = _)` (fn openth =>
        qpat_assum `Abbrev (LiveShape = _)` (fn shth =>
          qpat_assum `Abbrev (live_edge = _)` (fn eth =>
            PURE_REWRITE_TAC [REWRITE_RULE[markerTheory.Abbrev_def] openth] >>
            CONV_TAC (REDEPTH_CONV (BETA_CONV ORELSEC HO_REWR_CONV UNWIND_FORALL_THM2)) >>
            SIMP_TAC bool_ss [GSYM (REWRITE_RULE[markerTheory.Abbrev_def] shth),
              REWRITE_RULE[markerTheory.Abbrev_def] eth, DIFF_EMPTY, EMPTY_SUBSET]))) >>
      conj_tac >- metis_tac[SUBSET_FINITE_I] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      conj_tac
      >- (map_every qx_gen_tac [`x`,`y`] >> strip_tac >>
          `y IN live_set` by metis_tac[] >>
          qpat_assum `!x y. edge x y ==> _`
            (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >>
          rpt (conj_tac >- (first_assum ACCEPT_TAC)) >> first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`x`,`t`] >> strip_tac >>
      `x IN V` by metis_tac[] >>
      qpat_assum `!x t. x IN V /\ LiveShape x t ==> _`
        (qspecl_then [`x`,`t`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  qx_gen_tac `a` >> disch_tac >>
  `Reach edge z a` by metis_tac[] >>
  qpat_assum `Abbrev (Reach = _)` (fn rth =>
    qpat_x_assum `Reach edge z a`
      (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac) o
       SRULE [REWRITE_RULE [markerTheory.Abbrev_def] rth])) >>
  simp[Abbr `Reach`] >> qexistsl [`n`,`path`] >>
  simp[Abbr `live_edge`] >> qx_gen_tac `k` >> disch_tac >>
  `edge (path k) (path (SUC k))` by metis_tac[] >>
  `path k IN V` by
    (qpat_assum `!x y. edge x y ==> _`
      (qspecl_then [`path k`,`path (SUC k)`] (drule_then strip_assume_tac)) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`k`,`path`] >> simp[] >> qx_gen_tac `j` >> disch_tac >>
  `j < n` by decide_tac >>
  qpat_assum `!i. i < n ==> edge (path i) (path (SUC i))`
    (qspec_then `j` (drule_then ACCEPT_TAC))
QED

Finalise merge_iszero_pending_root_contraction
