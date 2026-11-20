Theory staticAbortOptPruneJumpsBypass
Ancestors
  symInstPieces asmSymBridge asmSymSem asmWf stackOpAsmSim
  asmSem asmIR pred_set finite_map list rich_list arithmetic words
  symInstPiecesFacts

Theorem prune_jump_site_bypass:
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
  !Sh. Sh = Shape p cc req pc height need tag boolean ==>
  !target. target = (\x y.
      ?l origin off. tag x 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !b. b = LENGTH pre ==>
  !d. d = (if pc v = b then 0 else 1) ==>
  p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail /\
  asm_static_wf p /\
  (FINITE V /\ {} SUBSET V /\
    (!x:num#num. x IN V ==> ?t. Shape p cc req pc height need tag boolean x t) /\
    (!x. x IN V DIFF {} ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF {} /\ y IN V /\ (rank:(num#num)->num) y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ target x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF {} /\ Shape p cc req pc height need tag boolean x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ Shape p cc req pc height need tag boolean y u))) /\
  v IN V /\ (pc v = b \/ (pc v = b+1 /\ (!l org. tag v 0 = SOME(l,org) ==> l=x))) ==>
  ?z. z IN V /\ pc z = b+2 /\ rank z < rank v /\
      (if pc v = b then
         ?j. j IN V /\ edge v j /\ pc j = b+1 /\ tag j 0 = SOME(x,b) /\ edge j z
       else edge v z /\ (?org. tag v 0 = SOME(x,org))) /\
      height v = height z + d /\
      (!k l org. tag z k = SOME(l,org) ==> tag v (k+d) = SOME(l,org)) /\
      (!k. boolean z k ==> boolean v (k+d)) /\
      (!t. Sh v t ==> Sh z (t with <| as_pc := pc z; as_stack := DROP d t.as_stack |>))
Proof
  (* Keep the shape and flow schemas opaque until projecting their clauses. *)
  map_every (fn name => qx_gen_tac name >>
    disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def] o
      CONV_RULE (RAND_CONV (REDEPTH_CONV Unwind.UNWIND_FORALL_CONV))))
    [`Shape`,`Flow`,`Sh`,`target`,`b`,`d`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
  qpat_x_assum `FINITE V /\ _` mp_tac >>
  simp[Abbr `target`, DIFF_EMPTY, NoAsms] >>
  disch_then strip_assume_tac >>
  `b < LENGTH p /\ b+1 < LENGTH p /\ b+2 < LENGTH p /\
   EL b p = AsmPushLabel x /\ EL (b+1) p = AsmOp "JUMP" /\
   EL (b+2) p = AsmLabel x`
    by (simp[Abbr `b`, EL_APPEND_EQN] >> EVAL_TAC) >>
  `INDEX_OF (AsmLabel x) p = SOME (b+2)` by
    (irule symInstPiecesFactsTheory.asm_unique_label_index >> fs[asm_static_wf_def]) >>
  drule_all asm_static_wf_code_label >> strip_tac >>
  `!i. i IN V /\ (pc i = b \/ pc i = b+1) ==> ?j. edge i j`
    by suspend "progress" >>
  `!i j. edge i j /\ pc i = b ==>
     j IN V /\ rank j < rank i /\ pc j = b+1 /\
     height j = height i + 1 /\
     (!l org. tag j 0 = SOME(l,org) ==> l=x /\ org=b) /\
     (!k l org. tag j (k+1) = SOME(l,org) ==> tag i k = SOME(l,org)) /\
     (!k. boolean j (k+1) ==> boolean i k)`
    by suspend "push" >>
  `!i j. edge i j /\ pc i = b+1 /\ (!l org. tag i 0 = SOME(l,org) ==> l=x) ==>
     j IN V /\ rank j < rank i /\ pc j = b+2 /\ height i = height j + 1 /\
     (?org. tag i 0 = SOME(x,org)) /\
     (!k l org. tag j k = SOME(l,org) ==> tag i (k+1) = SOME(l,org)) /\
     (!k. boolean j k ==> boolean i (k+1))`
    by suspend "jump" >>
  `?z. z IN V /\ pc z = b+2 /\ rank z < rank v /\
       (if pc v = b then
          ?j. j IN V /\ edge v j /\ pc j = b+1 /\ tag j 0 = SOME(x,b) /\ edge j z
        else edge v z /\ (?org. tag v 0 = SOME(x,org))) /\
       height v = d + height z /\
       (!k l org. tag z k = SOME(l,org) ==> tag v (d+k) = SOME(l,org)) /\
       (!k. boolean z k ==> boolean v (d+k))`
    by suspend "path" >>
  qexists_tac `z` >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >> suspend "shape"
QED

Resume prune_jump_site_bypass[progress]:
  qx_gen_tac `i` >> strip_tac >>
  qpat_assum `!i. i IN V ==> ?t. Shape _ _ _ _ _ _ _ _ i t`
    (qspec_then `i` (drule_then (qx_choose_then `t` assume_tac))) >>
  `t.as_pc = pc i` by
    (qpat_assum `Shape _ _ _ _ _ _ _ _ i t` mp_tac >>
     simp[Abbr `Shape`, NoAsms]) >>
  qpat_assum `!i t. i IN V /\ Shape _ _ _ _ _ _ _ _ i t ==> _`
    (qspecl_then [`i`,`t`] mp_tac) >>
  (impl_tac >- simp[IgnAsm `p = _`]) >>
  (disch_then (DISJ_CASES_THEN2 mp_tac (qx_choose_then `j` strip_assume_tac))
   >- (pure_rewrite_tac[numLib.num_CONV ``1:num``, asm_steps_def] >>
       simp[asm_step_jump, IgnAsm `p = _`] >>
       simp[asm_jump_def, asm_step_def, IgnAsm `p = _`] >>
       Cases_on `t.as_stack` >> simp[IgnAsm `p = _`] >>
       rename1 `t.as_stack = a::stk` >>
       Cases_on `FLOOKUP (build_offset_to_pc p) (w2n a)` >> simp[IgnAsm `p = _`])
   >> qexists_tac `j` >> first_assum ACCEPT_TAC)
QED

Resume prune_jump_site_bypass[push]:
  map_every qx_gen_tac [`i`,`j`] >> strip_tac >>
  qpat_x_assum `!a b. edge a b ==> _`
    (qspecl_then [`i`,`j`] (drule_then strip_assume_tac)) >>
  `pc j = b+1` by
    (qpat_x_assum `if EL (pc i) p = _ then _ else _` mp_tac >>
     simp[IgnAsm `p = _`]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `_ p pc height tag boolean i j` mp_tac >>
  simp[SimpLHS, Abbr `Flow`, LET_THM, IgnAsm `p = _`] >>
  disch_then strip_assume_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every qx_gen_tac [`l`,`org`] >> disch_tac >>
      qpat_x_assum `!k l org. tag j k = SOME(l,org) ==> _`
        (qspecl_then [`0`,`l`,`org`] (drule_then mp_tac)) >>
      simp[NoAsms] >> metis_tac[]) >>
  conj_tac
  >- (map_every qx_gen_tac [`k`,`l`,`org`] >> disch_tac >>
      qpat_x_assum `!k l org. tag j k = SOME(l,org) ==> _`
        (qspecl_then [`k+1`,`l`,`org`] (drule_then mp_tac)) >>
      simp[NoAsms, ADD_SUB] >> disch_then strip_assume_tac) >>
  qx_gen_tac `k` >> disch_tac >>
  qpat_x_assum `!k. boolean j k ==> _` (qspec_then `k+1` (drule_then mp_tac)) >>
  simp[NoAsms, ADD_SUB] >> disch_then strip_assume_tac
QED

Resume prune_jump_site_bypass[jump]:
  map_every qx_gen_tac [`i`,`j`] >> strip_tac >>
  qpat_x_assum `!a b. edge a b ==> _`
    (qspecl_then [`i`,`j`] (drule_then strip_assume_tac)) >>
  `EL (pc i) p = AsmOp "JUMP"` by
    (qpat_assum `pc i = b+1` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `EL (pc i) p = AsmOp "JUMP"` (fn fetch =>
    qpat_x_assum `if EL (pc i) p = _ then _ else _`
      (mp_tac o REWRITE_RULE [fetch])) >>
  disch_then (qx_choose_then `l` (qx_choose_then `org`
    (qx_choose_then `destoff` strip_assume_tac))) >>
  qpat_x_assum `!l org. tag i 0 = SOME(l,org) ==> l=x`
    (qspecl_then [`l`,`org`] (drule_then SUBST_ALL_TAC)) >>
  `pc j = b+2` by metis_tac[optionTheory.SOME_11] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  `ALOOKUP dup_table "JUMP" = NONE /\ ALOOKUP swap_table "JUMP" = NONE /\
   asm_op_arity "JUMP" = 1` by EVAL_TAC >>
  qpat_x_assum `_ p pc height tag boolean i j` mp_tac >>
  qpat_assum `p❲pc i❳ = AsmOp "JUMP"` (fn fetch =>
  qpat_assum `ALOOKUP dup_table "JUMP" = NONE` (fn dup =>
  qpat_assum `ALOOKUP swap_table "JUMP" = NONE` (fn swap =>
  qpat_assum `asm_op_arity "JUMP" = 1` (fn arity =>
    simp[NoAsms, SimpLHS, Abbr `Flow`, LET_THM, fetch, dup, swap, arity])))) >>
  disch_then strip_assume_tac >>
  `height j + 1 - height i = 0` by
    (qpat_assum `height j + 1 <= height i` mp_tac >> decide_tac) >>
  (conj_tac >- (qexists_tac `org` >> first_assum ACCEPT_TAC)) >>
  conj_tac
  >- (map_every qx_gen_tac [`k`,`lab`,`o1`] >> disch_tac >>
      qpat_x_assum `!k l org. tag j k = SOME(l,org) ==> _`
        (qspecl_then [`k`,`lab`,`o1`] (drule_then mp_tac)) >>
      qpat_assum `height j + 1 - height i = 0` (fn hz => simp[NoAsms, hz]) >>
      disch_then strip_assume_tac) >>
  qx_gen_tac `k` >> disch_tac >>
  qpat_x_assum `!k. boolean j k ==> _` (qspec_then `k` (drule_then mp_tac)) >>
  qpat_assum `height j + 1 - height i = 0` (fn hz => simp[NoAsms, hz]) >>
  disch_then strip_assume_tac
QED

Resume prune_jump_site_bypass[path]:
  qpat_x_assum `pc v = b \/ _` (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
  >- (qpat_assum `!i. i IN V /\ _ ==> ?j. edge i j` (qspec_then `v` mp_tac) >>
      (impl_tac >- ((conj_tac >- first_assum ACCEPT_TAC) >> disj1_tac >>
                    first_assum ACCEPT_TAC)) >>
      disch_then (qx_choose_then `j` assume_tac) >>
      qpat_x_assum `!i j. edge i j /\ pc i = b ==> _`
        (qspecl_then [`v`,`j`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then strip_assume_tac >>
      qpat_x_assum `!i. i IN V /\ _ ==> ?j. edge i j` (qspec_then `j` mp_tac) >>
      (impl_tac >- ((conj_tac >- first_assum ACCEPT_TAC) >> disj2_tac >>
                    first_assum ACCEPT_TAC)) >>
      disch_then (qx_choose_then `z` assume_tac) >>
      `!l org. tag j 0 = SOME(l,org) ==> l=x` by
        (rpt gen_tac >> disch_tac >>
         qpat_assum `!l org. tag j 0 = SOME(l,org) ==> _`
           (qspecl_then [`l`,`org`] (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
      qpat_x_assum `!i j. edge i j /\ pc i = b+1 /\ _ ==> _`
        (qspecl_then [`j`,`z`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then strip_assume_tac >>
      `tag j 0 = SOME(x,b)` by metis_tac[] >>
      qexists_tac `z` >>
      qpat_assum `pc v = b` (fn hv => simp[NoAsms, Abbr `d`, hv]) >>
      ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
      (conj_tac >- (Q_TAC (TRANS_TAC arithmeticTheory.LESS_TRANS) `rank j` >>
                    conj_tac >> first_assum ACCEPT_TAC)) >>
      (conj_tac >- (qexists_tac `j` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      (conj_tac >- (qpat_assum `height j = height v + 1` mp_tac >>
                    qpat_assum `height j = height z + 1` mp_tac >> decide_tac)) >>
      conj_tac >> rpt gen_tac >> disch_tac >> metis_tac[])
  >> qpat_x_assum `!i. i IN V /\ _ ==> ?j. edge i j` (qspec_then `v` mp_tac) >>
  (impl_tac >- ((conj_tac >- first_assum ACCEPT_TAC) >> disj2_tac >>
                first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `z` assume_tac) >>
  qpat_x_assum `!i j. edge i j /\ pc i = b+1 /\ _ ==> _`
    (qspecl_then [`v`,`z`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then strip_assume_tac >>
  qexists_tac `z` >>
  qpat_assum `pc v = b+1` (fn hv => simp[NoAsms, Abbr `d`, hv, ADD_COMM]) >>
  asm_rewrite_tac[] >> metis_tac[ADD_COMM]
QED

Resume prune_jump_site_bypass[shape]:
  (* An inhabitant of z supplies its bounds and static requirement. *)
  qpat_assum `!i. i IN V ==> ?t. Shape _ _ _ _ _ _ _ _ i t`
    (qspec_then `z` (drule_then (qx_choose_then `tz` mp_tac))) >>
  simp[NoAsms, Abbr `Shape`] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `need z ==> cc.cc_static` by
    (qpat_assum `tz.as_call_ctx = cc` (fn hc =>
       qpat_assum `need z ==> tz.as_call_ctx.cc_static`
         (ACCEPT_TAC o REWRITE_RULE [hc]))) >>
  qx_gen_tac `t` >>
  simp[NoAsms, Abbr `Sh`, LENGTH_DROP] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH t.as_stack = d + height z` by
    (qpat_assum `LENGTH t.as_stack = height v` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!k. k < height z ==> EL k (DROP d t.as_stack) = EL (d+k) t.as_stack` by
    (qx_gen_tac `k` >> disch_tac >>
     qpat_assum `LENGTH t.as_stack = d + height z` (fn hs =>
       qpat_assum `k < height z` (fn hk =>
         simp[NoAsms, listTheory.EL_DROP, ADD_COMM, hs, hk]))) >>
  qpat_assum `height v = d + height z` (fn hs =>
  qpat_assum `t.as_call_ctx = cc` (fn hc =>
  qpat_assum `t.as_requests = req` (fn hr =>
  qpat_assum `need z ==> cc.cc_static` (fn ht =>
    simp[NoAsms, hs, hc, hr, ht, ADD_SUB2])))) >>
  conj_tac
  >- (map_every qx_gen_tac [`k`,`l`,`org`] >> disch_tac >>
      `k < height z` by
        (qpat_assum `!k l org. tag z k = SOME(l,org) ==> k < height z /\ _`
          (qspecl_then [`k`,`l`,`org`] (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
      `tag v (d+k) = SOME(l,org)` by
        (qpat_assum `!k l org. tag z k = SOME(l,org) ==> tag v _ = _`
          (qspecl_then [`k`,`l`,`org`] (drule_then ACCEPT_TAC))) >>
      qpat_assum `!k. k < height z ==> EL k (DROP d t.as_stack) = _`
        (qspec_then `k` (drule_then SUBST1_TAC)) >>
      qpat_assum `!k l org. tag v k = SOME(l,org) ==> k < height v /\ _`
        (qspecl_then [`d+k`,`l`,`org`] (drule_then (mp_tac o CONJUNCT2))) >>
      qpat_assum `k < height z` (fn hk => simp[NoAsms, hk])) >>
  qx_gen_tac `k` >> disch_tac >>
  `k < height z` by
    (qpat_assum `!k. boolean z k ==> k < height z /\ _`
      (qspec_then `k` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  `boolean v (d+k)` by
    (qpat_assum `!k. boolean z k ==> boolean v _`
      (qspec_then `k` (drule_then ACCEPT_TAC))) >>
  qpat_assum `!k. k < height z ==> EL k (DROP d t.as_stack) = _`
    (qspec_then `k` (drule_then SUBST1_TAC)) >>
  qpat_assum `!k. boolean v k ==> k < height v /\ _`
    (qspec_then `d+k` (drule_then (mp_tac o CONJUNCT2))) >>
  qpat_assum `k < height z` (fn hk => simp[NoAsms, hk])
QED

Finalise prune_jump_site_bypass
