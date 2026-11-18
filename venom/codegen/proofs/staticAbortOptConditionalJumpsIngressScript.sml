Theory staticAbortOptConditionalJumpsIngress
Ancestors
  staticAbortOptConditionalJumpsArms staticAbortOptPruneUnreachableLayout
  asmOpSim stackOpAsmSim asmSplice asmWf asmIR asmSem finite_map pred_set list
  arithmetic words

Theorem conditional_jump_strict_ports:
  let Shape =
    \p cc req pc height need tag boolean i (t:asm_state).
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
         (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))
  in
  let TagFlow = \tag u y hi hj src fresh.
    !k l origin. tag y k = SOME(l,origin) ==>
      k < hj /\ (fresh k = SOME(l,origin) \/
      ?a. src k = SOME a /\ a < hi /\ tag u a = SOME(l,origin)) in
  let Flow =
    \p pc height tag boolean (u:num#num) (y:num#num).
    let hi = height u; hj = height y; ins = EL (pc u) p in
    let inherit =
      \(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        TagFlow tag u y hi hj src fresh /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean u a))
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
          (\k. if k=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc u) else NONE) (\k. F)
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
  let Open =
    \p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need
      (tag:(num#num)->num->(string#num)option)
      (boolean:(num#num)->num->bool) edge.
    let S = Shape p cc req pc height need tag boolean in
    let target = \u y.
      ?l origin off. tag u 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)
    in
      FINITE V /\ X SUBSET V /\
      (!u. u IN V ==> ?t. S u t) /\
      (!u. u IN V DIFF X ==> pc u < LENGTH p) /\
      (!u y. edge u y ==>
         u IN V DIFF X /\ y IN V /\ rank y < rank u /\
         Flow p pc height tag boolean u y /\
         (if EL (pc u) p = AsmOp "JUMP" then target u y
          else if EL (pc u) p = AsmOp "JUMPI"
               then pc y = pc u+1 \/ target u y
          else pc y = pc u+1)) /\
      (!u t. u IN V DIFF X /\ S u t ==>
         (?s. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmRevert s \/
                asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmFault s) /\ s.as_requests=req) \/
         (?y s. edge u y /\
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
              p 1 t = AsmOK s /\ S y s))
  in
  let b = LENGTH pre; r = splice_pc (LENGTH pre) 4 3;
      H = height e - 1;
      C = \s l d. ?off. FLOOKUP (SND(compute_label_offsets s)) l = SOME off /\
                         off < dimword(:256) /\
                         FLOOKUP (build_offset_to_pc s) off = SOME d in
  let Kept = \z. z IN V /\ (pc z < b \/ b+4 <= pc z) in
  let Port = \shift z. Kept z /\ rank z < rank e /\ height z + shift = height e /\
    (!k l i. tag z k = SOME(l,i) ==> tag e (k+shift) = SOME(l,i)) /\
    (!k. boolean z k ==> boolean e (k+shift)) in
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail /\
  asm_static_wf p /\ Open p cc req V {} rank pc height need tag boolean edge /\
  e IN V /\
  (* Only these projections of Rows are needed. *)
  (!u k. u IN V /\ boolean u k ==> tag u k = NONE) /\
  (pc e = b+1 ==> 2 <= height e /\ tag e 1 = NONE /\
                   ?j. edge e j /\ pc j = b+2) /\
  (!u. u IN V /\ pc u = b+2 ==> ?j. edge u j /\ pc j = b+3) /\
  (!u. u IN V /\ pc u = b+3 ==> ?z. edge u z) ==>
  ((pc e = b+2 \/ (pc e = b+3 /\ ?i. tag e 0 = SOME(x,i))) ==>
    ?z. C p x (pc z) /\ Port (if pc e = b+2 then 0 else 1) z) /\
  (pc e = b+1 /\ (?i. tag e 0 = SOME(c,i)) ==>
    0 < H /\ ?z0 z1.
    C p x (pc z0) /\ pc z1 = b+5 /\ Port 2 z0 /\ Port 2 z1 /\
    !rho:string->num->num.
      let raw = \k. case tag z0 k of NONE => tag z1 k | SOME u => SOME u in
      let translate = OPTION_MAP (\(l,i). (l,rho l i)) in
      let U = \k. translate (raw k); UB = \k. boolean z0 k \/ boolean z1 k in
      let I = (0:num,0:num); P = (1,0); J = (2,0); L = (3,0);
          E0 = (4,0); E1 = (5,0) in
      let W = {I;P;J;L;E0;E1};
          pcq = \u. if u=I then b else if u=P then b+1 else
            if u=J then b+2 else if u=L then b+3 else
            if u=E0 then r (pc z0) else r (pc z1);
          hq = \u. if u=I \/ u=P then H else if u=J then H+1 else H-1;
          nq = \u. (u=E0 /\ need z0) \/ (u=E1 /\ need z1);
          rq = \u. if u=I then 4*rank e+3 else if u=P then 4*rank e+2 else
            if u=J then 4*rank e+1 else if u=L then 4*rank e else
            if u=E0 then 4*rank z0+3 else 4*rank z1+3;
          tq = \u k. if u=I \/ u=P then (if k=0 then NONE else U (k-1)) else
            if u=J then (if k=0 then SOME(x,b+1) else
                         if k=1 then NONE else U (k-2)) else
            if u=E0 then translate (tag z0 k) else translate (tag z1 k);
          bq = \u k. if u=I then k<>0 /\ UB (k-1) else
            if u=P then k=0 \/ UB (k-1) else
            if u=J then k=1 \/ (2<=k /\ UB (k-2)) else
            if u=E0 then boolean z0 k else boolean z1 k;
          edges = \u y. (u=I /\ y=P) \/ (u=P /\ y=J) \/
            (u=J /\ y=E0) \/ (u=J /\ y=L) \/ (u=L /\ y=E1) in
      (!k t s. tag z0 k=SOME t /\ tag z1 k=SOME s ==> t=s) /\
      (!k l i. raw k=SOME(l,i) ==> k<H-1 /\ tag e (k+2)=SOME(l,i)) /\
      (!k. UB k ==> k<H-1 /\ boolean e (k+2) /\ U k=NONE) /\
      (!u. u IN W ==> (nq u ==> cc.cc_static) /\
         (!k. bq u k ==> k<hq u /\ tq u k=NONE) /\
         (!k l i. tq u k=SOME(l,i) ==> k<hq u)) /\
      (!u. u IN {I;P;J;L} ==> pcq u < LENGTH q) /\
      EL (pcq I) q = AsmOp "ISZERO" /\ static_abort_straight "ISZERO" 1 /\
      EL (pcq P) q = AsmPushLabel x /\ EL (pcq J) q = AsmOp "JUMPI" /\
      EL (pcq L) q = AsmLabel c /\
      (!u y. edges u y ==> rq y < rq u /\ Flow q pcq hq tq bq u y) /\
      (C q x (r (pc z0)) /\
       (!z k l i. (z=z0 \/ z=z1) /\ tag z k=SOME(l,i) ==>
          rho l i < LENGTH q /\
          (EL (rho l i) q=AsmPushLabel l \/ EL (rho l i) q=AsmPushOfst l 0) /\
          ?d. C q l d) ==>
       (!u k l i. u IN W /\ tq u k=SOME(l,i) ==>
          i < LENGTH q /\
          (EL i q=AsmPushLabel l \/ EL i q=AsmPushOfst l 0) /\ ?d. C q l d) /\
       IS_SOME (FLOOKUP (SND(compute_label_offsets q)) x) /\
       edges I P /\ pcq P = pcq I+1 /\ edges P J /\ pcq J = pcq P+1 /\
       edges J E0 /\ tq J 0=SOME(x,pcq P) /\ C q x (pcq E0) /\
       edges J L /\ pcq L = pcq J+1 /\
       edges L E1 /\ pcq E1 = pcq L+1 /\ pcq E1 = b+4 /\
       (!t w stk. t.as_stack=w::stk ==>
         asm_step (SND(compute_label_offsets q)) (build_offset_to_pc q)
           (EL (pcq I) q) t =
         AsmOK (asm_next (t with as_stack := (if w=0w then 1w else 0w)::stk))) /\
       (!off w stk t.
          FLOOKUP (SND(compute_label_offsets q)) x=SOME off /\
          t.as_pc=pcq J /\ t.as_stack=n2w off::(if w=0w then 1w else 0w)::stk ==>
          asm_step (SND(compute_label_offsets q)) (build_offset_to_pc q)
            (EL (pcq J) q) t =
          AsmOK (t with <|as_pc := if w=0w then pcq E0 else pcq L;
                           as_stack := stk|>))))
Proof
  qmatch_goalsub_abbrev_tac `LET _ Shape` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ TagFlow` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Flow` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Open` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ b` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  ntac 2 (CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV)) >>
  qmatch_goalsub_abbrev_tac `LET _ C` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Kept` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Port` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  strip_tac >>
  qpat_x_assum `p = _` (mk_asm "p_window") >>
  qpat_x_assum `q = _` (mk_asm "q_window") >>
  `EL b p = AsmPushLabel c /\
   EL (b+1) p = AsmOp "JUMPI" /\
   EL (b+2) p = AsmPushLabel x /\
   EL (b+3) p = AsmOp "JUMP" /\
   b+4 < LENGTH p` by
    (asm "p_window" SUBST1_TAC >>
     once_rewrite_tac [GSYM APPEND_ASSOC] >> simp[Abbr `b`, EL_APPEND_EQN]) >>
  qpat_assum `Abbrev (Open = _)` (fn od =>
    qpat_assum `Open p cc req V {} rank pc height need tag boolean edge`
      (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] od])) >>
  simp_tac std_ss [LET_THM, DIFF_EMPTY, EMPTY_SUBSET] >>
  strip_tac >>
  `ALOOKUP dup_table "JUMPI" = NONE /\ ALOOKUP swap_table "JUMPI" = NONE /\
   ALOOKUP dup_table "JUMP" = NONE /\ ALOOKUP swap_table "JUMP" = NONE /\
   asm_op_arity "JUMPI" = 2 /\ asm_op_arity "JUMP" = 1` by EVAL_TAC >>
  `!z l. z IN V /\ C p l (pc z) ==> Kept z` by suspend "kept" >>
  `!u y l. edge u y /\ EL (pc u) p = AsmPushLabel l ==>
     y IN V /\ rank y < rank u /\ height y = height u + 1 /\
     (!k j i. tag y k = SOME(j,i) ==>
        (if k=0 then j=l /\ i=pc u else tag u (k-1) = SOME(j,i))) /\
     (!k. boolean y k ==> 0<k /\ boolean u (k-1))` by suspend "push_edge" >>
  `!u y. edge u y /\ EL (pc u) p = AsmOp "JUMP" ==>
     y IN V /\ rank y < rank u /\ height y + 1 = height u /\
     (?l i. tag u 0 = SOME(l,i) /\ C p l (pc y)) /\
     (!k l i. tag y k = SOME(l,i) ==> tag u (k+1) = SOME(l,i)) /\
     (!k. boolean y k ==> boolean u (k+1))` by suspend "jump_edge" >>
  conj_tac >- suspend "late" >>
  suspend "early"
QED

Resume conditional_jump_strict_ports[kept]:
  simp[Abbr `Kept`, Abbr `C`, NoAsms] >> rpt strip_tac >>
  `INDEX_OF (AsmLabel l) p = SOME (pc z)` by metis_tac[lookup_pair_code_label_index] >>
  `EL (pc z) p = AsmLabel l` by metis_tac[INDEX_OF_eq_SOME] >>
  Cases_on `pc z < b \/ b+4 <= pc z` >> simp[] >>
  `pc z=b \/ pc z=b+1 \/ pc z=b+2 \/ pc z=b+3` by decide_tac >> gvs[]
QED

Resume conditional_jump_strict_ports[push_edge]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!u y. edge u y ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `Flow p pc height tag boolean u y` mp_tac >>
  qpat_assum `EL (pc u) p = AsmPushLabel l` (fn fetch =>
    qpat_assum `Abbrev (Flow = _)` (fn fd =>
      qpat_assum `Abbrev (TagFlow = _)` (fn td =>
        CONV_TAC (LAND_CONV (SIMP_CONV std_ss
          ([LET_THM, asm_inst_case_def, fetch] @
           map (REWRITE_RULE [markerTheory.Abbrev_def]) [fd,td])))))) >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (map_every qx_gen_tac [`k`,`j`,`i`] >> DISCH_TAC >>
      qpat_assum `!k l i. tag y k = SOME(l,i) ==> _` drule >>
      Cases_on `k=0` >> simp[] >> metis_tac[]) >>
  qx_gen_tac `k` >> DISCH_TAC >>
  qpat_assum `!k. boolean y k ==> _` (qspec_then `k` mp_tac) >>
  metis_tac[DECIDE ``(k:num) <> 0 ==> 0 < k``]
QED

Resume conditional_jump_strict_ports[jump_edge]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!u y. edge u y ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `Flow p pc height tag boolean u y` mp_tac >>
  qpat_assum `Abbrev (Flow = _)` (fn fd =>
    qpat_assum `Abbrev (TagFlow = _)` (fn td =>
      CONV_TAC (LAND_CONV (SIMP_CONV std_ss
        (map (REWRITE_RULE [markerTheory.Abbrev_def]) [fd,td] @
         [LET_THM, asm_inst_case_def]))))) >>
  simp[Abbr `C`] >> strip_tac >>
  `height y + 1 = height u` by decide_tac >>
  qpat_x_assum `if EL (pc u) p = _ then _ else _` mp_tac >>
  qpat_assum `EL (pc u) p = AsmOp "JUMP"` (fn fetch => simp_tac std_ss [fetch]) >>
  disch_then (qx_choose_then `l` (qx_choose_then `i` (qx_choose_then `off` strip_assume_tac))) >>
  rpt conj_tac
  >- ((simp[])) >>
  `height y + 1 - height u = 0` by decide_tac >>
  gvs[] >> metis_tac[]
QED

Resume conditional_jump_strict_ports[late]:
  strip_tac
  >- (`?j. edge e j /\ pc j = b+3` by metis_tac[] >>
      `EL (pc e) p = AsmPushLabel x /\ EL (pc j) p = AsmOp "JUMP"` by simp[] >>
      qpat_assum `!u y l. edge u y /\ EL (pc u) p = AsmPushLabel l ==> _`
        (qspecl_then [`e`,`j`,`x`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `?z. edge j z` by metis_tac[] >>
      qpat_assum `!u y. edge u y /\ EL (pc u) p = AsmOp "JUMP" ==> _`
        (qspecl_then [`j`,`z`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >> qexists `z` >>
      `l = x` by metis_tac[] >>
      `height z = height e /\ rank z < rank e` by decide_tac >>
      simp[Abbr `Port`] >>
      metis_tac[DECIDE ``((k:num)+1)-1=k /\ k+1<>0``]) >>
  `?z. edge e z` by metis_tac[] >>
  qpat_assum `!u y. edge u y /\ EL (pc u) p = AsmOp "JUMP" ==> _`
    (qspecl_then [`e`,`z`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> qexists `z` >>
  `l = x` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  gvs[Abbr `Port`] >> metis_tac[]
QED

Resume conditional_jump_strict_ports[early]:
  strip_tac >> rename1 `tag e 0 = SOME(c,origin)` >>
  `~boolean e 0` by
    (qpat_assum `!a k. a IN V /\ boolean a k ==> tag a k = NONE`
       (qspecl_then [`e`,`0`] mp_tac) >> simp[]) >>
  `2 <= height e /\ tag e 1 = NONE` by metis_tac[] >>
  `AsmOp "JUMPI" <> AsmOp "JUMP"` by EVAL_TAC >>
  `EL (pc e) p = AsmOp "JUMPI"` by simp[] >>
  `!y. edge e y ==> pc y = pc e + 1 \/ C p c (pc y)` by
    (qx_gen_tac `y` >> disch_tac >>
     qpat_assum `!a d. edge a d ==> _ /\ _ /\ _ /\ Flow p pc height tag boolean a d /\ _`
       (qspecl_then [`e`,`y`] mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `EL (pc e) p = AsmOp "JUMPI"` (fn fetch =>
       qpat_assum `AsmOp "JUMPI" <> AsmOp "JUMP"` (fn neq =>
         qpat_x_assum `if EL (pc e) p = AsmOp "JUMP" then _ else _`
           (strip_assume_tac o SIMP_RULE std_ss [fetch,neq]))) >>
     simp[Abbr `C`] >>
     `l = c` by metis_tac[optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
     qpat_x_assum `l = c` SUBST_ALL_TAC >>
     disj2_tac >> qexists `off` >> asm_rewrite_tac[]) >>
  `?t. Shape p cc req pc height need tag boolean e t` by metis_tac[] >>
  `(!i. i=origin ==> i < LENGTH p /\
     (EL i p = AsmPushLabel c \/ (?d. EL i p = AsmPushOfst c d) \/
      EL i p = AsmDataLabel c)) /\
   (?off dest. FLOOKUP (SND (compute_label_offsets p)) c = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)` by
    (qpat_assum `Abbrev (Shape = _)` (fn sd =>
       qpat_assum `Shape p cc req pc height need tag boolean e t`
         (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
           [REWRITE_RULE [markerTheory.Abbrev_def] sd])) >>
     qpat_assum `!k l i. tag e k = SOME(l,i) ==> _`
       (qspecl_then [`0`,`c`,`origin`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2 kall_tac
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
         (qx_choose_then `off` (qx_choose_then `dest` strip_assume_tac))))) >>
     conj_tac >- simp[] >> qexistsl [`off`,`dest`] >> asm_rewrite_tac[]) >>
  qabbrev_tac `m = MAX_SET (IMAGE FST (V:(num#num)->bool))` >>
  qabbrev_tac `v = (SUC m,0:num)` >> qabbrev_tac `j = (SUC (SUC m),0:num)` >>
  `v <> j /\ v NOTIN V /\ j NOTIN V` by suspend "fresh" >>
  qabbrev_tac `V' = v INSERT j INSERT V` >>
  qabbrev_tac `pc' = \u. if u=v then b else pc (if u=j then e else u)` >>
  qabbrev_tac `height' = \u. if u=v then height e - 1 else height (if u=j then e else u)` >>
  qabbrev_tac `need' = \u. need (if u=v \/ u=j then e else u)` >>
  qabbrev_tac `rank' = \u. if u=v then rank e + 1 else rank (if u=j then e else u)` >>
  qabbrev_tac `tag' = \u k. if u=v then tag e (k+1) else
                            if u=j then (if k=0 then SOME(c,b) else tag e k) else tag u k` >>
  qabbrev_tac `bool' = \u k. if u=v then boolean e (k+1) else boolean (if u=j then e else u) k` >>
  qabbrev_tac `edge' = \u y. if u=v then y=j else edge (if u=j then e else u) y` >>
  `!u. u IN V ==> u <> v /\ u <> j` by metis_tac[] >>
  `!u y. edge u y ==> u IN V /\ y IN V /\ rank y < rank u` by metis_tac[] >>
  `!u t. u IN V ==> (Shape p cc req pc' height' need' tag' bool' u t <=>
                      Shape p cc req pc height need tag boolean u t)` by
    (rpt gen_tac >> strip_tac >>
     `u <> v /\ u <> j` by metis_tac[] >>
     simp[Abbr `Shape`, Abbr `pc'`, Abbr `height'`, Abbr `need'`, Abbr `tag'`, Abbr `bool'`]) >>
  `!t. Shape p cc req pc' height' need' tag' bool' j t <=>
       Shape p cc req pc height need tag boolean e t` by suspend "copy_shape" >>
  `?t. Shape p cc req pc' height' need' tag' bool' v t` by suspend "pred_shape" >>
  `Open p cc req V' {} rank' pc' height' need' tag' bool' edge'` by suspend "extended_open" >>
  suspend "apply_packet"
QED

Resume conditional_jump_strict_ports[fresh]:
  `!u. u IN V ==> FST u <= m` by
    (rw[Abbr `m`] >> irule MAX_SET_PROPERTY >> simp[] >> metis_tac[IN_IMAGE]) >>
  conj_tac >- simp[Abbr `v`, Abbr `j`] >>
  `m < FST v /\ m < FST j` by simp[Abbr `v`, Abbr `j`] >>
  conj_tac >> DISCH_TAC >>
  qpat_assum `!u. u IN V ==> FST u <= m` drule >> decide_tac
QED

Resume conditional_jump_strict_ports[copy_shape]:
  `b < LENGTH p` by decide_tac >>
  qpat_assum `!i. i=origin ==> _` (qspec_then `origin` mp_tac) >>
  simp_tac std_ss [] >> disch_then (mk_asm "producer") >>
  (* E0650 attempted to transport whole Shape directions with FIRST_PROVE. *)
  qx_gen_tac `st` >>
  qabbrev_tac `P = \l i. i < LENGTH p /\
    (EL i p = AsmPushLabel l \/ (?d. EL i p = AsmPushOfst l d) \/
       EL i p = AsmDataLabel l)` >>
  qabbrev_tac `WordHit = \k l. ?off dest.
    FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest /\
    EL k st.as_stack = n2w off` >>
  `P c b /\ P c origin` by (asm "producer" (fn pr => simp[Abbr `P`, pr])) >>
  `(!k l i. (if k=0 then SOME(c,b) else tag e k) = SOME(l,i) ==>
       k < height e /\ P l i /\ WordHit k l) <=>
    (!k l i. tag e k = SOME(l,i) ==> k < height e /\ P l i /\ WordHit k l)` by
   (CONV_TAC (BINOP_CONV (HO_REWR_CONV arithmeticTheory.FORALL_NUM THENC
        DEPTH_CONV BETA_CONV)) >>
    simp[optionTheory.SOME_11, pairTheory.PAIR_EQ, GSYM AND_IMP_INTRO]) >>
  qpat_x_assum `(!k l i. _ ==> _ /\ P l i /\ WordHit k l) <=> _`
    (fn eqn => qpat_assum `Abbrev (P = _)` (fn pd =>
       simp[Abbr `Shape`, Abbr `pc'`, Abbr `height'`, Abbr `need'`,
            Abbr `tag'`, Abbr `bool'`,
            REWRITE_RULE [GSYM CONJ_ASSOC] (BETA_RULE (PURE_REWRITE_RULE
              [REWRITE_RULE [markerTheory.Abbrev_def] pd] eqn))]))
QED

Resume conditional_jump_strict_ports[pred_shape]:
  qpat_assum `Abbrev (Shape = _)` (fn sd =>
    qpat_assum `Shape p cc req pc height need tag boolean e t`
      (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
        [REWRITE_RULE [markerTheory.Abbrev_def] sd])) >>
  Cases_on `t.as_stack` >-
    (`height e = 0` by metis_tac[LENGTH] >> fs[]) >>
  rename1 `t.as_stack = w::stk` >>
  `LENGTH stk = height e - 1` by (fs[LENGTH] >> decide_tac) >>
  `need e ==> cc.cc_static` by metis_tac[] >>
  qexists `t with <|as_pc := b; as_stack := stk|>` >>
  simp[Abbr `Shape`, Abbr `pc'`, Abbr `height'`, Abbr `need'`, Abbr `tag'`, Abbr `bool'`] >>
  conj_tac
  >- (map_every qx_gen_tac [`k`,`l`,`i`] >>
      disch_then (fn hit => qpat_assum `!k l i. tag e k = SOME(l,i) ==> _`
        (qspecl_then [`k+1`,`l`,`i`] (strip_assume_tac o C MATCH_MP hit))) >>
      `k < height e - 1` by decide_tac >>
      fs[GSYM ADD1, EL]) >>
  qx_gen_tac `k` >>
  disch_then (fn hit => qpat_assum `!k. boolean e k ==> _`
    (qspec_then `k+1` (strip_assume_tac o C MATCH_MP hit))) >>
  `k < height e - 1` by decide_tac >>
  fs[GSYM ADD1, EL]
QED

Resume conditional_jump_strict_ports[extended_open]:
  simp[NoAsms, Abbr `Open`, LET_THM, DIFF_EMPTY, Abbr `V'`] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[Abbr `pc'`] >>
      metis_tac[DECIDE ``(b:num)+4<n ==> b<n``]) >>
  conj_tac >- suspend "extended_edges" >>
  suspend "extended_steps"
QED

Resume conditional_jump_strict_ports[extended_edges]:
  rpt gen_tac >> rename1 `edge' u y ==> _` >>
  Cases_on `u=v` >> simp[Abbr `edge'`] >> strip_tac
  >- (simp[Abbr `rank'`] >>
      `!f h T B a d l. EL (f a) p = AsmPushLabel l /\
          h d = h a + 1 /\
          TagFlow T a d (h a) (h d)
            (\k. if k=0 then NONE else SOME(k-1))
            (\k. if k=0 then SOME(l,f a) else NONE) /\
          (!k. B d k ==> k<h d /\ k<>0 /\ k-1<h a /\ B a (k-1)) ==>
          Flow p f h T B a d` by
        (rpt gen_tac >> strip_tac >>
         qpat_assum `EL (f a) p = AsmPushLabel l` (fn fetch =>
           qpat_assum `Abbrev (Flow = _)` (fn fd =>
             simp_tac std_ss [REWRITE_RULE [markerTheory.Abbrev_def] fd,
                              LET_THM, fetch, asm_inst_case_def])) >>
         simp[] >> gen_tac >> strip_tac >>
         qpat_assum `!k. B d k ==> _` (drule_then strip_assume_tac) >>
         decide_tac) >>
      `Flow p pc' height' tag' bool' v j` suffices_by simp[Abbr `pc'`] >>
      qpat_assum `!f h T B a d l. _ ==> Flow p f h T B a d` irule >>
      conj_tac
      >- (simp[Abbr `height'`, Abbr `bool'`] >> qx_gen_tac `k` >> strip_tac >>
          qpat_assum `Abbrev (Shape = _)` (fn sd =>
            qpat_assum `Shape p cc req pc height need tag boolean e t`
              (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
                [REWRITE_RULE [markerTheory.Abbrev_def] sd])) >>
          `k < height e` by
            (qpat_assum `!i. boolean e i ==> _` (drule_then strip_assume_tac) >> simp[]) >>
          `k <> 0` by
            (disch_tac >> gvs[] >>
             qpat_assum `!u k. u IN V /\ boolean u k ==> tag u k = NONE`
               (qspecl_then [`e`,`0`] mp_tac) >> simp[]) >>
          `k-1 < height e-1 /\ k-1+1=k` by decide_tac >> simp[]) >>
      conj_tac >- simp[Abbr `height'`] >>
      qexists `c` >> simp[Abbr `pc'`, Abbr `height'`, Abbr `TagFlow`, Abbr `tag'`] >>
      map_every qx_gen_tac [`k`,`l`,`i`] >> Cases_on `k=0` >> simp[] >>
      strip_tac >>
      `k < height e` by
        (qpat_assum `Abbrev (Shape = _)` (fn sd =>
           qpat_assum `Shape p cc req pc height need tag boolean e t`
             (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
               [REWRITE_RULE [markerTheory.Abbrev_def] sd])) >>
         qpat_assum `!k l i. tag e k = SOME(l,i) ==> _` (drule_then strip_assume_tac) >> simp[]) >>
      `k-1 < height e-1 /\ k-1+1=k` by decide_tac >> simp[]) >>
  Cases_on `u=j`
  >- (`edge e y` by (gvs[]) >>
      qpat_assum `!a d. edge a d ==> _ /\ _ /\ _ /\ Flow p pc height tag boolean a d /\ _`
        (qspecl_then [`e`,`y`] mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      `y <> v /\ y <> j` by metis_tac[] >>
      simp[Abbr `rank'`] >> conj_tac
      >- (`EL (pc e) p = AsmOp "JUMPI" /\ EL (pc' j) p = AsmOp "JUMPI" /\
           height' j = height e /\ height' y = height y` by
            simp[Abbr `pc'`, Abbr `height'`] >>
          `!f h T B a d. EL (f a) p = AsmOp "JUMPI" ==>
             (Flow p f h T B a d <=>
               h d + 2 = h a /\
               (!k l i. T d k = SOME(l,i) ==>
                   k < h d /\ k+2 < h a /\ T a (k+2) = SOME(l,i)) /\
               (!k. B d k ==> k < h d /\ k+2 < h a /\ B a (k+2)))` by
            (rpt gen_tac >> disch_tac >>
             qpat_assum `EL (f a) p = AsmOp "JUMPI"` (fn fetch =>
               qpat_assum `Abbrev (Flow = _)` (fn fd =>
                 qpat_assum `Abbrev (TagFlow = _)` (fn td =>
                   qpat_assum `ALOOKUP dup_table "JUMPI" = NONE` (fn dn =>
                   qpat_assum `ALOOKUP swap_table "JUMPI" = NONE` (fn sn =>
                   qpat_assum `asm_op_arity "JUMPI" = 2` (fn ar =>
                     simp_tac std_ss
                       ([LET_THM, asm_inst_case_def, fetch, dn, sn, ar] @
                        map (REWRITE_RULE [markerTheory.Abbrev_def]) [fd,td]))))))) >>
             Cases_on `h d + 2 = h a`
             >- (`h d + 2 - h a = 0 /\ 2 <= h a /\ h a - 2 = h d` by decide_tac >>
                 asm_simp_tac std_ss []) >>
             asm_simp_tac std_ss [] >>
             disch_tac >>
             `2 <= h a ==> ~(h d + 2 <= h a)` by decide_tac >>
             Cases_on `2 <= h a` >> simp[]) >>
          `Flow p pc height tag boolean e y <=> Flow p pc' height' tag' bool' j y` by
            (qpat_x_assum `Flow p pc height tag boolean e y` kall_tac >>
             qpat_assum `!f h T B a d. _ ==> (Flow p f h T B a d <=> _)`
               (fn nf => dep_rewrite.DEP_ONCE_REWRITE_TAC [nf]) >>
             simp[Abbr `tag'`, Abbr `bool'`, DECIDE ``!k:num. k+2 <> 0``]) >>
          metis_tac[]) >>
      `pc' j = pc e /\ pc' y = pc y /\ tag' j 0 = SOME(c,b)` by
        simp[Abbr `pc'`, Abbr `tag'`] >>
      qpat_assum `!d. edge e d ==> pc d = pc e + 1 \/ C p c (pc d)`
        (drule_then strip_assume_tac)
      >- simp[Abbr `C`] >>
      `dest = pc y` by
        (qpat_x_assum `C p c (pc y)` mp_tac >> simp[Abbr `C`]) >>
      simp[Abbr `C`]) >>
  `edge u y` by (gvs[]) >>
  qpat_assum `!a d. edge a d ==> _ /\ _ /\ _ /\ Flow p pc height tag boolean a d /\ _`
    (qspecl_then [`u`,`y`] mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  `y <> v /\ y <> j` by metis_tac[] >>
  `pc' u = pc u /\ pc' y = pc y /\ height' u = height u /\ height' y = height y /\
   tag' u = tag u /\ tag' y = tag y /\ bool' u = boolean u /\ bool' y = boolean y` by
    simp[Abbr `pc'`, Abbr `height'`, Abbr `tag'`, Abbr `bool'`, FUN_EQ_THM] >>
  `TagFlow tag' u y = TagFlow tag u y` by
    (qpat_assum `Abbrev (TagFlow = _)` (fn td =>
       simp_tac std_ss [REWRITE_RULE [markerTheory.Abbrev_def] td]) >>
     asm_rewrite_tac[]) >>
  `Flow p pc' height' tag' bool' u y = Flow p pc height tag boolean u y` by
    (qpat_assum `Abbrev (Flow = _)` (fn fd =>
       simp_tac std_ss [REWRITE_RULE [markerTheory.Abbrev_def] fd,LET_THM]) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `if EL (pc u) p = _ then _ else _` mp_tac >>
  simp[Abbr `rank'`]
QED

Resume conditional_jump_strict_ports[extended_steps]:
  map_every qx_gen_tac [`u`,`st`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `u = v`
  >- (`Shape p cc req pc' height' need' tag' bool' v st` by metis_tac[] >>
      qpat_x_assum `Shape p cc req pc' height' need' tag' bool' v st` mp_tac >>
      simp[Abbr `Shape`, Abbr `pc'`, Abbr `height'`, Abbr `need'`, Abbr `tag'`, Abbr `bool'`] >>
      strip_tac >>
      `b < LENGTH p` by decide_tac >>
      qabbrev_tac `out = asm_next (st with as_stack := n2w off :: st.as_stack)` >>
      disj2_tac >> qexistsl [`j`,`out`] >> simp[Abbr `edge'`] >>
      conj_tac
      >- (once_rewrite_tac [DECIDE ``1 = SUC 0``] >>
          once_rewrite_tac [asm_steps_def] >>
          simp[Abbr `out`, asm_step_def, Once asm_steps_def]) >>
      simp[Abbr `out`, asm_next_def] >>
      conj_tac
      >- (qpat_assum `st.as_call_ctx = cc` (fn eqn =>
            qpat_assum `need e ==> st.as_call_ctx.cc_static`
              (ACCEPT_TAC o REWRITE_RULE [eqn]))) >>
      conj_tac
      >- (Cases >- (simp[] >> metis_tac[]) >>
          simp[EL, GSYM ADD1] >>
          rpt gen_tac >> disch_tac >>
          qpat_assum `!k l i. tag e (k+1) = SOME(l,i) ==> _`
            (drule_then strip_assume_tac o REWRITE_RULE [GSYM ADD1]) >> simp[] >> decide_tac) >>
      Cases >> simp[EL, GSYM ADD1] >>
      rpt strip_tac >> qpat_assum `!k. boolean e (k+1) ==> _`
        (drule_then strip_assume_tac o REWRITE_RULE [GSYM ADD1]) >> simp[] >> decide_tac) >>
  qabbrev_tac `src = if u = j then e else u` >>
  `src IN V /\ Shape p cc req pc height need tag boolean src st` by
    (Cases_on `u = j` >> simp[Abbr `src`]
     >- (qpat_x_assum `u = j` SUBST_ALL_TAC >>
         qpat_assum `!s. Shape p cc req pc' height' need' tag' bool' j s <=> _`
           (qspec_then `st` (fn th => simp[GSYM th]))) >>
     `u IN V` by (qpat_x_assum `u = v \/ u = j \/ u IN V` mp_tac >> simp[]) >>
     qpat_assum `!a s. a IN V ==> (Shape p cc req pc' height' need' tag' bool' a s <=> _)`
       (qspecl_then [`u`,`st`] (fn th => simp[GSYM th]))) >>
  qpat_assum `!a s. a IN V /\ Shape p cc req pc height need tag boolean a s ==> _`
    (qspecl_then [`src`,`st`] mp_tac) >> (impl_tac >- simp[]) >>
  strip_tac
  >- (disj1_tac >> qexists `s` >> simp[])
  >- (disj1_tac >> qexists `s` >> simp[]) >>
  disj2_tac >>
  `y IN V` by
    (qpat_assum `!a d. edge a d ==> a IN V /\ d IN V /\ _`
       (qspecl_then [`src`,`y`] mp_tac) >> simp[]) >>
  qexistsl [`y`,`s`] >>
  `edge' u y` by
    (qpat_assum `Abbrev (src = _)` (fn eqn =>
       simp[Abbr `edge'`, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eqn)])) >>
  simp[] >>
  qpat_assum `!a s. a IN V ==> (Shape p cc req pc' height' need' tag' bool' a s <=> _)`
    (qspecl_then [`y`,`s`] mp_tac) >> simp[]
QED

Resume conditional_jump_strict_ports[apply_packet]:
  `v IN V' /\ pc' v = b /\ (?a. edge' v a /\ pc' a = b+1) /\
    (!a. edge' v a ==> tag' a 1 = NONE)` by
    (simp[Abbr `V'`, Abbr `pc'`, Abbr `edge'`, Abbr `tag'`]) >>
  `!u k. u IN V' /\ bool' u k ==> tag' u k = NONE` by
    (rpt gen_tac >> Cases_on `u=v`
     >- (qpat_x_assum `u=v` SUBST_ALL_TAC >>
         simp[Abbr `bool'`, Abbr `tag'`] >>
         qpat_assum `!u k. u IN V /\ boolean u k ==> tag u k = NONE`
           (qspecl_then [`e`,`k+1`] mp_tac) >> simp[]) >>
     Cases_on `u=j`
     >- (qpat_x_assum `u=j` SUBST_ALL_TAC >>
         simp[Abbr `bool'`, Abbr `tag'`] >>
         qpat_assum `!u k. u IN V /\ boolean u k ==> tag u k = NONE`
           (qspecl_then [`e`,`k`] mp_tac) >>
         Cases_on `k=0` >> simp[]) >>
     simp[Abbr `V'`, Abbr `bool'`, Abbr `tag'`] >>
     qpat_assum `!u k. u IN V /\ boolean u k ==> tag u k = NONE`
       (qspecl_then [`u`,`k`] ACCEPT_TAC)) >>
  let
    val packet = Q.INST [`V` |-> `V'`, `rank` |-> `rank'`, `pc` |-> `pc'`,
                        `height` |-> `height'`, `need` |-> `need'`, `tag` |-> `tag'`,
                        `boolean` |-> `bool'`, `edge` |-> `edge'`]
      (SPEC_ALL conditional_jump_whole_visit_rows)
    val expose = CONV_RULE (REWR_CONV LET_THM THENC BETA_CONV)
    fun fold eq = PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]
  in
    qpat_assum `Abbrev (Shape = _)` (fn sh =>
    qpat_assum `Abbrev (TagFlow = _)` (fn tf =>
    qpat_assum `Abbrev (Flow = _)` (fn fl =>
    qpat_assum `Abbrev (Open = _)` (fn opn =>
    qpat_assum `Abbrev (b = _)` (fn base =>
    qpat_assum `Abbrev (C = _)` (fn canon =>
      let val body = List.foldl (fn (eq, th) => fold eq (expose th)) packet [sh,tf,fl,opn]
      in mp_tac (fold canon (fold base (funpow 5 expose body))) end))))))
  end >>
  (impl_tac >-
    (asm "p_window" assume_tac >> asm "q_window" assume_tac >>
     simp[] >> metis_tac[optionTheory.NOT_NONE_SOME])) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `j0` (qx_choose_then `h` (qx_choose_then `i`
     (qx_choose_then `z0` (qx_choose_then `j1` (qx_choose_then `ca`
      (qx_choose_then `z1` strip_assume_tac)))))))) >>
  `j <> v` by (qpat_assum `v <> j` mp_tac >> simp[Once EQ_SYM_EQ]) >>
  `!y. edge' v y ==> y = j` by simp[Abbr `edge'`] >>
  `!y. edge' j y ==> edge e y` by simp[Abbr `edge'`] >>
  `j0 = j /\ j1 = j` by
    (qpat_assum `!y. edge' v y ==> y = j` (fn th =>
       qspec_then `j0` mp_tac th >> qspec_then `j1` mp_tac th) >> simp[]) >>
  qpat_x_assum `j0 = j` SUBST_ALL_TAC >>
  qpat_x_assum `j1 = j` SUBST_ALL_TAC >>
  `edge e h /\ edge e ca` by
    (qpat_assum `!y. edge' j y ==> edge e y` (fn th =>
       qspec_then `h` mp_tac th >> qspec_then `ca` mp_tac th) >> simp[]) >>
  `!u. u IN V ==> pc' u = pc u /\ height' u = height u /\
    rank' u = rank u /\ (!k. tag' u k = tag u k) /\
    (!k. bool' u k = boolean u k) /\ need' u = need u` by
    (rpt strip_tac >>
     `u <> v /\ u <> j` by
       (qpat_assum `!u. u IN V ==> u <> v /\ u <> j`
          (qspec_then `u` mp_tac) >> simp[]) >>
     simp[Abbr `pc'`, Abbr `height'`, Abbr `rank'`, Abbr `tag'`, Abbr `bool'`, Abbr `need'`]) >>
  `!u y. u IN V /\ edge' u y ==> edge u y` by
    (rpt gen_tac >> strip_tac >>
     `u <> v /\ u <> j` by
       (qpat_assum `!u. u IN V ==> u <> v /\ u <> j`
          (qspec_then `u` mp_tac) >> simp[]) >>
     qpat_x_assum `edge' u y` mp_tac >> simp[Abbr `edge'`]) >>
  qpat_assum `!u y. edge u y ==> u IN V /\ y IN V /\ rank y < rank u`
    (fn th => qpat_assum `edge e h` (strip_assume_tac o MATCH_MP th) >>
              qpat_assum `edge e ca` (strip_assume_tac o MATCH_MP th)) >>
  `edge h i /\ edge ca z1` by
    (qpat_assum `!u y. u IN V /\ edge' u y ==> edge u y` (fn th =>
       map_every (fn (u,y) => qspecl_then [u,y] mp_tac th) [(`h`,`i`),(`ca`,`z1`)]) >> simp[]) >>
  qpat_assum `!u y. edge u y ==> u IN V /\ y IN V /\ rank y < rank u`
    (fn th => qpat_assum `edge h i` (strip_assume_tac o MATCH_MP th) >>
              qpat_assum `edge ca z1` (strip_assume_tac o MATCH_MP th)) >>
  `edge i z0` by
    (qpat_assum `!u y. u IN V /\ edge' u y ==> edge u y`
       (qspecl_then [`i`,`z0`] mp_tac) >> simp[]) >>
  qpat_assum `!u y. edge u y ==> u IN V /\ y IN V /\ rank y < rank u`
    (fn th => qpat_assum `edge i z0` (strip_assume_tac o MATCH_MP th)) >>
  `rank z0 < rank e /\ rank z1 < rank e` by (simp[]) >>
  qpat_assum `!u. u IN V ==> pc' u = pc u /\ _`
    (fn th => map_every (fn (mem,label) => qpat_assum mem (fn h =>
       let val fields = MATCH_MP th h
       in strip_assume_tac fields >> mk_asm label fields end))
       [(`z0 IN V`,"z0 fields"), (`z1 IN V`,"z1 fields")]) >>
  `height' v = height e - 1 /\ rank' v = rank e + 1 /\
   (!k. tag' v k = tag e (k+1)) /\ (!k. bool' v k = boolean e (k+1))` by
    simp[Abbr `height'`, Abbr `rank'`, Abbr `tag'`, Abbr `bool'`] >>
  qpat_assum `pc' z0 = pc z0` (fn eq =>
    qpat_assum `C p x (pc' z0)` (assume_tac o PURE_REWRITE_RULE [eq])) >>
  qpat_assum `pc' z1 = pc z1` (fn eq =>
    qpat_assum `pc' z1 = b+5` (assume_tac o PURE_REWRITE_RULE [eq])) >>
  `Kept z0 /\ Kept z1` by
    (conj_tac
     >- (qpat_assum `!z l. z IN V /\ C p l (pc z) ==> Kept z`
           (qspecl_then [`z0`,`x`] mp_tac) >> simp[]) >>
     simp[Abbr `Kept`, SimpLHS]) >>
  asm "z0 fields" (fn f0 => asm "z1 fields" (fn f1 =>
  qpat_assum `!k. tag' v k = _` (fn vt =>
  qpat_assum `!k. bool' v k = _` (fn vb =>
    let
      val normalize = strip_assume_tac o
        SIMP_RULE arith_ss ([ADD_ASSOC,vt,vb] @ CONJUNCTS f0 @ CONJUNCTS f1) o
        CONV_RULE BETA_CONV
    in
      qpat_x_assum `(\z. z IN V' /\ rank' z < rank' v /\ _) z0` normalize >>
      qpat_x_assum `(\z. z IN V' /\ rank' z < rank' v /\ _) z1` normalize
    end)))) >>
  `Port 2 z0 /\ Port 2 z1` by simp[Abbr `Port`, ADD_ASSOC] >>
  conj_tac >- (qpat_assum `height' v = height e - 1` (fn eq =>
    qpat_assum `0 < height' v` (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  qexistsl [`z0`,`z1`] >>
  conj_tac >- (qpat_assum `C p x (pc z0)` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `pc z1 = b+5` (fn th => ACCEPT_TAC th ORELSE ACCEPT_TAC (SYM th))) >>
  conj_tac >- (qpat_assum `Port 2 z0` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `Port 2 z1` ACCEPT_TAC) >>
  qx_gen_tac `move_origin` >>
  `!k:num. k+1+1 = k+2` by (simp[]) >>
  qpat_assum `!k:num. k+1+1 = k+2` (fn slot =>
  asm "z0 fields" (fn f0 => asm "z1 fields" (fn f1 =>
  qpat_assum `height' v = height e - 1` (fn vh =>
  qpat_assum `rank' v = rank e + 1` (fn vr =>
  qpat_assum `!k. tag' v k = _` (fn vt =>
  qpat_assum `!k. bool' v k = _` (fn vb =>
  qpat_x_assum `!rho:string->num->num. LET _ _`
    (qspec_then `move_origin` (strip_assume_tac o SIMP_RULE std_ss
      ([LET_THM,slot,vh,vr,vt,vb] @ CONJUNCTS f0 @ CONJUNCTS f1)))))))))) >>
  SIMP_TAC std_ss [LET_THM] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (pop_assum (fn raw =>
          qpat_assum `!k l i. (case tag z0 k of NONE => tag z1 k | SOME u => SOME u) = SOME(l,i) ==> _`
            (ACCEPT_TAC o CONJUNCT1 o C MATCH_MP raw))) >>
     pop_assum mp_tac >> Cases_on `tag z0 k` >> simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (pop_assum mp_tac >> rpt strip_tac >> simp[]) >>
     pop_assum (fn step =>
       qpat_assum `!u y. _ ==> _ /\ Flow q _ _ _ _ u y`
         (ACCEPT_TAC o CONJUNCT2 o C MATCH_MP step))) >>
  strip_tac >>
  qpat_assum `C q x _ /\ _ ==> _` mp_tac >>
  (impl_tac >-
    (conj_tac >- (first_assum ACCEPT_TAC) >>
     map_every qx_gen_tac [`z`,`k`,`l`,`i'`] >> strip_tac >>
     qpat_assum `!z k l i. (z=z0 \/ z=z1) /\ tag z k = SOME(l,i) ==> _`
       (qspecl_then [`z`,`k`,`l`,`i'`] mp_tac) >>
     qpat_assum `z = _` (fn zeq =>
     qpat_assum `tag' z k = SOME(l,i')` (fn hit =>
     qpat_assum `!k. tag' z0 k = tag z0 k` (fn tag0 =>
     qpat_assum `!k. tag' z1 k = tag z1 k` (fn tag1 =>
       SIMP_TAC std_ss [zeq, SIMP_RULE std_ss [zeq,tag0,tag1] hit])))))) >>
  disch_then (fn packet =>
    rpt conj_tac >> (MAP_FIRST ACCEPT_TAC (CONJUNCTS packet) ORELSE simp[NoAsms]))
QED

Finalise conditional_jump_strict_ports
