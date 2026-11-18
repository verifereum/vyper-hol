Theory staticAbortOptConditionalJumpsStrictPortReceipt
Ancestors
  staticAbortOptConditionalJumpsIngress
  asmOpSim stackOpAsmSim asmSplice asmWf asmIR asmSem finite_map pred_set list
  arithmetic words

Theorem conditional_jump_strict_port_receipt:
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
  let keep = {z | Kept z} in
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail /\
  asm_static_wf p /\ Open p cc req V {} rank pc height need tag boolean edge /\
  e IN V /\
  (!u k. u IN V /\ boolean u k ==> tag u k = NONE) /\
  (pc e = b+1 ==> 2 <= height e /\ tag e 1 = NONE /\
                   ?j. edge e j /\ pc j = b+2) /\
  (!u. u IN V /\ pc u = b+2 ==> ?j. edge u j /\ pc j = b+3) /\
  (!u. u IN V /\ pc u = b+3 ==> ?z. edge u z) /\
  pc e = b+1 /\ (?i. tag e 0 = SOME(c,i)) ==>
  0 < H /\ ?z0 z1.
    z0 IN keep /\ z1 IN keep /\ rank z0 < rank e /\ rank z1 < rank e /\
    height z0 = H-1 /\ height z1 = H-1 /\
    C p x (pc z0) /\ pc z1 = b+5 /\
    (!k t s. tag z0 k = SOME t /\ tag z1 k = SOME s ==> t = s) /\
    (!k t. (tag z0 k = SOME t \/ tag z1 k = SOME t) ==> tag e (k+2) = SOME t) /\
    (!k. (boolean z0 k \/ boolean z1 k) ==> boolean e (k+2)) /\
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
      (!u. u IN W ==> (nq u ==> cc.cc_static) /\
         (!k. bq u k ==> k<hq u /\ tq u k=NONE) /\
         (!k l i. tq u k=SOME(l,i) ==> k<hq u)) /\
      (!u. u IN {I;P;J;L} ==> pcq u < LENGTH q) /\
      EL (pcq I) q = AsmOp "ISZERO" /\ static_abort_straight "ISZERO" 1 /\
      EL (pcq P) q = AsmPushLabel x /\ EL (pcq J) q = AsmOp "JUMPI" /\
      EL (pcq L) q = AsmLabel c /\
      (!u y. edges u y ==> Flow q pcq hq tq bq u y) /\
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
       edges L E1 /\ pcq E1 = pcq L+1 /\ pcq E1 = b+4)
Proof
  mp_tac conditional_jump_strict_ports >>
  (let
     val both = CONV_TAC (BINOP_CONV (REWR_CONV LET_THM THENC BETA_CONV))
   in
     map_every (fn pat => qmatch_goalsub_abbrev_tac pat >> both)
       [`LET _ Shape`, `LET _ TagFlow`, `LET _ Flow`, `LET _ Open`,
        `LET _ b`, `LET _ r`, `LET _ H`, `LET _ C`, `LET _ Kept`] >> both
   end) >>
  disch_then (mk_asm "ingress") >> strip_tac >>
  asm_x "ingress" mp_tac >>
  impl_tac >- simp[] >>
  disch_then (mp_tac o CONJUNCT2) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `z0` (qx_choose_then `z1`
      (MAP_EVERY (strip_assume_tac o CONV_RULE
        (TRY_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV))) o CONJUNCTS)))) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`z0`,`z1`] >>
  ntac 2 (conj_tac >- simp[GSPECIFICATION]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gvs[Abbr `H`] >> decide_tac)
  >- (gvs[Abbr `H`] >> decide_tac)
  >- (qpat_assum `!rho:string->num->num. _` (qspec_then `\l i. i`
        (ACCEPT_TAC o CONJUNCT1 o CONV_RULE (REPEATC (REWR_CONV LET_THM THENC BETA_CONV)))))
  >- (rpt gen_tac >> PairCases_on `t` >> metis_tac[])
  >- metis_tac[] >>
  qx_gen_tac `origin_map` >>
  qpat_x_assum `!rho:string->num->num. _` (qspec_then `origin_map`
    (MAP_EVERY assume_tac o CONJUNCTS o CONV_RULE (REPEATC (REWR_CONV LET_THM THENC BETA_CONV)))) >>
  CONV_TAC (REPEATC (REWR_CONV LET_THM THENC BETA_CONV)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!u y. _ ==> _ /\ Flow _ _ _ _ _ _ _`
        (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  disch_tac >>
  qpat_assum `C q x (r (pc z0)) /\ _ ==> _` mp_tac >>
  impl_tac >- (first_assum ACCEPT_TAC) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
