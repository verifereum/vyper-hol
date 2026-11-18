Theory staticAbortOptConditionalJumpsWholePortReceipt
Ancestors
  staticAbortOptConditionalJumpsArms asmSplice asmIR asmSem stackOpAsmSim
  finite_map pred_set list arithmetic words

Theorem conditional_jump_whole_port_receipt:
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
      H = height v;
      C = \s l d. ?off. FLOOKUP (SND(compute_label_offsets s)) l = SOME off /\
                         off < dimword(:256) /\
                         FLOOKUP (build_offset_to_pc s) off = SOME d in
  let keep = {u | u IN V /\ (pc u<b \/ b+4<=pc u)} in
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail /\
  asm_static_wf p /\ Open p cc req V {} rank pc height need tag boolean edge /\
  v IN V /\ pc v = b /\ IS_SOME (FLOOKUP (SND(compute_label_offsets p)) c) /\
  (?j. edge v j /\ pc j = b+1) /\ (!j. edge v j ==> tag j 1 = NONE) /\
  (!u k. u IN V /\ boolean u k ==> tag u k = NONE) /\
  (!l d. C p l d ==> d<b \/ b+4<=d) ==>
  0 < H /\
  ?z0 z1.
    z0 IN keep /\ z1 IN keep /\ rank z0 < rank v /\ rank z1 < rank v /\
    height z0 = H-1 /\ height z1 = H-1 /\ C p x (pc z0) /\ pc z1 = b+5 /\
    (!k t s. tag z0 k=SOME t /\ tag z1 k=SOME s ==> t=s) /\
    (!k t. (tag z0 k=SOME t \/ tag z1 k=SOME t) ==> tag v (k+1)=SOME t) /\
    (!k. (boolean z0 k \/ boolean z1 k) ==> boolean v (k+1)) /\
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
  let val lets = REPEATC (REWR_CONV LET_THM THENC BETA_CONV) in
    CONV_TAC lets >> BETA_TAC >> strip_tac >>
    mp_tac (BETA_RULE (CONV_RULE lets conditional_jump_whole_visit_rows))
  end >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
                              (qexists `j` >> asm_rewrite_tac[])))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `j0` (qx_choose_then `h` (qx_choose_then `i`
      (qx_choose_then `z0` (qx_choose_then `j1` (qx_choose_then `a`
        (qx_choose_then `z1` strip_assume_tac)))))))) >>
  conj_tac >- first_assum ACCEPT_TAC >> qexistsl [`z0`,`z1`] >>
  let val target = qexists `off` >> asm_rewrite_tac[] in
    conj_tac
    >- (simp[GSPECIFICATION] >>
        qpat_assum `!l d. _ ==> d < LENGTH pre \/ _`
          (qspecl_then [`x`,`pc z0`] mp_tac) >>
        (impl_tac >- target) >> simp[]) >>
    conj_tac >- simp[GSPECIFICATION] >>
    ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
    ntac 2 (conj_tac >- decide_tac) >>
    conj_tac >- target >> conj_tac >- first_assum ACCEPT_TAC
  end >>
  conj_tac
  >- (qpat_assum `!rho. LET _ _` (qspec_then `\l i. i` mp_tac) >>
      CONV_TAC (LAND_CONV (REPEATC (REWR_CONV LET_THM THENC BETA_CONV))) >>
      disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  conj_tac
  >- (rpt gen_tac >> PairCases_on `t` >> strip_tac >>
      first_assum (fn th => irule th >> first_assum ACCEPT_TAC)) >>
  conj_tac >- (rpt strip_tac >> first_assum (fn th => irule th >> first_assum ACCEPT_TAC)) >>
  qx_gen_tac `reloc` >>
  let val lets = REPEATC (REWR_CONV LET_THM THENC BETA_CONV) in
    qpat_x_assum `!reloc. LET _ _`
      (qspec_then `reloc` (strip_assume_tac o CONV_RULE lets)) >> CONV_TAC lets
  end >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!u y. _ ==> _ < _ /\ _`
        (qspecl_then [`u`,`y`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  disch_tac >>
  qpat_assum `_ ==> ((!u k l i. _) /\ _)` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED
