Theory staticAbortOptConditionalJumpsStrictPortReceipt
Ancestors
  staticAbortOptConditionalJumpsIngress
  asmOpSim stackOpAsmSim asmSplice asmWf asmIR asmSem finite_map pred_set list
  arithmetic words

Theorem conditional_jump_strict_port_receipt:
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
  !TagFlow. TagFlow = (\tag u y hi hj src fresh.
    !k l origin. tag y k = SOME(l,origin) ==>
      k < hj /\ (fresh k = SOME(l,origin) \/
      ?a. src k = SOME a /\ a < hi /\ tag u a = SOME(l,origin))) ==>
  !Flow. Flow =
    (\p pc height tag boolean (u:num#num) (y:num#num).
    !hi. hi = height u ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc u) p ==>
    !inherit. inherit =
      (\(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        TagFlow tag u y hi hj src fresh /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean u a))) ==>
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
    (\p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need
      (tag:(num#num)->num->(string#num)option)
      (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
    !target. target = (\u y.
      ?l origin off. tag u 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
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
              p 1 t = AsmOK s /\ S y s))) ==>
  !b. b = LENGTH pre ==>
  !r. r = splice_pc b 4 3 ==>
  !H. H = height e - 1 ==>
  !C. C = (\s l d. ?off. FLOOKUP (SND(compute_label_offsets s)) l = SOME off /\
                         off < dimword(:256) /\
                         FLOOKUP (build_offset_to_pc s) off = SOME d) ==>
  !Kept. Kept = (\z. z IN V /\ (pc z < b \/ b+4 <= pc z)) ==>
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
    Kept z0 /\ Kept z1 /\ rank z0 < rank e /\ rank z1 < rank e /\
    height z0 = H-1 /\ height z1 = H-1 /\
    C p x (pc z0) /\ pc z1 = b+5 /\
    (!k t s. tag z0 k = SOME t /\ tag z1 k = SOME s ==> t = s) /\
    (!k t. (tag z0 k = SOME t \/ tag z1 k = SOME t) ==> tag e (k+2) = SOME t) /\
    (!k. (boolean z0 k \/ boolean z1 k) ==> boolean e (k+2)) /\
    !rho:string->num->num.
      !translate. translate = OPTION_MAP (\(l,i). (l,rho l i)) ==>
      !U. U = (\k. translate (case tag z0 k of NONE => tag z1 k | SOME u => SOME u)) ==>
      !UB. UB = (\k. boolean z0 k \/ boolean z1 k) ==>
      !I. I = (0:num,0:num) ==>
      !P. P = (1:num,0:num) ==>
      !J. J = (2:num,0:num) ==>
      !L. L = (3:num,0:num) ==>
      !E0. E0 = (4:num,0:num) ==>
      !E1. E1 = (5:num,0:num) ==>
      !W. W = {I;P;J;L;E0;E1} ==>
      !pcq. pcq = (\u. if u=I then b else if u=P then b+1 else
            if u=J then b+2 else if u=L then b+3 else
            if u=E0 then r (pc z0) else r (pc z1)) ==>
      !hq. hq = (\u. if u=I \/ u=P then H else if u=J then H+1 else H-1) ==>
      !tq. tq = (\u k. if u=I \/ u=P then (if k=0 then NONE else U (k-1)) else
            if u=J then (if k=0 then SOME(x,b+1) else
                         if k=1 then NONE else U (k-2)) else
            if u=E0 then translate (tag z0 k) else translate (tag z1 k)) ==>
      !bq. bq = (\u k. if u=I then k<>0 /\ UB (k-1) else
            if u=P then k=0 \/ UB (k-1) else
            if u=J then k=1 \/ (2<=k /\ UB (k-2)) else
            if u=E0 then boolean z0 k else boolean z1 k) ==>
      !edges. edges = (\u y. (u=I /\ y=P) \/ (u=P /\ y=J) \/
            (u=J /\ y=E0) \/ (u=J /\ y=L) \/ (u=L /\ y=E1)) ==>
      (!u. u IN W ==> (((u=E0 /\ need z0) \/ (u=E1 /\ need z1)) ==> cc.cc_static) /\
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
  (let
     val unwind = HO_REWR_CONV UNWIND_FORALL_THM2
     val expose = QUANT_CONV (LAND_CONV (RAND_CONV (TOP_DEPTH_CONV unwind))) THENC unwind
     fun fold eq th = PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)] th
     fun specialize name k th = qpat_assum name (fn eq => k (fold eq (CONV_RULE expose th)))
     val names = [`Abbrev (Shape = _)`, `Abbrev (TagFlow = _)`, `Abbrev (Flow = _)`,
                  `Abbrev (Open = _)`, `Abbrev (b = _)`, `Abbrev (r = _)`,
                  `Abbrev (H = _)`, `Abbrev (C = _)`, `Abbrev (Kept = _)`]
   in
     map_every (fn name => qx_gen_tac name >> disch_then (assume_tac o CONV_RULE
       (RAND_CONV (TOP_DEPTH_CONV unwind) THENC REWR_CONV (GSYM markerTheory.Abbrev_def))))
       [`Shape`, `TagFlow`, `Flow`, `Open`, `b`, `r`, `H`, `C`, `Kept`] >>
     strip_tac >>
     List.foldr (fn (name,k) => specialize name k) (mp_tac o CONV_RULE unwind)
       names conditional_jump_strict_ports
   end) >>
  impl_tac >- simp[] >>
  disch_then (mp_tac o CONJUNCT2) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `z0` (qx_choose_then `z1`
      (fn th =>
         let val fields = CONJUNCTS th in
           map_every (strip_assume_tac o CONV_RULE (REDEPTH_CONV BETA_CONV))
             (List.take (fields, length fields - 1)) >>
           mk_asm "relocated packet" (List.last fields)
         end)))) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`z0`,`z1`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gvs[Abbr `H`] >> decide_tac)
  >- (gvs[Abbr `H`] >> decide_tac)
  >- (asm "relocated packet" (qspec_then `\l i. i`
        (ACCEPT_TAC o CONJUNCT1 o CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)))))
  >- (rpt gen_tac >> PairCases_on `t` >> metis_tac[])
  >- metis_tac[] >>
  qx_gen_tac `origin_map` >>
  (let val unwind = TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2) in
    asm_x "relocated packet" (qspec_then `origin_map`
      (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE o CONV_RULE unwind)) >>
    CONV_TAC unwind >> BETA_TAC
  end) >>
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
