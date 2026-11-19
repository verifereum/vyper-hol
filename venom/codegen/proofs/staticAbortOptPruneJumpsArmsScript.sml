(* Contract a structural arm without selecting a branch by its runtime value. *)
Theory staticAbortOptPruneJumpsArms
Ancestors
  staticAbortOptPruneJumpsBypass asmSplice asmToBytecodeProofs
  symInstPieces asmSymBridge asmSymSem asmWf stackOpAsmSim
  asmSem asmIR pred_set finite_map list rich_list arithmetic words

Theorem prune_jump_site_retained_arms:
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
  !port_target. port_target = (\x y.
      ?l origin off. tag x 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !b. b = LENGTH pre ==>
  !r. r = splice_pc b 2 0 ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  !d. d = (\i. if pc i = b+1 then 1 else 0) ==>
  !Inherit. Inherit = (\w j.
    (!k l i. tag w k = SOME(l,i) ==>
       k < height w /\ (fresh (k+j) = SOME(l,i) \/
       ?h. src (k+j) = SOME h /\ h < height u /\ tag u h = SOME(l,i))) /\
    (!k. boolean w k ==> k < height w /\
       (bnew (k+j) \/ ?h. src (k+j) = SOME h /\ h < height u /\ boolean u h))) ==>
  !Target. Target = (\w.
    ?l org off. tag u 0 = SOME(l,org) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc w)) ==>
  p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail /\
  asm_static_wf p /\
  (FINITE V /\ {} SUBSET V /\
    (!x:num#num. x IN V ==> ?t. Shape p cc req pc height need tag boolean x t) /\
    (!x. x IN V DIFF {} ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF {} /\ y IN V /\ (rank:(num#num)->num) y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then port_target x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ port_target x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF {} /\ Shape p cc req pc height need tag boolean x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ Shape p cc req pc height need tag boolean y u))) /\
  pc u <> b /\ pc u <> b+1 /\
  (!a:'arm. legal a ==>
     edge u (v a) /\ height (v a) = H /\ Inherit (v a) 0 /\
     (if taken a then Target (v a) else pc (v a) = pc u + 1)) ==>
  ?z. !a. legal a ==>
    z a IN V /\ rank (z a) < rank u /\
    (if pc (v a) = b \/ pc (v a) = b+1 then
       pc (z a) = b+2 /\ r (pc (z a)) = b /\
       (if pc (v a) = b then
          ?j. j IN V /\ edge (v a) j /\ pc j = b+1 /\
              tag j 0 = SOME(x,b) /\ edge j (z a)
        else edge (v a) (z a) /\ (?org. tag (v a) 0 = SOME(x,org)))
     else z a = v a /\ r (pc (z a)) = r (pc (v a))) /\
    height (z a) + d (v a) = H /\ Inherit (z a) (d (v a)) /\ d (v a) = 0 /\
    (if taken a then
       z a = v a /\ Target (z a) /\
       (?l. EL (pc (z a)) p = AsmLabel l /\ EL (r (pc (z a))) q = AsmLabel l)
     else r (pc (z a)) = r (pc u) + 1)
Proof
  map_every (fn name => qx_gen_tac name >>
    disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def] o
      CONV_RULE (RAND_CONV (REDEPTH_CONV Unwind.UNWIND_FORALL_CONV))))
    [`Shape`,`Flow`,`port_target`,`b`,`r`,`q`,`d`,`Inherit`,`Target`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  `!i. i IN V ==> pc i < LENGTH p /\
    (!k l org. tag i k = SOME(l,org) ==> k < height i) /\
    (!k. boolean i k ==> k < height i)` by suspend "bounds" >>
  `!i j. edge i j ==> j IN V /\ rank j < rank i` by
    (qpat_assum `FINITE V /\ _` mp_tac >>
     simp[SimpLHS, NoAsms, DIFF_EMPTY] >> metis_tac[]) >>
  `EL b p = AsmPushLabel x /\ EL (b+1) p = AsmOp "JUMP"` by
    (simp[Abbr `b`, EL_APPEND_EQN] >> EVAL_TAC) >>
  `!w. w IN V /\
      (pc w = b \/ (pc w = b+1 /\ (!l org. tag w 0 = SOME(l,org) ==> l=x))) ==>
      ?e. e IN V /\ pc e = b+2 /\ rank e < rank w /\
        (if pc w = b then
           ?j. j IN V /\ edge w j /\ pc j = b+1 /\ tag j 0 = SOME(x,b) /\ edge j e
         else edge w e /\ (?org. tag w 0 = SOME(x,org))) /\
        height w = height e + d w /\
        (!k l org. tag e k = SOME(l,org) ==> tag w (k+d w) = SOME(l,org)) /\
        (!k. boolean e k ==> boolean w (k+d w))` by suspend "bypass" >>
  CONV_TAC (HO_REWR_CONV (GSYM SKOLEM_THM)) >>
  qx_gen_tac `a` >> Cases_on `legal a` >> simp[] >>
  qpat_assum `!a. legal a ==> _` (qspec_then `a` (drule_then strip_assume_tac)) >>
  `v a IN V /\ rank (v a) < rank u` by metis_tac[] >>
  `taken a ==> ?l. EL (pc (v a)) p = AsmLabel l` by
    (disch_tac >>
     qpat_assum `taken a` (fn th =>
       qpat_assum `if taken a then Target (v a) else _`
         (mp_tac o PURE_REWRITE_RULE [th, COND_CLAUSES])) >>
     qunabbrev_tac `Target` >> BETA_TAC >>
     disch_then (qx_choose_then `l` (qx_choose_then `org`
       (qx_choose_then `off` strip_assume_tac))) >>
     drule_then ACCEPT_TAC offset_to_pc_label) >>
  `pc (v a) <> b+1 /\ (taken a ==> pc (v a) <> b)` by suspend "ingress" >>
  simp[] >>
  Cases_on `pc (v a) = b`
  >- suspend "hit"
  >> suspend "miss"
QED

Resume prune_jump_site_retained_arms[bounds]:
  qpat_assum `FINITE V /\ _` mp_tac >>
  simp[SimpLHS, NoAsms, Abbr `port_target`, DIFF_EMPTY] >>
  disch_then strip_assume_tac >> qx_gen_tac `i` >> disch_tac >>
  (conj_tac >- metis_tac[]) >>
  qpat_assum `!i. i IN V ==> ?t. Shape _ _ _ _ _ _ _ _ i t`
    (qspec_then `i` (drule_then (qx_choose_then `t` mp_tac))) >>
  simp[SimpLHS, NoAsms, Abbr `Shape`] >> metis_tac[]
QED

Resume prune_jump_site_retained_arms[bypass]:
  qx_gen_tac `w` >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  mp_tac (Q.INST [`v` |-> `w`] (SPEC_ALL
    (CONV_RULE (REDEPTH_CONV (Unwind.UNWIND_FORALL_CONV ORELSEC BETA_CONV))
      prune_jump_site_bypass))) >>
  qunabbrev_tac `d` >> qunabbrev_tac `b` >> BETA_TAC >>
  (impl_tac >-
    ((conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `FINITE V /\ _` mp_tac >>
     qunabbrev_tac `port_target` >> qunabbrev_tac `Flow` >> qunabbrev_tac `Shape` >>
     CONV_TAC (REDEPTH_CONV BETA_CONV) >>
     disch_then ACCEPT_TAC)) >>
  disch_then (qx_choose_then `e`
    (MAP_EVERY assume_tac o (fn ths => List.take(ths,7)) o CONJUNCTS)) >>
  qexists_tac `e` >>
  `(if pc w = LENGTH pre + 1 then (1:num) else 0) =
   (if pc w = LENGTH pre then 0 else 1)` by
    (Cases_on `pc w = LENGTH pre`
     >- simp[] >>
     metis_tac[]) >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Resume prune_jump_site_retained_arms[ingress]:
  Cases_on `taken a`
  >- (qpat_assum `taken a ==> ?l. _`
        (drule_then (qx_choose_then `l` assume_tac)) >>
      metis_tac[asm_inst_distinct]) >>
  `pc (v a) = pc u + 1` by metis_tac[] >> simp[]
QED

Resume prune_jump_site_retained_arms[hit]:
  `~taken a` by metis_tac[] >>
  `pc (v a) = pc u + 1` by fs[] >>
  qpat_assum `!w. w IN V /\ _ ==> ?e. e IN V /\ _`
    (qspec_then `v a` mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `e` strip_assume_tac) >>
  qexists_tac `e` >>
  `d (v a) = 0` by simp[Abbr `d`] >>
  `pc u + 1 = b` by metis_tac[] >>
  `pc u < b` by (qpat_assum `pc u + 1 = b` mp_tac >> decide_tac) >>
  `r (pc e) = b /\ r (pc u) + 1 = b` by simp[Abbr `r`, splice_pc_def] >>
  `rank e < rank u` by metis_tac[LESS_TRANS] >>
  qpat_assum `pc (v a) = b` (fn heq =>
    qpat_assum `if pc (v a) = b then _ else _`
      (assume_tac o REWRITE_RULE [heq])) >>
  `Inherit e 0` by
    (qpat_x_assum `Inherit (v a) 0` mp_tac >>
     qpat_assum `!k l org. tag e k = _ ==> _` mp_tac >>
     qpat_assum `!k. boolean e k ==> _` mp_tac >>
     qpat_assum `!i. i IN V ==> _` (qspec_then `e` (drule_then mp_tac)) >>
     qpat_assum `d (v a) = 0` (fn th => simp[NoAsms, Abbr `Inherit`, th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> metis_tac[]) >>
  simp[] >>
  qpat_assum `?j. j IN V /\ edge (v a) j /\ _` (qx_choose_then `j` strip_assume_tac) >>
  qexists_tac `j` >> simp[]
QED

Resume prune_jump_site_retained_arms[miss]:
  `r (pc u + 1) = r (pc u) + 1` by
    (qunabbrev_tac `r` >> irule (cj 1 splice_pc_next) >>
     qpat_assum `pc u <> b` mp_tac >> qpat_assum `pc u <> b+1` mp_tac >>
     decide_tac) >>
  qexists_tac `v a` >> simp[Abbr `d`, IgnAsm `p = _`] >>
  Cases_on `taken a` >> fs[IgnAsm `p = _`]
  >- ((rename1 `EL (pc (v a)) p = AsmLabel lab` >>
      `pc (v a) < LENGTH p` by metis_tac[] >>
      `pc (v a) < b \/ b+2 <= pc (v a)` by
        (qpat_assum `pc (v a) <> b` mp_tac >>
         qpat_assum `pc (v a) <> b+1` mp_tac >> decide_tac) >>
      `EL (r (pc (v a))) q = EL (pc (v a)) p` by
        (`EL (r (pc (v a))) (pre ++ [] ++ (AsmLabel x::tail)) =
          EL (pc (v a)) (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ (AsmLabel x::tail))`
           suffices_by
             (qunabbrev_tac `q` >> qpat_assum `p = _`
               (fn th => simp[NoAsms, APPEND_ASSOC_CONS, th])) >>
         `r = splice_pc (LENGTH pre) (LENGTH [AsmPushLabel x; AsmOp "JUMP"])
                       (LENGTH ([]:asm_inst list))` by simp[Abbr `r`, Abbr `b`] >>
         pop_assum SUBST1_TAC >> irule (cj 2 splice_fetch) >>
         qpat_assum `p = _` (fn th =>
           qpat_assum `pc (v a) < LENGTH p`
             (assume_tac o SRULE [th, APPEND_ASSOC_CONS])) >>
         simp[Abbr `b`, APPEND_ASSOC_CONS]) >>
      qexists_tac `lab` >> simp[IgnAsm `p = _`] >> (metis_tac[NoAsms, APPEND_ASSOC_CONS, Abbr `r`, Abbr `b`, IgnAsm `p = _`, cj 2 splice_fetch]))) >>
  simp[]
QED

Finalise prune_jump_site_retained_arms
