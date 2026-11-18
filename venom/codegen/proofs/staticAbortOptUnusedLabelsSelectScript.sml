Theory staticAbortOptUnusedLabelsSelect
Ancestors arithmetic[qualified,ignore_grammar]
  staticAbortOptUnusedLabelsArms staticAbortOptUnusedLabelsSource
  staticAbortStraight asmSplice asmWf asmSymSem asmSem asmIR asmOptimizer
  symbolResolve list rich_list finite_map pred_set words

Theorem unused_label_one_selected_control:
  !p pre l tail cc req V e (rank:(num#num)->rat) pc height need tag boolean edge.
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
  let I = \u src bnew tg fr w.
    (!k n j. tg w k = SOME(n,j) ==> k < height w /\
       (fr k = SOME(n,j) \/ ?h. src k = SOME h /\ h < height u /\ tg u h = SOME(n,j))) /\
    (!k. boolean w k ==> k < height w /\
       (bnew k \/ ?h. src k = SOME h /\ h < height u /\ boolean u h))
  in
  let Descriptor = \u H.
    let hi = height u; ins = EL (pc u) p in
    case ins of
      AsmLabel l => ((\k. SOME k), (\k. NONE), (\k. F))
    | AsmPush bs =>
        ((\k. if k=0 then NONE else SOME(k-1)), (\k. NONE),
         (\k. k=0 /\ !t v.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK v ==>
            (EL 0 v.as_stack = 0w \/ EL 0 v.as_stack = 1w)))
    | AsmPushLabel l =>
        ((\k. if k=0 then NONE else SOME(k-1)),
         (\k. if k=0 then SOME(l,pc u) else NONE), (\k. F))
    | AsmPushOfst l d =>
        ((\k. if k=0 then NONE else SOME(k-1)),
         (\k. if k=0 /\ d=0 then SOME(l,pc u) else NONE), (\k. F))
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => ((\k. SOME(if k=0 then n else k-1)), (\k. NONE), (\k. F))
         | NONE =>
           case ALOOKUP swap_table name of
             SOME n => ((\k. SOME(if k=0 then n else if k=n then 0 else k)),
                        (\k. NONE), (\k. F))
           | NONE =>
               let a = asm_op_arity name; m = H + asm_op_arity name - hi in
               ((\k. if k<m then NONE else SOME(k-m+a)), (\k. NONE),
                (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                 !t v. LENGTH t.as_stack=hi /\
                   asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                     ins t = AsmOK v ==>
                   (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w))))
    | _ => ((\k. NONE), (\k. NONE), (\k. F))
  in
  let Flow = \(x:num#num) (y:num#num).
    let hi = height x; hj = height y; ins = EL (pc x) p in
    let inherit = \src fr bn. I x src bn tag fr y in
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t v.
              asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                (AsmPush bs) t = AsmOK v ==>
              (EL 0 v.as_stack = 0w \/ EL 0 v.as_stack = 1w))
    | AsmPushLabel l => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmPushOfst l d => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
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
                 let a = asm_op_arity name; m = hj + asm_op_arity name - hi in
                 a <= hi /\ hj = m+(hi-a) /\
                 ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
                 inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                   (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                    !t v. LENGTH t.as_stack=hi /\
                      asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                        ins t = AsmOK v ==>
                      (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w)))
    | _ => F
  in
  let C = \s n w. ?off. FLOOKUP (SND (compute_label_offsets s)) n = SOME off /\
                     off < dimword(:256) /\ FLOOKUP (build_offset_to_pc s) off = SOME w in
  let target = \s pc tg x y. ?n j. tg x 0 = SOME(n,j) /\ C s n (pc y) in
  let Control = \s pc tg x y.
    if EL (pc x) s = AsmOp "JUMP" then target s pc tg x y
    else if EL (pc x) s = AsmOp "JUMPI" then pc y = pc x+1 \/ target s pc tg x y
    else pc y = pc x+1
  in
  let Open = \(V:(num#num)->bool) X.
    let S = Shape p cc req pc height need tag boolean in
      FINITE V /\ X SUBSET V /\
      (!x. x IN V ==> ?t. S x t) /\
      (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
      (!x y. edge x y ==>
         x IN V DIFF X /\ y IN V /\ rank y < rank x /\
         Flow x y /\ Control p pc tag x y) /\
      (!x t. x IN V DIFF X /\ S x t ==>
         (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmRevert u \/
                asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmFault u) /\ u.as_requests=req) \/
         (?y u. edge x y /\
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
              p 1 t = AsmOK u /\ S y u))
  in
  let Reach = \(edge:(num#num)->(num#num)->bool) e x.
    ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))
  in
  let Rows = \V edge.
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
                    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)) /\
    (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Flow x y) /\
    (!x. x IN V ==>
      pc x < LENGTH p /\
      let h = height x in
      let fall = \y. pc y = pc x+1 in
      let arm = \P n. ?y. edge x y /\ P y /\ height y = n in
      let legal = \P n. !y. edge x y ==> P y /\ height y = n in
      let next = \n. arm fall n /\ legal fall n in
      let untagged = \a. !k. k<a ==> tag x k=NONE in
      let stop = \a. a<=h /\ untagged a /\ !y. ~edge x y in
      case EL (pc x) p of
        AsmLabel l => next h
      | AsmPush bs => next (h+1)
      | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
      | AsmPushOfst l d => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
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
                      1<=h /\ arm (target p pc tag x) (h-1) /\ legal (target p pc tag x) (h-1)
                   else if name="JUMPI" then
                      2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target p pc tag x) (h-2) /\
                      legal (\y. fall y \/ target p pc tag x y) (h-2)
                   else
                      ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                          untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
      | _ => F)
  in
  let d = LENGTH pre in
  let q = pre++tail in
  let r = splice_pc d 1 0 in
  let P = OPTION_MAP (\(n,j). (n,r j)) in
  let T = \x k. P (tag x k) in
  let pcQ = r o pc in
  let K = {u | u IN V /\ pc u<>d} in
  let Legal = \u (a:bool#(num#num)).
    edge u (SND a) /\
    if FST a then (EL (pc u) p = AsmOp "JUMP" \/ EL (pc u) p = AsmOp "JUMPI") /\
                  target p pc tag u (SND a)
    else EL (pc u) p <> AsmOp "JUMP" /\ pc(SND a)=pc u+1
  in
  let E = \z u w. u IN K /\ ?a. Legal u a /\ w=z u a in
  let Input = \u H src fresh bnew.
    !a. Legal u a ==> edge u (SND a) /\ height(SND a)=H /\ I u src bnew tag fresh (SND a) /\
      (if FST a then ?n j. tag u 0 = SOME(n,j) /\ C p n (pc(SND a))
       else pc(SND a)=pc u+1)
  in
  let Output = \u H src fresh bnew z.
    !a. Legal u a ==>
      z a IN V /\ pc(z a) <> d /\ rank(z a) < rank u /\ height(z a) = H /\
      I u src bnew T (P o fresh) (z a) /\
      (if pc(SND a) = d then
         ~FST a /\ edge (SND a) (z a) /\ pc(z a) = d+1 /\ height(z a) = height(SND a) /\
         (!k n j. tag (z a) k = SOME(n,j) ==> tag (SND a) k = SOME(n,j)) /\
         (!k. boolean (z a) k ==> boolean (SND a) k)
       else z a = SND a) /\
      (~FST a ==> r(pc(z a)) = r(pc u)+1) /\
      (FST a ==> z a = SND a /\ ?n j. tag u 0 = SOME(n,j) /\ T u 0 = SOME(n,r j) /\
          EL (pc(z a)) p = AsmLabel n /\ EL (r(pc(z a))) q = AsmLabel n /\
          C q n (r(pc(z a))))
  in
  let Layout =
    !x k n j. x IN V /\ tag x k = SOME(n,j) ==>
      j <> d /\ j < LENGTH p /\ r j < LENGTH q /\ EL (r j) q = EL j p /\
      T x k = SOME(n,r j) /\
      !w. C p n w ==> w <> d /\ INDEX_OF (AsmLabel n) p = SOME w /\
        INDEX_OF (AsmLabel n) q = SOME(r w) /\ C q n (r w)
  in
  p=pre++[AsmLabel l]++tail /\ asm_static_wf p /\
  ~MEM l (asm_label_refs p) /\ Open V {} /\ Rows V edge /\
  e IN V /\ (!x. x IN V ==> Reach edge e x) ==>
  asm_static_wf q /\ (!u. u IN K ==> pcQ u < LENGTH q /\ EL (pcQ u) q = EL (pc u) p) /\
  Layout /\
  ?z. (!u. u IN K ==> ?H src fresh bnew.
        (src,fresh,bnew) = Descriptor u H /\ Input u H src fresh bnew /\
        Output u H src fresh bnew (z u)) /\
      !u w. E z u w ==> u IN K /\ w IN K /\ rank w < rank u /\ Control q pcQ T u w
Proof
  rpt gen_tac >>
  map_every (fn name => qmatch_goalsub_abbrev_tac name >>
      CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ Shape`,`LET _ inherits`,`LET _ Descriptor`,`LET _ Flow`,`LET _ canon`,
     `LET _ target`,`LET _ Control`,`LET _ Open`,`LET _ Reach`,`LET _ Rows`,
     `LET _ d`,`LET _ q`,`LET _ r`,`LET _ P`,`LET _ tags`,`LET _ pcQ`,`LET _ kept`,
     `LET _ Legal`,`LET _ sel_edge`,`LET _ Input`,`LET _ Output`,`LET _ Layout`] >>
  strip_tac >>
  `!u. u IN kept <=> u IN V /\ pc u <> d` by simp[Abbr `kept`] >>
  `asm_label_refs q = asm_label_refs p` by
    (`asm_label_refs [AsmLabel l] = []` by simp[asm_label_refs_def] >>
     simp[Abbr `q`, label_refs_append]) >>
  `~MEM l (asm_label_refs q)` by
    (qpat_assum `asm_label_refs q = asm_label_refs p` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `asm_static_wf q` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `tail`,
                     `pat` |-> `[AsmLabel l]`, `repl` |-> `[]`] asm_splice_static_wf) >>
     (impl_tac >-
       ((conj_tac >- simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def] >>
        simp[] >>
        qpat_assum `~MEM l (asm_label_refs q)` mp_tac >>
        qpat_assum `asm_static_wf p` mp_tac >>
        simp[Abbr `q`, IgnAsm `asm_label_refs _ = asm_label_refs _`] >> (gvs[])))) >>
     simp[Abbr `q`]) >>
  `!u. u IN V ==> pc u < LENGTH p` by
    (qpat_x_assum `Rows V edge` mp_tac >>
     simp[Abbr `Rows`, IgnAsm `p = _`] >>
     disch_then (mp_tac o last o CONJUNCTS) >>
     simp[FORALL_AND_THM]) >>
  `!u. u IN kept ==> pcQ u < LENGTH q /\ EL (pcQ u) q = EL (pc u) p` by
    (gen_tac >> disch_tac >>
     `pc u < LENGTH p /\ pc u <> d` by metis_tac[] >>
     mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `tail`,
                      `pat` |-> `[AsmLabel l]`, `repl` |-> `[]`,
                      `i` |-> `(pc:(num#num)->num) u`]
                      (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch)) >>
     gvs[Abbr `pcQ`, Abbr `q`, Abbr `r`, Abbr `d`]) >>
  `!u y. edge u y ==> Flow u y` by
    (qpat_x_assum `Rows V edge` mp_tac >>
     simp[Abbr `Rows`, IgnAsm `p = _`] >>
     disch_then (mp_tac o hd o tl o CONJUNCTS) >>
     simp[FORALL_AND_THM]) >>
  `!u. u IN V ==> ?H. !y. edge u y ==> height y = H` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `Rows V edge` mp_tac >>
     simp[Abbr `Rows`, IgnAsm `p = _`] >>
     disch_then (qspec_then `u` mp_tac o last o CONJUNCTS) >>
     simp[IgnAsm `p = _`] >>
     Cases_on `EL (pc u) p` >> simp[IgnAsm `p = _`] >>
     TRY (strip_tac >> goal_assum (drule_at Any) >> NO_TAC) >>
     rename1 `EL (pc u) p = AsmOp name` >>
     let
       val stop = strip_tac >> qexists `0` >> simp[] >> NO_TAC
       val next = strip_tac >> qpat_assum `!y. edge u y ==> _` mp_tac >>
                  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
     in
       Cases_on `name = "INVALID"` >> simp[] >> TRY stop >>
       Cases_on `name = "REVERT"` >> simp[] >> TRY stop >>
       Cases_on `name = "SSTORE" \/ name = "TSTORE" \/ name = "LOG0" \/
                 name = "LOG1" \/ name = "LOG2" \/ name = "LOG3" \/ name = "LOG4"` >>
       simp[] >> TRY stop >>
       Cases_on `ALOOKUP dup_table name` >> simp[] >-
         (Cases_on `ALOOKUP swap_table name` >> simp[] >-
           (Cases_on `name = "JUMP"` >> simp[] >>
            TRY (Cases_on `name = "JUMPI"` >> simp[]) >> next) >> next) >> next
     end) >>
  `!u. u IN kept ==> ?H src fresh bnew.
       (src,fresh,bnew) = Descriptor u H /\ Input u H src fresh bnew` by
    (rpt gen_tac >> disch_tac >>
     `u IN V` by metis_tac[] >>
     qpat_assum `!u. u IN V ==> ?H. _` drule >> strip_tac >>
     Cases_on `Descriptor u H` >> rename1 `Descriptor u H = (src,frbn)` >>
     PairCases_on `frbn` >> rename1 `Descriptor u H = (src,fresh,bnew)` >>
     qexistsl [`H`,`src`,`fresh`,`bnew`] >>
     simp[Abbr `Input`, IgnAsm `p = _`] >>
     gen_tac >> disch_tac >>
     `edge u (SND a) /\ (if FST a then ?n j. tag u 0 = SOME(n,j) /\
        canon p n (pc (SND a)) else pc (SND a) = pc u + 1)` by
       (qpat_x_assum `Legal u a` mp_tac >>
        Cases_on `FST a` >> simp[Abbr `Legal`, Abbr `target`, IgnAsm `p = _`]) >>
     `height (SND a) = H` by metis_tac[] >>
     `Flow u (SND a)` by metis_tac[] >>
     simp[IgnAsm `p = _`] >>
     reverse conj_tac >- simp[Abbr `target`, IgnAsm `p = _`] >>
     qpat_x_assum `Descriptor u H = _` mp_tac >>
     qpat_x_assum `Flow u (SND a)` mp_tac >>
     qpat_x_assum `!u y. edge u y ==> Flow u y` kall_tac >>
     simp[Abbr `Descriptor`, Abbr `Flow`, IgnAsm `p = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `EL (pc u) p` >> simp[] >>
     TRY (rename1 `EL (pc u) p = AsmOp name` >>
       Cases_on `ALOOKUP dup_table name` >> simp[] >>
       TRY (Cases_on `ALOOKUP swap_table name` >> simp[])) >>
     rpt strip_tac >> gvs[]) >>
  `!u. u IN kept ==> ?H src fresh bnew za.
     (src,fresh,bnew) = Descriptor u H /\ Input u H src fresh bnew /\
     Layout /\ Output u H src fresh bnew za` by
    (gen_tac >> disch_tac >>
     `u IN V /\ pc u <> d` by metis_tac[] >>
     qpat_assum `!u. u IN kept ==> ?H src fresh bnew. _` drule >> strip_tac >>
     `Layout /\ (?za. Output u H src fresh bnew za)` suffices_by
       (strip_tac >> qexistsl [`H`, `src`, `fresh`, `bnew`, `za`] >> simp[]) >>
     qspecl_then [`p`,`pre`,`l`,`tail`,`cc`,`req`,`V`,`e`,`rank`,`pc`,
                  `height`,`need`,`tag`,`boolean`,`edge`,
                  `u`,`src`,`fresh`,`bnew`,`H`,`Legal u`,
                  `FST:bool#(num#num)->bool`, `SND:bool#(num#num)->num#num`]
       mp_tac unused_label_one_retained_arms >>
     CONV_TAC (LAND_CONV (REPEATC (REWR_CONV LET_THM THENC BETA_CONV))) >>
     (impl_tac >-
       (qpat_x_assum `Open V {}` mp_tac >>
        qpat_x_assum `Input u H src fresh bnew` mp_tac >>
        qpat_x_assum `!x. x IN V ==> Reach edge e x` mp_tac >>
        qpat_x_assum `pc u <> d` mp_tac >>
        simp[NoAsms, Abbr `Open`, Abbr `Shape`, Abbr `Flow`, Abbr `inherits`,
             Abbr `Control`, Abbr `target`, Abbr `canon`, Abbr `Reach`,
             Abbr `Input`, Abbr `d`, GSYM RIGHT_EXISTS_AND_THM] >>
        rpt (first_assum ACCEPT_TAC ORELSE strip_tac) >>
        qpat_assum `!x y. edge x y ==> x IN V /\ y IN V /\ _`
          (drule_then strip_assume_tac) >> simp[])) >>
     qpat_x_assum `Input u H src fresh bnew` mp_tac >>
     simp[NoAsms, Abbr `Layout`, Abbr `Output`, Abbr `Input`, Abbr `inherits`,
          Abbr `tags`, Abbr `P`, Abbr `target`, Abbr `canon`, Abbr `r`,
          Abbr `q`, Abbr `d`, GSYM RIGHT_EXISTS_AND_THM] >>
     strip_tac >> (impl_tac >-
       (simp[IgnAsm `p = _`] >> gen_tac >> disch_tac >>
        qpat_assum `!a. Legal u a ==> edge u (SND a) /\ _` (qspec_then `a` mp_tac) >>
        simp[IgnAsm `p = _`] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])) >>
     disch_then ACCEPT_TAC) >>
  `?u. u IN kept` by
    (Cases_on `pc e = d` >- (
       qspecl_then [`p`,`pre`,`l`,`tail`,`cc`,`req`,`V`,`e`,`rank`,`pc`,
                    `height`,`need`,`tag`,`boolean`,`edge`]
         mp_tac unused_label_source_contraction >>
       CONV_TAC (LAND_CONV (REPEATC (REWR_CONV LET_THM THENC BETA_CONV))) >>
       (impl_tac >-
          (qpat_assum `Open V {}` mp_tac >>
           qpat_assum `!x. x IN V ==> Reach edge e x` mp_tac >>
           simp[NoAsms, Abbr `Open`, Abbr `Shape`, Abbr `Flow`, Abbr `inherits`,
                Abbr `Control`, Abbr `target`, Abbr `canon`, Abbr `Reach`,
                GSYM RIGHT_EXISTS_AND_THM] >>
           rpt (first_assum ACCEPT_TAC ORELSE strip_tac) >>
           qpat_assum `!x y. edge x y ==> x IN V /\ y IN V /\ _`
             (drule_then strip_assume_tac) >> simp[])) >>
       disch_then (mp_tac o last o CONJUNCTS) >>
       disch_then (qspec_then `e` mp_tac) >>
       simp[Abbr `d`, IgnAsm `p = _`] >>
       disch_then (qx_choose_then `y` strip_assume_tac) >>
       qexists `y` >> simp[]) >>
     qexists `e` >> simp[]) >>
  `Layout` by metis_tac[] >>
  `!u. ?za. u IN kept ==> ?H src fresh bnew.
      (src,fresh,bnew) = Descriptor u H /\ Input u H src fresh bnew /\
      Output u H src fresh bnew za` by
    (qx_gen_tac `x0` >> Cases_on `x0 IN kept` >-
       (qpat_assum `!u. u IN kept ==> ?H src fresh bnew za. _`
          (qspec_then `x0` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        strip_tac >> qexists `za` >> disch_tac >>
        qexistsl [`H`,`src`,`fresh`,`bnew`] >> simp[IgnAsm `p = _`]) >>
     qexists `ARB` >> simp[IgnAsm `!u. u IN kept <=> _`]) >>
  pop_assum (mp_tac o CONV_RULE SKOLEM_CONV) >>
  disch_then (qx_choose_then `selected` assume_tac) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists `selected` >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `x0` >> qx_gen_tac `w0` >>
  simp[NoAsms, Abbr `sel_edge`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `arm` strip_assume_tac)) >>
  qpat_assum `!u. u IN kept ==> ?H src fresh bnew. _ /\ _ /\ Output _ _ _ _ _ _`
    (qspec_then `x0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `Output x0 _ _ _ _ (selected x0)` mp_tac >>
  simp[NoAsms, Abbr `Output`] >>
  disch_then (qspec_then `arm` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `selected x0 arm IN kept` by simp[] >>
  `EL (pcQ x0) q = EL (pc x0) p` by metis_tac[] >>
  simp[IgnAsm `p = _`, Abbr `Control`] >>
  Cases_on `FST arm` >> gvs[Abbr `Legal`, Abbr `pcQ`, IgnAsm `p = _`] >>
  simp[NoAsms, Abbr `target`, GSYM RIGHT_EXISTS_AND_THM] >>
  rename1 `tag x0 0 = SOME (name,origin)` >>
  TRY disj2_tac >> qexistsl [`name`,`r origin`] >>
  simp[Abbr `tags`, Abbr `P`]
QED
