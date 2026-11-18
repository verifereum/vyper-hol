Theory staticAbortOptPruneUnreachableShape
Ancestors
  staticAbortOptPruneUnreachableLayout staticAbortOptPruneUnreachablePrefix
  asmOptimizer asmSem asmSymSem stackOpAsmSim finite_map words arithmetic list
  pred_set

Theorem reachable_tag_boolean_disjoint:
  let Flow =
    \p pc height tag boolean (a:num#num) (b:num#num).
    let hi = height a; hj = height b; ins = EL (pc a) p in
    let inherit =
      \(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag b k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
           ?j. src k = SOME j /\ j < hi /\ tag a j = SOME(l,origin))) /\
        (!k. boolean b k ==> k < hj /\
           (bnew k \/ ?j. src k = SOME j /\ j < hi /\ boolean a j))
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
          (\k. if k=0 then SOME(l,pc a) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc a) else NONE) (\k. F)
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
  let Reach = \(edge:(num#num)->(num#num)->bool) e v.
    ?n (path:num->num#num).
      path 0=e /\ path n=v /\ !k. k<n ==> edge (path k) (path(SUC k))
  in
  !p E e pc height tag boolean ss v.
    (!a b. E a b ==> Flow p pc height tag boolean a b) /\
    (!k l origin. tag e k = SOME(l,origin) ==> EL k ss.sym_stack = Lab l 0) /\
    (!k. boolean e k ==> EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w) /\
    Reach E e v ==>
    !k l origin. tag v k = SOME(l,origin) ==> ~boolean v k
Proof
  qmatch_goalsub_abbrev_tac `LET _ Flow` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  `!a b k l origin. E a b /\ tag b k = SOME(l,origin) /\ boolean b k ==>
     ?j. tag a j = SOME(l,origin) /\ boolean a j` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!a b. E a b ==> _` drule >>
     Cases_on `EL (pc a) p` >> simp[Abbr `Flow`] >>
     TRY (qmatch_goalsub_rename_tac `ALOOKUP dup_table opn` >>
          Cases_on `ALOOKUP dup_table opn` >> simp[] >>
          TRY (Cases_on `ALOOKUP swap_table opn` >> simp[])) >>
     strip_tac >>
     qpat_x_assum `!k l origin. tag b k = _ ==> _`
       (qspecl_then [`k`,`l`,`origin`] mp_tac) >>
     qpat_x_assum `!k. boolean b k ==> _` (qspec_then `k` mp_tac) >>
     Cases_on `k = 0` >> simp[] >>
     TRY (qmatch_goalsub_rename_tac `k < height b + aarity - height a` >>
          Cases_on `k < height b + aarity - height a` >> simp[]) >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `!a b. E a b ==> _` kall_tac >>
  qpat_x_assum `Abbrev (Flow = _)` kall_tac >>
  `!i. i <= n ==> !k l origin. tag (path i) k = SOME(l,origin) ==>
      ~boolean (path i) k` by
    (Induct >- (simp[] >> rpt strip_tac >>
                 qpat_assum `!k l origin. tag e k = _ ==> _`
                   (drule_then assume_tac) >>
                 qpat_assum `!k. boolean e k ==> _` drule >> simp[]) >>
     rpt strip_tac >>
     `i < n /\ i <= n` by decide_tac >> metis_tac[]) >>
  metis_tac[LESS_EQ_REFL]
QED

(* These witnesses certify satisfiability, not execution or root actuality. *)
Theorem prune_one_live_shapes:
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
  let Flow =
    \p pc height tag boolean (a:num#num) (b:num#num).
    let hi = height a; hj = height b; ins = EL (pc a) p in
    let inherit =
      \(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag b k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
           ?j. src k = SOME j /\ j < hi /\ tag a j = SOME(l,origin))) /\
        (!k. boolean b k ==> k < hj /\
           (bnew k \/ ?j. src k = SOME j /\ j < hi /\ boolean a j))
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
          (\k. if k=0 then SOME(l,pc a) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc a) else NONE) (\k. F)
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
  let Reach = \(edge:(num#num)->(num#num)->bool) e v.
    ?n (path:num->num#num).
      path 0=e /\ path n=v /\ !k. k<n ==> edge (path k) (path(SUC k))
  in
  !pre t x tail s env n ss cc req live E e pc height need tag boolean.
    let p = pre ++ [t;x] ++ tail in
    let q = pre ++ [t] ++ tail in
    let d = LENGTH pre + 1 in
    let r = \i. if i < d then i else i-1 in
    let R = \prog l j. j < LENGTH prog /\
      (EL j prog = AsmPushLabel l \/
       (?delta. EL j prog = AsmPushOfst l delta) \/ EL j prog = AsmDataLabel l) in
    let pick = \l. @j. R q l j in
    let tag' = \v k. OPTION_MAP (\(l,i). (l,if i=d then pick l else r i)) (tag v k) in
    asm_terminal_op t /\ ~asm_reachable_marker x /\ asm_static_wf p /\
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK ss /\
    (!k l origin. tag e k = SOME(l,origin) ==>
       k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0) /\
    (!k. boolean e k ==> k < LENGTH ss.sym_stack /\
       (EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w)) /\
    (!v. v IN live ==> ?t. Shape p cc req pc height need tag boolean v t) /\
    (!a b. E a b ==> Flow p pc height tag boolean a b) /\
    (!v. v IN live ==> Reach E e v) /\
    (!v k l. v IN live /\ tag v k = SOME(l,d) ==> ?j. tag e j = SOME(l,d)) ==>
    !v. v IN live ==> ?u. Shape q cc req (r o pc) height need tag' boolean v u
Proof
  map_every (fn q => qmatch_goalsub_abbrev_tac q >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ Shape`, `LET _ Flow`, `LET _ Reach`] >>
  rpt gen_tac >>
  map_every (fn q => qmatch_goalsub_abbrev_tac q >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ p`, `LET _ q`, `LET _ d`, `LET _ r`, `LET _ R`, `LET _ pick`, `LET _ tag'`] >>
  strip_tac >>
  gen_tac >> strip_tac >>
  `!k l origin. tag v k = SOME(l,origin) ==> ~boolean v k` by
    (`!k l origin. tag e k = SOME(l,origin) ==> EL k ss.sym_stack = Lab l 0`
       by metis_tac[] >>
     `!k. boolean e k ==> EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w`
       by metis_tac[] >>
     qpat_x_assum `!v. v IN live ==> Reach E e v` (drule_then assume_tac) >>
     gns[Abbr `Flow`, Abbr `Reach`] >>
     drule (SIMP_RULE (boss_ss()) [LET_THM] reachable_tag_boolean_disjoint) >>
     disch_then (qspecl_then [`e`,`ss`,`v`] mp_tac) >> simp[]) >>
  qpat_x_assum `!a b. E a b ==> _` kall_tac >>
  qpat_x_assum `Abbrev (Flow = _)` kall_tac >>
  `!l old dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME old /\
      FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
      ?fresh. FLOOKUP (SND(compute_label_offsets q)) l = SOME fresh /\
        fresh < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) fresh = SOME (r dest)` by
    (mp_tac (Q.SPECL [`pre`,`t`,`x`,`tail`] prune_one_canonical_layout) >>
     fs[Abbr `p`, Abbr `q`, Abbr `r`, Abbr `d`] >> metis_tac[]) >>
  `!l i. R p l i /\ (i = d ==> R q l (pick l)) ==>
         R q l (if i = d then pick l else r i)` by
    (rpt gen_tac >>
     mp_tac (Q.SPECL [`pre`,`t`,`x`,`tail`] prune_one_canonical_layout) >>
     fs[Abbr `p`, Abbr `q`, Abbr `r`, Abbr `R`, Abbr `d`] >>
     disch_then (qspecl_then [`l`,`i`,`pick`] mp_tac o cj 2) >> simp[]) >>
  `!l. (?j. tag e j = SOME(l,d)) ==> R q l (pick l)` by
    (rpt strip_tac >>
     `?i. R q l i` suffices_by (disch_then (mp_tac o SELECT_RULE) >> simp[Abbr `pick`]) >>
     mp_tac prune_one_stopped_prefix >>
     fs[Abbr `p`, Abbr `q`] >>
     disch_then (qspecl_then [`j`,`l`] mp_tac o cj 3) >>
     simp[Abbr `R`]) >>
  qpat_x_assum `!v. v IN live ==> ?t. Shape _ _ _ _ _ _ _ _ v t` drule >>
  simp[Abbr `Shape`] >> disch_then (qx_choose_then `src` strip_assume_tac) >>
  qexists `src with <| as_pc := r (pc v); as_stack := GENLIST
     (\k. case tag v k of NONE => 0w | SOME(l,i) =>
       n2w (THE (FLOOKUP (SND(compute_label_offsets q)) l))) (height v) |>` >>
  simp[] >> conj_tac >- (strip_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >>
      Cases_on `tag v k` >- simp[Abbr `tag'`] >>
      rename1 `tag v k = SOME pair` >> PairCases_on `pair` >>
      simp[Abbr `tag'`] >> strip_tac >>
      qpat_x_assum `!k l origin. tag v k = _ ==> _ /\ _`
        (drule_then strip_assume_tac) >>
      `R p pair0 pair1` by simp[Abbr `R`] >>
      `R q pair0 (if pair1 = d then pick pair0 else r pair1)` by metis_tac[] >>
      qpat_x_assum `!l old dest. FLOOKUP (SND(compute_label_offsets p)) l = _ /\ _ ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_x_assum `pair0 = l` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `(if pair1 = d then pick pair0 else r pair1) = origin`
        (SUBST_ALL_TAC o SYM) >>
      gns[Abbr `R`] >> qexistsl [`fresh`,`r dest`] >> simp[]) >>
  gen_tac >> disch_tac >>
  `tag v k = NONE` by
    (Cases_on `tag v k` >- simp[] >>
     rename1 `tag v k = SOME pair` >> PairCases_on `pair` >> metis_tac[]) >>
  `k < height v` by metis_tac[] >> simp[]
QED
