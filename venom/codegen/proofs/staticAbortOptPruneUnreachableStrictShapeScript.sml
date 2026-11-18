Theory staticAbortOptPruneUnreachableStrictShape
Ancestors
  staticAbortOptPruneUnreachableShape asmOptimizer asmSem asmSymSem
  stackOpAsmSim finite_map words arithmetic list pred_set

Theorem prune_one_strict_shapes:
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
  let Hit = \p l dest. ?off.
    FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest
  in
  !pre t x tail s env n ss cc req V edge e pc height need tag boolean.
    let p = pre ++ [t;x] ++ tail in
    let q = pre ++ [t] ++ tail in
    let d = LENGTH pre + 1 in
    let r = \i. if i<d then i else i-1 in
    let Z = \l j. j<LENGTH q /\ (EL j q=AsmPushLabel l \/ EL j q=AsmPushOfst l 0) in
    let pick = \l. @j. Z l j in
    let tagQ = \v k. OPTION_MAP (\(l,i). (l,if i=d then pick l else r i)) (tag v k) in
    asm_terminal_op t /\ ~asm_reachable_marker x /\ asm_static_wf p /\
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK ss /\
    (!k l origin. tag e k = SOME(l,origin) ==>
       k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0) /\
    (!k. boolean e k ==> k < LENGTH ss.sym_stack /\
       (EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w)) /\
    (!v. v IN V ==> ?t. Shape p cc req pc height need tag boolean v t) /\
    (!a b. edge a b ==> Flow p pc height tag boolean a b) /\
    (!v. v IN V ==> Reach edge e v) /\
    (!v k l. v IN V /\ tag v k = SOME(l,d) ==> ?j. tag e j = SOME(l,d)) /\
    (!v k l j. v IN V /\ tagQ v k = SOME(l,j) ==>
       k < height v /\ Z l j /\ ?dest. Hit q l dest) ==>
    !v. v IN V ==> ?u. Shape q cc req (r o pc) height need tagQ boolean v u
Proof
  map_every (fn q => qmatch_goalsub_abbrev_tac q >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ Shape`, `LET _ Flow`, `LET _ Reach`, `LET _ Hit`] >>
  rpt gen_tac >>
  map_every (fn q => qmatch_goalsub_abbrev_tac q >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ p`, `LET _ q`, `LET _ d`, `LET _ r`, `LET _ Z`, `LET _ pick`, `LET _ tagQ`] >>
  strip_tac >> gen_tac >> strip_tac >>
  qabbrev_tac `pickW = \l. @j. j < LENGTH q /\
     (EL j q = AsmPushLabel l \/
      (?delta. EL j q = AsmPushOfst l delta) \/ EL j q = AsmDataLabel l)` >>
  qabbrev_tac `tagW = \v k. OPTION_MAP (\(l,i). (l,if i=d then pickW l else r i)) (tag v k)` >>
  `?u. Shape q cc req (r o pc) height need tagW boolean v u` by
    (unabbrev_all_tac >>
     rule_assum_tac (SIMP_RULE bool_ss [LET_THM]) >>
     SIMP_TAC bool_ss [LET_THM] >>
     irule (SIMP_RULE bool_ss [LET_THM] prune_one_live_shapes) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  rename1 `Shape q cc req _ height need tagW boolean v u` >>
  qexists `u` >>
  qpat_x_assum `Shape q cc req _ height need tagW boolean v u` mp_tac >>
  simp[Abbr `Shape`] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!v k l j. v IN V /\ tagQ v k = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  `?i. tagW v k = SOME(l,i)` by
    (qpat_x_assum `tagQ v k = SOME(l,origin)` mp_tac >>
     Cases_on `tag v k` >- simp[Abbr `tagQ`] >>
     rename1 `tag v k = SOME pair` >> PairCases_on `pair` >>
     simp[Abbr `tagQ`, Abbr `tagW`]) >>
  qpat_assum `!k l origin. tagW v k = _ ==> _` (drule_then strip_assume_tac) >>
  fs[Abbr `Z`] >> metis_tac[]
QED
