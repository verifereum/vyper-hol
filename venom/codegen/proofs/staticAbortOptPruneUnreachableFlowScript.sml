(* Rooted origin traceback and Flow transport at a singleton deletion. *)
Theory staticAbortOptPruneUnreachableFlow
Ancestors
  staticAbortStraight stackOpAsmSim asmOptimizer asmSem
  alist arithmetic finite_map list option pair pred_set words

Triviality prune_straight_boolean_result:
  static_abort_straight name m /\ asm_returns_zero_or_one (AsmOp name) /\
  asm_step lo o2pc (AsmOp name) s = AsmOK u ==>
  EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w
Proof
  strip_tac >> drule static_abort_straight_known >> strip_tac >>
  `MEM name ["LT";"GT";"SLT";"SGT";"EQ";"ISZERO"]` by
    gvs[asm_returns_zero_or_one_def] >>
  pop_assum mp_tac >> simp[] >> strip_tac >> gvs[] >>
  fs[asm_step_def, asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  Cases_on `s.as_stack` >> gvs[asm_unop_def,asm_binop_def] >>
  TRY (rename1 `s.as_stack = x::xs` >> Cases_on `xs` >> gvs[asm_binop_def]) >>
  simp[asm_next_def] >>
  `!b. vfmExecution$b2w b = (0w:bytes32) \/ vfmExecution$b2w b = (1w:bytes32)` by
    (Cases >> simp[]) >> pop_assum MATCH_ACCEPT_TAC
QED

Theorem prune_one_rooted_flow:
  !Inherit Flow.
  Inherit = (\height tag boolean (a:num#num) (b:num#num)
      (src:num->num option) (fresh:num->(string#num)option) (bnew:num->bool).
    (!k l origin. tag b k = SOME(l,origin) ==>
       k < height b /\ (fresh k = SOME(l,origin) \/
         ?j. src k = SOME j /\ j < height a /\ tag a j = SOME(l,origin))) /\
    (!k. boolean b k ==> k < height b /\
       (bnew k \/ ?j. src k = SOME j /\ j < height a /\ boolean a j))) ==>
  Flow = (\p pc height tag boolean (a:num#num) (b:num#num).
    !hi hj ins inherit.
    hi = height a ==> hj = height b ==> ins = EL (pc a) p ==>
    inherit = Inherit height tag boolean a b ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !s u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) s = AsmOK u ==>
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
               !ar m. ar = asm_op_arity name ==> m = hj + ar - hi ==>
               ar <= hi /\ hj = m+(hi-ar) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+ar)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !s u. LENGTH s.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins s = AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !pre t x tail V e pc height tag boolean edge p q d r.
    p = pre ++ [t;x] ++ tail ==> q = pre ++ [t] ++ tail ==>
    d = LENGTH pre+1 ==> r = (\i. if i<d then i else i-1) ==>
    e IN V /\ (!v. v IN V ==> ?n (path:num->num#num).
      path 0=e /\ path n=v /\ !k. k<n ==> edge (path k) (path (SUC k))) /\
    (!a b. edge a b ==> a IN V /\ b IN V /\ Flow p pc height tag boolean a b) /\
    (!a b name. edge a b /\ EL (pc a) p = AsmOp name ==>
       IS_SOME (ALOOKUP dup_table name) \/ IS_SOME (ALOOKUP swap_table name) \/
       name="JUMP" \/ name="JUMPI" \/ (?m. static_abort_straight name m)) /\
    (!a. a IN V ==> pc a<>d /\ r (pc a)<LENGTH q /\ EL (r (pc a)) q=EL (pc a) p) ==>
    (!v k l. v IN V /\ tag v k=SOME(l,d) ==> ?j. tag e j=SOME(l,d)) /\
    (!a b. edge a b ==> Flow q (r o pc) height
      (\v k. OPTION_MAP (\(l,i). (l,if i=d then
        (@j. j<LENGTH q /\ (EL j q=AsmPushLabel l \/ EL j q=AsmPushOfst l 0))
        else r i)) (tag v k)) boolean a b)
Proof
  ntac 2 gen_tac >>
  ntac 2 (disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def] o
    SIMP_RULE (pure_ss ++ boolSimps.UNWIND_ss) [])) >>
  rpt gen_tac >>
  ntac 4 (disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])) >>
  qmatch_goalsub_abbrev_tac `Flow q (r o pc) height tagQ boolean _ _` >>
  strip_tac >> conj_tac >- suspend "traceback" >> suspend "transport"
QED

Resume prune_one_rooted_flow[traceback]:
  `!a b k l. edge a b /\ tag b k = SOME(l,d) ==> ?j. tag a j = SOME(l,d)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!a b. edge a b ==> _` (drule_then strip_assume_tac) >>
     `pc a <> d` by metis_tac[] >>
     qpat_x_assum `Flow p pc height tag boolean a b` mp_tac >>
     Cases_on `EL (pc a) p` >> simp[Abbr `Flow`,Abbr `Inherit`] >>
     TRY (qmatch_goalsub_rename_tac `ALOOKUP dup_table opn` >>
          Cases_on `ALOOKUP dup_table opn` >> simp[] >>
          TRY (Cases_on `ALOOKUP swap_table opn` >> simp[])) >>
     strip_tac >>
     qpat_x_assum `!k l origin. tag b k = _ ==> _`
       (qspecl_then [`k`,`l`,`d`] mp_tac) >>
     simp[AllCaseEqs()] >> strip_tac >> goal_assum (drule_at Any)) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!v. v IN V ==> ?n path. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!a b. edge a b ==> _` kall_tac >>
  `!i. i <= n ==> !s. tag (path i) s = SOME(l,d) ==> ?j. tag e j = SOME(l,d)` by
    (Induct >> simp[] >- metis_tac[] >> rpt strip_tac >>
     `i < n /\ i <= n` by decide_tac >>
     `edge (path i) (path (SUC i))` by simp[] >>
     qpat_assum `!a b k l. edge a b /\ _ ==> _`
       (drule_all_then strip_assume_tac) >>
     qpat_assum `i <= n ==> _` (drule_then drule) >> simp[]) >>
  qpat_x_assum `!i. i <= n ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Resume prune_one_rooted_flow[transport]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a b. edge a b ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!a. a IN V ==> pc a <> d /\ _` (qspec_then `a` mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `retag = \(l,i). (l,if i=d then
    (@j. j<LENGTH q /\ (EL j q=AsmPushLabel l \/ EL j q=AsmPushOfst l 0)) else r i)` >>
  `!k. tagQ a k = OPTION_MAP retag (tag a k) /\ tagQ b k = OPTION_MAP retag (tag b k)` by
    simp[Abbr `tagQ`,Abbr `retag`] >>
  `!l. retag (l,pc a) = (l,r (pc a))` by simp[Abbr `retag`] >>
  `!src f g bn bq.
       Inherit height tag boolean a b src f bn /\
       (!k. g k = OPTION_MAP retag (f k)) /\ (!k. bn k ==> bq k) ==>
       Inherit height tagQ boolean a b src g bq` by
    (rpt gen_tac >>
     qpat_assum `Abbrev (Inherit = _)`
       (simp_tac bool_ss o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     strip_tac >> conj_tac
     >- (`!k. tag b k = NONE \/
               (k < height b /\ (f k = tag b k \/
                 ?j. src k = SOME j /\ j < height a /\ tag a j = tag b k))` by
           (gen_tac >> namedCases_on `tag b k` ["", "slot"] >>
            rewrite_tac[optionTheory.NOT_SOME_NONE] >>
            PairCases_on `slot` >>
            qpat_assum `!k l origin. tag b k = _ ==> _`
              (drule_then ACCEPT_TAC)) >>
         rpt gen_tac >> disch_tac >>
         qpat_assum `!k. tagQ a k = _ /\ tagQ b k = _`
           (qspec_then `k` (assume_tac o CONJUNCT2)) >>
         qpat_x_assum `!k. tag b k = NONE \/ _` (qspec_then `k` strip_assume_tac)
         >- (qpat_x_assum `tagQ b k = SOME _` mp_tac >>
             asm_rewrite_tac[OPTION_MAP_DEF,NOT_NONE_SOME])
         >- (conj_tac >- first_assum ACCEPT_TAC >> disj1_tac >>
             qpat_assum `!k. g k = _` (qspec_then `k` SUBST1_TAC) >>
             qpat_assum `f k = tag b k` SUBST1_TAC >>
             qpat_assum `tagQ b k = OPTION_MAP retag _` (SUBST1_TAC o SYM) >>
             first_assum ACCEPT_TAC) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         disj2_tac >> qexists `j` >>
         qpat_assum `!k. tagQ a k = _ /\ tagQ b k = _`
           (qspec_then `j` (SUBST1_TAC o CONJUNCT1)) >>
         qpat_assum `tag a j = tag b k` SUBST1_TAC >>
         asm_rewrite_tac[] >>
         qpat_assum `tagQ b k = OPTION_MAP retag _` (SUBST1_TAC o SYM) >>
         first_assum ACCEPT_TAC) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!k. boolean b k ==> _` (drule_then strip_assume_tac)
     >- (disj1_tac >> qpat_assum `!k. bn k ==> bq k` irule >> first_assum ACCEPT_TAC) >>
     disj2_tac >> qexists `j` >> asm_rewrite_tac[]) >>
  pop_assum (mk_asm "inherit_map") >>
  qpat_x_assum `Flow p pc height tag boolean a b` mp_tac >>
  qpat_assum `Abbrev (Flow = _)`
    (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rewrite_tac[LET_THM,combinTheory.o_THM] >>
  qpat_assum `EL (r (pc a)) q = EL (pc a) p` SUBST1_TAC >>
  Cases_on `EL (pc a) p` >>
  qpat_assum `EL (pc a) p = _` (fn src =>
    qpat_assum `EL (r (pc a)) q = _` (fn dst =>
      simp_tac (srw_ss()) [src,dst])) >>
  TRY (qmatch_goalsub_rename_tac `ALOOKUP dup_table opn` >>
       Cases_on `ALOOKUP dup_table opn` >>
       qpat_assum `ALOOKUP dup_table opn = _` (simp_tac (srw_ss()) o single) >>
       TRY (qpat_assum `ALOOKUP dup_table opn = NONE` (K ALL_TAC) >>
            Cases_on `ALOOKUP swap_table opn` >>
            qpat_assum `ALOOKUP swap_table opn = _` (simp_tac (srw_ss()) o single))) >>
  strip_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  asm "inherit_map" irule >>
  goal_assum (drule_at Any) >>
  simp[asm_step_push_ok,asm_next_def,AllCaseEqs()] >>
  strip_tac >>
  `opn = "JUMP" \/ opn = "JUMPI" \/ ?m. static_abort_straight opn m` by
    (qpat_assum `!a b name. edge a b /\ EL (pc a) p = AsmOp name ==> _`
       (qspecl_then [`a`,`b`,`opn`] mp_tac) >>
     simp[])
  >- gvs[]
  >- gvs[] >>
  rpt gen_tac >> strip_tac >>
  drule_all_then (ACCEPT_TAC o REWRITE_RULE [EL]) prune_straight_boolean_result
QED

Finalise prune_one_rooted_flow
