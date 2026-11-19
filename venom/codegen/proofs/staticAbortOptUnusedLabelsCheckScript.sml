Theory staticAbortOptUnusedLabelsCheck
Ancestors
  staticAbortStraight asmSplice asmSymBridge asmToBytecodeProofs
  asmSymSem asmSem asmIR asmOptimizer finite_map words list alist pred_set arithmetic

Theorem unused_label_one_selected_check:
  !pre l tail cc (V:(num#num)->bool) pc height tag edge H z.
  !p. p = pre ++ [AsmLabel l] ++ tail ==>
  !d. d = LENGTH pre ==>
  !q. q = pre ++ tail ==>
  !r. r = splice_pc d 1 0 ==>
  !tagsQ. tagsQ = (\u k. OPTION_MAP (\(n,j). (n,r j)) (tag u k)) ==>
  !pcQ. pcQ = r o pc ==>
  !keep. keep = {u | u IN V /\ pc u <> d} ==>
  !canon. canon = (\s n w. ?off. FLOOKUP (SND (compute_label_offsets s)) n = SOME off /\
                        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc s) off = SOME w) ==>
  !target. target = (\s m tags u y. ?n j. tags u 0 = SOME(n,j) /\ canon s n (m y)) ==>
  !fall. fall = (\m u y. m y = m u + 1) ==>
  !arm. arm = (\R u P n. ?y. R u y /\ P y /\ height y = n) ==>
  !legal. legal = (\R u P n. !y. R u y ==> P y /\ height y = n) ==>
  !next. next = (\R m u n. arm R u (fall m u) n /\ legal R u (fall m u) n) ==>
  !untagged. untagged = (\tags u a. !k. k < a ==> tags u k = NONE) ==>
  !stop. stop = (\R tags u a. a <= height u /\ untagged tags u a /\ !y. ~R u y) ==>
  !Check. Check = (\s cc m h tags R u.
    case EL (m u) s of
      AsmLabel n => next R m u (h u)
    | AsmPush bs => next R m u (h u + 1)
    | AsmPushLabel n => IS_SOME (FLOOKUP (SND (compute_label_offsets s)) n) /\
                        next R m u (h u + 1)
    | AsmPushOfst n delta => IS_SOME (FLOOKUP (SND (compute_label_offsets s)) n) /\
                              next R m u (h u + 1)
    | AsmOp name =>
        if name = "INVALID" then stop R tags u 0
        else if name = "REVERT" then stop R tags u 2
        else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
             then cc.cc_static /\ stop R tags u (asm_op_arity name)
        else
          (case ALOOKUP dup_table name of
             SOME n => n < h u /\ next R m u (h u + 1)
           | NONE => case ALOOKUP swap_table name of
               SOME n => 0 < n /\ n < h u /\ next R m u (h u)
             | NONE =>
                 if name = "JUMP" then
                   1 <= h u /\ arm R u (target s m tags u) (h u - 1) /\
                   legal R u (target s m tags u) (h u - 1)
                 else if name = "JUMPI" then
                   2 <= h u /\ tags u 1 = NONE /\ arm R u (fall m u) (h u - 2) /\
                   arm R u (target s m tags u) (h u - 2) /\
                   legal R u (\y. fall m u y \/ target s m tags u y) (h u - 2)
                 else
                   ?n. static_abort_straight name n /\ asm_op_arity name <= h u /\
                        untagged tags u (asm_op_arity name) /\
                        next R m u (h u - asm_op_arity name + n))
    | _ => F) ==>
  !Legal. Legal = (\u a. edge u (SND a) /\
    (if FST a then
       (EL (pc u) p = AsmOp "JUMP" \/ EL (pc u) p = AsmOp "JUMPI") /\
       target p pc tag u (SND a)
     else EL (pc u) p <> AsmOp "JUMP" /\ fall pc u (SND a))) ==>
  asm_static_wf q /\
  (!u. u IN V ==> Check p cc pc height tag edge u) /\
  (!u. u IN keep ==> pcQ u < LENGTH q /\ EL (pcQ u) q = EL (pc u) p) /\
  (!u a. u IN keep /\ Legal u a ==> height (SND a) = H u) /\
  (!u a. u IN keep /\ Legal u a ==>
     height (z u a) = H u /\
     (~FST a ==> r (pc (z u a)) = r (pc u) + 1) /\
     (FST a ==> z u a = SND a /\ ?n j. tag u 0 = SOME(n,j) /\ tagsQ u 0 = SOME(n,r j) /\
          EL (pc (z u a)) p = AsmLabel n /\ EL (r (pc (z u a))) q = AsmLabel n /\
          canon q n (r (pc (z u a))))) ==>
  !u. u IN keep ==> pcQ u < LENGTH q /\
    Check q cc pcQ height tagsQ (\u w. u IN keep /\ ?a. Legal u a /\ w = z u a) u
Proof
  map_every qx_gen_tac [`pre`,`l`,`tail`,`cc`,`V`,`pc`,`height`,`tag`,`edge`,`H`,`z`] >>
  map_every (fn name => qx_gen_tac name >>
    disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`p`,`d`,`q`,`r`,`tagsQ`,`pcQ`,`keep`,`canon`,`target`,`fall`,`arm`,`legal`,
     `next`,`untagged`,`stop`,`Check`,`Legal`] >>
  qabbrev_tac `E = \u w. u IN keep /\ ?a. Legal u a /\ w = z u a` >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "wf")
    (CONJUNCTS_THEN2 (mk_asm "source")
    (CONJUNCTS_THEN2 (mk_asm "fetch")
    (CONJUNCTS_THEN2 (mk_asm "input") (mk_asm "output"))))) >>
  qx_gen_tac `u` >> disch_tac >>
  `u IN V` by fs[Abbr `keep`] >>
  asm_x "fetch" (drule_then strip_assume_tac) >>
  asm_x "source" (drule_then (mk_asm "row")) >>
  qabbrev_tac `ins = EL (pc u) p` >>
  `!a. Legal u a ==>
     edge u (SND a) /\ height (z u a) = height (SND a) /\
     (if FST a then
        (ins = AsmOp "JUMP" \/ ins = AsmOp "JUMPI") /\ target q pcQ tagsQ u (z u a)
      else ins <> AsmOp "JUMP" /\ fall pcQ u (z u a))` by suspend "output_arm" >>
  asm_x "input" kall_tac >> asm_x "output" kall_tac >>
  `!n. ins <> AsmOp "JUMP" /\ arm edge u (fall pc u) n ==>
       arm E u (fall pcQ u) n` by suspend "fall_arm" >>
  `!n. (ins = AsmOp "JUMP" \/ ins = AsmOp "JUMPI") /\ arm edge u (target p pc tag u) n ==>
       arm E u (target q pcQ tagsQ u) n` by suspend "taken_arm" >>
  `!n Q. legal edge u Q n ==> !w. E u w ==> height w = n` by suspend "height" >>
  `!w. E u w ==>
       if ins = AsmOp "JUMP" then target q pcQ tagsQ u w
       else if ins = AsmOp "JUMPI" then fall pcQ u w \/ target q pcQ tagsQ u w
       else fall pcQ u w` by suspend "control" >>
  `!n Q. legal edge u Q n ==>
     legal E u (\w. if ins = AsmOp "JUMP" then target q pcQ tagsQ u w
                    else if ins = AsmOp "JUMPI" then fall pcQ u w \/ target q pcQ tagsQ u w
                    else fall pcQ u w) n` by suspend "outgoing" >>
  `!n. ins <> AsmOp "JUMP" /\ ins <> AsmOp "JUMPI" /\ next edge pc u n ==>
       next E pcQ u n` by suspend "straight" >>
  `!a. untagged tag u a ==> untagged tagsQ u a` by suspend "untagged" >>
  `tagsQ u 1 = NONE <=> tag u 1 = NONE` by suspend "none" >>
  `!a. stop edge tag u a ==> stop E tagsQ u a` by suspend "terminal" >>
  `!n. (ins = AsmPushLabel n \/ (?delta. ins = AsmPushOfst n delta)) ==>
       IS_SOME (FLOOKUP (SND (compute_label_offsets q)) n)` by suspend "lookup" >>
  suspend "dispatch"
QED

Resume unused_label_one_selected_check[output_arm]:
  qx_gen_tac `a` >> disch_tac >>
  asm "input" (qspecl_then [`u`,`a`] mp_tac) >> simp[] >> disch_tac >>
  asm "output" (qspecl_then [`u`,`a`] mp_tac) >> simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "next_pc") (mk_asm "taken_pc"))) >>
  qpat_x_assum `Legal u a` mp_tac >> simp[Abbr `Legal`, Abbr `ins`] >>
  Cases_on `FST a` >> simp[]
  >- (asm "taken_pc" mp_tac >> simp[Abbr `target`, Abbr `pcQ`] >> metis_tac[]) >>
  asm "next_pc" mp_tac >> simp[Abbr `fall`, Abbr `pcQ`]
QED

Resume unused_label_one_selected_check[fall_arm]:
  simp[Abbr `arm`] >> rpt strip_tac >>
  `Legal u (F,y)` by simp[Abbr `Legal`, Abbr `ins`] >>
  qexists `z u (F,y)` >>
  `E u (z u (F,y))` by (simp[Abbr `E`] >> qexists `(F,y)` >> simp[]) >>
  qpat_assum `!a. Legal u a ==> _`
    (qspec_then `(F,y)` (drule_then strip_assume_tac o SRULE [])) >> simp[]
QED

Resume unused_label_one_selected_check[taken_arm]:
  simp[Abbr `arm`] >> rpt strip_tac >>
  `Legal u (T,y)` by simp[Abbr `Legal`, Abbr `ins`] >>
  qexists `z u (T,y)` >>
  `E u (z u (T,y))` by (simp[Abbr `E`] >> qexists `(T,y)` >> simp[]) >>
  qpat_assum `!a. Legal u a ==> _`
    (qspec_then `(T,y)` (drule_then strip_assume_tac o SRULE [])) >> simp[]
QED

Resume unused_label_one_selected_check[height]:
  simp[Abbr `legal`, Abbr `E`] >> rpt strip_tac >>
  qpat_assum `!a. Legal u a ==> _` (drule_then strip_assume_tac) >> metis_tac[]
QED

Resume unused_label_one_selected_check[control]:
  simp[Abbr `E`] >> rpt strip_tac >>
  qpat_x_assum `!a. Legal u a ==> edge u _ /\ _`
    (qspec_then `a` (drule_then assume_tac)) >>
  Cases_on `FST a` >> fs[] >>
  Cases_on `ins = AsmOp "JUMP"` >> fs[] >>
  Cases_on `ins = AsmOp "JUMPI"` >> fs[]
QED

Resume unused_label_one_selected_check[outgoing]:
  rpt gen_tac >> disch_tac >>
  qpat_assum `!n Q. legal edge u Q n ==> _` (drule_then assume_tac) >>
  simp[Abbr `legal`]
QED

Resume unused_label_one_selected_check[straight]:
  simp[Abbr `next`, Abbr `legal`] >> rpt strip_tac >> metis_tac[markerTheory.Abbrev_def]
QED

Resume unused_label_one_selected_check[untagged]:
  simp[Abbr `untagged`, Abbr `tagsQ`]
QED

Resume unused_label_one_selected_check[none]:
  simp[Abbr `tagsQ`, optionTheory.OPTION_MAP_EQ_NONE]
QED

Resume unused_label_one_selected_check[terminal]:
  simp[Abbr `stop`, Abbr `E`, Abbr `Legal`] >> metis_tac[]
QED

Resume unused_label_one_selected_check[lookup]:
  rpt strip_tac >>
  `MEM ins q` by
    (qpat_assum `EL (pcQ u) q = ins` (SUBST1_TAC o SYM) >> metis_tac[EL_MEM]) >>
  `MEM n (asm_label_refs q)` by
    (simp[asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     qexists `ins` >> simp[]) >>
  `MEM (AsmLabel n) q \/ MEM (AsmDataHeader n) q` by
    (asm "wf" mp_tac >> simp[asm_static_wf_def]) >>
  `n IN FDOM (SND (compute_label_offsets q))` by
    (simp[symbolResolveTheory.compute_label_offsets_def, clo_step_eq] >> irule clo_FDOM >> simp[]) >>
  simp[FLOOKUP_DEF]
QED

Resume unused_label_one_selected_check[dispatch]:
  asm_x "row" mp_tac >> simp[Abbr `Check`, Abbr `ins`] >>
  Cases_on `EL (pc u) p` >> gs[SF CONJ_ss] >>
  TRY (rename1 `AsmOp name` >>
    Cases_on `name = "JUMP"` >> gs[SF CONJ_ss,
      EVAL ``ALOOKUP dup_table "JUMP"``, EVAL ``ALOOKUP swap_table "JUMP"``] >>
    Cases_on `name = "JUMPI"` >> gs[SF CONJ_ss,
      EVAL ``ALOOKUP dup_table "JUMPI"``, EVAL ``ALOOKUP swap_table "JUMPI"``] >>
    TRY (rename1 `ALOOKUP dup_table name` >>
      Cases_on `name = "INVALID"` >> gs[SF CONJ_ss] >>
      Cases_on `name = "REVERT"` >> gs[SF CONJ_ss] >>
      Cases_on `MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]` >>
      gs[SF CONJ_ss] >>
      Cases_on `ALOOKUP dup_table name` >> gs[SF CONJ_ss] >>
      Cases_on `ALOOKUP swap_table name` >> gs[SF CONJ_ss])) >>
  rpt strip_tac >> metis_tac[]
QED

Finalise unused_label_one_selected_check
