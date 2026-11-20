Theory staticAbortOptPruneUnreachableStrictSlots
Ancestors
  codegenSymRel
  staticAbortOptPruneUnreachableLayout staticAbortOptPruneUnreachableZeroOrigin
  asmSplice asmSymPc asmSymSem asmOptimizer asmWf
  arithmetic finite_map list option pair pred_set words

Theorem prune_one_strict_slots_mode:
  !pre t x tail V e height need tag boolean cc env n s ss p q d r Z tagQ Hit.
  p = pre ++ [t;x] ++ tail ==> q = pre ++ [t] ++ tail ==>
  d = LENGTH pre+1 ==> r = (\i. if i<d then i else i-1) ==>
  Z = (\l j. j<LENGTH q /\ (EL j q=AsmPushLabel l \/ EL j q=AsmPushOfst l 0)) ==>
  tagQ = (\v k. OPTION_MAP (\(l,i). (l,if i=d then (@j. Z l j) else r i)) (tag v k)) ==>
  Hit = (\prog l j. ?off.
    FLOOKUP (SND(compute_label_offsets prog)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc prog) off = SOME j) ==>
  asm_terminal_op t /\ ~asm_reachable_marker x /\ asm_static_wf p /\
  (!v:num#num. v IN V ==>
    (need v ==> cc.cc_static) /\
    (!k. boolean v k ==> k<height v /\ tag v k=NONE) /\
    (!k l i. tag v k=SOME(l,i) ==> k<height v /\ i<LENGTH p /\
      (EL i p=AsmPushLabel l \/ EL i p=AsmPushOfst l 0) /\
      ?dest. Hit p l dest)) /\
  (!k l i. tag e k=SOME(l,i) ==> k<LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
  s.as_pc=0 /\
  sym_steps_mode allow_own q env own n (sym_init s) = SymOK (sym_with_pc (r ss.sym_base.as_pc) ss) /\
  (!v k l. v IN V /\ tag v k=SOME(l,d) ==> ?j. tag e j=SOME(l,d)) ==>
  !v. v IN V ==>
    (need v ==> cc.cc_static) /\
    (!k. boolean v k ==> k<height v /\ tagQ v k=NONE) /\
    (!k l j. tagQ v k=SOME(l,j) ==> k<height v /\ Z l j /\ ?dest. Hit q l dest)
Proof
  rpt gen_tac >>
  ntac 7 (disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])) >>
  strip_tac >>
  `!l dest. Hit p l dest ==> Hit q l (r dest)` by
    (qspecl_then [`pre`,`t`,`x`,`tail`] mp_tac (SIMP_RULE bool_ss [] prune_one_canonical_layout) >>
     simp[Abbr `Hit`, Abbr `p`, Abbr `q`, Abbr `r`, Abbr `d`, LET_THM] >>
     strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!l old dest. _` (drule_all_then strip_assume_tac) >>
     qexists `fresh` >> asm_rewrite_tac[]) >>
  `!i. i<>d /\ i<LENGTH p ==> r i<LENGTH q /\ EL (r i) q=EL i p` by
    (qabbrev_tac `h = pre ++ [t:asm_inst]` >>
     `p = h ++ x::tail /\ q = h ++ tail /\ LENGTH h = d` by
       (simp[Abbr `h`, Abbr `p`, Abbr `q`, Abbr `d`] >>
        pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND]) >>
     gen_tac >> strip_tac >> Cases_on `i<d`
     >- (`r i = i` by simp[Abbr `r`] >>
         asm_rewrite_tac[listTheory.EL_APPEND_EQN, LENGTH_APPEND] >> decide_tac) >>
     `?k. i = d + SUC k` by (qexists `i-d-1` >> decide_tac) >>
     pop_assum strip_assume_tac >>
     `k < LENGTH tail` by
       (qpat_x_assum `i < LENGTH p` mp_tac >>
        asm_rewrite_tac[LENGTH_APPEND, LENGTH] >> decide_tac) >>
     `r i = d+k` by (simp[Abbr `r`] >> decide_tac) >>
     conj_tac
     >- (asm_rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
     `~(d+k<d) /\ ~(d+SUC k<d) /\ d+k-d=k /\ d+SUC k-d=SUC k`
       by decide_tac >>
     asm_rewrite_tac[listTheory.EL_APPEND_EQN, EL, TL]) >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!v. v IN V ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `tagQ`] >>
  rpt gen_tac >>
  simp[Abbr `tagQ`, pairTheory.EXISTS_PROD, pairTheory.PAIR_EQ] >> strip_tac >>
  rename1 `tag v k = SOME(l,i)` >>
  qpat_x_assum `j = _` SUBST_ALL_TAC >>
  qpat_x_assum `!k l i. tag v k=SOME(l,i) ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (qpat_x_assum `?dest. Hit p l dest` (qx_choose_then `dest` assume_tac) >>
      qexists `r dest` >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  Cases_on `i=d`
  >- (`?a. tag e a=SOME(l,d)` by metis_tac[] >>
      qpat_x_assum `!k l i. tag e k = SOME(l,i) ==> _`
        (drule_then strip_assume_tac) >>
      `MEM (Lab l 0) (sym_with_pc (r ss.sym_base.as_pc) ss).sym_stack` by
        (simp[sym_with_pc_def] >> metis_tac[EL_MEM]) >>
      `?j. Z l j` suffices_by
        (disch_then (assume_tac o SELECT_RULE) >> simp[]) >>
      drule_all stopped_lab_zero_producer_mode >>
      disch_then (qx_choose_then `m` (qx_choose_then `u` strip_assume_tac)) >>
      qexists `u.sym_base.as_pc` >> simp[Abbr `Z`]) >>
  qpat_x_assum `!i. i<>d /\ i<LENGTH p ==> _`
    (drule_all_then strip_assume_tac) >>
  simp[Abbr `Z`]
QED

Theorem prune_one_strict_slots:
  !pre t x tail V e height need tag boolean cc env n s ss p q d r Z tagQ Hit.
  p = pre ++ [t;x] ++ tail ==> q = pre ++ [t] ++ tail ==>
  d = LENGTH pre+1 ==> r = (\i. if i<d then i else i-1) ==>
  Z = (\l j. j<LENGTH q /\ (EL j q=AsmPushLabel l \/ EL j q=AsmPushOfst l 0)) ==>
  tagQ = (\v k. OPTION_MAP (\(l,i). (l,if i=d then (@j. Z l j) else r i)) (tag v k)) ==>
  Hit = (\prog l j. ?off.
    FLOOKUP (SND(compute_label_offsets prog)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc prog) off = SOME j) ==>
  asm_terminal_op t /\ ~asm_reachable_marker x /\ asm_static_wf p /\
  (!v:num#num. v IN V ==>
    (need v ==> cc.cc_static) /\
    (!k. boolean v k ==> k<height v /\ tag v k=NONE) /\
    (!k l i. tag v k=SOME(l,i) ==> k<height v /\ i<LENGTH p /\
      (EL i p=AsmPushLabel l \/ EL i p=AsmPushOfst l 0) /\
      ?dest. Hit p l dest)) /\
  (!k l i. tag e k=SOME(l,i) ==> k<LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
  s.as_pc=0 /\
  sym_steps q env n (sym_init s) = SymOK (sym_with_pc (r ss.sym_base.as_pc) ss) /\
  (!v k l. v IN V /\ tag v k=SOME(l,d) ==> ?j. tag e j=SOME(l,d)) ==>
  !v. v IN V ==>
    (need v ==> cc.cc_static) /\
    (!k. boolean v k ==> k<height v /\ tagQ v k=NONE) /\
    (!k l j. tagQ v k=SOME(l,j) ==> k<height v /\ Z l j /\ ?dest. Hit q l dest)
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`] prune_one_strict_slots_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
