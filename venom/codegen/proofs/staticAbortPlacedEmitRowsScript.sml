(* Structural rows at the placed emission PCs.  The graph vertices name
   occurrences even when different arms refer to the same program counter. *)
Theory staticAbortPlacedEmitRows
Ancestors staticAbortAssert[qualified,ignore_grammar] staticAbortUnreachable[qualified,ignore_grammar] symbolResolve[qualified,ignore_grammar]
  staticAbortEmitRows staticAbortEmit staticAbortStraight stackPlanGen planExec
  stackOpSim asmSem asmIR asmSymSem venomInst alist finite_map words
  list arithmetic pred_set pair

(* A symbolic opcode in the single-instruction case is disjoint from the
   concrete permutation and branch tables. *)
Triviality straight_no_permutation_or_branch:
  static_abort_straight name m ==>
  ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE /\
  name <> "JUMP" /\ name <> "JUMPI"
Proof
  (* Split only the straight-name inventory, not the lookup domains. *)
  simp[static_abort_straight_def] >> strip_tac >> gvs[] >> EVAL_TAC
QED

(* Resolve only the dispatch at the root of an already fetched row.  Never
   simplify the unused successor predicates. *)
val select_emit_arm =
  ASSUM_LIST (fn facts => CONV_TAC (REPEATC (fn tm =>
    if boolSyntax.is_cond tm then
      (RATOR_CONV (RATOR_CONV (RAND_CONV EVAL)) THENC COND_CONV) tm
    else if optionSyntax.is_option_case tm then
      let val lookup = FIRST_CONV (map REWR_CONV
            (List.filter (boolSyntax.is_eq o concl) facts))
      in ((RATOR_CONV (RATOR_CONV (RAND_CONV lookup)) ORELSEC RAND_CONV lookup) THENC
          FIRST_CONV (map REWR_CONV (CONJUNCTS optionTheory.option_case_def)) THENC
          TRY_CONV BETA_CONV) tm
      end
    else NO_CONV tm)))

val check_placed_fetch =
  qpat_abbrev_tac `ins = EL _ p` >>
  qpat_x_assum `Abbrev (ins = _)`
    (fn eq => ASSUM_LIST (fn facts =>
      SUBST1_TAC (RIGHT_CONV_RULE (SIMP_CONV (srw_ss()) facts)
        (REWRITE_RULE [markerTheory.Abbrev_def] eq)))) >>
  PURE_ONCE_REWRITE_TAC [asm_inst_case_def] >> BETA_TAC >> select_emit_arm

Theorem placed_static_emit_rows:
let Flow =
  \p pc height tag boolean (x:num#num) (y:num#num).
  let hi = height x; hj = height y; ins = EL (pc x) p in
  let inherit =
    \(src:num -> num option)
      (fresh:num -> (string#num)option) (bnew:num -> bool).
      (!k l origin. tag y k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
         ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
      (!k. boolean y k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))
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
let Reach = \(edge:(num#num)->(num#num)->bool) e x.
  ?n (path:num->num#num).
    path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))
in
let Rows = \p cc V X (rank:num#num->num) pc height need tag boolean edge.
  let lo = SND(compute_label_offsets p); invmap = build_offset_to_pc p in
  let target = \x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\ FLOOKUP lo l = SOME off /\
      off < dimword(:256) /\ FLOOKUP invmap off = SOME(pc y) in
  (!x. x IN V ==>
    (need x ==> cc.cc_static) /\
    (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
    (!k l origin. tag x k = SOME(l,origin) ==>
       k < height x /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
       ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                  FLOOKUP invmap off = SOME dest)) /\
  (!x y. edge x y ==>
    x IN V DIFF X /\ y IN V /\ rank y < rank x /\
    Flow p pc height tag boolean x y) /\
  (!x. x IN V DIFF X ==>
    pc x < LENGTH p /\
    let h = height x in
    let fall = \y. pc y = pc x + 1 in
    let arm = \P n. ?y. edge x y /\ P y /\ height y = n in
    let legal = \P n. !y. edge x y ==> P y /\ height y = n in
    let next = \n. arm fall n /\ legal fall n in
    let untagged = \a. !k. k<a ==> tag x k=NONE in
    let stop = \a. a<=h /\ untagged a /\ !y. ~edge x y in
    case EL (pc x) p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ next (h+1)
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
                    1<=h /\ arm (target x) (h-1) /\ legal (target x) (h-1)
                 else if name="JUMPI" then
                    2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target x) (h-2) /\
                    legal (\y. fall y \/ target x y) (h-2)
                 else
                    ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                        untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F)
in
let Table = \p cc f b H V X e rank pc height need tag boolean edge.
  FINITE V /\ X SUBSET V /\ e IN V /\
  (!x. x IN V ==> FST x=f /\ Reach edge e x) /\ pc e=b /\ height e=H /\
  (!x. ~need x) /\ (!x k. ~boolean x k) /\ (!k. tag e k=NONE) /\
  Rows p cc V X rank pc height need tag boolean edge
in
!p b f cc fmp inst topics ps6 emit ps7 H.
  let code=execute_plan fmp emit;
      lo=SND(compute_label_offsets p); invmap=build_offset_to_pc p in
  generate_emit_ops inst topics ps6=(emit,ps7) /\ asm_block_at p b code ==>
  (!nin nout.
    ~is_terminator inst.inst_opcode /\
    ~MEM inst.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                           SSTORE;TSTORE;LOG] /\
    static_abort_emit_io inst nin nout /\ nin<=H /\
    static_abort_emit_labels lo invmap p fmp b inst emit /\
    (inst.inst_opcode=ASSERT ==>
       ?off dest. FLOOKUP lo "revert"=SOME off /\ off<dimword(:256) /\
         FLOOKUP invmap off=SOME dest) /\
    (inst.inst_opcode=ASSERT_UNREACHABLE ==>
       !lbl. emit=[SOPushLabel lbl;SOEmit "JUMPI";SOEmit "INVALID";SOLabel lbl] ==>
         ?off dest. FLOOKUP lo lbl=SOME off /\ off<dimword(:256) /\
           FLOOKUP invmap off=SOME dest) ==>
     ?V e z rank pc height need tag boolean edge.
       Table p cc f b H V {z} e rank pc height need tag boolean edge /\
       pc z=b+LENGTH code /\ height z=H-nin+nout /\ (!k. tag z k=NONE) /\
       (!x. x IN V DIFF {z} /\ EL (pc x) p = AsmOp "JUMPI" ==>
          ?lbl. tag x 0 = SOME(lbl,pc x-1)) /\
       (!x k lbl origin. tag x k = SOME(lbl,origin) ==>
          x IN V DIFF {z} /\ EL (pc x) p = AsmOp "JUMPI" /\ k=0 /\
          0 < pc x /\ origin=pc x-1 /\ EL origin p = AsmPushLabel lbl)) /\
  (MEM inst.inst_opcode [SSTORE;TSTORE;LOG] /\
   (inst.inst_opcode=LOG ==> topics<=4) /\
   (if inst.inst_opcode=LOG then 2+topics else 2)<=H /\ cc.cc_static ==>
     ?e rank pc height need tag boolean edge.
       Table p cc f b H {e} {} e rank pc height need tag boolean edge /\
       (!x k. tag x k=NONE) /\ (!x y. ~edge x y))
Proof
  simp_tac bool_ss[LET_THM] >> rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (strip_tac >> drule (SIMP_RULE bool_ss[LET_THM] pending_static_emit_rows) >>
      disch_then (qspecl_then [`fmp`, `0`, `0`] (mp_tac o CONJUNCT2)) >>
      (impl_tac >- simp[]) >>
      disch_then (qx_choose_then `name` (CONJUNCTS_THEN2 assume_tac
                                           (CONJUNCTS_THEN2 (mk_asm "opcode_case") assume_tac))) >>
      suspend "terminal") >>
  rpt gen_tac >> strip_tac >>
  drule (SIMP_RULE bool_ss[LET_THM] pending_static_emit_rows) >>
  disch_then (qspecl_then [`fmp`, `nout`, `nin`] (mp_tac o CONJUNCT1)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac
  >- suspend "straight"
  >- suspend "push"
  >- suspend "bump"
  >- suspend "istore"
  >- suspend "assert"
  >- suspend "unreachable" >>
  suspend "empty"
QED

Resume placed_static_emit_rows[terminal]:
  `name <> "INVALID" /\ name <> "REVERT" /\
   MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]` by
    (asm "opcode_case" mp_tac >> strip_tac >> fs[]) >>
  asm_x "opcode_case" kall_tac >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[asm_block_at_cons] >> strip_tac >>
  qexistsl [`(f,0)`, `\x. 0`, `\x. b`, `\x. H`, `\x. F`,
            `\x k. NONE`, `\x k. F`, `\x y. F`] >>
  simp[FORALL_IN_INSERT, DIFF_EMPTY, FORALL_AND_THM] >>
  conj_tac >- (qexistsl [`0`, `\_. (f,0)`] >> simp[]) >> fs[]
QED

Resume placed_static_emit_rows[straight]:
  drule straight_no_permutation_or_branch >> strip_tac >>
  `name <> "INVALID" /\ name <> "REVERT" /\
   ~MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]` by
    (qpat_x_assum `static_abort_straight _ _` mp_tac >>
     simp[static_abort_straight_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >> simp[asm_block_at_cons] >> strip_tac >>
  qexistsl [`{(f,0);(f,1)}`, `(f,0)`, `(f,1)`, `\x. 1-SND x`,
    `\x. b+SND x`, `\x. if SND x=0 then H else H-nin+nout`,
    `\x. F`, `\x k. NONE`, `\x k. F`, `\x y. x=(f,0) /\ y=(f,1)`] >>
  simp[FORALL_IN_INSERT, FORALL_AND_THM, GSYM AND_IMP_INTRO, DISJ_IMP_THM] >>
  conj_tac >- (conj_tac
    >- (qexistsl [`0`, `\j:num. (f,j)`] >> simp[])
    >- (qexistsl [`1`, `\j:num. (f,j)`] >> simp[] >> decide_tac)) >>
  fs[] >> qexists_tac `nout` >> simp[]
QED

Resume placed_static_emit_rows[push]:
  qpat_x_assum `asm_block_at _ _ _` mp_tac >> simp[asm_block_at_cons] >> strip_tac >>
  qexistsl [`{(f,0);(f,1)}`, `(f,0)`, `(f,1)`, `\x. 1-SND x`,
    `\x. b+SND x`, `\x. if SND x=0 then H else H+1`,
    `\x. F`, `\x k. NONE`, `\x k. F`, `\x y. x=(f,0) /\ y=(f,1)`] >>
  simp[FORALL_IN_INSERT, FORALL_AND_THM, GSYM AND_IMP_INTRO, DISJ_IMP_THM] >>
  conj_tac >- (qexistsl [`0`, `\j:num. (f,j)`] >> simp[]) >>
  qexistsl [`1`, `\j:num. (f,j)`] >> simp[] >> decide_tac
QED

Resume placed_static_emit_rows[bump]:
  drule straight_no_permutation_or_branch >> strip_tac >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >> simp[asm_block_at_cons] >> strip_tac >>
  qexistsl [`{(f,0);(f,1);(f,2)}`, `(f,0)`, `(f,2)`, `\x. 2-SND x`,
    `\x. b+SND x`, `\x. if SND x=1 then H+1 else H`,
    `\x. F`, `\x k. NONE`, `\x k. F`,
    `\x y. x=(f,0) /\ y=(f,1) \/ x=(f,1) /\ y=(f,2)`] >>
  simp[FORALL_IN_INSERT, FORALL_AND_THM, GSYM AND_IMP_INTRO, DISJ_IMP_THM] >>
  conj_tac >- (rpt conj_tac
    >- (qexistsl [`0`, `\j:num. (f,j)`] >> simp[])
    >- (qexistsl [`1`, `\j:num. (f,j)`] >> simp[] >> decide_tac)
    >- (qexistsl [`2`, `\j:num. (f,j)`] >> simp[] >> decide_tac)) >>
  qexists_tac `1` >> simp[]
QED

Resume placed_static_emit_rows[istore]:
  drule straight_no_permutation_or_branch >> strip_tac >>
  `ALOOKUP dup_table "SWAP1" = NONE` by EVAL_TAC >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >> simp[asm_block_at_cons] >> strip_tac >>
  qexistsl [`{(f,0);(f,1);(f,2)}`, `(f,0)`, `(f,2)`, `\x. 2-SND x`,
    `\x. b+SND x`, `\x. if SND x=2 then H-2 else H`,
    `\x. F`, `\x k. NONE`, `\x k. F`,
    `\x y. x=(f,0) /\ y=(f,1) \/ x=(f,1) /\ y=(f,2)`] >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- (simp[FORALL_IN_INSERT] >> rpt conj_tac
      >- (qexistsl [`0`, `\j:num. (f,j)`] >> simp[])
      >- (qexistsl [`1`, `\j:num. (f,j)`] >> simp[] >> decide_tac)
      >> qexistsl [`2`, `\j:num. (f,j)`] >> simp[] >> decide_tac)
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- (rpt gen_tac >> simp[SimpLHS] >> strip_tac >> simp[])
  >- (qx_gen_tac `v` >> simp[SimpLHS] >> strip_tac >>
      qpat_x_assum `v = (_,_)` SUBST1_TAC >> simp[] >>
      qexists_tac `0` >> simp[])
  >> simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM]
QED
Resume placed_static_emit_rows[assert]:
  qpat_x_assum `inst.inst_opcode = ASSERT ==> _` mp_tac >> simp[] >>
  disch_then (qx_choose_then `off` (qx_choose_then `d` strip_assume_tac)) >>
  qpat_x_assum `!lo o2pc prog pc. static_abort_emit_labels _ _ _ _ _ _ _ ==> _`
    (qspecl_then [`SND(compute_label_offsets p)`, `build_offset_to_pc p`, `p`, `b`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[w2n_n2w] >>
  qpat_x_assum `asm_block_at p b _` mp_tac >>
  qpat_x_assum `asm_block_at p d _` mp_tac >>
  simp[asm_block_at_cons] >> rpt strip_tac >>
  `ALOOKUP dup_table "ISZERO" = NONE /\ ALOOKUP swap_table "ISZERO" = NONE /\
   ALOOKUP dup_table "JUMPI" = NONE /\ ALOOKUP swap_table "JUMPI" = NONE` by EVAL_TAC >>
  qexistsl [`{(f,0);(f,1);(f,2);(f,3);(f,4);(f,5);(f,6);(f,7)}`,
    `(f,0)`, `(f,3)`,
    `\x. if SND x<3 then 6-SND x else if SND x=3 then 0 else 7-SND x`,
    `\x. if SND x<4 then b+SND x else d+(SND x-4)`,
    `\x. if SND x<2 then H else if SND x=2 \/ SND x=7 then H+1
         else if SND x=6 then H else H-1`,
    `\x. F`, `\x k. if x=(f,2) /\ k=0 then SOME("revert",b+1) else NONE`, `\x k. F`,
    `\x y. x=(f,0) /\ y=(f,1) \/ x=(f,1) /\ y=(f,2) \/
           x=(f,2) /\ (y=(f,3) \/ y=(f,4)) \/ x=(f,4) /\ y=(f,5) \/
           x=(f,5) /\ y=(f,6) \/ x=(f,6) /\ y=(f,7)`] >>
  (* Do not expand the edge implications under the generic opcode case. *)
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- (simp[FORALL_IN_INSERT] >> rpt conj_tac
      >- (qexistsl [`0`, `\j:num. (f,j)`] >> simp[])
      >- (qexistsl [`1`, `\j:num. (f,j)`] >> simp[] >> decide_tac)
      >- (qexistsl [`2`, `\j:num. (f,j)`] >> simp[] >> decide_tac)
      >- (qexistsl [`3`, `\j:num. (f,j)`] >> simp[] >> decide_tac)
      >- (qexistsl [`3`, `\j:num. (f,if j<3 then j else j+1)`] >>
          simp[] >> rpt strip_tac >> `k=0 \/ k=1 \/ k=2` by decide_tac >> fs[])
      >- (qexistsl [`4`, `\j:num. (f,if j<3 then j else j+1)`] >>
          simp[] >> rpt strip_tac >> `k=0 \/ k=1 \/ k=2 \/ k=3` by decide_tac >> fs[])
      >- (qexistsl [`5`, `\j:num. (f,if j<3 then j else j+1)`] >>
          simp[] >> rpt strip_tac >> `k=0 \/ k=1 \/ k=2 \/ k=3 \/ k=4` by decide_tac >> fs[])
      >> qexistsl [`6`, `\j:num. (f,if j<3 then j else j+1)`] >>
         simp[] >> rpt strip_tac >> `k=0 \/ k=1 \/ k=2 \/ k=3 \/ k=4 \/ k=5` by decide_tac >> fs[])
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[FORALL_IN_INSERT]
  >- (rpt gen_tac >> simp[SimpLHS] >> strip_tac >> simp[] >> decide_tac)
  >- (qx_gen_tac `v` >> simp[SimpLHS] >> strip_tac >>
      qpat_x_assum `v = (_,_)` SUBST1_TAC >>
      (conj_tac >- simp[]) >>
      check_placed_fetch
      >- (qexists_tac `1` >> simp[GSYM AND_IMP_INTRO] >> decide_tac)
      >- simp[GSYM AND_IMP_INTRO]
      >- (rpt conj_tac
          >- (simp[] >> decide_tac)
          >- (qexists_tac `(f,3)` >> simp[] >> decide_tac)
          >- (qexists_tac `(f,4)` >> simp[] >> decide_tac)
          >> simp[DISJ_IMP_THM] >> decide_tac)
      >- simp[GSYM AND_IMP_INTRO]
      >- (simp[GSYM AND_IMP_INTRO] >> decide_tac)
      >- simp[GSYM AND_IMP_INTRO]
      >> simp[] >> decide_tac)
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[FORALL_IN_INSERT, GSYM AND_IMP_INTRO, DISJ_IMP_THM]
  >> simp[IN_DIFF]
QED

Resume placed_static_emit_rows[unreachable]:
  `emit=[SOPushLabel lbl;SOEmit "JUMPI";SOEmit "INVALID";SOLabel lbl]` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _` mp_tac >>
     simp[generate_emit_ops_def, venom_to_evm_name_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     gvs[execute_plan_def,exec_stack_op_def]) >>
  qpat_x_assum `inst.inst_opcode = ASSERT_UNREACHABLE ==> _` mp_tac >>
  simp[] >> strip_tac >>
  qpat_x_assum `!lo o2pc prog pc. static_abort_emit_labels _ _ _ _ _ _ _ ==> _`
    (qspecl_then [`SND(compute_label_offsets p)`, `build_offset_to_pc p`, `p`, `b`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[w2n_n2w] >>
  qpat_x_assum `asm_block_at p b _` mp_tac >> simp[asm_block_at_cons] >> strip_tac >>
  `ALOOKUP dup_table "JUMPI" = NONE /\ ALOOKUP swap_table "JUMPI" = NONE` by EVAL_TAC >>
  qexistsl [`{(f,0);(f,1);(f,2);(f,3);(f,4)}`, `(f,0)`, `(f,4)`, `\x. 4-SND x`,
    `\x. b+SND x`,
    `\x. if SND x=0 then H else if SND x=1 then H+1 else H-1`,
    `\x. F`, `\x k. if x=(f,1) /\ k=0 then SOME(lbl,b) else NONE`, `\x k. F`,
    `\x y. x=(f,0) /\ y=(f,1) \/ x=(f,1) /\ (y=(f,2) \/ y=(f,3)) \/
           x=(f,3) /\ y=(f,4)`] >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- (simp[FORALL_IN_INSERT] >> rpt conj_tac
      >- (qexistsl [`0`, `\j:num. (f,j)`] >> simp[])
      >- (qexistsl [`1`, `\j:num. (f,j)`] >> simp[] >> decide_tac)
      >- (qexistsl [`2`, `\j:num. (f,j)`] >> simp[] >> decide_tac)
      >- (qexistsl [`2`, `\j:num. (f,if j<2 then j else j+1)`] >>
          simp[] >> rpt strip_tac >> `k=0 \/ k=1` by decide_tac >> fs[])
      >> qexistsl [`3`, `\j:num. (f,if j<2 then j else j+1)`] >>
         simp[] >> rpt strip_tac >> `k=0 \/ k=1 \/ k=2` by decide_tac >> fs[])
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[FORALL_IN_INSERT]
  >- (rpt gen_tac >> simp[SimpLHS] >> strip_tac >> simp[] >> decide_tac)
  >- (qx_gen_tac `v` >> simp[SimpLHS] >> strip_tac >>
      qpat_x_assum `v = (_,_)` SUBST1_TAC >>
      (conj_tac >- simp[]) >>
      check_placed_fetch
      >- simp[GSYM AND_IMP_INTRO]
      >- (rpt conj_tac
          >- (simp[] >> decide_tac)
          >- (qexists_tac `(f,2)` >> simp[] >> decide_tac)
          >- (qexists_tac `(f,3)` >> simp[] >> decide_tac)
          >> simp[DISJ_IMP_THM] >> decide_tac)
      >> simp[GSYM AND_IMP_INTRO])
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[FORALL_IN_INSERT, GSYM AND_IMP_INTRO, DISJ_IMP_THM]
  >> simp[IN_DIFF]
QED

Resume placed_static_emit_rows[empty]:
  qexistsl [`{(f,0)}`, `(f,0)`, `(f,0)`, `\x. 0`, `\x. b`, `\x. H`,
            `\x. F`, `\x k. NONE`, `\x k. F`, `\x y. F`] >>
  simp[FORALL_IN_INSERT, GSYM AND_IMP_INTRO] >>
  qexistsl [`0`, `\_. (f,0)`] >> simp[]
QED

Finalise placed_static_emit_rows
