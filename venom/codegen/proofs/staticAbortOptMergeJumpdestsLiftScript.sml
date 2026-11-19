Theory staticAbortOptMergeJumpdestsLift
Ancestors
  asmSem asmOptimizer staticAbortStraight asmToBytecodeProofs
  pred_set arithmetic list finite_map words

(* Number the occurrences, not their projected PCs.  The decoder need
   only be correct on the numbered vertices. *)
Theorem rooted_occurrences[local]:
  !A z (R:'a -> 'a -> bool).
    FINITE A /\ z IN A ==>
    ?verts (e:num#num) (dec:num#num -> 'a) E.
      FINITE verts /\ e IN verts /\ dec e = z /\
      (!x. x IN verts ==> dec x IN A /\
         ?n (path:num->num#num). path 0=e /\ path n=x /\
           !k. k<n ==> E (path k) (path (SUC k))) /\
      (!x y. E x y ==> x IN verts /\ y IN verts /\ R (dec x) (dec y)) /\
      (!x u. x IN verts /\ u IN A /\ R (dec x) u ==>
         ?y. E x y /\ dec y = u)
Proof
  rpt strip_tac >> drule FINITE_BIJ_COUNT >>
  disch_then (qx_choose_then `f` (qx_choose_then `b` assume_tac)) >>
  `!i. i < b ==> f i IN A` by fs[BIJ_DEF, INJ_DEF] >>
  `!u. u IN A ==> ?i. i < b /\ f i = u` by metis_tac[BIJ_DEF, SURJ_DEF, IN_COUNT] >>
  qpat_assum `!u. u IN A ==> ?i. i < b /\ f i = u`
    (drule_then (qx_choose_then `root_index` strip_assume_tac)) >>
  qabbrev_tac `e = (root_index:num,0:num)` >>
  qabbrev_tac `dec = \v:num#num. f (FST v)` >>
  qabbrev_tac `B = count b CROSS {0:num}` >>
  `e IN B /\ dec e = z` by simp[Abbr `e`, Abbr `dec`, Abbr `B`] >>
  `!v. v IN B ==> dec v IN A` by simp[Abbr `B`, Abbr `dec`] >>
  `!u. u IN A ==> ?v. v IN B /\ dec v = u` by
    (rpt strip_tac >> qpat_assum `!u. u IN A ==> ?i. i < b /\ f i = u`
       (qspec_then `u` (drule_then (qx_choose_then `j` strip_assume_tac))) >>
     qexists `(j:num,0:num)` >> simp[Abbr `dec`, Abbr `B`]) >>
  qabbrev_tac `base_edge = \x y. x IN B /\ y IN B /\ R (dec x) (dec y)` >>
  qabbrev_tac `verts = {x | x IN B /\ ?n (path:num->num#num).
                         path 0=e /\ path n=x /\ !k. k<n ==> base_edge (path k) (path (SUC k))}` >>
  `e IN verts` by (simp[Abbr `verts`] >> qexistsl [`0`, `\k. e`] >> simp[]) >>
  `!x y. x IN verts /\ base_edge x y ==> y IN verts` by
    (rpt gen_tac >> strip_tac >>
     `y IN B` by (qpat_x_assum `base_edge x y` mp_tac >> simp[Abbr `base_edge`]) >>
     qpat_x_assum `x IN verts` mp_tac >>
     simp[Abbr `verts`, PULL_EXISTS] >> rpt strip_tac >>
     qexistsl [`SUC n`, `\k. if k <= n then path k else y`] >>
     simp[] >> rpt strip_tac >> Cases_on `k < n`
     >- (`SUC k <= n` by decide_tac >> simp[]) >>
     `k = n` by decide_tac >> simp[]) >>
  `!x. x IN verts ==> x IN B` by simp[Abbr `verts`] >>
  qexistsl [`verts`, `e`, `dec`, `\x y. x IN verts /\ base_edge x y`] >> simp[] >>
  conj_tac
  >- (irule SUBSET_FINITE >> qexists `B` >> simp[SUBSET_DEF, Abbr `B`]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `dec x IN A` by metis_tac[] >> simp[] >>
      qpat_x_assum `x IN verts` mp_tac >> simp[Abbr `verts`, PULL_EXISTS] >>
      rpt strip_tac >> qexistsl [`n`, `path`] >> simp[] >> rpt strip_tac >>
      `base_edge (path k) (path (SUC k))` by metis_tac[] >> simp[] >>
      `path k IN B` by
        (metis_tac[Abbr `base_edge`]) >>
      simp[] >> qexistsl [`k`, `path`] >> simp[] >> rpt strip_tac >>
      `k' < n` by decide_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `y IN verts` by metis_tac[] >>
      qpat_x_assum `base_edge x y` mp_tac >> simp[Abbr `base_edge`]) >>
  rpt strip_tac >>
  qpat_assum `!u. u IN A ==> (?v. v IN B /\ dec v = u)`
    (qspec_then `u` (drule_then (qx_choose_then `v` strip_assume_tac))) >>
  `x IN B` by metis_tac[] >>
  qexists `v` >> simp[Abbr `base_edge`]
QED

Theorem bounded_occurrence_vectors[local]:
  !V (height:(num#num)->num) n (A:((num#num) # (num option list)) set).
    FINITE V /\
    (!u. u IN A ==> FST u IN V /\ LENGTH (SND u) = height (FST u) /\
      !i. MEM (SOME i) (SND u) ==> i < n) ==>
    FINITE A
Proof
  rpt strip_tac >>
  qabbrev_tac `B = NONE INSERT IMAGE SOME (count n)` >>
  qabbrev_tac `H = MAX_SET (IMAGE height V)` >>
  `!x. x IN V ==> height x <= H` by
    (simp[Abbr `H`] >> metis_tac[MAX_SET_PROPERTY, IMAGE_FINITE, IN_IMAGE]) >>
  `FINITE B` by simp[Abbr `B`] >>
  irule SUBSET_FINITE >>
  qexists `V CROSS {d | set d SUBSET B /\ LENGTH d <= H}` >>
  conj_tac
  >- (irule FINITE_CROSS >> simp[FINITE_BOUNDED_LISTS]) >>
  simp[SUBSET_DEF, IN_CROSS] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  simp[SUBSET_DEF, Abbr `B`] >> Cases_on `x'` >> simp[]
QED

(* An arbitrary default state suffices: only these four fields enter the
   shape.  At a tagged slot the forward lookup uniquely fixes the word. *)
Theorem decorated_shape_inhabited[local]:
  !q cc req pc h need tag boolean lo.
  lo = SND (compute_label_offsets q) ==>
  (need ==> cc.cc_static) /\
  (!k. boolean k ==> k < h /\ tag k = NONE) /\
  (!k l orig. tag k = SOME(l,orig) ==>
    k < h /\ orig < LENGTH q /\
    (EL orig q = AsmPushLabel l \/ EL orig q = AsmPushOfst l 0) /\
    ?off j. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
            FLOOKUP (build_offset_to_pc q) off = SOME j) ==>
  ?t:asm_state.
    t.as_pc = pc /\ LENGTH t.as_stack = h /\ t.as_call_ctx = cc /\
    t.as_requests = req /\ (need ==> t.as_call_ctx.cc_static) /\
    (!k l orig. tag k = SOME(l,orig) ==>
      k < h /\ orig < LENGTH q /\
      (EL orig q = AsmPushLabel l \/ (?d. EL orig q = AsmPushOfst l d) \/
       EL orig q = AsmDataLabel l) /\
      ?off j. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
              FLOOKUP (build_offset_to_pc q) off = SOME j /\
              EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean k ==> k < h /\ (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))
Proof
  rpt gen_tac >> disch_then kall_tac >> strip_tac >>
  qexists `(ARB:asm_state) with
    <|as_pc := pc; as_call_ctx := cc; as_requests := req;
      as_stack := GENLIST (\k. case tag k of NONE => 0w
         | SOME (l,orig) => n2w (THE (FLOOKUP lo l))) h|>` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!k l orig. tag k = SOME(l,orig) ==> _`
    (drule_then strip_assume_tac) >> simp[] >> metis_tac[]
QED

(* Each arm is summarized by its required PC and height. The summary is
   exact: absence of an arm is preserved too (notably for terminals).
   A and the local projections are the admissibility set and projections
   supplied by the rename construction; only the finite bounds are used
   to number A. R installs just the certified local arms. *)
Theorem merge_rename_reachable_lift:
  !q cc req.
  !Canon. Canon = (\l j. ?off.
    FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME j) ==>
  !Target. Target = (\tag j. ?l orig. tag 0 = SOME(l,orig) /\ Canon l j) ==>
  !Slots. Slots = (\h need tag boolean.
    (need ==> cc.cc_static) /\
    (!k. boolean k ==> k < h /\ tag k = NONE) /\
    (!k l orig. tag k = SOME(l,orig) ==>
      k < h /\ orig < LENGTH q /\
      (EL orig q = AsmPushLabel l \/ EL orig q = AsmPushOfst l 0) /\
      ?j. Canon l j)) ==>
  !Row. Row = (\i h tag (arms:num -> num -> bool).
    !fall. fall = (\j. j = i+1) ==>
    !clear. clear = (\a. !k. k < a ==> tag k = NONE) ==>
    case EL i q of
      AsmLabel l => (!j hj. arms j hj <=> fall j /\ hj = h)
    | AsmPush bs => (!j hj. arms j hj <=> fall j /\ hj = h+1)
    | AsmPushLabel l =>
        IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l) /\
        (!j hj. arms j hj <=> fall j /\ hj = h+1)
    | AsmPushOfst l d =>
        IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l) /\
        (!j hj. arms j hj <=> fall j /\ hj = h+1)
    | AsmOp name =>
        (name = "INVALID" \/ (name = "REVERT" /\ 2 <= h /\ clear 2) \/
         (MEM name ["SSTORE"; "TSTORE"; "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"] /\
          asm_op_arity name <= h /\ clear (asm_op_arity name) /\ cc.cc_static)) /\
        (!j hj. ~arms j hj) \/
        (case ALOOKUP dup_table name of
           SOME n => n < h /\ (!j hj. arms j hj <=> fall j /\ hj = h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < h /\ (!j hj. arms j hj <=> fall j /\ hj = h)
           | NONE =>
               if name = "JUMP" then
                 1 <= h /\ (?j. Target tag j) /\
                 (!j hj. arms j hj <=> Target tag j /\ hj = h-1)
               else if name = "JUMPI" then
                 2 <= h /\ tag 1 = NONE /\ (?j. Target tag j) /\
                 (!j hj. arms j hj <=> (fall j \/ Target tag j) /\ hj = h-2)
               else
                 ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                   clear (asm_op_arity name) /\
                   (!j hj. arms j hj <=> fall j /\ hj = h-asm_op_arity name+m))
    | _ => F) ==>
  !Flow. Flow = (\i hi hj tx ty bx by'.
    !ins. ins = EL i q ==>
    !inherit. inherit = (\(src:num -> num option)
                  (fresh:num -> (string#num) option) (bnew:num -> bool).
      (!k l orig. ty k = SOME(l,orig) ==>
         k < hj /\ (fresh k = SOME(l,orig) \/
         ?a. src k = SOME a /\ a < hi /\ tx a = SOME(l,orig))) /\
      (!k. by' k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ bx a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
    | AsmPushLabel l =>
        hj = hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,i) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,i) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj + asm_op_arity name - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
                       ins t = AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !Control. Control = (\i j tag.
    if EL i q = AsmOp "JUMP" then Target tag j
    else if EL i q = AsmOp "JUMPI" then j = i+1 \/ Target tag j
    else j = i+1) ==>
  !Shape. Shape = (\i h need tag boolean (t:asm_state).
    t.as_pc = i /\ LENGTH t.as_stack = h /\ t.as_call_ctx = cc /\
    t.as_requests = req /\ (need ==> t.as_call_ctx.cc_static) /\
    (!k l orig. tag k = SOME(l,orig) ==>
      k < h /\ orig < LENGTH q /\
      (EL orig q = AsmPushLabel l \/ (?d. EL orig q = AsmPushOfst l d) \/
       EL orig q = AsmDataLabel l) /\
      ?off j. FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
              off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME j /\
              EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean k ==> k < h /\ (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !V rank0 pc0 h0 need0 tag0 boolean0 (A:((num#num) # num option list) set)
    seed R.
    FINITE V /\ seed IN A /\
    (!u. u IN A ==> FST u IN V /\ LENGTH (SND u) = h0 (FST u) /\
      !i. MEM (SOME i) (SND u) ==> i < LENGTH q) /\
    (!u. u IN A ==> pc0 (FST u) < LENGTH q /\
      Slots (h0 (FST u)) (need0 (FST u)) (tag0 u) (boolean0 (FST u)) /\
      Row (pc0 (FST u)) (h0 (FST u)) (tag0 u)
        (\j hj. ?v. v IN A /\ R u v /\ pc0 (FST v) = j /\ h0 (FST v) = hj)) /\
    (!u v. u IN A /\ v IN A /\ R u v ==>
      rank0 (FST v) < rank0 (FST u) /\
      Flow (pc0 (FST u)) (h0 (FST u)) (h0 (FST v))
        (tag0 u) (tag0 v) (boolean0 (FST u)) (boolean0 (FST v)) /\
      Control (pc0 (FST u)) (pc0 (FST v)) (tag0 u)) ==>
    ?V' (e:num#num) rank pc height need tag boolean edge.
      FINITE V' /\ {} SUBSET V' /\ e IN V' /\
      (!x. x IN V' ==> ?n (path:num->num#num). path 0=e /\ path n=x /\
         !k. k<n ==> edge (path k) (path (SUC k))) /\
      (!x. x IN V' ==> pc x < LENGTH q /\
         Slots (height x) (need x) (tag x) (boolean x) /\
         Row (pc x) (height x) (tag x)
           (\j hj. ?y. edge x y /\ pc y = j /\ height y = hj)) /\
      (!x. x IN V' ==> ?t. Shape (pc x) (height x) (need x) (tag x) (boolean x) t) /\
      (!x y. edge x y ==> x IN V' /\ y IN V' /\ rank y < rank x /\
         Flow (pc x) (height x) (height y) (tag x) (tag y) (boolean x) (boolean y) /\
         Control (pc x) (pc y) (tag x)) /\
      pc e = pc0 (FST seed) /\ height e = h0 (FST seed) /\
      need e = need0 (FST seed) /\ tag e = tag0 seed /\
      boolean e = boolean0 (FST seed) /\ rank e = rank0 (FST seed)
Proof
  ntac 3 gen_tac >>
  ntac 7 (gen_tac >> disch_then
    (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def)))) >>
  rpt gen_tac >> strip_tac >>
  `FINITE A` by
    (irule bounded_occurrence_vectors >> qexistsl [`V`, `h0`, `LENGTH q`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [`A`, `seed`, `R`] mp_tac rooted_occurrences >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `verts` (qx_choose_then `e` (qx_choose_then `dec`
    (qx_choose_then `E` strip_assume_tac)))) >>
  `!x. x IN verts ==> dec x IN A` by metis_tac[] >>
  `!x. x IN verts ==>
    (\j hj. ?y. E x y /\ pc0 (FST (dec y)) = j /\ h0 (FST (dec y)) = hj) =
    (\j hj. ?v. v IN A /\ R (dec x) v /\ pc0 (FST v) = j /\ h0 (FST v) = hj)` by
     (rw[FUN_EQ_THM] >> eq_tac >> metis_tac[]) >>
  qexistsl [`verts`, `e`, `\x. rank0 (FST (dec x))`, `\x. pc0 (FST (dec x))`,
            `\x. h0 (FST (dec x))`, `\x. need0 (FST (dec x))`, `\x. tag0 (dec x)`,
            `\x. boolean0 (FST (dec x))`, `E`] >> BETA_TAC >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!u. u IN A ==> _ /\ Slots _ _ _ _ /\ _`
        (qspec_then `dec x` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (mp_tac o cj 2) >>
      qunabbrev_tac `Slots` >> qunabbrev_tac `Canon` >>
      qunabbrev_tac `Shape` >> BETA_TAC >>
      POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
      irule (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV)
               decorated_shape_inhabited) >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!x y. E x y ==> _` (drule_then strip_assume_tac) >> simp[]
QED
