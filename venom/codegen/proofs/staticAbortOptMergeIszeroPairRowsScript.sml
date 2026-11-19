Theory staticAbortOptMergeIszeroPairRows
Ancestors
  staticAbortRoleStep staticAbortStraight staticAbortOptMergeIszeroLive
  staticAbortOptMergeIszeroLayout staticAbortOptMergeIszeroBranchPackage
  asmSplice asmSymBridge asmSymSem asmOptimizer
  asmSem asmIR stackOpSim pred_set relation list rich_list alist words arithmetic

Theorem pair_producer_shape[local]:
  asm_returns_zero_or_one (AsmOp name) /\ static_abort_straight name m ==>
  m = 1 /\ ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE /\
  (!lo inv s u. asm_step lo inv (AsmOp name) s = AsmOK u ==>
    EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w)
Proof
  simp[asm_returns_zero_or_one_def, static_abort_straight_def] >>
  strip_tac >> gvs[] >>
  simp[EVAL ``dup_table``, EVAL ``swap_table``, asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def] >>
  rpt gen_tac >> Cases_on `s.as_stack` >>
  simp[asm_binop_def, asm_unop_def, asm_next_def, asm_state_fupdcanon] >>
  TRY (Cases_on `t` >> simp[asm_next_def, asm_state_fupdcanon]) >>
  strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `b2w test` >> Cases_on `test` >> simp[]
QED

(* The guard alone does not classify X as a pending opcode.  Here it is
   used only to show that changing either relocation map has no effect
   on the guarded instruction's dispatcher. *)
Theorem pair_boolean_dispatch_maps[local]:
  asm_returns_zero_or_one ins ==>
  asm_step lo otp ins s = asm_step lo' otp' ins s
Proof
  simp[asm_returns_zero_or_one_def] >> strip_tac >> gvs[] >>
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def]
QED

Theorem pair_skip_fall[local]:
  ((i:num) < b+1 \/ b+3 <= i) /\
  (if i+1 < b+1 \/ b+3 <= i+1 then j=i+1 else j=b+3) ==>
  (if j < b+1 then j else j-2) = (if i < b+1 then i else i-2)+1
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "keep") (mk_asm "destination")) >>
  qsuff_tac `i < b \/ i = b \/ b+3 <= i`
  >- (asm_x "keep" kall_tac >>
      disch_then (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN assume_tac))
      >- (`i+1 < b+1 /\ i < b+1` by simp[] >>
          asm_x "destination" mp_tac >> simp[])
      >- (`~(i+1 < b+1 \/ b+3 <= i+1)` by simp[] >>
          asm_x "destination" mp_tac >> simp[]) >>
      `b+3 <= i+1 /\ ~(i+1 < b+1) /\ ~(i < b+1) /\ 2 <= i` by
        (asm_x "destination" kall_tac >> decide_tac) >>
      asm_x "destination" mp_tac >> simp[] >> disch_then SUBST1_TAC >>
      `(i-2)+2 = i` by simp[SUB_ADD] >>
      `(i-2+1)+2 = i+1` by simp[AC ADD_ASSOC ADD_COMM] >>
      pop_assum (fn th => simp[GSYM th])) >>
  asm_x "destination" kall_tac >> asm_x "keep" mp_tac >>
  simp[GSYM ADD1, LT]
QED

Theorem pair_slice_blocks[local]:
  p = pre ++ [ins; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail ==>
  EL (LENGTH pre) p = ins /\
  !i. LENGTH pre < i /\ i < LENGTH pre+3 ==>
    asm_block_at p i (REPLICATE (LENGTH pre+3-i) (AsmOp "ISZERO"))
Proof
  disch_then SUBST1_TAC >> simp[EL_APPEND_EQN] >> rpt strip_tac >>
  `i = LENGTH pre+1 \/ i = LENGTH pre+2` by decide_tac >>
  qpat_x_assum `i = _` SUBST_ALL_TAC >>
  simp[DECIDE ``!b:num. b+3-(b+1)=2 /\ b+3-(b+2)=1``,
       EVAL ``REPLICATE 2 (AsmOp "ISZERO")``, EVAL ``REPLICATE 1 (AsmOp "ISZERO")``] >>
  simp[asm_block_at_cons, EL_APPEND_EQN, GSYM ADD_ASSOC]
QED

Theorem merge_iszero_pair_cut_rows:
  !Shape. Shape = (\p cc req pc height need tag boolean i (t:asm_state).
    t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need i ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest /\
         EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !Flow. Flow = (\p pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) p ==>
    !inherit. inherit = (\(src:num -> num option)
         (fresh:num -> (string#num)option) (bnew:num -> bool).
      (!k l origin. tag y k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
         ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
      (!k. boolean y k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
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
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < hi /\ hj = hi /\
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
  !Target. Target = (\p pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !Control. Control = (\p pc tag x y.
    if EL (pc x) p = AsmOp "JUMP" then Target p pc tag x y
    else if EL (pc x) p = AsmOp "JUMPI"
         then pc y = pc x+1 \/ Target p pc tag x y
    else pc y = pc x+1) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) X rank pc height need
        (tag:(num#num)->num->(string#num)option)
        (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
      FINITE V /\ X SUBSET V /\
      (!x. x IN V ==> ?t. S x t) /\
      (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
      (!x y. edge x y ==>
         x IN V DIFF X /\ y IN V /\ rank y < rank x /\
         Flow p pc height tag boolean x y /\ Control p pc tag x y) /\
      (!x t. x IN V DIFF X /\ S x t ==>
         (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmRevert u \/
                asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmFault u) /\ u.as_requests=req) \/
         (?y u. edge x y /\
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmOK u /\ S y u))) ==>
  !Reach. Reach = (\(edge:(num#num)->(num#num)->bool) e x.
    ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) ==>
  !Slots. Slots = (\p cc height need tag boolean (x:num#num).
    (need x ==> cc.cc_static) /\
    (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
    (!k l origin. tag x k = SOME(l,origin) ==>
       k < height x /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
       ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)) ==>
  !Rows. Rows = (\p cc (V:(num#num)->bool) X (rank:num#num->num) pc height need tag boolean edge.
    !lo. lo = SND(compute_label_offsets p) ==>
    (!x. x IN V ==> Slots p cc height need tag boolean x) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y) /\
    (!x. x IN V DIFF X ==>
       pc x < LENGTH p /\
       !h. h = height x ==>
       !fall. fall = (\y. pc y = pc x + 1) ==>
       !arm. arm = (\P n. ?y. edge x y /\ P y /\ height y = n) ==>
       !legal. legal = (\P n. !y. edge x y ==> P y /\ height y = n) ==>
       !next. next = (\n. arm fall n /\ legal fall n) ==>
       !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
       !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
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
           else (case ALOOKUP dup_table name of
                   SOME n => n<h /\ next (h+1)
                 | NONE => case ALOOKUP swap_table name of
                     SOME n => 0<n /\ n<h /\ next h
                   | NONE =>
                       if name="JUMP" then
                         1<=h /\ arm (Target p pc tag x) (h-1) /\
                         legal (Target p pc tag x) (h-1)
                       else if name="JUMPI" then
                         2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\
                         arm (Target p pc tag x) (h-2) /\
                         legal (\y. fall y \/ Target p pc tag x y) (h-2)
                       else ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                                untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
       | _ => F)) ==>
  !Root. Root = (\p ss a pc height need tag boolean e.
    Shape p a.as_call_ctx a.as_requests pc height need tag boolean e a /\
    (!k l origin. tag e k=SOME(l,origin) ==>
       k<LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
    (!k. boolean e k ==> k<LENGTH ss.sym_stack /\
       (EL k ss.sym_stack=Val 0w \/ EL k ss.sym_stack=Val 1w))) ==>
  !Cert. Cert = (\p ss a. ?V e rank pc height need tag boolean edge.
    Rows p a.as_call_ctx V {} rank pc height need tag boolean edge /\
    Open p a.as_call_ctx a.as_requests V {} rank pc height need tag boolean edge /\
    e IN V /\ (!x. x IN V ==> Reach edge e x) /\
    Root p ss a pc height need tag boolean e) ==>
  !b. b = LENGTH pre ==>
  !c. c = ss.sym_base.as_pc ==>
  p = pre ++ [ins; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail /\
  q = pre ++ [ins] ++ tail /\ asm_returns_zero_or_one ins /\
  asm_static_wf p /\ asm_sym_rel p (asm_data_env p (assemble p ++ data)) a ss /\
  Cert p ss a /\
  asm_sym_rel q (asm_data_env q (assemble q ++ data)) t u /\
  t.as_call_ctx=a.as_call_ctx /\ t.as_requests=a.as_requests /\
  (if b<c /\ c<b+3 then u.sym_base.as_pc=b+1 /\ ?w stk.
      (w=0w \/ w=1w) /\ u.sym_stack=Val w::stk /\
      ss.sym_stack=Val (FUNPOW (\w:bytes32. (b2w (w=0w):bytes32)) (c-b-1) w)::stk
   else u=sym_with_pc (splice_pc b 3 1 c) ss) ==>
  Cert q u t
Proof
  map_every (fn name =>
    qx_gen_tac name >> disch_then (assume_tac o CONV_RULE
      (RAND_CONV (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV)) THENC
       REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`Shape`, `Flow`, `Target`, `Control`, `Open`, `Reach`, `Slots`, `Rows`, `Root`, `Cert`] >>
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qsuff_tac `?V e rank pc height need tag boolean edge.
    FINITE V /\ e IN V /\ Rows q t.as_call_ctx V {} rank pc height need tag boolean edge /\
    (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\
       Flow q pc height tag boolean x y /\ Control q pc tag x y) /\
    (!x. x IN V ==> Slots q t.as_call_ctx height need tag boolean x) /\
    Root q u t pc height need tag boolean e`
  >- suspend "package" >>
  qpat_x_assum `Cert p ss a` mp_tac >>
  qpat_assum `Abbrev (Cert = _)`
    (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  BETA_TAC >>
  disch_then (qx_choose_then `V` (qx_choose_then `e` (qx_choose_then `rank`
    (qx_choose_then `pc` (qx_choose_then `height` (qx_choose_then `need`
    (qx_choose_then `tag` (qx_choose_then `boolean` (qx_choose_then `edge`
    (map_every assume_tac o CONJUNCTS)))))))))) >>
  qabbrev_tac `b = LENGTH (pre:asm_inst list)` >>
  qabbrev_tac `keep = \i:num. i<b+1 \/ b+3<=i` >>
  qabbrev_tac `f = \i:num. if i<b+1 then i else i-2` >>
  suspend "select"
QED

Resume merge_iszero_pair_cut_rows[select]:
  `!y. ?z. y IN V ==>
       z IN V /\ keep (pc z) /\ height z = height y /\
       (if keep (pc y) then z=y else
          pc z=b+3 /\ rank z<rank y /\ tag z 0=NONE /\
          (!k l orig. tag z k = SOME(l,orig) ==> 0<k /\ tag y k=SOME(l,orig)) /\
          (!k. 0<k /\ boolean z k ==> boolean y k))` by
    suspend "choose" >>
  pop_assum (qx_choose_then `exit` assume_tac o CONV_RULE SKOLEM_CONV) >>
  suspend "table"
QED

Resume merge_iszero_pair_cut_rows[choose]:
  qx_gen_tac `y` >> reverse (Cases_on `y IN V`)
  >- (qexists_tac `y` >> simp[]) >>
  Cases_on `keep (pc y)` >- (qexists_tac `y` >> simp[]) >>
  `b < pc y /\ pc y < b+3` by fs[Abbr `keep`] >>
  `asm_block_at p (pc y) (REPLICATE (b+3-pc y) (AsmOp "ISZERO"))` by (
    drule_then (mp_tac o CONJUNCT2) pair_slice_blocks >> simp[Abbr `b`]) >>
  Q.SUBGOAL_THEN `b+3-pc y=1 \/ b+3-pc y=2` assume_tac >- decide_tac >>
  qpat_assum `Abbrev (Shape = _)` (mk_asm "liveShape") >>
  qpat_assum `Abbrev (Flow = _)` (mk_asm "liveFlow") >>
  qpat_assum `Abbrev (Target = _)` (mk_asm "liveTarget") >>
  qpat_assum `Abbrev (Control = _)` (mk_asm "liveControl") >>
  qpat_assum `Abbrev (Open = _)` (mk_asm "liveOpen") >>
  qpat_assum `Open p a.as_call_ctx a.as_requests V {} rank pc height need tag boolean edge`
    (mk_asm "liveSource") >>
  asm "liveShape" (fn sh => asm "liveFlow" (fn fl =>
    asm "liveTarget" (fn tg => asm "liveControl" (fn ctl =>
      asm "liveOpen" (fn opn => asm "liveSource" (fn th =>
        let
          val norm = SIMP_RULE bool_ss [LET_THM]
          val source = norm (BETA_RULE (REWRITE_RULE
            (map (REWRITE_RULE[markerTheory.Abbrev_def]) [opn,ctl,tg,fl,sh]) th))
          (* Live uses rational ranks; embed the same natural order. *)
          val contraction = CONV_RULE
            (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV))
            merge_iszero_pending_root_contraction
          val live = CONV_RULE (STRIP_QUANT_CONV ANTE_CONJ_CONV)
            (GEN_ALL (SIMP_RULE bool_ss [ratTheory.RAT_OF_NUM_LES]
              (BETA_RULE (Q.INST [`rank:num#num->rat` |->
                `\x:num#num. rat$rat_of_num (natRank x)`]
                (SPEC_ALL contraction)))))
        in
          qspecl_then [`y`, `b+3-pc y`] mp_tac (MATCH_MP live source)
        end)))))) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)) >>
  `pc z=b+3` by decide_tac >>
  qexists `z` >> simp[Abbr `keep`]
QED

Resume merge_iszero_pair_cut_rows[table]:
  mp_tac (SIMP_RULE bool_ss [LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``,
                           DECIDE ``!b:num. b+1+2 = b+3``]
    (CONV_RULE (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV))
      (Q.INST [`pat` |-> `[ins; AsmOp "ISZERO"; AsmOp "ISZERO"]`,
               `repl` |-> `[ins]`] merge_iszero_one_canonical_layout))) >>
  impl_tac >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    disj1_tac >> qexists_tac `ins` >> simp[]) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "layoutWf") (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 (mk_asm "layoutTarget")
      (CONJUNCTS_THEN2 (mk_asm "layoutFetch") (mk_asm "layoutOrigin"))))) >>
  qpat_assum `p:asm_inst list = _` (fn peq => qpat_assum `q:asm_inst list = _` (fn qeq =>
    map_every (fn l => asm_x l (mk_asm l o PURE_REWRITE_RULE [GSYM peq,GSYM qeq]))
      ["layoutWf","layoutTarget","layoutFetch","layoutOrigin"])) >>
  qpat_assum `Abbrev (Rows = _)` (fn rwth =>
    qpat_assum `Rows p _ V {} rank pc height need tag boolean edge`
      (CONJUNCTS_THEN2 (mk_asm "oldSlots")
        (CONJUNCTS_THEN2 (mk_asm "oldFlow") (mk_asm "oldRow")) o
        SIMP_RULE bool_ss [REWRITE_RULE[markerTheory.Abbrev_def] rwth, LET_THM, DIFF_EMPTY])) >>
  qpat_assum `Abbrev (Open = _)` (fn opth =>
    qpat_assum `Open p _ _ V {} rank pc height need tag boolean edge`
      (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 kall_tac
         (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 (mk_asm "oldControl") kall_tac)))) o
       SIMP_RULE bool_ss [LET_THM, DIFF_EMPTY] o BETA_RULE o
       REWRITE_RULE[REWRITE_RULE[markerTheory.Abbrev_def] opth])) >>
  qabbrev_tac `retained = {x | x IN V /\ keep (pc x)}` >>
  qabbrev_tac `pc' = \x:num#num. f (pc x)` >>
  qabbrev_tac `tag' = \x:num#num k. OPTION_MAP (\(l,i). (l,f i)) (tag x k)` >>
  qabbrev_tac `newEdge = \x:num#num z. x IN retained /\ ?y. edge x y /\ exit y=z` >>
  `!x:num#num. x IN retained ==> x IN V /\ keep (pc x)` by simp[Abbr `retained`] >>
  Q.SUBGOAL_THEN `!x. x IN V ==> exit x IN retained /\ height (exit x) = height x`
    (mk_asm "exitRetained") >-
     (simp[Abbr `retained`] >> metis_tac[]) >>
  `!x k. (tag' x k = NONE <=> tag x k = NONE) /\
     !l j. tag' x k = SOME(l,j) <=> ?i. tag x k = SOME(l,i) /\ j=f i`
    by simp[Abbr `tag'`, pairTheory.EXISTS_PROD] >>
  `!x. x IN retained ==> Slots q a.as_call_ctx height need tag' boolean x` by
    suspend "slots" >>
  Q.SUBGOAL_THEN `!x. x IN retained ==> pc' x < LENGTH q /\ EL (pc' x) q = EL (pc x) p`
    (mk_asm "retainedFetch") >- suspend "fetch" >>
  Q.SUBGOAL_THEN `!x y. x IN retained /\ edge x y /\ pc y = pc x+1 ==>
      pc' (exit y) = pc' x+1` (mk_asm "relocateFall") >- suspend "fall" >>
  Q.SUBGOAL_THEN `!x y. Target p pc tag x y ==> keep (pc y) /\ Target q pc' tag' x y`
    (mk_asm "relocateTarget") >- suspend "taken" >>
  Q.SUBGOAL_THEN `!y. y IN V /\ keep (pc y) ==> exit y=y`
    (mk_asm "exitFixed") >- (
      qx_gen_tac `y` >> strip_tac >>
      qpat_assum `!y. y IN V ==> _ /\ _ /\ _ /\ (if _ then _ else _)`
        (qspec_then `y` (drule_then (mp_tac o List.last o CONJUNCTS))) >>
      qpat_assum `keep (pc y)` (fn th => simp[NoAsms,th])) >>
  Q.SUBGOAL_THEN `!x y. x IN retained /\ edge x y /\ Target p pc tag x y ==>
      Target q pc' tag' x (exit y)` (mk_asm "relocateTaken") >- (
      rpt gen_tac >> strip_tac >>
      asm "relocateTarget" (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >>
      asm "oldFlow" (qspecl_then [`x`,`y`] (drule_then (assume_tac o el 2 o CONJUNCTS))) >>
      asm "exitFixed" (qspec_then `y` (drule_all_then SUBST1_TAC)) >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `!x z. newEdge x z ==> x IN retained /\ z IN retained /\ rank z < rank x /\
       Flow q pc' height tag' boolean x z /\ Control q pc' tag' x z`
    (mk_asm "newEdges") >- suspend "edges" >>
  map_every qexists_tac [`retained`,`exit e`,`rank`,`pc'`,`height`,`need`,`tag'`,`boolean`,`newEdge`] >>
  qpat_assum `q:asm_inst list = _` (fn eq => pure_rewrite_tac [GSYM eq]) >>
  qpat_assum `t.as_call_ctx = a.as_call_ctx` (pure_rewrite_tac o single) >>
  conj_tac >- (irule SUBSET_FINITE_I >> qexists `V` >> simp[SUBSET_DEF]) >>
  conj_tac >- (asm "exitRetained" (qspec_then `e` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  reverse conj_tac >-
    (conj_tac >- asm "newEdges" ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >> suspend "root") >>
  suspend "rows_edges"
QED

Resume merge_iszero_pair_cut_rows[slots]:
  qx_gen_tac `x` >> disch_tac >> `x IN V` by metis_tac[] >>
  asm "oldSlots" (qspec_then `x` (drule_then mp_tac)) >>
  qunabbrev_tac `Slots` >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (mk_asm "oldBoolean") (mk_asm "oldTag"))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qx_gen_tac `k` >> disch_tac >>
    asm "oldBoolean" (qspec_then `k` (drule_then strip_assume_tac)) >> simp[]) >>
  map_every qx_gen_tac [`k`,`l`,`j`] >>
  simp[IgnAsm `q:asm_inst list = _`, IgnAsm `p:asm_inst list = _`] >>
  disch_then (qx_choose_then `i` (CONJUNCTS_THEN2 assume_tac SUBST1_TAC)) >>
  asm "oldTag" (qspecl_then [`k`,`l`,`i`] (drule_then
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "oldOrigin")
        (qx_choose_then `off` (qx_choose_then `dest` (map_every assume_tac o CONJUNCTS)))))))) >>
  Q.SUBGOAL_THEN `i < LENGTH pre + 1 \/ LENGTH pre + 3 <= i` assume_tac >- (
    asm "layoutOrigin" (qspecl_then [`l`,`i`] mp_tac) >>
    asm "oldOrigin" strip_assume_tac >>
    simp[IgnAsm `p:asm_inst list = _`]) >>
  asm "layoutFetch" (qspec_then `i` mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "originFetch")) >>
  qunabbrev_tac `f` >> qunabbrev_tac `b` >> BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (asm "originFetch" (rewrite_tac o single) >> asm "oldOrigin" ACCEPT_TAC) >>
  asm "layoutTarget" (qspecl_then [`l`,`off`,`dest`] (drule_all_then
    (qx_choose_then `off'` (map_every assume_tac o CONJUNCTS) o List.last o CONJUNCTS))) >>
  qexistsl [`off'`,`if dest < LENGTH pre+1 then dest else dest-2`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Resume merge_iszero_pair_cut_rows[root]:
  qpat_assum `Root p ss a pc height need tag boolean e` mp_tac >>
  qunabbrev_tac `Root` >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "oldShape")
    (CONJUNCTS_THEN2 (mk_asm "oldRootTag") (mk_asm "oldRootBoolean"))) >>
  asm "oldShape" mp_tac >> qunabbrev_tac `Shape` >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac kall_tac)) >>
  qpat_assum `asm_sym_rel p _ a ss` (mp_then Any (map_every assume_tac o CONJUNCTS) asm_sym_rel_pc) >>
  qpat_assum `asm_sym_rel q _ t u` (mp_then Any (map_every assume_tac o CONJUNCTS) asm_sym_rel_pc) >>
  `pc e = ss.sym_base.as_pc` by
    (qpat_assum `a.as_pc = pc e` (rewrite_tac o single o SYM) >> simp[]) >>
  asm "exitRetained" (qspec_then `e` (drule_then strip_assume_tac)) >>
  `pc' (exit e) = t.as_pc /\ LENGTH u.sym_stack = LENGTH ss.sym_stack /\
   (!k l origin. tag' (exit e) k = SOME(l,origin) ==>
       k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
   (!k. boolean (exit e) k ==> k < LENGTH u.sym_stack /\
       (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))` by
    suspend "root_endpoint" >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "root_shape"
QED

Resume merge_iszero_pair_cut_rows[root_endpoint]:
  qpat_assum `!y. y IN V ==> _ /\ _ /\ _ /\ (if _ then _ else _)`
    (qspec_then `e` (drule_then (mp_tac o List.last o CONJUNCTS))) >>
  qpat_x_assum `if _ then _ else u = _` mp_tac >>
  Cases_on `b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+3`
  >- (`~keep (pc e)` by
        (qunabbrev_tac `keep` >> BETA_TAC >>
         qpat_assum `pc e = ss.sym_base.as_pc` (rewrite_tac o single) >> decide_tac) >>
      pop_assum (rewrite_tac o single) >> suspend "root_interior") >>
  `keep (pc e)` by
    (qunabbrev_tac `keep` >> BETA_TAC >>
     qpat_assum `pc e = ss.sym_base.as_pc` (rewrite_tac o single) >> decide_tac) >>
  pop_assum (rewrite_tac o single) >> suspend "root_kept"
QED

Resume merge_iszero_pair_cut_rows[root_interior]:
  qpat_assum `b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+3`
    (fn th => simp[NoAsms, th]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `w` (qx_choose_then `stk` (map_every assume_tac o CONJUNCTS)))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 (mk_asm "exitTag") (mk_asm "exitBoolean"))))) >>
  conj_tac >- (
    simp[NoAsms, Abbr `pc'`, Abbr `f`] >>
    qpat_assum `pc (exit e) = b+3` (rewrite_tac o single) >>
    qpat_assum `u.sym_base.as_pc = t.as_pc` (rewrite_tac o single o SYM) >>
    qpat_assum `u.sym_base.as_pc = b+1` (rewrite_tac o single) >> decide_tac) >>
  `LENGTH u.sym_stack = LENGTH ss.sym_stack` by
    (qpat_assum `u.sym_stack = Val w::stk` (rewrite_tac o single) >>
     qpat_assum `ss.sym_stack = _::stk` (rewrite_tac o single) >> simp[NoAsms]) >>
  `!k. 0 < k ==> EL k u.sym_stack = EL k ss.sym_stack` by
    (qpat_assum `u.sym_stack = Val w::stk` (rewrite_tac o single) >>
     qpat_assum `ss.sym_stack = _::stk` (rewrite_tac o single) >>
     simp[NoAsms, rich_listTheory.EL_CONS]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (
    map_every qx_gen_tac [`k`,`l`,`j`] >> disch_tac >>
    qpat_assum `!x k. _ /\ !l j. _` (qspecl_then [`exit e`,`k`] (mp_tac o CONJUNCT2)) >>
    disch_then (qspecl_then [`l`,`j`] (drule_then strip_assume_tac o iffLR)) >>
    asm "exitTag" (qspecl_then [`k`,`l`,`i`] (drule_then strip_assume_tac)) >>
    asm "oldRootTag" (qspecl_then [`k`,`l`,`i`] (drule_then strip_assume_tac)) >>
    simp[IgnAsm `ss.sym_stack = _`, IgnAsm `u.sym_stack = _`]) >>
  qx_gen_tac `k` >> disch_tac >> Cases_on `k=0`
  >- (qpat_assum `k=0` (rewrite_tac o single) >>
      qpat_assum `u.sym_stack = Val w::stk` (rewrite_tac o single) >>
      qpat_assum `w = 0w \/ w = 1w` (fn th => simp[NoAsms, th])) >>
  `0 < k` by decide_tac >>
  asm "exitBoolean" (qspec_then `k` (drule_all_then assume_tac)) >>
  asm "oldRootBoolean" (qspec_then `k` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  simp[IgnAsm `ss.sym_stack = _`, IgnAsm `u.sym_stack = _`]
QED

Resume merge_iszero_pair_cut_rows[root_kept]:
  qpat_assum `~(b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+3)`
    (fn th => simp[NoAsms, th]) >>
  disch_tac >> disch_then (rewrite_tac o single) >>
  `u.sym_stack = ss.sym_stack` by
    (qpat_assum `u = sym_with_pc _ ss` (rewrite_tac o single) >> simp[NoAsms, asmSymPcTheory.sym_with_pc_def]) >>
  conj_tac >- (
    simp[NoAsms, Abbr `pc'`, Abbr `f`] >>
    qpat_assum `pc e = ss.sym_base.as_pc` (rewrite_tac o single) >>
    qpat_assum `u.sym_base.as_pc = t.as_pc` (rewrite_tac o single o SYM) >>
    qpat_assum `u = sym_with_pc _ ss` (rewrite_tac o single) >>
    simp[NoAsms, asmSymPcTheory.sym_with_pc_def, splice_pc_def] >> decide_tac) >>
  qpat_assum `u.sym_stack = ss.sym_stack` (rewrite_tac o single) >>
  conj_tac >- (
    map_every qx_gen_tac [`k`,`l`,`j`] >> disch_tac >>
    qpat_assum `!x k. _ /\ !l j. _` (qspecl_then [`e`,`k`] (mp_tac o CONJUNCT2)) >>
    disch_then (qspecl_then [`l`,`j`] (drule_then strip_assume_tac o iffLR)) >>
    asm "oldRootTag" (qspecl_then [`k`,`l`,`i`] (drule_then ACCEPT_TAC))) >>
  asm "oldRootBoolean" ACCEPT_TAC
QED

Resume merge_iszero_pair_cut_rows[root_shape]:
  qpat_assum `!x. x IN retained ==> Slots q _ _ _ _ _ x`
    (qspec_then `exit e` (drule_then mp_tac)) >>
  qunabbrev_tac `Slots` >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "staticSlot")
    (CONJUNCTS_THEN2 (mk_asm "boolSlot") (mk_asm "tagSlot"))) >>
  qpat_assum `asm_sym_rel q _ t u`
    (mk_asm "concreteSlot" o CONJUNCT2 o
     REWRITE_RULE[listTheory.LIST_REL_EL_EQN] o CONJUNCT1 o PURE_REWRITE_RULE[asm_sym_rel_def]) >>
  conj_tac >- (sym_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (
    qpat_assum `LENGTH u.sym_stack = LENGTH t.as_stack` (rewrite_tac o single o SYM) >>
    qpat_assum `LENGTH u.sym_stack = LENGTH ss.sym_stack` (rewrite_tac o single) >>
    qpat_assum `LENGTH ss.sym_stack = LENGTH a.as_stack` (rewrite_tac o single) >>
    qpat_assum `LENGTH a.as_stack = height e` (rewrite_tac o single) >>
    qpat_assum `height (exit e) = height e` (rewrite_tac o single)) >>
  simp[NoAsms] >> conj_tac >- (
    qpat_assum `t.as_call_ctx = a.as_call_ctx` (rewrite_tac o single) >> asm "staticSlot" ACCEPT_TAC) >>
  conj_tac >- (
    map_every qx_gen_tac [`k`,`l`,`j`] >> disch_tac >>
    asm "tagSlot" (qspecl_then [`k`,`l`,`j`] (drule_then
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 (mk_asm "pos")
          (qx_choose_then `off` (qx_choose_then `dest` (map_every assume_tac o CONJUNCTS)))))))) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (asm "pos" (DISJ_CASES_THEN assume_tac) >- (disj1_tac >> first_assum ACCEPT_TAC) >>
                  disj2_tac >> disj1_tac >> qexists_tac `0` >> first_assum ACCEPT_TAC) >>
    qexistsl [`off`,`dest`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `!k l origin. tag' (exit e) k = SOME(l,origin) ==> _`
      (qspecl_then [`k`,`l`,`j`] (drule_then strip_assume_tac)) >>
    asm "concreteSlot" (qspec_then `k` (drule_then mp_tac)) >>
    simp[sval_conc_def, IgnAsm `q:asm_inst list = _`]) >>
  qx_gen_tac `k` >> disch_tac >>
  asm "boolSlot" (qspec_then `k` (drule_then (assume_tac o CONJUNCT1))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!k. boolean (exit e) k ==> k < LENGTH u.sym_stack /\ _`
    (qspec_then `k` (drule_then (CONJUNCTS_THEN2 assume_tac (DISJ_CASES_THEN assume_tac)))) >>
  asm "concreteSlot" (qspec_then `k` (drule_then mp_tac)) >> simp[sval_conc_def]
QED

Resume merge_iszero_pair_cut_rows[fetch]:
  qx_gen_tac `x` >> disch_tac >>
  qpat_assum `!x. x IN retained ==> _ /\ _` (qspec_then `x` (drule_then strip_assume_tac)) >>
  asm "oldRow" (qspec_then `x` (drule_then (assume_tac o CONJUNCT1))) >>
  asm "layoutFetch" (qspec_then `pc x` mp_tac) >>
  simp[NoAsms, Abbr `pc'`, Abbr `f`, Abbr `b`] >>
  impl_tac >- (conj_tac >- fs[Abbr `keep`] >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Resume merge_iszero_pair_cut_rows[fall]:
  map_every qx_gen_tac [`x`,`y`] >> strip_tac >>
  qpat_assum `!x. x IN retained ==> _ /\ _` (qspec_then `x` (drule_then strip_assume_tac)) >>
  asm "oldFlow" (qspecl_then [`x`,`y`] (drule_then (assume_tac o el 2 o CONJUNCTS))) >>
  simp[NoAsms, Abbr `pc'`, Abbr `f`] >> irule pair_skip_fall >>
  qpat_assum `pc y = pc x+1` (pure_rewrite_tac o single o SYM) >>
  conj_tac >- fs[Abbr `keep`] >>
  qpat_assum `!y. y IN V ==> _ /\ _ /\ _ /\ (if _ then _ else _)`
    (qspec_then `y` (drule_then (mp_tac o List.last o CONJUNCTS))) >>
  qunabbrev_tac `keep` >> BETA_TAC >>
  Cases_on `pc y < b+1 \/ b+3 <= pc y` >>
  pop_assum (fn guard => simp[NoAsms, guard]) >>
  disch_then strip_assume_tac >> first_assum ACCEPT_TAC
QED

Resume merge_iszero_pair_cut_rows[taken]:
  map_every qx_gen_tac [`x`,`y`] >> qunabbrev_tac `Target` >> BETA_TAC >>
  disch_then (qx_choose_then `l` (qx_choose_then `i` (qx_choose_then `old`
    (map_every assume_tac o CONJUNCTS)))) >>
  asm "layoutTarget" (qspecl_then [`l`,`old`,`pc y`] (drule_all_then
    (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `off` (map_every assume_tac o CONJUNCTS) o List.last o CONJUNCTS)))) >>
  conj_tac >- simp[Abbr `keep`, Abbr `b`] >>
  qexistsl [`l`,`f i`,`off`] >>
  simp[Abbr `pc'`, Abbr `f`, Abbr `b`, IgnAsm `q:asm_inst list = _`, IgnAsm `p:asm_inst list = _`]
QED

Resume merge_iszero_pair_cut_rows[edges]:
  map_every qx_gen_tac [`x`,`z`] >> qunabbrev_tac `newEdge` >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `y` (CONJUNCTS_THEN2 assume_tac (SUBST1_TAC o SYM)))) >>
  asm "oldControl" (qspecl_then [`x`,`y`] (drule_then (map_every assume_tac o CONJUNCTS))) >>
  asm "exitRetained" (qspec_then `y` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (
    qpat_assum `!y. y IN V ==> _ /\ _ /\ _ /\ (if _ then _ else _)`
      (qspec_then `y` (drule_then (mp_tac o List.last o CONJUNCTS))) >>
    Cases_on `keep (pc y)` >> pop_assum (fn th => simp[NoAsms,th]) >>
    strip_tac >> simp[]) >>
  asm "retainedFetch" (qspec_then `x` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (mk_asm "edgeFetch" o CONJUNCT2) >>
  reverse conj_tac >- suspend "edge_control" >>
  Cases_on `keep (pc y)`
  >- (asm "exitFixed" (qspec_then `y` (drule_all_then SUBST1_TAC)) >> suspend "flow_kept") >>
  suspend "flow_bypass"
QED

Resume merge_iszero_pair_cut_rows[edge_control]:
  qpat_x_assum `Control p pc tag x y` mp_tac >> qunabbrev_tac `Control` >> BETA_TAC >>
  asm "edgeFetch" (pure_rewrite_tac o single) >>
  Cases_on `EL (pc x) p = AsmOp "JUMP"`
  >- (pop_assum (fn th => simp[NoAsms,th]) >> disch_tac >>
      asm "relocateTaken" (qspecl_then [`x`,`y`] irule) >> simp[]) >>
  pop_assum (fn th => simp[NoAsms,th]) >>
  Cases_on `EL (pc x) p = AsmOp "JUMPI"`
  >- (pop_assum (fn th => simp[NoAsms,th]) >> strip_tac
      >- (disj1_tac >> asm "relocateFall" (qspecl_then [`x`,`y`] irule) >> simp[]) >>
      disj2_tac >> asm "relocateTaken" (qspecl_then [`x`,`y`] irule) >> simp[]) >>
  pop_assum (fn th => simp[NoAsms,th]) >> disch_tac >>
  asm "relocateFall" (qspecl_then [`x`,`y`] irule) >> simp[]
QED

Resume merge_iszero_pair_cut_rows[flow_kept]:
  `!bs s. asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
      (AsmPush bs) s = asm_step (SND (compute_label_offsets p))
      (build_offset_to_pc p) (AsmPush bs) s` by
    simp[NoAsms, asm_step_def] >>
  pop_assum (mk_asm "pushMaps") >>
  `!name h.
    (asm_returns_zero_or_one (AsmOp name) /\
      !s v. LENGTH s.as_stack = h /\
        asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
          (AsmOp name) s = AsmOK v ==> HD v.as_stack = 0w \/ HD v.as_stack = 1w) =
    (asm_returns_zero_or_one (AsmOp name) /\
      !s v. LENGTH s.as_stack = h /\
        asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
          (AsmOp name) s = AsmOK v ==> HD v.as_stack = 0w \/ HD v.as_stack = 1w)` by
    (rpt gen_tac >> Cases_on `asm_returns_zero_or_one (AsmOp name)` >>
     simp[IgnAsm `p:asm_inst list = _`, IgnAsm `q:asm_inst list = _`] >>
     `!s. asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
            (AsmOp name) s = asm_step (SND (compute_label_offsets p))
            (build_offset_to_pc p) (AsmOp name) s` by
       (gen_tac >> irule pair_boolean_dispatch_maps >> first_assum ACCEPT_TAC) >>
     pop_assum (fn th => simp[NoAsms, th])) >>
  pop_assum (mk_asm "boolMaps") >>
  qpat_x_assum `Flow p pc height tag boolean x y` mp_tac >>
  qunabbrev_tac `Flow` >> BETA_TAC >>
  asm "edgeFetch" (pure_rewrite_tac o single) >> simp[NoAsms] >>
  qunabbrev_tac `tag'` >> qunabbrev_tac `pc'` >> BETA_TAC >>
  Cases_on `EL (pc x) p` >> simp[NoAsms, Excl "OPTION_MAP_EQ_SOME"] >>
  TRY (qmatch_goalsub_rename_tac `ALOOKUP dup_table name` >>
       Cases_on `ALOOKUP dup_table name` >>
       TRY (qmatch_goalsub_rename_tac `ALOOKUP swap_table name` >>
            Cases_on `ALOOKUP swap_table name`) >>
       simp[NoAsms, Excl "OPTION_MAP_EQ_SOME"]) >>
  asm "pushMaps" (fn push => asm "boolMaps" (fn opmap =>
    simp[NoAsms, push, opmap, Excl "OPTION_MAP_EQ_SOME"])) >>
  strip_tac >> rpt conj_tac >>
  TRY (drule_all_then (pure_rewrite_tac o single)
    (DECIDE ``!h j d:num. d <= h /\ j = (j+d-h)+(h-d) ==>
      !k. ((k+h)-(j+d))+d = (k-(j+d-h))+d``)) >>
  (first_assum ACCEPT_TAC ORELSE
   (qx_gen_tac `k` >> disch_tac >>
    qpat_assum `!j. boolean y j ==> _`
      (qspec_then `k` (drule_then (ACCEPT_TAC o CONJUNCT2)))) ORELSE
   (rpt gen_tac >> disch_then (fn th =>
      qpat_assum `!j. boolean y j ==> _`
        (fn rule => strip_assume_tac (MATCH_MP rule th))) >> first_assum ACCEPT_TAC) ORELSE
   (rpt gen_tac >>
    simp[NoAsms, optionTheory.OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD] >>
    strip_tac >> rename1 `tag y k = SOME(lab,srcOrigin)` >>
    qpat_assum `!k l i. tag y k = SOME(l,i) ==> _`
      (qspecl_then [`k`,`lab`,`srcOrigin`] (drule_then
        (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()]))) >>
    simp[]))
QED

Resume merge_iszero_pair_cut_rows[flow_bypass]:
  `~Target p pc tag x y` by
    (strip_tac >> asm "relocateTarget" (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >>
     qpat_assum `~keep (pc y)` mp_tac >> simp[]) >>
  `pc y = pc x+1` by
    (qpat_assum `Control p pc tag x y` mp_tac >>
     qunabbrev_tac `Control` >> BETA_TAC >>
     Cases_on `EL (pc x) p = AsmOp "JUMP"` >>
     Cases_on `EL (pc x) p = AsmOp "JUMPI"` >> simp[]) >>
  qpat_assum `!x. x IN retained ==> _ /\ _` (qspec_then `x` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then strip_assume_tac >>
  `pc x=b` by
    (qpat_assum `keep (pc x)` mp_tac >> qpat_assum `~keep (pc y)` mp_tac >>
     qpat_assum `pc y = pc x+1` mp_tac >> simp[NoAsms, Abbr `keep`] >> decide_tac) >>
  `EL (pc x) p = ins` by
    (drule_then (assume_tac o CONJUNCT1) pair_slice_blocks >>
     qpat_assum `pc x=b` SUBST1_TAC >> simp[NoAsms, Abbr `b`] >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `?name. ins = AsmOp name` (qx_choose_then `name` assume_tac) >-
    (qpat_assum `asm_returns_zero_or_one ins` mp_tac >>
     rewrite_tac[asm_returns_zero_or_one_def, MEM_MAP] >>
     disch_then (qx_choose_then `opname` strip_assume_tac) >>
     qexists `opname` >> first_assum ACCEPT_TAC) >>
  `~MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] /\
   name<>"INVALID" /\ name<>"REVERT" /\ name<>"JUMP" /\ name<>"JUMPI" /\
   ALOOKUP dup_table name=NONE /\ ALOOKUP swap_table name=NONE` by
    (qpat_assum `asm_returns_zero_or_one ins` mp_tac >>
     qpat_assum `ins = AsmOp name` (pure_rewrite_tac o single) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[asm_returns_zero_or_one_def] >> strip_tac >> gvs[] >> EVAL_TAC) >>
  asm "oldRow" (qspec_then `x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT2) >>
  qpat_assum `EL (pc x) p = ins` (pure_rewrite_tac o single) >>
  qpat_assum `ins = AsmOp name` (pure_rewrite_tac o single) >>
  simp[IgnAsm `p:asm_inst list = _`, IgnAsm `q:asm_inst list = _`] >>
  disch_then (qx_choose_then `m` strip_assume_tac) >>
  `asm_returns_zero_or_one (AsmOp name)` by
    (qpat_assum `ins = AsmOp name` (pure_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  drule_all_then
    (CONJUNCTS_THEN2 assume_tac (mk_asm "producerBoolean" o CONJUNCT2 o CONJUNCT2))
    pair_producer_shape >>
  `height y = height x - asm_op_arity name + 1` by
    (qpat_assum `!v. edge x v ==> _` (qspec_then `y` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >>
     disch_then (mp_tac o CONJUNCT2) >> simp[]) >>
  qpat_assum `!z. z IN V ==> _ /\ _ /\ _ /\ (if _ then _ else _)`
    (qspec_then `y` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `~keep (pc y)` (fn th => simp[NoAsms,th]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `height y + asm_op_arity name - height x = 1` by
    (irule (DECIDE ``!d h j:num. d <= h /\ j = h-d+1 ==> j+d-h=1``) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `height y = 1 + (height x - asm_op_arity name)` by
    (pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  qpat_assum `Flow p pc height tag boolean x y` mp_tac >>
  qunabbrev_tac `Flow` >> BETA_TAC >>
  asm "edgeFetch" (pure_rewrite_tac o single) >>
  qpat_assum `EL (pc x) p = ins` (pure_rewrite_tac o single) >>
  qpat_assum `ins = AsmOp name` (pure_rewrite_tac o single) >>
  qpat_assum `height (exit y) = height y` (pure_rewrite_tac o single) >>
  qpat_assum `ALOOKUP dup_table name = NONE` (fn dup =>
    qpat_assum `ALOOKUP swap_table name = NONE` (fn swap =>
      qpat_assum `height y + asm_op_arity name - height x = 1` (fn ar =>
        qpat_assum `name <> "JUMP"` (fn jump =>
          qpat_assum `name <> "JUMPI"` (fn jumpi =>
            SIMP_TAC bool_ss [LET_THM, asm_inst_case_def, dup, swap, ar, jump, jumpi,
              optionTheory.option_case_def, optionTheory.NOT_NONE_SOME,
              DECIDE ``!k:num. k < 1 <=> k=0``]))))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `height y = 1 + _` (pure_rewrite_tac o single o SYM) >>
  conj_tac >- (
    map_every qx_gen_tac [`k`,`l`,`j`] >> disch_tac >>
    qpat_assum `!x k. _ /\ !l j. _`
      (qspecl_then [`exit y`,`k`] (mp_tac o CONJUNCT2)) >>
    disch_then (qspecl_then [`l`,`j`] (drule_then strip_assume_tac o iffLR)) >>
    qpat_assum `!k l i. tag (exit y) k = SOME(l,i) ==> _`
      (qspecl_then [`k`,`l`,`i`] (drule_then strip_assume_tac)) >>
    qpat_assum `!k l i. tag y k = SOME(l,i) ==> _`
      (qspecl_then [`k`,`l`,`i`] (drule_then strip_assume_tac)) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    rename1 `tag x src = SOME(l,i)` >> qexists `src` >>
    conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!x k. _ /\ !l j. _`
      (qspecl_then [`x`,`src`] (mp_tac o CONJUNCT2)) >>
    disch_then (qspecl_then [`l`,`j`] (irule o iffRL)) >>
    qexists `i` >> simp[]) >>
  qx_gen_tac `k` >> disch_tac >> Cases_on `k=0`
  >- (qpat_assum `k = 0` (fn zero => SIMP_TAC bool_ss [zero]) >>
      conj_tac >- (qpat_assum `height y = 1 + _` (fn h => simp[NoAsms,h])) >>
      disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      asm "producerBoolean" (drule_then mp_tac) >> simp[NoAsms]) >>
  `0 < k` by (irule (DECIDE ``!k:num. k <> 0 ==> 0 < k``) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!k. 0 < k /\ boolean (exit y) k ==> _`
    (qspec_then `k` (drule_all_then assume_tac)) >>
  qpat_assum `!k. boolean y k ==> _`
    (qspec_then `k` (drule_then mp_tac)) >>
  qpat_assum `k <> 0` (fn nz => SIMP_TAC bool_ss [nz])
QED

Resume merge_iszero_pair_cut_rows[rows_edges]:
  qunabbrev_tac `Rows` >> SIMP_TAC bool_ss [LET_THM, DIFF_EMPTY] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt gen_tac >> disch_tac >>
    asm "newEdges" (drule_then (map_every assume_tac o CONJUNCTS)) >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `x` >> disch_tac >>
  `x IN V` by (qpat_assum `!x. x IN retained ==> x IN V /\ _`
    (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  asm "retainedFetch" (qspec_then `x` (drule_then
    (CONJUNCTS_THEN2 assume_tac (mk_asm "fetchRow")))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!y. edge x y ==> newEdge x (exit y) /\ height (exit y) = height y` by (
    qx_gen_tac `y` >> disch_tac >>
    conj_tac >- (qunabbrev_tac `newEdge` >> BETA_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >> qexists `y` >> simp[]) >>
    asm "oldFlow" (qspecl_then [`x`,`y`] (drule_then (assume_tac o el 2 o CONJUNCTS))) >>
    asm "exitRetained" (qspec_then `y` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  `!z. newEdge x z ==> ?y. edge x y /\ z=exit y` by (
    qunabbrev_tac `newEdge` >> BETA_TAC >> metis_tac[]) >>
  `!y. edge x y ==> (pc y = pc x+1 ==> pc' (exit y) = pc' x+1) /\
                   (Target p pc tag x y ==> Target q pc' tag' x (exit y))` by (
    rpt gen_tac >> disch_tac >> conj_tac >> disch_tac
    >- asm "relocateFall" (qspecl_then [`x`,`y`] (drule_all_then ACCEPT_TAC)) >>
    asm "relocateTaken" (qspecl_then [`x`,`y`] (drule_all_then ACCEPT_TAC))) >>
  Q.SUBGOAL_THEN `!P Q n.
      (!y. edge x y /\ P y ==> Q (exit y)) ==>
      ((?y. edge x y /\ P y /\ height y=n) ==>
       (?z. newEdge x z /\ Q z /\ height z=n)) /\
      ((!y. edge x y ==> P y /\ height y=n) ==>
       (!z. newEdge x z ==> Q z /\ height z=n))` (mk_asm "transport") >- (
    rpt gen_tac >> disch_tac >> conj_tac
    >- (disch_then (qx_choose_then `y` strip_assume_tac) >>
        qexists `exit y` >> metis_tac[]) >>
    disch_tac >> qx_gen_tac `z` >> disch_tac >>
    qpat_assum `!z. newEdge x z ==> ?y. _` (drule_then strip_assume_tac) >>
    metis_tac[]) >>
  map_every (fn (label, old, new) =>
    asm "transport" (qspecl_then [old,new] mp_tac) >>
    SIMP_TAC bool_ss [] >> (impl_tac >- metis_tac[]) >>
    disch_then (mk_asm label o REWRITE_RULE[FORALL_AND_THM]))
    [("fallTransfer", `\y. pc y = pc x+1`, `\y. pc' y = pc' x+1`),
     ("takenTransfer", `Target p pc tag x`, `Target q pc' tag' x`),
     ("eitherTransfer", `\y. pc y = pc x+1 \/ Target p pc tag x y`,
                       `\y. pc' y = pc' x+1 \/ Target q pc' tag' x y`)] >>
  Q.SUBGOAL_THEN `(!y. ~edge x y) ==> !z. ~newEdge x z` (mk_asm "stopTransfer")
    >- (disch_tac >> qx_gen_tac `z` >> disch_tac >>
        qpat_assum `!z. newEdge x z ==> ?y. _` (drule_then strip_assume_tac) >>
        metis_tac[]) >>
  Q.SUBGOAL_THEN `!k. tag' x k = NONE <=> tag x k = NONE` (mk_asm "tagNone")
    >- (qx_gen_tac `k` >> qpat_assum `!x k. _ /\ !l j. _`
          (qspecl_then [`x`,`k`] (ACCEPT_TAC o CONJUNCT1))) >>
  `MEM (EL (pc x) p) q` by
    (asm "fetchRow" (rewrite_tac o single o SYM) >> irule EL_MEM >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `!l. (EL (pc x) p = AsmPushLabel l \/
                       (?d. EL (pc x) p = AsmPushOfst l d)) ==>
                       IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l)`
    (mk_asm "pushLookup") >- (
    qx_gen_tac `l` >> disch_tac >>
    `MEM l (asm_label_refs q)` by (
      simp[NoAsms, asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      qexists `EL (pc x) p` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      first_x_assum (DISJ_CASES_THEN2 (rewrite_tac o single)
        (CHOOSE_THEN (rewrite_tac o single))) >> simp[NoAsms]) >>
    `MEM (AsmLabel l) q \/ MEM (AsmDataHeader l) q` by (
      asm "layoutWf" (mp_tac o REWRITE_RULE[asm_static_wf_def]) >>
      strip_tac >> first_assum (drule_then ACCEPT_TAC)) >>
    simp[NoAsms, finite_mapTheory.FLOOKUP_DEF, symbolResolveTheory.compute_label_offsets_def,
         asmToBytecodeProofsTheory.clo_step_eq] >>
    `l IN FDOM (SND (FOLDL
      (\(pc,labels) inst. (pc + asm_inst_size inst,
         case inst of AsmLabel lbl => labels |+ (lbl,pc)
                    | AsmDataHeader lbl => labels |+ (lbl,pc) | _ => labels))
      (0,FEMPTY) q))` by (irule clo_FDOM >> simp[]) >> simp[]) >>
  asm "oldRow" (qspec_then `x` (drule_then (mp_tac o CONJUNCT2))) >>
  asm "fetchRow" (rewrite_tac o single) >>
  map_every (fn label => asm label mp_tac)
    ["fallTransfer","takenTransfer","eitherTransfer","stopTransfer","tagNone","pushLookup"] >>
  POP_ASSUM_LIST kall_tac >> ntac 6 disch_tac >>
  Cases_on `EL (pc x) p` >> SIMP_TAC bool_ss [TypeBase.case_def_of ``:asm_inst``]
  >- (rename1 `EL (pc x) p = AsmOp name` >>
      qpat_x_assum `!l. _ ==> IS_SOME _` kall_tac >>
      Cases_on `name = "INVALID"` >> pop_assum (fn th => SIMP_TAC bool_ss [th])
      >- metis_tac[] >>
      Cases_on `name = "REVERT"` >> pop_assum (fn th => SIMP_TAC bool_ss [th])
      >- metis_tac[] >>
      Cases_on `MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]` >>
      pop_assum (fn th => SIMP_TAC bool_ss [th]) >- metis_tac[] >>
      Cases_on `ALOOKUP dup_table name` >>
      pop_assum (fn th => SIMP_TAC bool_ss [th,optionTheory.option_case_def])
      >- (Cases_on `ALOOKUP swap_table name` >>
          pop_assum (fn th => SIMP_TAC bool_ss [th,optionTheory.option_case_def])
          >- (Cases_on `name = "JUMP"` >> pop_assum (fn th => SIMP_TAC bool_ss [th])
              >- metis_tac[] >>
              Cases_on `name = "JUMPI"` >> pop_assum (fn th => SIMP_TAC bool_ss [th])
              >- metis_tac[] >>
              disch_then (qx_choose_then `m` strip_assume_tac) >> qexists `m` >> metis_tac[]) >>
          metis_tac[]) >>
      metis_tac[]) >>
  qpat_x_assum `!l. _ ==> IS_SOME _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  metis_tac[]
QED

Resume merge_iszero_pair_cut_rows[package]:
  disch_then (qx_choose_then `V` (qx_choose_then `e` (qx_choose_then `rank`
    (qx_choose_then `pc` (qx_choose_then `height` (qx_choose_then `need`
    (qx_choose_then `tag` (qx_choose_then `boolean` (qx_choose_then `edge`
    (map_every assume_tac o CONJUNCTS)))))))))) >>
  `!x y. edge x y ==> Flow q pc height tag boolean x y /\ Control q pc tag x y` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x y. edge x y ==> x IN V /\ _`
       (qspecl_then [`x`,`y`] (drule_then (fn th => simp[th])))) >>
  qabbrev_tac `liveSet = {x | x IN V /\ Reach edge e x}` >>
  qabbrev_tac `liveEdge = \x y. x IN liveSet /\ edge x y` >>
  qpat_x_assum `Cert p ss a` kall_tac >>
  map_every qunabbrev_tac
    [`Cert`,`Rows`,`Root`,`Open`,`Reach`,`Control`,`Slots`,`Flow`,`Target`,`Shape`] >>
  (* Normalize lexical bindings without using the package premises to rewrite
     its conclusion: the final join uses the returned clauses verbatim. *)
  (let
     val normalize = TOP_DEPTH_CONV (FIRST_CONV
       [BETA_CONV, HO_REWR_CONV UNWIND_FORALL_THM2, REWR_CONV DIFF_EMPTY,
        REWR_CONV ratTheory.RAT_OF_NUM_LES])
   in
     rule_assum_tac (CONV_RULE normalize) >> CONV_TAC normalize >>
     qpat_assum `q:asm_inst list = _` (pure_rewrite_tac o single o GSYM) >>
     (* The package only compares ranks; embed the retained natural rank. *)
     mp_tac (CONV_RULE normalize
       (Q.SPECL [`q`,`u`,`t`,`V`,`e`,`\x. rat$rat_of_num (rank x)`,
                  `pc`,`height`,`need`,`tag`,`boolean`,`edge`] pending_rows_rooted_package))
   end) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
  qexistsl [`liveSet`,`e`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`liveEdge`] >>
  qpat_assum `Abbrev (liveEdge = _)` (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (liveSet = _)` (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Finalise merge_iszero_pair_cut_rows
