Theory staticAbortOptStackCommRow
Ancestors
  staticAbortOptStackGuardedSource staticAbortStraight asmSplice
  asmOptimizer asmSem asmIR alist list pred_set arithmetic words pair option

Theorem stack_comm_replacement_row:
!p q cc req V rank pc height need tag boolean edge v pre tail a.
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
let Open =
  \p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need
    (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) edge.
  let LiveShape = Shape p cc req pc height need tag boolean in
  let target = \x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME(pc y)
  in
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. LiveShape x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ target x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF X /\ LiveShape x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ LiveShape y u))
in
let b = LENGTH pre in
let h = height v in
let f = splice_pc b 2 1 in
let T = \x k. OPTION_MAP (\(l,org). (l,f org)) (tag x k) in
asm_static_wf p /\ Open p cc req V {} rank pc height need tag boolean edge /\
v IN V /\ pc v=b /\ asm_commutative_op a /\
p=pre++[AsmOp "SWAP1";a]++tail /\ q=pre++[a]++tail ==>
?name (path:num->num#num).
  let z = path 2 in
  let P = \x. b+FST x in
  let H = \x. if FST x=0 then h else height z in
  let R = \x. if FST x=0 then rank v else rank z in
  let Tag = \x k. if FST x=0 then (if k<2 then NONE else T v k) else T z k in
  let Bool = \x k. if FST x=0 then (2<=k /\ boolean v k) else boolean z k in
  a=AsmOp name /\ path 0=v /\ path 1 IN V /\ z IN V /\
  edge v (path 1) /\ edge (path 1) z /\ pc (path 1)=b+1 /\ pc z=b+2 /\
  R (1,0)<R (0,0) /\ height z=h-1 /\ 2<=h /\
  P (0,0)<LENGTH q /\ EL (P (0,0)) q=AsmOp name /\ P (1,0)=P (0,0)+1 /\
  ALOOKUP dup_table name=NONE /\ ALOOKUP swap_table name=NONE /\
  static_abort_straight name 1 /\ asm_op_arity name=2 /\
  Flow q P H Tag Bool (0,0) (1,0)
Proof
  rpt gen_tac >> SIMP_TAC bool_ss [LET_THM] >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [AND_IMP_INTRO]
    (underAIs CONJUNCT2 (SIMP_RULE bool_ss [LET_THM]
      (Q.INST [`w` |-> `[AsmOp "SWAP1";a]`]
        (SPEC_ALL stack_guarded_source_demand_paths))))) >>
  SIMP_TAC bool_ss [LENGTH, DECIDE ``SUC (SUC 0) = 2``] >>
  disch_then (qx_choose_then `name` (qx_choose_then `path` strip_assume_tac)) >>
  `path 1 IN V /\ path 2 IN V /\ pc (path 1)=LENGTH pre+1 /\ pc (path 2)=LENGTH pre+2` by
    (qpat_assum `!i. i<=2 ==> _` (fn th => mp_tac (Q.SPEC `1` th) >> mp_tac (Q.SPEC `2` th)) >> simp[]) >>
  (* Simplifying implications with all assumptions can erase these instances
     before the two concrete successors and path 0 have been normalized. *)
  qpat_assum `path 0=v` (fn root =>
    qpat_x_assum `!i. i<2 ==> _` (fn th =>
      map_every (fn i => strip_assume_tac (SRULE[root,ADD1] (Q.SPEC i th))) [`0`,`1`])) >>
  `rank (path 2)<rank v` by
    (irule LESS_TRANS >> qexists `rank (path 1)` >> simp[]) >>
  `ALOOKUP dup_table name=NONE /\ ALOOKUP swap_table name=NONE /\
   static_abort_straight name 1 /\ asm_op_arity name=2 /\
   name<>"JUMP" /\ name<>"JUMPI"` by
    (qpat_assum `MEM name _` mp_tac >> simp[NoAsms] >> strip_tac >> pop_assum SUBST1_TAC >> EVAL_TAC) >>
  `LENGTH pre < LENGTH q /\ EL (LENGTH pre) q=AsmOp name` by simp[EL_APPEND_EQN] >>
  `height (path 2) = height v - 1 /\ height (path 2) + 2 - height v = 1 /\
   height (path 2) = 1+(height v-2)` by decide_tac >>
  qexistsl [`name`,`path`] >> simp[EL_APPEND_EQN] >>
  suspend "slots"
QED

Resume stack_comm_replacement_row[slots]:
  conj_tac >- suspend "tags" >> suspend "booleans"
QED

Resume stack_comm_replacement_row[tags]:
  simp[optionTheory.OPTION_MAP_EQ_SOME] >>
  rpt gen_tac >> disch_then (qx_choose_then `demand` strip_assume_tac) >>
  Cases_on `k=0` >- fs[] >>
  `0<k /\ 1<=k /\ k-1+2=k+1 /\ 2<=k+1` by decide_tac >>
  PairCases_on `demand` >>
  qpat_assum `!k. 0<k ==> _` (qspec_then `k` (drule_then
    (fn th => qspecl_then [`demand0`,`demand1`] (drule_then strip_assume_tac) (CONJUNCT1 th)))) >>
  simp[] >> qexists `(demand0,demand1)` >> simp[]
QED

Resume stack_comm_replacement_row[booleans]:
  qx_gen_tac `k` >> disch_tac >> Cases_on `k=0`
  >- suspend "result_boolean" >>
  `0<k /\ 1<=k /\ k-1+2=k+1 /\ 2<=k+1` by decide_tac >>
  qpat_assum `!k. 0<k ==> _` (qspec_then `k` (drule_then
    (drule_then strip_assume_tac o CONJUNCT2))) >>
  simp[]
QED

Resume stack_comm_replacement_row[result_boolean]:
  qpat_x_assum `k=0` SUBST_ALL_TAC >>
  `name="EQ"` by (qpat_assum `boolean (path 2) 0 ==> _` (drule_then ACCEPT_TAC)) >>
  `0<height v-1` by decide_tac >>
  simp[asm_returns_zero_or_one_def] >>
  rpt gen_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``asm_binop``]) >>
  namedCases_on `t.as_stack` ["", "x xs"]
  >- simp[asm_binop_def] >>
  namedCases_on `xs` ["", "y rest"]
  >- simp[asm_binop_def] >>
  Cases_on `x=y` >>
  simp[asm_binop_def,asm_next_def,vfmExecutionTheory.b2w_def] >>
  strip_tac >> gvs[]
QED

Finalise stack_comm_replacement_row
