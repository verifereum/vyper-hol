(* Interpret a destination row table without any source-program or splice facts. *)
Theory staticAbortOptMergeIszeroBranchPackage
Ancestors
  staticAbortRoleStep asmIR asmSem asmSymSem asmOptimizer staticAbortStraight
  finite_map words list pred_set arithmetic alist

Theorem pending_rows_rooted_package:
  !q u (t:asm_state) (V:(num#num)->bool) e rank pc height need tag boolean edge.
  !cc. cc = t.as_call_ctx ==>
  !req. req = t.as_requests ==>
  !lo. lo = SND (compute_label_offsets q) ==>
  !otp. otp = build_offset_to_pc q ==>
  !Shape. Shape = (\(x:num#num) (s:asm_state).
    s.as_pc = pc x /\ LENGTH s.as_stack = height x /\
    s.as_call_ctx = cc /\ s.as_requests = req /\
    (need x ==> s.as_call_ctx.cc_static) /\
    (!k l origin. tag x k = SOME(l,origin) ==>
       k < height x /\ origin < LENGTH q /\
       (EL origin q = AsmPushLabel l \/
        (?d. EL origin q = AsmPushOfst l d) \/ EL origin q = AsmDataLabel l) /\
       ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
         FLOOKUP otp off = SOME dest /\ EL k s.as_stack = (n2w off:bytes32)) /\
    (!k. boolean x k ==> k < height x /\
       (EL k s.as_stack = 0w \/ EL k s.as_stack = 1w))) ==>
  !target. target = (\(x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\ FLOOKUP lo l = SOME off /\
      off < dimword(:256) /\ FLOOKUP otp off = SOME(pc y)) ==>
  !Flow. Flow = (\(x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) q ==>
    !inherit. inherit =
      (\(src:num -> num option)
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
          (\k. k=0 /\ !s v. asm_step lo otp (AsmPush bs) s = AsmOK v ==>
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
                   !s v. LENGTH s.as_stack=hi /\ asm_step lo otp ins s=AsmOK v ==>
                     (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w)))
    | _ => F) ==>
  !Rows. Rows = (\A R.
    (!x. x IN A ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH q /\
         (EL origin q = AsmPushLabel l \/ EL origin q = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                    FLOOKUP otp off = SOME dest)) /\
    (!x y. R x y ==> x IN A /\ y IN A /\ rank y < rank x /\ Flow x y) /\
    (!x. x IN A ==>
      pc x < LENGTH q /\
      !h. h = height x ==>
      !fall. fall = (\y. pc y = pc x+1) ==>
      !arm. arm = (\P n. ?y. R x y /\ P y /\ height y = n) ==>
      !legal. legal = (\P n. !y. R x y ==> P y /\ height y = n) ==>
      !next. next = (\n. arm fall n /\ legal fall n) ==>
      !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
      !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~R x y) ==>
      case EL (pc x) q of
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
      | _ => F)) ==>
  !EdgeOK. EdgeOK = (\x y.
    Flow x y /\
    (if EL (pc x) q = AsmOp "JUMP" then target x y
     else if EL (pc x) q = AsmOp "JUMPI" then pc y = pc x+1 \/ target x y
     else pc y = pc x+1)) ==>
  !Reach. Reach = (\(R:(num#num)->(num#num)->bool) a x.
    ?n (path:num->num#num).
      path 0=a /\ path n=x /\ !k. k<n ==> R (path k) (path(SUC k))) ==>
  !Root. Root = (\a s. Shape a s /\
    (!k l origin. tag a k=SOME(l,origin) ==>
       k<LENGTH u.sym_stack /\ EL k u.sym_stack=Lab l 0) /\
    (!k. boolean a k ==>
       k<LENGTH u.sym_stack /\ (EL k u.sym_stack=Val 0w \/ EL k u.sym_stack=Val 1w))) ==>
  FINITE V /\ e IN V /\ Rows V edge /\ (!x y. edge x y ==> EdgeOK x y) /\ Root e t ==>
  !live_set. live_set = {x | x IN V /\ Reach edge e x} ==>
  !live_edge. live_edge = (\x y. x IN live_set /\ edge x y) ==>
  e IN live_set /\ (!x. x IN live_set ==> Reach live_edge e x) /\
  Rows live_set live_edge /\
  (FINITE live_set /\ {} SUBSET live_set /\
   (!x. x IN live_set ==> ?s. Shape x s) /\
   (!x. x IN live_set DIFF {} ==> pc x < LENGTH q) /\
   (!x y. live_edge x y ==>
      x IN live_set DIFF {} /\ y IN live_set /\ rank y < rank x /\ EdgeOK x y) /\
   (!x s. x IN live_set DIFF {} /\ Shape x s ==>
      (?v. (asm_steps lo otp q 1 s = AsmRevert v \/
            asm_steps lo otp q 1 s = AsmFault v) /\ v.as_requests=req) \/
      (?y v. live_edge x y /\ asm_steps lo otp q 1 s = AsmOK v /\ Shape y v))) /\
  Root e t
Proof
  ntac 12 gen_tac >>
  ntac 2 (CONV_TAC (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  let
    fun intro_alias conv name =
      qx_gen_tac name >> disch_then (assume_tac o CONV_RULE
        (RAND_CONV conv THENC REWR_CONV (GSYM markerTheory.Abbrev_def)))
  in
    map_every (intro_alias ALL_CONV) [`lo`,`otp`,`Shape`,`target`,`Flow`] >>
    intro_alias (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV)) `Rows` >>
    map_every (intro_alias ALL_CONV) [`EdgeOK`,`Reach`,`Root`] >>
    strip_tac >> map_every (intro_alias ALL_CONV) [`live_set`,`live_edge`]
  end >>
  `!a. a IN live_set <=> a IN V /\ Reach edge e a` by
    simp[Abbr `live_set`, numberTheory.equiv_class_element] >>
  qpat_assum `Abbrev (Rows = _)` (fn rows_eq =>
    qpat_x_assum `Rows V edge`
      (CONJUNCTS_THEN2 (mk_asm "slots")
        (CONJUNCTS_THEN2 (mk_asm "edges") (mk_asm "dispatch")) o BETA_RULE o
        PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] rows_eq])) >>
  asm "edges" assume_tac >>
  `e IN live_set` by (simp[Abbr `Reach`] >> qexistsl [`0`,`\k. e`] >> simp[]) >>
  `!a b. a IN live_set /\ edge a b ==> b IN live_set` by
    (map_every qx_gen_tac [`a`,`b`] >> strip_tac >>
     `b IN V /\ Reach edge e a` by metis_tac[] >>
     qpat_x_assum `Reach edge e a` mp_tac >>
     simp[Abbr `Reach`] >> disch_then (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) >>
     qexistsl [`SUC n`,`\k. if k = SUC n then b else path k`] >>
     simp[] >> qx_gen_tac `k` >> disch_tac >> Cases_on `k=n`
     >- (`n <> SUC n` by decide_tac >> simp[]) >>
     `k < n /\ k <> SUC n` by decide_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "paths" >>
  conj_tac >- suspend "rows" >>
  suspend "interpret"
QED

Resume pending_rows_rooted_package[paths]:
  qx_gen_tac `a` >> disch_tac >>
  `Reach edge e a` by metis_tac[] >>
  qpat_x_assum `Reach edge e a` mp_tac >>
  simp[Abbr `Reach`, Abbr `live_edge`] >>
  disch_then (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) >>
  qexistsl [`n`,`path`] >> simp[] >> qx_gen_tac `k` >> disch_tac >>
  `edge (path k) (path (SUC k))` by metis_tac[] >>
  `path k IN V` by metis_tac[] >>
  simp[] >> qexistsl [`k`,`path`] >> simp[] >>
  qx_gen_tac `j` >> disch_tac >> `j < n` by decide_tac >> metis_tac[]
QED

Resume pending_rows_rooted_package[rows]:
  simp[Abbr `Rows`, LET_THM] >>
  conj_tac >- (qx_gen_tac `x` >> disch_tac >> `x IN V` by metis_tac[] >>
              asm "slots" (qspec_then `x` (drule_then ACCEPT_TAC))) >>
  conj_tac >- (simp[Abbr `live_edge`] >> metis_tac[]) >>
  qx_gen_tac `x` >> disch_tac >> `x IN V` by metis_tac[] >>
  asm "dispatch" (qspec_then `x` (drule_then mp_tac)) >> simp[Abbr `live_edge`, LET_THM]
QED

Resume pending_rows_rooted_package[interpret]:
  simp[DIFF_EMPTY, EMPTY_SUBSET] >>
  conj_tac >- (irule SUBSET_FINITE_I >> qexists `V` >> simp[SUBSET_DEF]) >>
  conj_tac >- suspend "inhabit" >>
  conj_tac >- (qx_gen_tac `x` >> disch_tac >> `x IN V` by metis_tac[] >>
    asm "dispatch" (qspec_then `x` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  conj_tac >- (simp[Abbr `live_edge`] >> metis_tac[]) >>
  suspend "step"
QED

Resume pending_rows_rooted_package[inhabit]:
  qx_gen_tac `x` >> disch_tac >> Cases_on `x=e`
  >- ((qexists `t` >> qpat_assum `Root e t` mp_tac >> simp[Abbr `Root`] >> (gvs[]))) >>
  `x IN V` by metis_tac[] >>
  asm "slots" (qspec_then `x` (drule_then strip_assume_tac)) >>
  qexists `t with <|as_pc := pc x;
    as_stack := GENLIST (\k. case tag x k of NONE => 0w
                  | SOME lr => n2w (THE (FLOOKUP lo (FST lr)))) (height x)|>` >>
  qunabbrev_tac `Shape` >> BETA_TAC >> simp[] >>
  map_every qx_gen_tac [`k`,`l`,`origin`] >> disch_tac >>
  qpat_assum `!k l origin. tag x k = SOME(l,origin) ==> _`
    (qspecl_then [`k`,`l`,`origin`] (drule_then strip_assume_tac)) >>
  simp[] >> metis_tac[]
QED

Resume pending_rows_rooted_package[step]:
  map_every qx_gen_tac [`x`,`s`] >> strip_tac >>
  `x IN V` by metis_tac[] >>
  `x IN live_set` by metis_tac[] >>
  `!y. live_edge x y = edge x y` by simp[Abbr `live_edge`] >>
  pop_assum (rewrite_tac o single) >>
  map_every qunabbrev_tac [`Shape`,`lo`,`otp`] >>
  BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
  match_mp_tac (GEN_ALL
    (CONV_RULE (REDEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV))
      pending_role_step)) >>
  asm "dispatch" (qspec_then `x` (drule_then
    (CONJUNCTS_THEN2 assume_tac (mk_asm "row")))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "successor_slots" >>
  suspend "positive_dispatch"
QED

Resume pending_rows_rooted_package[successor_slots]:
  qx_gen_tac `y` >> disch_tac >>
  asm "edges" (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >>
  conj_tac
  >- (qpat_assum `Abbrev (Flow = _)` (fn flow_eq =>
        qpat_assum `Flow x y` (ACCEPT_TAC o
          CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV)) o
          PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] flow_eq]))) >>
  asm "slots" (qspec_then `y` (drule_then strip_assume_tac)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  map_every qx_gen_tac [`k`,`l`,`origin`] >> disch_tac >>
  qpat_assum `!k l origin. tag y k = SOME(l,origin) ==> _`
    (qspecl_then [`k`,`l`,`origin`] (drule_then strip_assume_tac)) >>
  simp[] >> metis_tac[]
QED

Resume pending_rows_rooted_package[positive_dispatch]:
  asm_x "row" mp_tac >> qunabbrev_tac `target` >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  CONV_TAC (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM, BETA_CONV])) >>
  Cases_on `EL (pc x) q` >> simp[asmIRTheory.asm_inst_case_def, Excl "MEM"] >>
  FIRST [rename1 `EL (pc x) q = AsmOp name` >> suspend "opcode_dispatch",
         metis_tac[]]
QED

Resume pending_rows_rooted_package[opcode_dispatch]:
  Cases_on `name = "INVALID"` >> simp[Excl "MEM"] >>
  Cases_on `name = "REVERT"` >> simp[Excl "MEM"] >>
  COND_CASES_TAC >- (asm_rewrite_tac[] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  Cases_on `ALOOKUP dup_table name` >> simp[Excl "MEM"]
  >- (Cases_on `ALOOKUP swap_table name` >> simp[Excl "MEM"]
      >- (Cases_on `name = "JUMP"` >> simp[Excl "MEM"]
          >- metis_tac[] >>
          Cases_on `name = "JUMPI"` >> simp[Excl "MEM"] >> metis_tac[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Finalise pending_rows_rooted_package
