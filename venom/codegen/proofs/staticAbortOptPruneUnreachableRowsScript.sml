(* Geometry is available before transporting Flow; packing consumes it only
   after deleted-origin traceback and destination Flow have been supplied. *)
Theory staticAbortOptPruneUnreachableRows
Ancestors
  staticAbortOptPruneUnreachableArms staticAbortOptPruneUnreachablePrefix
  staticAbortOptPruneUnreachableLegal staticAbortOptPruneUnreachableCheck
  staticAbortOptPruneUnreachableStrictSlots staticAbortOptPruneUnreachableStrictShape
  staticAbortStraight asmOptimizer asmSplice asmSymBridge asmSymSem asmSem asmIR asmSymPc
  finite_map words list rich_list arithmetic pred_set pair alist

val rows_unwind = SIMP_RULE (pure_ss ++ boolSimps.UNWIND_ss) [];

Theorem prune_one_covered_rows:
  !Shape Flow Hit Target Legal Check Rows.
  Shape =
    (\p cc req pc height need tag boolean i (t:asm_state).
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
  Flow = (\p pc height tag boolean (a:num#num) (b:num#num).
    !hi hj ins inherit.
    hi = height a ==> hj = height b ==> ins = EL (pc a) p ==>
    inherit = (\(src:num->num option) (fresh:num->(string#num)option) (bnew:num->bool).
      (!k l origin. tag b k = SOME(l,origin) ==>
        k < hj /\ (fresh k = SOME(l,origin) \/
          ?j. src k = SOME j /\ j < hi /\ tag a j = SOME(l,origin))) /\
      (!k. boolean b k ==> k < hj /\
        (bnew k \/ ?j. src k = SOME j /\ j < hi /\ boolean a j))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w)
    | AsmPushLabel l => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc a) else NONE) (\k. F)
    | AsmPushOfst l d => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc a) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
               !a0 m. a0 = asm_op_arity name ==> m = hj + asm_op_arity name - hi ==>
               a0 <= hi /\ hj = m+(hi-a0) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a0)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins t = AsmOK u ==>
                     EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))
    | _ => F) ==>
  Hit = (\p l j. ?off. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME j) ==>
  Target = (\p pc tag (a:num#num) (b:num#num).
    ?l i. tag a 0 = SOME(l,i) /\ Hit p l (pc b)) ==>
  Legal = (\p pc tag a b.
    if EL (pc a) p = AsmOp "JUMP" then Target p pc tag a b
    else if EL (pc a) p = AsmOp "JUMPI" then pc b=pc a+1 \/ Target p pc tag a b
    else pc b=pc a+1) ==>
  Check = (\p cc pc height tag edge x.
    !h fall arm legal next untagged stop.
    h = height x ==> fall = (\y. pc y = pc x+1) ==>
    arm = (\P n. ?y. edge x y /\ P y /\ height y=n) ==>
    legal = (\P n. !y. edge x y ==> P y /\ height y=n) ==>
    next = (\n. arm fall n /\ legal fall n) ==>
    untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
    stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
    case EL (pc x) p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
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
                1<=h /\ arm (Target p pc tag x) (h-1) /\ legal (Target p pc tag x) (h-1)
              else if name="JUMPI" then
                2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (Target p pc tag x) (h-2) /\
                legal (\y. fall y \/ Target p pc tag x y) (h-2)
              else ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F) ==>
  Rows = (\p cc V X rank pc height need tag boolean edge.
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l i. tag x k=SOME(l,i) ==>
        k < height x /\ i < LENGTH p /\
        (EL i p=AsmPushLabel l \/ EL i p=AsmPushOfst l 0) /\
        ?dest. Hit p l dest)) /\
    (!x y. edge x y ==>
      x IN V DIFF X /\ y IN V /\ rank y < rank x /\ Flow p pc height tag boolean x y) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p /\ Check p cc pc height tag edge x)) ==>
  !pre t x tail s env n ss cc req V e rank pc height need tag boolean edge.
  !p q d r tagQ fall taken.
    p = pre ++ [t;x] ++ tail ==> q = pre ++ [t] ++ tail ==>
    d = LENGTH pre+1 ==> r = (\i. if i<d then i else i-1) ==>
    tagQ = (\v k. OPTION_MAP (\(l,i). (l,if i=d then
      (@j. j<LENGTH q /\ (EL j q=AsmPushLabel l \/ EL j q=AsmPushOfst l 0))
      else r i)) (tag v k)) ==>
    fall = (\a b. edge a b /\ ~asm_terminal_op (EL (pc a) p) /\ pc b=pc a+1) ==>
    taken = (\a l b. edge a b /\
      (EL (pc a) p=AsmOp "JUMP" \/ EL (pc a) p=AsmOp "JUMPI") /\
      (?i. tag a 0=SOME(l,i)) /\ Hit p l (pc b)) ==>
    asm_terminal_op t /\ ~asm_reachable_marker x /\ asm_static_wf p /\ asm_static_wf q /\
    s.as_pc=0 /\ sym_steps p env n (sym_init s)=SymOK ss /\ pc e=ss.sym_base.as_pc /\
    (!k l i. tag e k=SOME(l,i) ==> k<LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
    (!k. boolean e k ==> k<LENGTH ss.sym_stack /\
      (EL k ss.sym_stack=Val 0w \/ EL k ss.sym_stack=Val 1w)) /\
    e IN V /\ (!v. v IN V ==> ?n (path:num->num#num).
       path 0=e /\ path n=v /\ !k. k<n ==> edge (path k) (path (SUC k))) /\
    (!v. v IN V ==> ?u. Shape p cc req pc height need tag boolean v u) /\
    (!a b. edge a b ==> Legal p pc tag a b) /\
    Rows p cc V {} rank pc height need tag boolean edge ==>
    ((!v. v IN V ==> pc v<>d /\ r (pc v)<LENGTH q /\ EL (r (pc v)) q=EL (pc v) p) /\
     (!a b. edge a b <=> fall a b \/ ?l. taken a l b) /\
     (!a b. fall a b ==> r (pc b)=r (pc a)+1) /\
     (!a l b. taken a l b ==> Hit q l (r (pc b)))) /\
    (((!v k l. v IN V /\ tag v k=SOME(l,d) ==> ?j. tag e j=SOME(l,d)) /\
      (!a b. edge a b ==> Flow q (r o pc) height tagQ boolean a b)) ==>
     Rows q cc V {} rank (r o pc) height need tagQ boolean edge /\
     (!a b. edge a b ==> Legal q (r o pc) tagQ a b) /\
     (!v. v IN V ==> ?u. Shape q cc req (r o pc) height need tagQ boolean v u))
Proof
  ntac 7 gen_tac >>
  ntac 7 (disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def] o rows_unwind)) >>
  rpt gen_tac >>
  ntac 7 (disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])) >>
  strip_tac >>
  qabbrev_tac `Z = \l j. j<LENGTH q /\ (EL j q=AsmPushLabel l \/ EL j q=AsmPushOfst l 0)` >>
  qpat_assum `Abbrev (Rows = _)` (fn eq =>
    qpat_x_assum `Rows p _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [REWRITE_RULE [markerTheory.Abbrev_def] eq])) >>
  `pc e <> d /\ sym_steps q env n (sym_init s) = SymOK (sym_with_pc (r (pc e)) ss)` by
    (mp_tac prune_one_stopped_prefix >>
     simp[Abbr `p`, Abbr `q`, Abbr `d`, Abbr `r`]) >>
  `!a b. edge a b /\ EL (pc a) p <> AsmOp "JUMP" ==>
           ~asm_terminal_op (EL (pc a) p)` by
    (rpt gen_tac >> strip_tac >>
     `a IN V` by (qpat_assum `!a b. edge a b ==> _` (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `!a. a IN V ==> pc a < LENGTH p /\ _` (drule_then strip_assume_tac) >>
     spose_not_then mp_tac >> simp[asm_terminal_op_def] >> strip_tac >>
     qpat_assum `Abbrev (Check = _)` (fn def =>
       qpat_x_assum `Check p cc pc height tag edge a`
         (mp_tac o BETA_RULE o REWRITE_RULE [markerTheory.Abbrev_def |> (fn th => REWRITE_RULE [th] def)])) >>
     simp_tac (srw_ss()) [LET_THM, dup_table_def, swap_table_def, static_abort_straight_def,
       SimpLHS] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!y. ~edge a y` (qspec_then `b` mp_tac) >> simp[]) >>
  `!a b. edge a b <=> fall a b \/ ?l. taken a l b` by
    (rpt gen_tac >> eq_tac >- (
       strip_tac >>
       `Legal p pc tag a b` by
         (qpat_assum `!a b. edge a b ==> Legal p pc tag a b`
           (qspecl_then [`a`,`b`] irule) >> asm_rewrite_tac[]) >>
       Cases_on `EL (pc a) p = AsmOp "JUMP"` >- (
         qpat_x_assum `Legal p pc tag a b` mp_tac >>
         simp[Abbr `Legal`, Abbr `Target`, Abbr `taken`, Abbr `fall`,
              asm_terminal_op_def, PULL_EXISTS, NoAsms] >>
         asm_rewrite_tac[]) >>
       `~asm_terminal_op (EL (pc a) p)` by
         (qpat_assum `!a b. _ /\ _ ==> ~asm_terminal_op _`
           (qspecl_then [`a`,`b`] mp_tac) >> simp[]) >>
       qpat_x_assum `Legal p pc tag a b` mp_tac >>
       simp[Abbr `Legal`, Abbr `Target`, NoAsms, SimpLHS] >>
       Cases_on `EL (pc a) p = AsmOp "JUMPI"` >>
       simp[Abbr `taken`, Abbr `fall`, PULL_EXISTS]) >>
     simp[Abbr `fall`, Abbr `taken`] >> rpt strip_tac) >>
  `(!v. v IN V ==> pc v<>d /\ r (pc v)<LENGTH q /\ EL (r (pc v)) q=EL (pc v) p) /\
   (!a b. fall a b ==> r (pc b)=r (pc a)+1) /\
   (!a l b. taken a l b ==> Hit q l (r (pc b)))` by suspend "geometry" >>
  conj_tac >- asm_rewrite_tac[] >>
  strip_tac >> suspend "pack"
QED

Resume prune_one_covered_rows[geometry]:
  `(!v. v IN V ==> pc v < LENGTH p /\
      ?n (path:num->num#num). path 0=e /\ path n=v /\
        !k. k<n ==> fall (path k) (path (SUC k)) \/ ?l. taken (path k) l (path (SUC k))) /\
   (!a b. fall a b ==> a IN V /\ b IN V /\
      ~asm_terminal_op (EL (pc a) p) /\ pc b = pc a+1) /\
   (!a l b. taken a l b ==> a IN V /\ b IN V /\ Hit p l (pc b))` by
    (conj_tac >- (
       rpt strip_tac >- (qpat_assum `!a. a IN V ==> pc a < LENGTH p /\ _`
                          (drule_then strip_assume_tac) >> simp[]) >>
       qpat_assum `!a. a IN V ==> ?n path. _` drule >>
       disch_then (qx_choose_then `m` (qx_choose_then `path` strip_assume_tac)) >>
       qexistsl [`m`,`path`] >> simp[] >>
       qpat_assum `!a b. edge a b <=> _` (fn th => simp[GSYM th])) >>
     conj_tac >> rpt gen_tac >>
     simp[Abbr `fall`, Abbr `taken`] >> strip_tac >>
     qpat_assum `!a b. edge a b ==> a IN V /\ _` (drule_then strip_assume_tac) >>
     simp[]) >>
  qspecl_then [`pre`,`t`,`x`,`tail`,`V`,`e`,`pc`,`fall`,`taken`] mp_tac
    (rows_unwind prune_one_arm_geometry) >>
  simp[Abbr `p`, Abbr `q`, Abbr `d`, Abbr `r`, Abbr `Hit`] >>
  (impl_tac >- (gvs[] >> conj_tac >> rpt strip_tac >>
    (qpat_assum `!a b. fall a b ==> _` (drule_then strip_assume_tac) ORELSE
     qpat_assum `!a l b. taken a l b ==> _` (drule_then strip_assume_tac)) >>
    simp[] >> goal_assum drule)) >> simp[]
QED


(* Compare the worker contracts and the local rows modulo their lexical lets. *)
val rows_normalize = REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV);
fun rows_contract th g =
  (mp_tac th >> unabbrev_all_tac >> rule_assum_tac (CONV_RULE rows_normalize) >>
   CONV_TAC rows_normalize >>
   (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
   disch_then ACCEPT_TAC) g;

Resume prune_one_covered_rows[pack]:
  `!a b. edge a b ==> a IN V /\ b IN V` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a b. edge a b ==> a IN V /\ _ /\ _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `(!a b. edge a b /\ EL (pc a) p <> AsmOp "JUMP" /\ pc b = pc a+1 ==>
      r (pc b) = r (pc a)+1) /\
   (!a b. edge a b /\
      (EL (pc a) p = AsmOp "JUMP" \/ EL (pc a) p = AsmOp "JUMPI") /\
      Target p pc tag a b ==> Target q (r o pc) tagQ a b) /\
   (!a b. edge a b ==> Legal q (r o pc) tagQ a b)` by
    (qspecl_then [`pre`,`t`,`x`,`tail`,`V`,`pc`,`tag`,`edge`] rows_contract
       (rows_unwind prune_one_relocated_legal)) >>
  `!v. v IN V ==> (r o pc) v < LENGTH q /\ Check q cc (r o pc) height tagQ edge v` by
    (qpat_x_assum `Abbrev (Check = _)`
       (assume_tac o CONV_RULE (RAND_CONV (RAND_CONV
         (QCHANGED_CONV (ONCE_DEPTH_CONV
           (HO_REWR_CONV (GSYM check_case_presentation))))))) >>
     qspecl_then [`pre`,`t`,`x`,`tail`,`V`,`cc`,`pc`,`height`,`tag`,`edge`]
       mp_tac (rows_unwind prune_one_relocated_check) >>
     unabbrev_all_tac >> rule_assum_tac (CONV_RULE rows_normalize) >>
     CONV_TAC rows_normalize >>
     (impl_tac >- (rpt conj_tac >>
       (first_assum ACCEPT_TAC ORELSE FAIL_TAC "unmatched aligned Check premise"))) >>
     disch_then ACCEPT_TAC) >>
  `!v. v IN V ==>
    (need v ==> cc.cc_static) /\
    (!k. boolean v k ==> k<height v /\ tagQ v k=NONE) /\
    (!k l j. tagQ v k=SOME(l,j) ==> k<height v /\ Z l j /\ ?dest. Hit q l dest)` by
    (qspecl_then [`pre`,`t`,`x`,`tail`,`V`,`e`,`height`,`need`,`tag`,
                  `boolean`,`cc`,`env`,`n`,`s`,`ss`]
       (fn th => qpat_assum `pc e = ss.sym_base.as_pc` (rows_contract o
         (fn eq => REWRITE_RULE [GSYM eq] th))) (rows_unwind prune_one_strict_slots)) >>
  `!v k l j. v IN V /\ tagQ v k=SOME(l,j) ==>
      k < height v /\ Z l j /\ ?dest. Hit q l dest` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!v. v IN V ==> _ /\ _ /\ !k l j. tagQ v k = _ ==> _`
       (drule_then (drule_then ACCEPT_TAC o cj 3))) >>
  reverse conj_tac >- (
    conj_tac >- asm_rewrite_tac[] >>
    `!a b. edge a b ==> Flow p pc height tag boolean a b` by
      (rpt gen_tac >> disch_tac >>
       qpat_assum `!a b. edge a b ==> a IN V /\ _ /\ _ /\ _`
         (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
    (* The unnormalized Shape application does not match modulo LET/beta. *)
    qspecl_then [`pre`,`t`,`x`,`tail`,`s`,`env`,`n`,`ss`,`cc`,`req`,
                 `V`,`edge`,`e`,`pc`,`height`,`need`,`tag`,`boolean`]
      mp_tac (CONV_RULE rows_normalize (rows_unwind prune_one_strict_shapes)) >>
    unabbrev_all_tac >> rule_assum_tac (CONV_RULE rows_normalize) >>
    CONV_TAC rows_normalize >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >>
  qpat_assum `Abbrev (Rows = _)` (fn def =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] def]) >>
  BETA_TAC >> pure_rewrite_tac [DIFF_EMPTY] >>
  conj_tac >- (
    qpat_assum `!v. v IN V ==> _ /\ _ /\ (!k l j. tagQ v k = _ ==> _ /\ Z l j /\ _)`
      mp_tac >>
    qpat_assum `Abbrev (Z = _)` (fn def =>
      pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] def]) >>
    BETA_TAC >> rewrite_tac [GSYM CONJ_ASSOC]) >>
  conj_tac >- (
    rpt gen_tac >> disch_tac >>
    qpat_assum `!a b. edge a b ==> a IN V /\ _ /\ _ /\ _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!a b. edge a b ==> Flow q _ _ _ _ a b` (drule_then assume_tac) >>
    asm_rewrite_tac[]) >>
  first_assum ACCEPT_TAC
QED

Finalise prune_one_covered_rows
