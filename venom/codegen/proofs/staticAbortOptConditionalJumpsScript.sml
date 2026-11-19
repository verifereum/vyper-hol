Theory staticAbortOptConditionalJumps
Ancestors
  staticAbortOptConditionalJumpsWalk staticAbortOptConditionalJumpsLayout
  staticAbortOptConditionalJumpsEndpoint staticAbortOptConditionalJumpsIngress
  staticAbortOptConditionalJumpsTable staticAbortOptConditionalJumpsRetained
  staticAbortOptConditionalJumpsArms staticAbortRoleStep
  staticAbortOptConditionalJumpsWholePortReceipt staticAbortOptConditionalJumpsStrictPortReceipt
  staticAbortOptConditionalJumpsPhaseReceipt staticAbortOptConditionalJumpsKeptReceipt
  staticAbortOptMergeIszeroBranchPackage staticAbortOptMergeJumpdests
  asmOptInefficientJumps asmSplice asmSymBridge asmSymSem asmSem asmWf
  asmDataEnv asmOptimizer asmIR symbolResolve staticAbortStraight
  finite_map pred_set words list alist arithmetic

val lets_conv = REDEPTH_CONV
  (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV, REWR_CONV LET_THM]);
val protected_terminal = staticAbortOptMergeJumpdestsTheory.merge_protected_terminal;

fun source_dispatch v pc_at fetch rules =
  qpat_assum `!a. a IN V ==> pc a < LENGTH p /\ _`
    (qspec_then v mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum pc_at (fn i => qpat_assum fetch (fn ins =>
    disch_then (map_every assume_tac o CONJUNCTS o
      SIMP_RULE (srw_ss()) (i :: ins :: rules) o CONJUNCT2)));

fun fold_abbrevs pats = map_every (fn pat =>
  qpat_assum pat (pure_rewrite_tac o single o GSYM o
                 REWRITE_RULE [markerTheory.Abbrev_def])) pats;

Theorem optimize_inefficient_jumps_abort_certificate:
  !orig s data req_bound.
  !Shape. Shape = (\p cc req pc height need tag boolean i (t:asm_state).
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
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !target. target = (\p pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !Flow. Flow = (\p pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==> !hj. hj = height y ==> !ins. ins = EL (pc x) p ==>
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
           | NONE => !a. a = asm_op_arity name ==> !m. m = hj + a - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins t=AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !Rows. Rows = (\p cc V rank pc height need tag boolean edge.
    !lo. lo = SND (compute_label_offsets p) ==>
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                    FLOOKUP (build_offset_to_pc p) off = SOME dest)) /\
    (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Flow p pc height tag boolean x y) /\
    (!x. x IN V ==>
      pc x < LENGTH p /\
      (!h. h = height x ==>
       !fall. fall = (\y. pc y = pc x+1) ==>
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
           else
             (case ALOOKUP dup_table name of
                SOME n => n<h /\ next (h+1)
              | NONE => case ALOOKUP swap_table name of
                  SOME n => 0<n /\ n<h /\ next h
                | NONE =>
                    if name="JUMP" then
                       1<=h /\ arm (target p pc tag x) (h-1) /\ legal (target p pc tag x) (h-1)
                    else if name="JUMPI" then
                       2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target p pc tag x) (h-2) /\
                       legal (\y. fall y \/ target p pc tag x y) (h-2)
                    else
                       ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                           untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
       | _ => F))) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) X rank pc height need
    (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target p pc tag x y
        else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ target p pc tag x y
        else pc y = pc x+1)) /\
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
  !bytes. bytes = (\p. assemble p ++ data) ==>
  !env0. env0 = asm_data_env orig (bytes orig) ==>
  !M_R. M_R = (\p.
    !start. start = (s with as_code := bytes p) ==>
    !run. run = asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p ==>
    s.as_pc = 0 /\ s.as_code = bytes orig /\
    asm_static_wf orig /\ asm_static_wf p /\
    FILTER is_data_inst p = FILTER is_data_inst orig /\
    ((?n out.
        (run n start = AsmRevert out \/ run n start = AsmFault out) /\
        sym_terminal (sym_steps p env0 n (sym_init s)) /\
        out.as_requests <<= req_bound) \/
     (?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
         pc height need tag boolean edge.
        run j start = AsmOK t /\
        sym_steps p env0 j (sym_init s) = SymOK u /\
        asm_sym_rel p (asm_data_env p (bytes p)) t u /\
        t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
        t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
        t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
        Rows p cc V rank pc height need tag boolean edge /\
        Open p cc req V {} rank pc height need tag boolean edge /\
        e IN V /\ (!x. x IN V ==> Reach edge e x) /\
        Shape p cc req pc height need tag boolean e t /\
        (!k l origin. tag e k = SOME(l,origin) ==>
           k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
        (!k. boolean e k ==>
           k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))))) ==>
  !p. M_R p ==> M_R (FST (optimize_inefficient_jumps p))
Proof
  ntac 4 gen_tac >> ntac 9 (gen_tac >> disch_tac) >>
  match_mp_tac (Q.INST [`P` |-> `M_R`] conditional_jumps_walk_preserves_contextual) >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 mp_tac assume_tac) >>
  Cases_on `a` >> Cases_on `e` >> simp[NoAsms, asm_jumpi_over_jump_def] >>
  Cases_on `c` >> simp[NoAsms, asm_is_push_label_def] >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  rename1 `M_R (pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail)` >>
  qabbrev_tac `p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x; AsmOp "JUMP"; AsmLabel c] ++ tail` >>
  qabbrev_tac `q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail` >>
  qpat_x_assum `M_R p` mp_tac >> qpat_x_assum `M_R = _` (pure_rewrite_tac o single) >>
  CONV_TAC lets_conv >> qpat_x_assum `bytes = _` SUBST_ALL_TAC >>
  rule_assum_tac BETA_RULE >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac mp_tac))))) >>
  mp_tac (Q.INST [`p` |-> `p`, `q` |-> `q`, `pre` |-> `pre`,
                  `c` |-> `c`, `x` |-> `x`, `tail` |-> `tail`]
                 (CONV_RULE lets_conv conditional_jump_one_layout)) >>
  (impl_tac >- simp[Abbr `p`, Abbr `q`]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!l d. _ ==> INDEX_OF (AsmLabel l) p = SOME d /\ _`
    (mk_asm "port_range" o cj 2) >>
  `FILTER is_data_inst q = FILTER is_data_inst orig` by metis_tac[] >>
  `asm_data_env p (assemble p ++ data) = env0 /\
   asm_data_env q (assemble q ++ data) = env0` by
    (qpat_assum `env0 = _` SUBST1_TAC >>
     conj_tac >> sym_tac >> irule asm_data_env_agree >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >> ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  pop_assum (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> suspend "terminal") >>
  disj2_tac >> suspend "pending"
QED

Resume optimize_inefficient_jumps_abort_certificate[terminal]:
  `asm_refines p q` by
    ((mp_tac (Q.INST [`pfx` |-> `pre`, `pat` |-> `[AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x; AsmOp "JUMP"]`,
                     `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"]`,
                     `sfx` |-> `AsmLabel c::tail`] asm_splice_window_refines) >>
     (impl_tac >- (simp[asm_splice_ok_def, jumpi_over_jump_window_refines,
           is_data_inst_def, asm_label_refs_def, asm_inst_size_def] >> rw[] >> EVAL_TAC)) >>
     simp[NoAsms, Abbr `p`, Abbr `q`] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> (metis_tac[asm_splice_ok_def, jumpi_over_jump_window_refines, is_data_inst_def, asm_label_refs_def, asm_inst_size_def, NoAsms, Abbr `p`, Abbr `q`, Q.INST [`pfx` |-> `pre`, `pat` |-> `[AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x; AsmOp "JUMP"]`,
                     `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"]`,
                     `sfx` |-> `AsmLabel c::tail`] asm_splice_window_refines]))) >>
  qpat_assum `env0 = _` SUBST_ALL_TAC >>
  drule_all (CONV_RULE lets_conv protected_terminal) >> strip_tac >>
  qexistsl [`m`,`t`] >> simp[]
QED

Resume optimize_inefficient_jumps_abort_certificate[pending]:
  qabbrev_tac `b = LENGTH (pre:asm_inst list)` >>
  qabbrev_tac `r = splice_pc b 4 3` >>
  qabbrev_tac `C = \p l d. ?off. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
                         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME d` >>
  qabbrev_tac `keep = {v | v IN V /\ (pc v < b \/ b+4 <= pc v)}` >>
  qabbrev_tac `D = {v | v IN V /\ pc v = b}` >>
  `EL b p = AsmPushLabel c /\ EL (b+1) p = AsmOp "JUMPI" /\
   EL (b+2) p = AsmPushLabel x /\ EL (b+3) p = AsmOp "JUMP"` by
     simp[Abbr `b`, Abbr `p`, EL_APPEND_EQN] >>
  qpat_assum `Rows = _` (fn eq =>
    qpat_assum `Rows p _ _ _ _ _ _ _ _ _`
      (map_every assume_tac o CONJUNCTS o CONV_RULE lets_conv o PURE_REWRITE_RULE [eq])) >>
  qpat_assum `Open = _` (fn eq =>
    qpat_assum `Open p _ _ _ {} _ _ _ _ _ _ _`
      (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [EMPTY_SUBSET, DIFF_EMPTY] o
       CONV_RULE lets_conv o PURE_REWRITE_RULE [eq])) >>
  `!v. v IN V /\ pc v = b+1 ==>
       2 <= height v /\ tag v 1 = NONE /\
       (?w. edge v w /\ pc w = b+2) /\ (?l i. tag v 0 = SOME(l,i))` by
    (gen_tac >> strip_tac >>
     source_dispatch `v` `pc v = b+1` `EL (b+1) p = _`
       [EVAL ``ALOOKUP dup_table "JUMPI"``, EVAL ``ALOOKUP swap_table "JUMPI"``] >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `?w. edge v w /\ pc w = _ /\ _`
                    (qx_choose_then `fall` strip_assume_tac) >>
                  qexists `fall` >> simp[]) >>
     qpat_assum `?w. edge v w /\ target p pc tag v w /\ _` mp_tac >>
     qpat_assum `target = _` (fn th => simp[th]) >> metis_tac[]) >>
  `!v. v IN V /\ pc v = b+2 ==> ?w. edge v w /\ pc w = b+3` by
    (gen_tac >> strip_tac >>
     source_dispatch `v` `pc v = b+2` `EL (b+2) p = _` [] >>
     qpat_assum `?w. edge v w /\ pc w = _ /\ _`
       (qx_choose_then `fall` strip_assume_tac) >>
     qexists `fall` >> simp[]) >>
  `!v. v IN V /\ pc v = b+3 ==> (?w. edge v w) /\ (?l i. tag v 0 = SOME(l,i))` by
    (gen_tac >> strip_tac >>
     source_dispatch `v` `pc v = b+3` `EL (b+3) p = _`
       [EVAL ``ALOOKUP dup_table "JUMP"``, EVAL ``ALOOKUP swap_table "JUMP"``] >>
     qpat_assum `?w. edge v w /\ target p pc tag v w /\ _` mp_tac >>
     qpat_assum `target = _` (fn th => simp[th]) >> metis_tac[]) >>
  `!v. v IN D ==> IS_SOME (FLOOKUP (SND (compute_label_offsets p)) c) /\
       (?w. edge v w /\ pc w = b+1) /\ (!w. edge v w ==> tag w 1 = NONE)` by
    (gen_tac >> simp[Abbr `D`] >> strip_tac >>
     source_dispatch `v` `pc v = b` `EL b p = _` [] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `?w. edge v w /\ pc w = _ /\ _`
                    (qx_choose_then `fall` strip_assume_tac) >>
                  qexists `fall` >> simp[]) >>
     gen_tac >> strip_tac >>
     `w IN V /\ pc w = b+1` by
       (conj_tac
        >- (qpat_assum `!u y. edge u y ==> _` drule >> simp[]) >>
        qpat_assum `!y. edge v y ==> pc y = _ /\ _` drule >> simp[]) >>
     qpat_assum `!v. v IN V /\ pc v = b+1 ==> _`
       (qspec_then `w` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`n` |-> `j`, `cut` |-> `t`, `ss` |-> `u`]
            (CONV_RULE lets_conv conditional_jump_actual_endpoint)) >>
  fold_abbrevs [`Abbrev (p = _)`, `Abbrev (q = _)`,
                `Abbrev (b = _)`, `Abbrev (r = _)`] >>
  (impl_tac >- (
    qpat_assum `Shape = _` (fn eq =>
      qpat_assum `Shape p _ _ _ _ _ _ _ e t`
        (map_every assume_tac o CONJUNCTS o CONV_RULE lets_conv o PURE_REWRITE_RULE [eq])) >>
    qpat_assum `!l d. _ ==> INDEX_OF (AsmLabel l) p = SOME d /\ _`
      (assume_tac o cj 4) >>
    simp[] >> conj_tac
    >- (qpat_assum `env0 = _` (pure_rewrite_tac o single o SYM) >>
        first_assum ACCEPT_TAC) >>
    conj_tac
    >- (rpt gen_tac >> disch_tac >>
        qpat_assum `!k l i. tag e k = SOME(l,i) ==> k < height e /\ _`
          (qspecl_then [`k`,`l`,`origin`] mp_tac) >>
        simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
    disch_then DISJ_CASES_TAC
    >- (qpat_assum `!v. v IN V /\ pc v = b+1 ==> _`
          (qspec_then `e` mp_tac) >> simp[]) >>
    qpat_assum `!v. v IN V /\ pc v = b+3 ==> _`
      (qspec_then `e` mp_tac) >> simp[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `Open = _` (fn oeq => qpat_assum `Shape = _` (fn seq =>
    qpat_assum `Flow = _` (fn feq => qpat_assum `target = _` (fn teq =>
      qpat_assum `Open p cc req V {} rank pc height need tag boolean edge`
        (mk_asm "source_open" o CONV_RULE lets_conv o
         PURE_REWRITE_RULE [oeq,seq,feq,teq]))))) >>
  mp_tac (CONV_RULE lets_conv conditional_jump_strict_ports) >>
  fold_abbrevs [`Abbrev (p = _)`, `Abbrev (q = _)`,
                `Abbrev (b = _)`, `Abbrev (r = _)`] >>
  (impl_tac >- (
    asm "source_open" (map_every assume_tac o CONJUNCTS) >>
    simp[] >> conj_tac
    >- (rpt gen_tac >> disch_tac >>
        qpat_assum `!u y. edge u y ==> _ /\ _ /\ rank y < rank u /\ _`
          drule >> simp[]) >>
    asm "source_open" (ACCEPT_TAC o SIMP_RULE bool_ss [DIFF_EMPTY] o cj 6))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!l d. C p l d ==> (d < b \/ b+4 <= d) /\ C q l (r d)` by
    (rpt gen_tac >> simp[Abbr `C`, Abbr `b`, Abbr `r`] >> strip_tac >>
     qpat_assum `!l d. _ ==> INDEX_OF (AsmLabel l) p = SOME d /\ _`
       (qspecl_then [`l`,`d`] mp_tac) >> simp[]) >>
  `?z. (pc e=b+2 \/ pc e=b+3) ==>
       z IN keep /\ C p x (pc z) /\
       height z=(if pc e=b+3 then height e-1 else height e) /\
       (!k l i. tag z k=SOME(l,i) ==> tag e (if pc e=b+3 then k+1 else k)=SOME(l,i)) /\
       (!k. boolean z k ==> boolean e (if pc e=b+3 then k+1 else k))` by
    (Cases_on `pc e=b+2 \/ pc e=b+3` >- (
       qpat_assum `_ ==> ?z. _ /\ (z IN V /\ _) /\ rank z < rank e /\ _` mp_tac >>
       (impl_tac >- (Cases_on `pc e=b+2` >> simp[])) >>
       disch_then (qx_choose_then `z` strip_assume_tac) >> qexists `z` >>
       `C p x (pc z)` by simp[Abbr `C`] >>
       `z IN keep` by (qpat_assum `!l d. C p l d ==> _` (drule_then (strip_assume_tac o cj 1)) >>
                       simp[Abbr `keep`]) >>
       qpat_assum `height z + _ = height e` mp_tac >>
       qpat_assum `!k l i. tag z k=SOME(l,i) ==> _` mp_tac >>
       qpat_assum `!k. boolean z k ==> _` mp_tac >>
       qpat_assum `z IN keep` mp_tac >>
       qpat_assum `C p x (pc z)` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >>
       ntac 5 disch_tac >> strip_tac >> gvs[]) >> simp[]) >>
  qabbrev_tac `Producer = \p l i. i<LENGTH p /\
    (EL i p=AsmPushLabel l \/ EL i p=AsmPushOfst l 0) /\ ?d. C p l d` >>
  qabbrev_tac `Slots = \p (h:num) n tg bl.
    (n ==> cc.cc_static) /\ (!k. bl k ==> k<h /\ tg k=NONE) /\
    (!k l i. tg k=SOME(l,i) ==> k<h /\ Producer p l i)` >>
  qabbrev_tac `Target = \p (tg:num->(string#num)option) d. ?l i. tg 0=SOME(l,i) /\ C p l d` >>
  qabbrev_tac `Legal = \p i tg j.
    if EL i p=AsmOp "JUMP" then Target p tg j else
    if EL i p=AsmOp "JUMPI" then j=i+1 \/ Target p tg j else j=i+1` >>
  qabbrev_tac `Row = \p i h tg (E:(num#num)->bool) pc height.
    let arm = \P n. ?v. E v /\ P (pc v) /\ height v=n in
    let legal = \P n. !v. E v ==> P (pc v) /\ height v=n in
    let fall = \d. d=i+1; taken = Target p tg in
    let next = \n. arm fall n /\ legal fall n in
    let untagged = \a. !k. k<a ==> tg k=NONE in
    let stop = \a. a<=h /\ untagged a /\ !v. ~E v in
    case EL i p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmOp name =>
        if name="INVALID" then stop 0 else if name="REVERT" then stop 2 else
        if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] then
          cc.cc_static /\ stop (asm_op_arity name) else
        (case ALOOKUP dup_table name of
           SOME n => n<h /\ next (h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<h /\ next h
           | NONE => if name="JUMP" then 1<=h /\ arm taken (h-1) /\ legal taken (h-1) else
                     if name="JUMPI" then 2<=h /\ tg 1=NONE /\ arm fall (h-2) /\
                       arm taken (h-2) /\ legal (\d. fall d \/ taken d) (h-2) else
                     ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                       untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F` >>
  qabbrev_tac `initial = (pc e=b+1)` >>
  qabbrev_tac `H = \v. if initial /\ v=e then height v-1 else height v` >>
  qabbrev_tac `shift = \v. if initial /\ v=e then 2 else 1:num` >>
  qabbrev_tac `Visit = \v z0 z1.
     0<H v /\ z0 IN keep /\ z1 IN keep /\ rank z0<rank v /\ rank z1<rank v /\
     height z0=H v-1 /\ height z1=H v-1 /\ C p x (pc z0) /\
     (!k ta tb. tag z0 k=SOME ta /\ tag z1 k=SOME tb ==> ta=tb) /\
     (!k ta. (tag z0 k=SOME ta \/ tag z1 k=SOME ta) ==>
       tag v (if initial /\ v=e then k+2 else k+1)=SOME ta) /\
     (!k. boolean z0 k \/ boolean z1 k ==> boolean v (if initial /\ v=e then k+2 else k+1)) /\
     (!rho.
       let U = \k. case tag z0 k of NONE => tag z1 k | SOME ta => SOME ta in
       let UB = \k. boolean z0 k \/ boolean z1 k in
       let vp = \i. if i<4 then b+i else if i=4 then r(pc z0) else r(pc z1) in
       let vh = \i. if i<2 then H v else if i=2 then H v+1 else H v-1 in
       let vn = \i. (i=4 /\ need z0) \/ (i=5 /\ need z1) in
       let raw = \i k.
         if i<2 then (if k=0 then NONE else U (k-1)) else
         if i=2 then (if k=0 then SOME(x,b+2) else if k=1 then NONE else U (k-2)) else
         (if i=4 then tag z0 else tag z1) k in
       let vb = \i k.
         if i=0 then k<>0 /\ UB (k-1) else if i=1 then k=0 \/ UB (k-1) else
         if i=2 then k=1 \/ (2<=k /\ UB (k-2)) else
         (if i=4 then boolean z0 else boolean z1) k in
       let VE = \i j. (i<3 /\ j=i+1) \/ (i=2 /\ j=4) \/ (i=3 /\ j=5) in
       let P = \w:num#num. vp (FST w) in
       let J = \w:num#num. vh (FST w) in
       let T = \(w:num#num) k. if FST w=2 /\ k=0 then SOME(x,b+1) else
              OPTION_MAP (\(l,i). (l,rho l i)) (raw (FST w) k) in
       let B = \w:num#num. vb (FST w) in
       (!i j. VE i j ==> Flow q P J T B (i,0) (j,0)) /\
       (C q x (r(pc z0)) /\
        (!w k l i. (w=z0 \/ w=z1) /\ tag w k=SOME(l,i) ==> Producer q l (rho l i)) ==>
        (!i. i<4 ==> Slots q (vh i) (vn i) (T (i,0)) (B (i,0))) /\
        (!i. i<4 ==> vp i<LENGTH q /\ Row q (vp i) (vh i) (T (i,0))
                             (\w. VE i (FST w)) P J) /\
        (!i j. VE i j ==> Legal q (vp i) (T (i,0)) (vp j))))` >>
  `!v. v IN D ==> ?z0 z1. Visit v z0 z1` by suspend "whole" >>
  `(initial ==> ?z0 z1. Visit e z0 z1)` by suspend "strict" >>
  `?z0 z1. !v. v IN D \/ (initial /\ v=e) ==> Visit v (z0 v) (z1 v)` by
    (simp[NoAsms, GSYM SKOLEM_THM] >> qx_gen_tac `v` >>
     simp[NoAsms, RIGHT_EXISTS_IMP_THM] >> disch_then DISJ_CASES_TAC
     >- (qpat_assum `!v. v IN D ==> ?z0 z1. Visit v z0 z1`
           (qspec_then `v` (drule_then ACCEPT_TAC))) >>
     pop_assum strip_assume_tac >> qpat_x_assum `v=e` SUBST_ALL_TAC >>
     qpat_assum `initial ==> ?z0 z1. Visit e z0 z1` (drule_then ACCEPT_TAC)) >>
  suspend "table"
QED

val strip_packet = map_every assume_tac o CONJUNCTS;
val fold_port_layout = fold_abbrevs [`Abbrev (p = _)`, `Abbrev (q = _)`,
  `Abbrev (b = _)`, `Abbrev (r = _)`, `Abbrev (C = _)`, `Abbrev (keep = _)`];
val normalize_port_receipt = CONV_RULE lets_conv;

fun phase_receipt h =
  qpat_assum `Flow = _` (pure_rewrite_tac o single) >>
  map_every (fn pat => qpat_assum pat
    (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (Slots = _)`, `Abbrev (Row = _)`, `Abbrev (Legal = _)`,
     `Abbrev (Target = _)`, `Abbrev (Producer = _)`, `Abbrev (C = _)`] >>
  CONV_TAC lets_conv >>
  mp_tac (Q.INST [`H` |-> h, `z0` |-> `a0:num#num`, `z1` |-> `a1:num#num`]
    (INST_TYPE [alpha |-> ``:asm_inst``, beta |-> ``:num#num``]
      (normalize_port_receipt conditional_jump_phase_receipt))) >>
  fold_abbrevs [`Abbrev (b = _)`, `Abbrev (r = _)`] >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  CONV_TAC lets_conv >> pure_rewrite_tac [COND_RATOR] >> disch_then ACCEPT_TAC;

Resume optimize_inefficient_jumps_abort_certificate[whole]:
  qx_gen_tac `v` >> disch_tac >>
  `v IN V /\ pc v=b` by
    (qpat_assum `v IN D` mp_tac >> simp_tac (srw_ss()) [Abbr `D`]) >>
  `~(initial /\ v=e)` by
    (qpat_assum `pc v=b` mp_tac >> simp_tac bool_ss [Abbr `initial`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[DECIDE ``!n:num. n<>n+1``]) >>
  qpat_assum `!v. v IN D ==> IS_SOME _ /\ _` (drule_then strip_packet) >>
  mp_tac (normalize_port_receipt conditional_jump_whole_port_receipt) >>
  fold_port_layout >>
  (impl_tac >- (
     asm "source_open" (strip_packet o SIMP_RULE bool_ss [EMPTY_SUBSET, DIFF_EMPTY]) >>
     simp_tac bool_ss [EMPTY_SUBSET, DIFF_EMPTY] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       asm "port_range" ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `a0` (qx_choose_then `a1` strip_packet))) >>
  qexistsl [`a0`,`a1`] >>
  qpat_assum `~(initial /\ v=e)` (fn th => simp_tac bool_ss [Abbr `Visit`, Abbr `H`, th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (simp_tac bool_ss [Abbr `C`] >> first_assum ACCEPT_TAC) >>
  phase_receipt `(height:num#num->num) v`
QED

Resume optimize_inefficient_jumps_abort_certificate[strict]:
  disch_tac >>
  `pc e=b+1` by simp[Abbr `initial`] >>
  `?i. tag e 0=SOME(c,i)` by
    (qpat_assum `initial ==> ?i. tag e 0=SOME(c,i)` (drule_then ACCEPT_TAC)) >>
  `2 <= height e /\ tag e 1 = NONE /\ (?w. edge e w /\ pc w=b+2)` by
    (qpat_assum `!v. v IN V /\ pc v = b+1 ==> _`
      (qspec_then `e` mp_tac) >> simp[]) >>
  mp_tac (normalize_port_receipt conditional_jump_strict_port_receipt) >>
  fold_port_layout >>
  (impl_tac >- (
     asm "source_open" (strip_packet o SIMP_RULE bool_ss [EMPTY_SUBSET, DIFF_EMPTY]) >>
     simp_tac bool_ss [EMPTY_SUBSET, DIFF_EMPTY] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `a0` (qx_choose_then `a1` strip_packet))) >>
  qexistsl [`a0`,`a1`] >>
  qpat_assum `initial` (fn th => simp_tac bool_ss [Abbr `Visit`, Abbr `H`, th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- simp[Abbr `keep`]
  >- simp[Abbr `keep`]
  >- (simp_tac bool_ss [Abbr `C`] >> first_assum ACCEPT_TAC) >>
  phase_receipt `(height:num#num->num) e - 1`
QED

Resume optimize_inefficient_jumps_abort_certificate[table]:
  qpat_x_assum `!v. v IN D \/ (initial /\ v=e) ==> Visit v (z0 v) (z1 v)`
    (mk_asm "visits") >>
  `!v. v IN D ==> ~(initial /\ v=e)` by
    (qx_gen_tac `v` >> disch_tac >>
     `v IN V /\ pc v=b` by
       (qpat_assum `v IN D` mp_tac >> simp_tac (srw_ss()) [Abbr `D`]) >>
     qpat_assum `pc v=b` mp_tac >> simp_tac bool_ss [Abbr `initial`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[DECIDE ``!n:num. n<>n+1``]) >>
  `!v. v IN D ==>
     (!k t. (tag (z0 v) k=SOME t \/ tag (z1 v) k=SOME t) ==> tag v (k+1)=SOME t) /\
     (!k. (boolean (z0 v) k \/ boolean (z1 v) k) ==> boolean v (k+1))` by
    (qx_gen_tac `v` >> disch_tac >>
     `~(initial /\ v=e)` by (first_assum (drule_then ACCEPT_TAC)) >>
     asm "visits" (qspec_then `v` mp_tac) >>
     (impl_tac >- (disj1_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `~(initial /\ v=e)` (fn th => simp_tac bool_ss [Abbr `Visit`, th]) >>
     disch_then (fn th => conj_tac >- ACCEPT_TAC (cj 10 th) >> ACCEPT_TAC (cj 11 th))) >>
  qspecl_then [`p`,`q`,`b`,`x`,`V`,`rank`,`pc`,`height`,`tag`,`boolean`,`edge`,`cc`,`z0`,`z1`]
    (mp_tac o normalize_port_receipt) conditional_jump_kept_receipt >>
  fold_abbrevs [`Abbrev (r = _)`, `Abbrev (keep = _)`, `Abbrev (D = _)`] >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (simp_tac bool_ss [GSYM AND_IMP_INTRO] >> rpt gen_tac >> disch_tac >>
        asm "port_range" (drule_then assume_tac) >>
        (simp[]))
    >- (qx_gen_tac `v` >> disch_tac >>
      `v IN V` by
        (qpat_assum `v IN keep` mp_tac >> simp_tac (srw_ss()) [Abbr `keep`] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >- (
        qpat_assum `target = _` (fn th =>
          qpat_assum `!v. v IN V ==> pc v < LENGTH p /\ _`
            (qspec_then `v` (drule_then (mp_tac o CONV_RULE lets_conv o
                                         PURE_REWRITE_RULE [th] o CONJUNCT2)))) >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [RIGHT_EXISTS_AND_THM]) >>
      qx_gen_tac `w` >> disch_tac >>
      asm "source_open" (qspec_then `v` (qspec_then `w`
        (drule_then mp_tac)) o cj 5) >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [RIGHT_EXISTS_AND_THM, DIFF_EMPTY, SF CONJ_ss]) >>
    FAIL_TAC "remaining retained receipt inputs")) >>
  disch_then (mk_asm "kept") >>
  qspecl_then [`p`,`q`,`b`,`x`,`V`,`e`,`rank`,`pc`,`height`,`need`,`tag`,
                `boolean`,`edge`,`cc`,`req`,`z`,`z0`,`z1`]
    (mp_tac o normalize_port_receipt) conditional_jump_port_table >>
  fold_abbrevs [`Abbrev (r = _)`, `Abbrev (C = _)`, `Abbrev (Producer = _)`,
                `Abbrev (Slots = _)`, `Abbrev (keep = _)`, `Abbrev (D = _)`,
                `Abbrev (initial = _)`, `Abbrev (H = _)`] >>
  (impl_tac >- (
    asm "kept" strip_packet >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (simp_tac bool_ss [Abbr `Slots`, Abbr `Producer`, Abbr `C`] >>
        qpat_assum `!u. u IN V ==> (need u ==> _) /\ _`
          (mp_tac o CONV_RULE lets_conv) >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
    >- (qpat_assum `!l d. _ ==> INDEX_OF (AsmLabel l) p = SOME d /\ _`
          (mp_tac o cj 4) >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [])
    >- (simp_tac bool_ss [Abbr `Producer`, Abbr `C`] >> rpt gen_tac >>
        disch_then strip_packet >>
        qpat_assum `!l i. i<LENGTH p /\ _ ==> _`
          (qspecl_then [`l`,`i`] mp_tac) >>
        (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
                      qpat_assum `_ = AsmPushLabel l \/ _` mp_tac >>
                      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])) >>
        disch_then DISJ_CASES_TAC
        >- (pop_assum strip_packet >> disj1_tac >>
            `?d off. FLOOKUP (SND (compute_label_offsets q)) l=SOME off /\
                     off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off=SOME d` by
              (qpat_assum `?d off. FLOOKUP (SND (compute_label_offsets p)) l=SOME off /\ _`
                 (qx_choose_then `d` mp_tac) >>
               qpat_assum `!l d. _ ==> INDEX_OF (AsmLabel l) p = SOME d /\ _`
                 (qspecl_then [`l`,`d`] (mp_tac o cj 4)) >>
               POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
            simp[])
        >> pop_assum DISJ_CASES_TAC >> simp[])
    >- (qpat_assum `(pc e=b+2 \/ pc e=b+3) ==> z IN keep /\ _` mp_tac >>
        simp_tac bool_ss [Abbr `C`])
    >- (asm "visits" mp_tac >>
        map_every (fn pat => qpat_assum pat
          (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]))
          [`Abbrev (Visit = _)`, `Abbrev (Slots = _)`, `Abbrev (Row = _)`,
           `Abbrev (Legal = _)`, `Abbrev (Target = _)`, `Abbrev (Producer = _)`,
           `Abbrev (C = _)`, `Abbrev (H = _)`] >>
        qpat_assum `Flow = _` (pure_rewrite_tac o single) >> CONV_TAC lets_conv >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        pure_rewrite_tac [COND_RATOR, pairTheory.FST, REFL_CLAUSE, AND_CLAUSES,
                          COND_CLAUSES, IMP_CLAUSES] >>
        disch_then (mk_asm "expanded_visits") >> qx_gen_tac `u` >> disch_tac >>
        asm "expanded_visits" (qspec_then `u` (drule_then strip_packet)) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qx_gen_tac `visit_rho` >> ntac 4 gen_tac >>
        disch_then (map_every SUBST1_TAC o CONJUNCTS) >>
        CONV_TAC lets_conv >>
        pure_rewrite_tac [COND_RATOR, pairTheory.FST, REFL_CLAUSE, AND_CLAUSES,
                          COND_CLAUSES, IMP_CLAUSES] >>
        first_assum (qspec_then `visit_rho` ACCEPT_TAC)) >>
    asm "kept" (mp_tac o cj 3) >>
    simp_tac bool_ss [combinTheory.o_THM, COND_RATOR] >> disch_then ACCEPT_TAC)) >>
  disch_then (qx_choose_then `family` (qx_choose_then `A` (qx_choose_then `root`
    (qx_choose_then `R` (qx_choose_then `P` (qx_choose_then `J` (qx_choose_then `N`
      (qx_choose_then `raw` (qx_choose_then `B` (qx_choose_then `E` strip_packet)))))))))) >>
  qpat_assum `!z root rootPC rootH rootNeed raw bl. _`
    (qspecl_then [`z`,`root`,`P`,`J`,`N`,`raw root`,`B`] mp_tac) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_assum `(pc e=b+2 \/ pc e=b+3) ==> z IN keep /\ _`
      (mp_tac o cj 2) >> simp_tac bool_ss [Abbr `C`])) >>
  disch_then (qx_choose_then `j'` (qx_choose_then `u'` (qx_choose_then `t'` strip_packet))) >>
  qpat_x_assum `(!k l. raw root k = SOME(l,b) ==> _) ==> ?rho. _` mp_tac >>
  (impl_tac >- (
    rpt gen_tac >> disch_tac >>
    qpat_assum `!k l i. raw root k = SOME(l,i) ==> ?m v. _`
      (drule_then (qx_choose_then `m` (qx_choose_then `v` strip_packet))) >>
    qexists `v.sym_base.as_pc` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    `?d. C p l d` by (
      qpat_assum `!k l i. raw root k = SOME(l,i) ==> _ /\ tag e _ = SOME(l,i)`
        (drule_then strip_packet) >>
      qpat_assum `!u. u IN V ==> (need u ==> _) /\ _`
        (qspec_then `e` (drule_then (strip_packet o CONV_RULE lets_conv))) >>
      first_x_assum (drule_then strip_packet) >>
      simp_tac bool_ss [Abbr `C`] >>
      qpat_assum `?off d. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\ _`
        (qx_choose_then `off` (qx_choose_then `d` strip_packet)) >>
      qexistsl [`d`,`off`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
    qpat_assum `!l d. C p l d ==> _ /\ C q l _` (drule_then mp_tac o cj 2) >>
    simp_tac bool_ss [Abbr `C`] >>
    disch_then (qx_choose_then `off` strip_packet) >>
    qexistsl [`r d`,`off`] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `rmap` strip_packet) >>
  qabbrev_tac `Tg = \a k. OPTION_MAP (\(l,i). (l,rmap l i)) (raw a k)` >>
  qpat_assum `!rho. (N root ==> _) /\ _ ==> _`
    (qspec_then `rmap` mp_tac) >>
  (impl_tac >- (
    qpat_assum `!a. a IN A ==> ((N a ==> _) /\ _) /\ _`
      (qspec_then `root` (drule_then (strip_packet o CONJUNCT1))) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    rpt gen_tac >> disch_tac >>
    first_x_assum (drule_then strip_packet) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "destination_root") >>
  qabbrev_tac `Ecut = \a y. a IN A /\ E a y` >>
  qpat_assum `t'.as_call_ctx=cc` (fn ctx_eq =>
    qpat_assum `t'.as_requests=req` (fn req_eq =>
      qspecl_then [`q`,`u'`,`t'`,`A`,`root`,`\a. rat$rat_of_num (R a)`,
                  `P`,`J`,`N`,`Tg`,`B`,`Ecut`]
        (mp_tac o PURE_REWRITE_RULE [ratTheory.RAT_OF_NUM_LES,ctx_eq,req_eq] o
          CONV_RULE lets_conv) pending_rows_rooted_package)) >>
  (impl_tac >- suspend "interpretation_inputs") >>
  suspend "assembled_output"
QED

Resume optimize_inefficient_jumps_abort_certificate[interpretation_inputs]:
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "package_rows" >>
  conj_tac >- suspend "package_edges" >>
  asm "destination_root" (mp_tac o CONV_RULE lets_conv) >>
  qpat_assum `t'.as_call_ctx=cc` (fn th =>
    simp_tac bool_ss [Abbr `Tg`, th, CONJ_ASSOC]) >>
  strip_tac >> rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
QED

Resume optimize_inefficient_jumps_abort_certificate[package_rows]:
  conj_tac >- suspend "package_slots" >>
  conj_tac >- suspend "package_rank_flow" >>
  suspend "package_dispatch"
QED

Resume optimize_inefficient_jumps_abort_certificate[package_slots]:
  qx_gen_tac `a` >> disch_tac >>
  qpat_assum `!a. a IN A ==> ((N a ==> _) /\ _) /\ _`
    (qspec_then `a` (drule_then (strip_packet o CONJUNCT1))) >>
  simp_tac bool_ss [Abbr `Tg`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >> first_x_assum (drule_then strip_packet) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `?d off. FLOOKUP _ _ = SOME off /\ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Resume optimize_inefficient_jumps_abort_certificate[package_rank_flow]:
  simp_tac bool_ss [Abbr `Ecut`, Abbr `Tg`] >>
  rpt gen_tac >> disch_then strip_packet >>
  qpat_assum `!a y. a IN A /\ E a y ==> y IN A /\ _`
    (drule_all_then strip_packet) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!a y. a IN A /\ E a y ==> (if _ then _ else _) /\ _`
    (drule_all_then (ACCEPT_TAC o SIMP_RULE bool_ss [] o CONJUNCT2))
QED

Resume optimize_inefficient_jumps_abort_certificate[package_edges]:
  simp_tac bool_ss [Abbr `Ecut`, Abbr `Tg`] >>
  rpt gen_tac >> disch_then strip_packet >>
  qpat_assum `!a y. a IN A /\ E a y ==> (if _ then _ else _) /\ _`
    (drule_all_then (CONJUNCTS_THEN2 (mk_asm "legal") assume_tac o SIMP_RULE bool_ss [])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  asm "legal" mp_tac >> simp_tac bool_ss [RIGHT_EXISTS_AND_THM]
QED

Resume optimize_inefficient_jumps_abort_certificate[package_dispatch]:
  qx_gen_tac `src` >> disch_tac >>
  qpat_assum `!a. a IN A ==> ((N a ==> _) /\ _) /\ _`
    (qspec_then `src` (drule_then (mp_tac o CONJUNCT2 o CONJUNCT2))) >>
  qpat_assum `src IN A` (fn th =>
    simp_tac bool_ss [th, Abbr `Ecut`, Abbr `Tg`, RIGHT_EXISTS_AND_THM, CONJ_ASSOC])
QED

Resume optimize_inefficient_jumps_abort_certificate[assembled_output]:
  disch_then (CONJUNCTS_THEN2 (mk_asm "live_root")
    (CONJUNCTS_THEN2 (mk_asm "live_reach")
    (CONJUNCTS_THEN2 (mk_asm "live_rows")
    (CONJUNCTS_THEN2 (mk_asm "live_open") (mk_asm "live_shape"))))) >>
  qabbrev_tac `live = {x | x IN A /\ ?n (path:num->num#num).
    path 0 = root /\ path n = x /\ !k. k<n ==> Ecut (path k) (path(SUC k))}` >>
  qabbrev_tac `live_edge = \x y. x IN live /\ Ecut x y` >>
  qexistsl [`j'`,`t'`,`u'`,`cc`,`req`,`live`,`root`,`R`,`P`,`J`,`N`,`Tg`,`B`,`live_edge`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `asm_data_env q (assemble q ++ data) = env0`
    (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `t'.as_requests = req` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single))
    [`Rows = _`,`Open = _`,`Shape = _`,`Reach = _`,`Flow = _`,`target = _`] >>
  CONV_TAC lets_conv >>
  conj_tac >- suspend "destination_rows" >>
  conj_tac >- suspend "destination_open" >>
  simp_tac bool_ss [Abbr `live_edge`, Abbr `live`] >>
  conj_tac >- asm "live_root" ACCEPT_TAC >>
  conj_tac >- asm "live_reach" ACCEPT_TAC >>
  asm "live_shape" mp_tac >>
  qpat_assum `t'.as_call_ctx = cc` (fn ctx_eq =>
    qpat_assum `t'.as_requests = req` (fn req_eq =>
      simp_tac bool_ss [ctx_eq,req_eq,CONJ_ASSOC])) >>
  disch_then strip_packet >> conj_tac >> first_assum ACCEPT_TAC
QED

Resume optimize_inefficient_jumps_abort_certificate[destination_rows]:
  simp_tac bool_ss [Abbr `live_edge`, Abbr `live`, RIGHT_EXISTS_AND_THM, GSYM CONJ_ASSOC] >>
  asm "live_rows" (strip_packet o SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM, GSYM CONJ_ASSOC]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume optimize_inefficient_jumps_abort_certificate[destination_open]:
  simp_tac bool_ss [Abbr `live_edge`, Abbr `live`, RIGHT_EXISTS_AND_THM, GSYM CONJ_ASSOC] >>
  asm "live_open" (strip_packet o SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM, GSYM CONJ_ASSOC]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise optimize_inefficient_jumps_abort_certificate
