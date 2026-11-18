Theory staticAbortOptPruneUnreachable
Ancestors
  staticAbortOptPruneUnreachableWalk staticAbortOptPruneUnreachableRows
  staticAbortOptPruneUnreachableFlow staticAbortOptPruneUnreachableActualRoot
  staticAbortOptMergeIszeroBranchPackage asmOptPruneUnreachable
  asmDataEnv asmSymBridge asmSplice asmSem asmSymSem codegenSymRel
  finalizerContract stackOpSim staticAbortStraight
  finite_map list rich_list option words arithmetic pred_set pair alist

Theorem prune_unreachable_abort_certificate:
  !orig s data req_bound.
  let Shape = \p cc req pc height need tag boolean i (t:asm_state).
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
  let target = \p (pc:(num#num)->num) tag x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)
  in
  let Flow = \p pc height tag boolean (x:num#num) (y:num#num).
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
  let Rows = \p cc (V:(num#num)->bool) rank pc height need tag boolean edge.
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
                    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)) /\
    (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y) /\
    (!x. x IN V ==>
      pc x < LENGTH p /\
      let h = height x in
      let fall = \y. pc y = pc x+1 in
      let arm = \P n. ?y. edge x y /\ P y /\ height y = n in
      let legal = \P n. !y. edge x y ==> P y /\ height y = n in
      let next = \n. arm fall n /\ legal fall n in
      let untagged = \a. !k. k<a ==> tag x k=NONE in
      let stop = \a. a<=h /\ untagged a /\ !y. ~edge x y in
      case EL (pc x) p of
        AsmLabel l => next h
      | AsmPush bs => next (h+1)
      | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
      | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
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
      | _ => F)
  in
  let Open = \p cc req (V:(num#num)->bool) X rank pc height need
      (tag:(num#num)->num->(string#num)option)
      (boolean:(num#num)->num->bool) edge.
    let S = Shape p cc req pc height need tag boolean in
      FINITE V /\ X SUBSET V /\
      (!x. x IN V ==> ?t. S x t) /\
      (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
      (!x y. edge x y ==>
         x IN V DIFF X /\ y IN V /\ rank y < rank x /\
         Flow p pc height tag boolean x y /\
         (if EL (pc x) p = AsmOp "JUMP" then target p pc tag x y
          else if EL (pc x) p = AsmOp "JUMPI"
               then pc y = pc x+1 \/ target p pc tag x y
          else pc y = pc x+1)) /\
      (!x t. x IN V DIFF X /\ S x t ==>
         (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmRevert u \/
                asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmFault u) /\ u.as_requests=req) \/
         (?y u. edge x y /\
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
              p 1 t = AsmOK u /\ S y u))
  in
  let Reach = \(edge:(num#num)->(num#num)->bool) e x.
    ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))
  in
  let bytes = \p. assemble p ++ data in
  let env0 = asm_data_env orig (bytes orig) in
  let M_R = \p.
    let envp = asm_data_env p (bytes p) in
    let start = s with as_code := bytes p in
    let run = asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p in
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
        asm_sym_rel p envp t u /\
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
           k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))))
  in
  !p. M_R p ==> M_R (FST (prune_unreachable_code p))
Proof
  rpt gen_tac >>
  map_every (fn pat => qmatch_goalsub_abbrev_tac pat >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ Shape`, `LET _ target`, `LET _ Flow`, `LET _ Rows`,
     `LET _ Open`, `LET _ Reach`, `LET _ bytes`, `LET _ env0`, `LET _ M_R`] >>
  ho_match_mp_tac prune_unreachable_walk_preserves_contextual >>
  map_every qx_gen_tac [`pre`,`opn`,`x`,`tail`] >>
  qabbrev_tac `p = pre ++ [opn;x] ++ tail` >>
  qabbrev_tac `q = pre ++ [opn] ++ tail` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `asm_refines p q` by
    (simp[Abbr `p`, Abbr `q`] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> irule prune_one_refines >> simp[]) >>
  qpat_x_assum `M_R p` mp_tac >> simp[Abbr `M_R`, NoAsms] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `asm_refines p q` (mp_tac o REWRITE_RULE [asm_refines_def]) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FILTER is_data_inst q = FILTER is_data_inst orig` by metis_tac[] >> simp[] >>
  qpat_x_assum `(?n out. _) \/ _`
    (DISJ_CASES_THEN2 (mk_asm "terminal") (mk_asm "pending"))
  >- (disj1_tac >> suspend "terminal") >>
  disj2_tac >> suspend "pending"
QED

Resume prune_unreachable_abort_certificate[terminal]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`Abbrev (Shape = _)`, `Abbrev (target = _)`, `Abbrev (Flow = _)`,
     `Abbrev (Rows = _)`, `Abbrev (Open = _)`, `Abbrev (Reach = _)`] >>
  asm_x "terminal" (qx_choose_then `n` (qx_choose_then `out`
    (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `exec = \g k. asm_steps (SND (compute_label_offsets g))
    (build_offset_to_pc g) g k (s with as_code := bytes g)` >>
  Q.SUBGOAL_THEN `exec p n = AsmRevert out \/ exec p n = AsmFault out` assume_tac
  >- simp[Abbr `exec`] >>
  qpat_x_assum `asm_steps _ _ p n _ = _ \/ _` kall_tac >>
  `!g fuel. asm_static_wf g /\ FILTER is_data_inst g = FILTER is_data_inst orig /\
      sym_terminal (sym_run g env0 fuel (sym_init s)) ==>
      ?m. sym_result_rel (sym_run g env0 fuel (sym_init s)) (asm_result_sym (exec g m))` by
    (rpt gen_tac >> strip_tac >>
     `env0 = asm_data_env g (bytes g)` by
       (simp[Abbr `env0`, Abbr `bytes`] >> irule asm_data_env_agree >> simp[]) >>
     simp[Abbr `exec`] >>
     qspecl_then [`g`,`env0`,`s with as_code := bytes g`,`fuel`] mp_tac
        (Q.GENL [`p`,`env`,`s`,`fuel`] asm_sym_backward) >>
     `sym_init (s with as_code := bytes g) = sym_init s` by simp[sym_init_def] >>
     gvs[asm_data_env_ok_asm_data_env]) >>
  `sym_terminal (sym_run p env0 n (sym_init s))` by
    (drule sym_steps_terminal_run >> disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `sym_result_rel (sym_run p env0 n (sym_init s)) (asm_result_sym (exec p n))` by
    (qpat_assum `!g fuel. _ ==> ?m. _` (qspecl_then [`p`,`n`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (qx_choose_then `m` assume_tac) >>
     `exec p m = exec p n` suffices_by metis_tac[] >>
     `sym_terminal (asm_result_sym (exec p m))` by metis_tac[sym_result_rel_terminal] >>
     `exec p (n+m) = exec p n` by
       (qpat_assum `exec p n = _ \/ _` strip_assume_tac >>
        qunabbrev_tac `exec` >> BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
        once_rewrite_tac[asm_steps_add] >> simp[]) >>
     `exec p (m+n) = exec p m` by
       (Cases_on `exec p m` >>
        qunabbrev_tac `exec` >> BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
        once_rewrite_tac[asm_steps_add] >> gvs[asm_result_sym_def, sym_terminal_def]) >>
     metis_tac[ADD_COMM]) >>
  qpat_assum `!env s fuel. sym_terminal _ ==> ?f. _`
    (qspecl_then [`env0`,`s`,`n`] (drule_then (qx_choose_then `fuel` assume_tac))) >>
  `sym_terminal (sym_run q env0 fuel (sym_init s))` by metis_tac[sym_result_rel_terminal] >>
  qpat_x_assum `!g fuel. _ ==> ?m. _` (qspecl_then [`q`,`fuel`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `m` assume_tac) >>
  `sym_terminal (sym_steps q env0 fuel (sym_init s))` by
    (drule sym_run_terminal_steps >> disch_then (qspec_then `fuel` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `sym_result_rel (asm_result_sym (exec p n)) (asm_result_sym (exec q m))` by
    (`sym_result_rel (asm_result_sym (exec p n)) (sym_run p env0 n (sym_init s))` by
       (Cases_on `asm_result_sym (exec p n)` >> Cases_on `sym_run p env0 n (sym_init s)` >>
        gvs[sym_result_rel_def]) >>
     metis_tac[sym_result_rel_trans]) >>
  qpat_x_assum `exec p n = _ \/ _` strip_assume_tac >>
  Cases_on `exec q m` >>
  qpat_x_assum `sym_result_rel (asm_result_sym _) (asm_result_sym _)` mp_tac >>
  simp[asm_result_sym_def, sym_result_rel_def, sym_obs_def, sym_init_def,
       asm_state_component_equality] >>
  strip_tac >> qmatch_asmsub_rename_tac `exec q m = _ dst` >>
  qexistsl [`m + fuel`,`dst`] >>
  `sym_terminal (sym_steps q env0 (m + fuel) (sym_init s))` by
    (once_rewrite_tac[ADD_COMM] >> simp[symFrameControlTheory.sym_steps_terminal_extend]) >>
  (conj_tac
   >- (qunabbrev_tac `exec` >> BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
       once_rewrite_tac[asm_steps_add] >> simp[]) >>
   conj_tac
   >- qpat_assum `sym_terminal (sym_steps q env0 (m + fuel) _)`
        (ACCEPT_TAC o REWRITE_RULE [sym_init_def]) >>
   qpat_assum `out.as_requests = dst.as_requests` (SUBST1_TAC o SYM) >>
   first_assum ACCEPT_TAC)
QED

val prune_lets = REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV);
fun prune_eqs [] k = k []
  | prune_eqs (pat::pats) k = qpat_assum pat (fn th =>
      prune_eqs pats (fn eqs => k (REWRITE_RULE [markerTheory.Abbrev_def] th :: eqs)));
fun prune_expand pats = prune_eqs pats (fn eqs =>
  pure_rewrite_tac eqs >> CONV_TAC prune_lets);
fun prune_fact pats pat ttac = prune_eqs pats (fn eqs =>
  qpat_assum pat (ttac o CONV_RULE prune_lets o PURE_REWRITE_RULE eqs));

Resume prune_unreachable_abort_certificate[pending]:
  asm_x "pending" (foldr (fn (v,k) => qx_choose_then v k)
    (map_every assume_tac o CONJUNCTS)
    [`j`,`t`,`u`,`V`,`e`,`pruneRnk`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`]) >>
  rename1 `Rows p _ V level pc height need tag boolean edge` >>
  qabbrev_tac `d = LENGTH pre + 1` >>
  qabbrev_tac `r = \i. if i < d then i else i - 1` >>
  qabbrev_tac `pick = \l. @k. k < LENGTH q /\
    (EL k q = AsmPushLabel l \/ EL k q = AsmPushOfst l 0)` >>
  qabbrev_tac `tagQ = \v k. OPTION_MAP (\(l,i). (l,if i=d then pick l else r i)) (tag v k)` >>
  `pc e = u.sym_base.as_pc` by
    (prune_fact [`Abbrev (Shape = _)`] `Shape p _ _ _ _ _ _ _ e t`
       (assume_tac o CONJUNCT1) >> metis_tac[]) >>
  prune_fact [`Abbrev (Open = _)`] `Open p _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [DIFF_EMPTY]) >>
  `!a b name. edge a b /\ EL (pc a) p = AsmOp name ==>
       IS_SOME (ALOOKUP dup_table name) \/ IS_SOME (ALOOKUP swap_table name) \/
       name="JUMP" \/ name="JUMPI" \/ (?m. static_abort_straight name m)` by
    suspend "source_dispatch" >>
  mp_tac (foldl (fn (a, th) => Q.SPEC a th)
    (CONV_RULE prune_lets prune_one_covered_rows)
    [`pre`,`opn`,`x`,`tail`,`s`,`env0`,`j`,`u`,
     `(t:asm_state).as_call_ctx`,`(t:asm_state).as_requests`,
     `V`,`e`,`\z. rat_of_num (level z)`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`]
    |> BETA_RULE |> REWRITE_RULE [ratTheory.RAT_OF_NUM_LES]) >>
  (impl_tac >- suspend "source_rows") >>
  suspend "packed_rows"
QED

Resume prune_unreachable_abort_certificate[source_rows]:
  prune_eqs [`Abbrev (p = _)`, `Abbrev (q = _)`] (fn eqs =>
    pure_once_rewrite_tac (map GSYM eqs)) >>
  simp_tac bool_ss [DIFF_EMPTY, RIGHT_EXISTS_AND_THM] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (prune_fact [`Abbrev (Reach = _)`] `!v. v IN V ==> Reach edge e v` ACCEPT_TAC) >>
  TRY (prune_fact [`Abbrev (Shape = _)`] `!v. v IN V ==> ?u. Shape p _ _ _ _ _ _ _ v u`
        (ACCEPT_TAC o SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM])) >>
  prune_fact [`Abbrev (Rows = _)`, `Abbrev (Flow = _)`, `Abbrev (target = _)`]
    `Rows p _ V level pc height need tag boolean edge`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]) >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (rpt gen_tac >> disch_tac >>
    prune_fact [`Abbrev (target = _)`] `!a b. edge a b ==> _ /\ _ /\ _ /\ _ /\ _`
      (drule_then (ACCEPT_TAC o last o CONJUNCTS o SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]))) >>
  gen_tac >> disch_tac >>
  qpat_assum `!v. v IN V ==> (need v ==> _) /\ _ /\ _`
    (drule_then (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (mk_asm "slot")))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >> asm "slot" (drule_then strip_assume_tac) >>
  simp[] >> metis_tac[]
QED

Resume prune_unreachable_abort_certificate[source_dispatch]:
  map_every qx_gen_tac [`a`,`b`,`name`] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "edge_ab") (mk_asm "fetch_a")) >>
  `a IN V` by
    (asm "edge_ab" (fn th =>
       qpat_assum `!a b. edge a b ==> _` (strip_assume_tac o C MP th o SPECL [``a:num#num``,``b:num#num``])) >>
     first_assum ACCEPT_TAC) >>
  prune_fact [`Abbrev (Rows = _)`] `Rows p _ V level pc height need tag boolean edge`
    (drule_then (mp_tac o CONJUNCT2) o last o CONJUNCTS) >>
  asm "fetch_a" (fn th =>
    CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV staticAbortOptPruneUnreachableCheckTheory.check_case_presentation)) >>
    pure_rewrite_tac [th, asmIRTheory.asm_inst_case_def] >> BETA_TAC) >>
  asm "edge_ab" (fn th =>
    let val stop = disch_then (qspec_then `b` mp_tac o last o CONJUNCTS) >>
                   rewrite_tac [th]
    in IF_CASES_TAC >- stop >> IF_CASES_TAC >- stop >> IF_CASES_TAC >- stop end) >>
  Cases_on `ALOOKUP dup_table name` >> simp[] >>
  Cases_on `ALOOKUP swap_table name` >> simp[] >>
  Cases_on `name="JUMP"` >> Cases_on `name="JUMPI"` >>
  simp[] >> disch_then strip_assume_tac >> goal_assum (drule_at Any)
QED

Resume prune_unreachable_abort_certificate[packed_rows]:
  disch_then (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS) (mk_asm "pack")) >>
  mp_tac (CONV_RULE prune_lets (Q.SPECL
    [`pre`,`opn`,`x`,`tail`,`V`,`e`,`pc`,`height`,`tag`,`boolean`,`edge`]
    (CONV_RULE prune_lets prune_one_rooted_flow))) >>
  (impl_tac >- suspend "flow_input") >>
  disch_then (fn flow =>
    mk_asm "dst_flow" (CONJUNCT2 flow) >>
    asm_x "pack" (fn pack =>
      mp_tac (MATCH_MP (SIMP_RULE bool_ss [] pack) (SIMP_RULE bool_ss [] flow)))) >>
  suspend "actual_root"
QED

Resume prune_unreachable_abort_certificate[flow_input]:
  prune_eqs [`Abbrev (p = _)`, `Abbrev (q = _)`] (fn eqs =>
    pure_once_rewrite_tac (map GSYM eqs)) >>
  ntac 2 (conj_tac >- (TRY (prune_fact [`Abbrev (Reach = _)`]
    `!v. v IN V ==> Reach edge e v` ACCEPT_TAC) >> first_assum ACCEPT_TAC)) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!x y. edge x y ==> _ /\ _ /\ _ /\ _ /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      prune_expand [`Abbrev (Flow = _)`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      prune_fact [`Abbrev (Flow = _)`] `Flow p pc height tag boolean _ _` ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  prune_fact [`Abbrev (p = _)`, `Abbrev (q = _)`]
    `!a. a IN V ==> pc a <> _ /\ _ /\ _`
    (fn th => prune_expand [`Abbrev (p = _)`, `Abbrev (q = _)`] >> ACCEPT_TAC th)
QED

Resume prune_unreachable_abort_certificate[actual_root]:
  disch_then (CONJUNCTS_THEN2 (mk_asm "dst_rows")
    (CONJUNCTS_THEN2 (mk_asm "dst_legal") kall_tac)) >>
  mp_tac (Q.SPECL [`opn`,`orig`,`j`,`u`,`t`,`t.as_call_ctx`,`t.as_requests`]
    (Q.GENL [`t`,`p0`,`n`,`ss`,`a`,`cc`,`req`]
      (CONV_RULE prune_lets prune_one_actual_root))) >>
  (impl_tac >- suspend "actual_root_inputs") >>
  suspend "interpret_rows"
QED

Resume prune_unreachable_abort_certificate[actual_root_inputs]:
  prune_eqs [`Abbrev (p = _)`,`Abbrev (q = _)`] (fn eqs =>
    pure_once_rewrite_tac (map GSYM eqs)) >>
  prune_fact [`Abbrev (Shape = _)`] `Shape p _ _ pc height need tag boolean e t`
    (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (prune_fact [`Abbrev (env0 = _)`,`Abbrev (bytes = _)`]
    `sym_steps p env0 j _ = SymOK u` ACCEPT_TAC) >>
  TRY (prune_fact [`Abbrev (bytes = _)`] `s.as_code = bytes orig` ACCEPT_TAC) >>
  TRY (prune_fact [`Abbrev (bytes = _)`] `asm_sym_rel p _ t u` ACCEPT_TAC) >>
  simp_tac bool_ss []
QED

Resume prune_unreachable_abort_certificate[interpret_rows]:
  qpat_abbrev_tac `uq = asmSymPc$sym_with_pc _ u` >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "sym_run")
    (qx_choose_then `tq` (map_every assume_tac o CONJUNCTS))) >>
  `tq.as_call_ctx = t.as_call_ctx /\ tq.as_requests = t.as_requests`
    by (simp[Abbr `uq`, asmSymPcTheory.sym_with_pc_def] >> metis_tac[]) >>
  prune_eqs [`Abbrev (tagQ = _)`, `Abbrev (pick = _)`, `Abbrev (r = _)`,
              `Abbrev (d = _)`, `Abbrev (q = _)`] (fn eqs =>
    mp_tac (REWRITE_RULE [DIFF_EMPTY, RIGHT_EXISTS_AND_THM, ratTheory.RAT_OF_NUM_LES]
      (CONV_RULE prune_lets (PURE_REWRITE_RULE eqs (Q.SPECL
        [`q`,`uq`,`tq`,`V`,`e`,`\z. rat_of_num (level z)`,
         `(r:num->num) o pc`,`height`,`need`,`tagQ`,`boolean`,`edge`]
        pending_rows_rooted_package))))) >>
  (impl_tac >- suspend "interpreter_inputs") >>
  suspend "destination_package"
QED

Resume prune_unreachable_abort_certificate[interpreter_inputs]:
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "interpreter_rows" >>
  conj_tac >- suspend "interpreter_edges" >>
  suspend "interpreter_root"
QED

val prune_norm = TOP_DEPTH_CONV (FIRST_CONV
  [BETA_CONV, REWR_CONV LET_THM, REWR_CONV DIFF_EMPTY,
   HO_REWR_CONV staticAbortOptPruneUnreachableCheckTheory.check_case_presentation]);

Resume prune_unreachable_abort_certificate[interpreter_rows]:
  qpat_assum `tq.as_call_ctx = t.as_call_ctx` SUBST1_TAC >>
  asm "dst_rows" (map_every assume_tac o CONJUNCTS o CONV_RULE prune_norm) >>
  CONV_TAC prune_norm >>
  conj_tac >- (first_assum ACCEPT_TAC ORELSE suspend "interpreter_slots") >>
  reverse conj_tac >- (first_assum ACCEPT_TAC ORELSE suspend "interpreter_dispatch") >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!a b. edge a b ==> a IN V /\ b IN V /\ level b < level a`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  asm "dst_flow" (drule_then ACCEPT_TAC o SIMP_RULE bool_ss [] o CONV_RULE prune_norm)
QED

Resume prune_unreachable_abort_certificate[interpreter_edges]:
  rpt gen_tac >> disch_tac >> conj_tac
  >- asm "dst_flow" (drule_then ACCEPT_TAC o SIMP_RULE bool_ss [] o CONV_RULE prune_norm) >>
  asm "dst_legal" (drule_then mp_tac) >>
  simp_tac bool_ss [RIGHT_EXISTS_AND_THM]
QED

Resume prune_unreachable_abort_certificate[interpreter_root]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp_tac bool_ss []
QED

Resume prune_unreachable_abort_certificate[interpreter_slots]:
  rpt gen_tac >> disch_tac >>
  qpat_assum `!v. v IN V ==> (need v ==> _) /\ _ /\ _`
    (drule_then (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (mk_asm "dst_tags")))) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >> asm "dst_tags" (drule_then strip_assume_tac) >>
  simp[] >> metis_tac[]
QED

Resume prune_unreachable_abort_certificate[interpreter_dispatch]:
  gen_tac >> disch_tac >>
  qpat_assum `!v. v IN V ==> _ < LENGTH _ /\ _`
    (drule_then mp_tac) >>
  CONV_TAC (TOP_DEPTH_CONV
    (HO_REWR_CONV (GSYM staticAbortOptPruneUnreachableCheckTheory.check_case_presentation))) >>
  simp_tac bool_ss [RIGHT_EXISTS_AND_THM]
QED

Resume prune_unreachable_abort_certificate[destination_package]:
  disch_then (CONJUNCTS_THEN2 (mk_asm "live_root")
    (CONJUNCTS_THEN2 (mk_asm "live_reach")
    (CONJUNCTS_THEN2 (mk_asm "live_rows")
    (CONJUNCTS_THEN2 (mk_asm "live_open") (mk_asm "live_shape"))))) >>
  qabbrev_tac `live_set = {x | x IN V /\ Reach edge e x}` >>
  qabbrev_tac `live_edge = \x y. x IN live_set /\ edge x y` >>
  qexistsl [`j`,`tq`,`uq`,`live_set`,`e`,`level`,`(r:num->num) o pc`,
            `height`,`need`,`tagQ`,`boolean`,`live_edge`] >>
  prune_expand [`Abbrev (bytes = _)`, `Abbrev (tagQ = _)`, `Abbrev (pick = _)`,
                `Abbrev (r = _)`, `Abbrev (d = _)`, `Abbrev (q = _)`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (prune_expand [`Abbrev (env0 = _)`, `Abbrev (bytes = _)`] >>
                asm "sym_run" ACCEPT_TAC) >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `tq.as_requests = t.as_requests` SUBST1_TAC >>
                first_assum ACCEPT_TAC) >>
  prune_expand [`Abbrev (live_edge = _)`, `Abbrev (live_set = _)`, `Abbrev (Reach = _)`] >>
  prune_expand [`Abbrev (Rows = _)`, `Abbrev (Open = _)`, `Abbrev (Shape = _)`,
                `Abbrev (Flow = _)`, `Abbrev (target = _)`] >>
  CONV_TAC prune_norm >>
  conj_tac >- suspend "destination_rows" >>
  conj_tac >- suspend "destination_open" >>
  conj_tac >- asm "live_root" ACCEPT_TAC >>
  conj_tac >- asm "live_reach" ACCEPT_TAC >>
  asm "live_shape" (mp_tac o CONV_RULE prune_norm) >>
  simp_tac bool_ss [RIGHT_EXISTS_AND_THM] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume prune_unreachable_abort_certificate[destination_rows]:
  asm "live_rows" (map_every assume_tac o CONJUNCTS o
    SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM, CONJ_ASSOC] o CONV_RULE prune_norm) >>
  simp_tac bool_ss [RIGHT_EXISTS_AND_THM, CONJ_ASSOC] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume prune_unreachable_abort_certificate[destination_open]:
  asm "live_open" (map_every assume_tac o CONJUNCTS o
    SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM, CONJ_ASSOC] o CONV_RULE prune_norm) >>
  simp_tac bool_ss [RIGHT_EXISTS_AND_THM, CONJ_ASSOC] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise prune_unreachable_abort_certificate
