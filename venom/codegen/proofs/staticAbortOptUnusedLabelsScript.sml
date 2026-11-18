Theory staticAbortOptUnusedLabels
Ancestors
  staticAbortOptUnusedLabelsWalk staticAbortOptUnusedLabelsSelect
  staticAbortOptUnusedLabelsRoot staticAbortOptUnusedLabelsSlots
  staticAbortOptUnusedLabelsFlow staticAbortOptUnusedLabelsCheck
  staticAbortOptMergeIszeroBranchPackage asmOptPruneUnused asmSplice
  asmSymSem asmSymBridge asmDataEnv codegenSymRel asmSem asmIR asmOptimizer
  asmWf staticAbortStraight symFrameControl stackOpSim finalizerContract
  finite_map pred_set rich_list list words arithmetic rat alist

Theorem prune_unused_jumpdests_abort_certificate:
  !orig (s:asm_state) data req_bound.
  let Shape = \p cc req pc height need tag boolean (i:num#num) (t:asm_state).
    t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need i ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest /\
         EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))
  in
  let Flow = \p pc height tag boolean (x:num#num) (y:num#num).
    let hi = height x; hj = height y; ins = EL (pc x) p in
    let inherit =
      \(src:num -> num option) (fresh:num -> (string#num) option) (bnew:num -> bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
             ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))
    in
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
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
               let a = asm_op_arity name; m = hj + asm_op_arity name - hi in
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
                       ins t = AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F
  in
  let target = \p pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)
  in
  let Control = \p pc tag x y.
    if EL (pc x) p = AsmOp "JUMP" then target p pc tag x y
    else if EL (pc x) p = AsmOp "JUMPI" then pc y=pc x+1 \/ target p pc tag x y
    else pc y=pc x+1
  in
  let Slots = \p cc (V:(num#num)->bool) height need tag boolean.
    !x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)
  in
  let Check = \p cc pc height tag edge (x:num#num).
    let h = height x in
    let fall = \y. pc y = pc x+1 in
    let arm = \P n. ?y. edge x y /\ P y /\ height y=n in
    let legal = \P n. !y. edge x y ==> P y /\ height y=n in
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
    | _ => F
  in
  let Rows = \p cc V (rank:(num#num)->num) pc height need tag boolean edge.
    Slots p cc V height need tag boolean /\
    (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Flow p pc height tag boolean x y) /\
    (!x. x IN V ==> pc x < LENGTH p /\ Check p cc pc height tag edge x)
  in
  let Open = \p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need tag boolean edge.
    let S = Shape p cc req pc height need tag boolean in
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\ Control p pc tag x y) /\
    (!x t. x IN V DIFF X /\ S x t ==>
       (?u. (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
                         p 1 t = AsmRevert u \/
             asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
                         p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
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
  !p. M_R p ==> M_R (FST (prune_unused_jumpdests p))
Proof
  rpt gen_tac >>
  map_every (fn name => qmatch_goalsub_abbrev_tac name >>
    CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ Shape`,`LET _ Flow`,`LET _ target`,`LET _ Control`,
     `LET _ Slots`,`LET _ Check`,`LET _ Rows`,`LET _ Open`,`LET _ Reach`,
     `LET _ bytes`,`LET _ env0`,`LET _ M_R`] >>
  match_mp_tac unused_labels_filter_preserves_contextual >>
  map_every qx_gen_tac [`pre`,`l`,`tail`] >>
  qabbrev_tac `p = pre ++ [AsmLabel l] ++ tail` >>
  qabbrev_tac `q = pre ++ tail` >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "source")) >>
  `asm_refines p q` by
    (simp[Abbr `p`, Abbr `q`] >>
     irule (SRULE [asm_splice_ok_def, is_data_inst_def,
                  EVAL ``asm_label_refs []``, unused_label_window_refines]
              (Q.INST [`pat` |-> `[AsmLabel l]`, `repl` |-> `[]`]
                 asm_splice_window_refines)) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (M_R = _)` (fn th =>
    let
      val expand = REWRITE_RULE [markerTheory.Abbrev_def] th
      val norm = REWRITE_CONV [expand, LET_THM] THENC DEPTH_CONV BETA_CONV
    in
      qpat_assum `Abbrev (p = _)` (fn pth =>
        asm_x "source" (map_every assume_tac o CONJUNCTS o
          REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] pth)] o
          CONV_RULE norm)) >>
      CONV_TAC norm
    end) >>
  qpat_assum `Abbrev (q = _)` (fn th =>
    rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst orig` by
    (drule (iffLR asm_refines_def) >> disch_then drule >>
     strip_tac >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  `env0 = asm_data_env p (bytes p) /\ env0 = asm_data_env q (bytes q)` by
    (simp[Abbr `env0`, Abbr `bytes`] >>
     conj_tac >> irule asm_data_env_agree >> simp[]) >>
  (* E0719's inactive route:
  qpat_assum `Abbrev (M_R = _)` (fn th =>
    rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th, LET_THM]) >>
  map_every (fn pat => qpat_assum pat (fn th =>
    rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
    [`Abbrev (p = _)`,`Abbrev (q = _)`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `asm_refines p q` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `tail`,
                     `pat` |-> `[AsmLabel l]`, `repl` |-> `[]`]
                    asm_splice_window_refines) >>
     (impl_tac >-
       (qpat_assum `~MEM l _` mp_tac >>
        simp[Abbr `p`, asm_splice_ok_def, is_data_inst_def,
             label_refs_append, unused_label_window_refines] >>
        simp[asm_label_refs_def])) >>
     simp[Abbr `p`, Abbr `q`]) >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p` by
    fs[asm_refines_def] >> simp[] >>
  *)
  qpat_x_assum `(?n out. _) \/ (?j t u. _)` DISJ_CASES_TAC
  >- suspend "terminal"
  >> suspend "pending"
QED

Resume prune_unused_jumpdests_abort_certificate[terminal]:
  disj1_tac >>
  qpat_x_assum `?n out. _`
    (qx_choose_then `n` (qx_choose_then `out`
      (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `sp = s with as_code := bytes p` >>
  qabbrev_tac `sq = s with as_code := bytes q` >>
  `sp.as_pc = 0 /\ sq.as_pc = 0 /\
   sym_init sp = sym_init s /\ sym_init sq = sym_init s` by
    simp[Abbr `sp`, Abbr `sq`, sym_init_def] >>
  `asm_data_env_ok p env0 sp.as_code /\ asm_data_env_ok q env0 sq.as_code` by
    (simp[Abbr `sp`, Abbr `sq`] >> metis_tac[asm_data_env_ok_asm_data_env]) >>
  `sym_terminal (sym_run p env0 n (sym_init s))` by
    ((drule sym_steps_terminal_run >> disch_then (qspec_then `0` mp_tac) >> simp[] >> (gvs[]))) >>
  rpt (qpat_x_assum `env0 = asm_data_env _ _` kall_tac) >>
  drule (iffLR asm_refines_def) >> disch_then drule >>
  disch_then (drule_then strip_assume_tac o cj 3) >>
  `sym_terminal (sym_run q env0 fuel' (sym_init s))` by
    (drule sym_result_rel_terminal >> simp[]) >>
  `?m. sym_result_rel (sym_run p env0 n (sym_init s))
          (asm_result_sym (asm_steps (SND (compute_label_offsets p))
            (build_offset_to_pc p) p m sp))` by
    (qpat_assum `sym_init sp = _` (fn th =>
       once_rewrite_tac[GSYM th]) >> irule asm_sym_backward >> simp[]) >>
  `?k. sym_result_rel (sym_run q env0 fuel' (sym_init s))
          (asm_result_sym (asm_steps (SND (compute_label_offsets q))
            (build_offset_to_pc q) q k sq))` by
    (qpat_assum `sym_init sq = _` (fn th =>
       once_rewrite_tac[GSYM th]) >> irule asm_sym_backward >> simp[]) >>
  qabbrev_tac `resP = asm_steps (SND (compute_label_offsets p))
                           (build_offset_to_pc p) p m sp` >>
  qabbrev_tac `resQ = asm_steps (SND (compute_label_offsets q))
                           (build_offset_to_pc q) q k sq` >>
  qabbrev_tac `rp = sym_run p env0 n (sym_init s)` >>
  qabbrev_tac `rq = sym_run q env0 fuel' (sym_init s)` >>
  `sym_result_rel (asm_result_sym resP) rp` by
    (Cases_on `rp` >> Cases_on `resP` >>
     fs[asm_result_sym_def, sym_result_rel_def]) >>
  `sym_result_rel (asm_result_sym resP) (asm_result_sym resQ)` by
    metis_tac[sym_result_rel_trans] >>
  `sym_terminal (asm_result_sym resP)` by metis_tac[sym_result_rel_terminal] >>
  `(asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
      p (m + n) sp = resP)` by
    (Cases_on `resP` >> fs[asm_result_sym_def, sym_terminal_def] >>
     simp[Once asm_steps_add]) >>
  `resP = AsmRevert out \/ resP = AsmFault out` by
    (qpat_x_assum `asm_steps _ _ _ (m + n) sp = resP` mp_tac >>
     once_rewrite_tac[ADD_COMM] >> simp[asm_steps_add] >>
     qpat_x_assum `_ = AsmRevert out \/ _ = AsmFault out` STRIP_ASSUME_TAC >> simp[]) >>
  `?outQ. (resQ = AsmRevert outQ \/ resQ = AsmFault outQ) /\
           outQ.as_requests = out.as_requests` by
    (Cases_on `resQ` >> fs[asm_result_sym_def, sym_result_rel_def] >>
     qpat_x_assum `sym_obs _ = sym_obs _`
       (mp_tac o SRULE [sym_obs_def, sym_init_def] o AP_TERM ``asm_state_as_requests``) >>
     disch_then (ACCEPT_TAC o SYM)) >>
  `sym_terminal (sym_steps q env0 fuel' (sym_init s))` by
    (`sym_run q env0 fuel' (sym_init s) = sym_steps q env0 fuel' (sym_init s)` by
       (mp_tac (Q.SPECL [`fuel'`,`fuel'`,`sym_init s`]
          (Q.INST [`p` |-> `q`, `env` |-> `env0`] sym_run_terminal_steps)) >>
        Cases_on `sym_steps q env0 fuel' (sym_init s)` >> simp[]) >>
     qpat_x_assum `sym_run q _ _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
     qpat_x_assum `sym_terminal rq` mp_tac >> simp[Abbr `rq`]) >>
  `asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q)
     q (k + fuel') sq = resQ` by
    (once_rewrite_tac[asm_steps_add] >>
     qpat_assum `Abbrev (resQ = _)`
       (fn th => once_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     simp[]) >>
  qpat_x_assum `asm_steps _ _ q (k + fuel') sq = resQ`
    (assume_tac o ONCE_REWRITE_RULE [ADD_COMM]) >>
  qexistsl [`fuel' + k`,`outQ`] >> simp[sym_steps_terminal_extend]
QED

Resume prune_unused_jumpdests_abort_certificate[pending]:
  disj2_tac >>
  qpat_x_assum `?j t u. _`
    (qx_choose_then `j` (qx_choose_then `t` (qx_choose_then `u`
      (qx_choose_then `cc` (qx_choose_then `req` (qx_choose_then `V`
      (qx_choose_then `e` (qx_choose_then `rankN` (qx_choose_then `pc`
      (qx_choose_then `height` (qx_choose_then `need` (qx_choose_then `tag`
      (qx_choose_then `boolean` (qx_choose_then `edge`
        (map_every assume_tac o CONJUNCTS))))))))))))))) >>
  qpat_x_assum `Abbrev (M_R = _)` kall_tac >>
  `p = pre ++ [AsmLabel l] ++ tail` by simp[Abbr `p`] >>
  qpat_assum `Abbrev (q = _)` (fn th =>
    mp_tac (SIMP_RULE bool_ss [LET_THM, RAT_OF_NUM_LES, RIGHT_EXISTS_AND_THM,
               GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      (Q.INST [`rank` |-> `\x. rat_of_num (rankN x)`]
          (SPEC_ALL unused_label_one_selected_control)))) >>
  (* E0759's inactive whole-packet route:
  (impl_tac >-
    (simp[] >>
     qpat_assum `Open p cc req V {} rankN pc height need tag boolean edge` mp_tac >>
     qpat_assum `Rows p cc V rankN pc height need tag boolean edge` mp_tac >>
     qpat_assum `!x. x IN V ==> Reach edge e x` mp_tac >>
     simp[Abbr `Open`, Abbr `Rows`, Abbr `Reach`, Abbr `Shape`,
          Abbr `Control`, Abbr `target`, Abbr `Flow`, Abbr `Slots`, Abbr `Check`,
          IgnAsm `p = _`])) >>
  *)
  (* E0768's inactive interpolated-name projector:
  (impl_tac >-
    (let
       fun project pat names =
         let
           fun use_eqs [] eqs =
                 qpat_assum pat
                   (map_every assume_tac o CONJUNCTS o
                    SIMP_RULE bool_ss [LET_THM, RIGHT_EXISTS_AND_THM] o
                    (fn fact => foldl (fn (eq, acc) => SUBS [eq] acc) fact (rev eqs)))
             | use_eqs (name::rest) eqs =
                 qpat_assum `Abbrev (^name = _)`
                   (fn th => use_eqs rest (REWRITE_RULE [markerTheory.Abbrev_def] th :: eqs))
         in use_eqs names [] end
     in
       project `Open p cc req V {} rankN pc height need tag boolean edge`
         [``Open``, ``Shape``, ``Flow``, ``Control``, ``target``] >>
       project `Rows p cc V rankN pc height need tag boolean edge`
         [``Rows``, ``Slots``, ``Check``, ``Flow``, ``target``] >>
       project `!x. x IN V ==> Reach edge e x` [``Reach``]
     end >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     FAIL_TAC "first projection mismatch")) >>
  *)
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qpat_assum `Open p cc req V {} rankN pc height need tag boolean edge` mp_tac >>
          SIMP_TAC bool_ss [SimpLHS, LET_THM, RIGHT_EXISTS_AND_THM,
                            Abbr `Open`, Abbr `Shape`, Abbr `Flow`,
                            Abbr `Control`, Abbr `target`] >>
          disch_then (FIRST o map ACCEPT_TAC o CONJUNCTS) >> NO_TAC) >>
     TRY (qpat_assum `Rows p cc V rankN pc height need tag boolean edge` mp_tac >>
          SIMP_TAC bool_ss [SimpLHS, LET_THM, RIGHT_EXISTS_AND_THM,
                            Abbr `Rows`, Abbr `Slots`, Abbr `Check`,
                            Abbr `Flow`, Abbr `target`] >>
          disch_then (FIRST o map ACCEPT_TAC o CONJUNCTS) >> NO_TAC) >>
     TRY (qpat_assum `!x. x IN V ==> Reach edge e x` mp_tac >>
          SIMP_TAC bool_ss [SimpLHS, Abbr `Reach`] >>
          disch_then ACCEPT_TAC >> NO_TAC) >>
     TRY (qpat_assum `Open p cc req V {} rankN pc height need tag boolean edge` mp_tac >>
          SIMP_TAC bool_ss [SimpLHS, LET_THM, Abbr `Open`, Abbr `Flow`,
                            Abbr `Control`, Abbr `target`] >>
          disch_then (mp_tac o cj 5) >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          SIMP_TAC bool_ss [RIGHT_EXISTS_AND_THM, DIFF_EMPTY] >>
          disch_tac >> map_every qx_gen_tac [`v`,`w`] >> disch_tac >>
          first_x_assum (qspecl_then [`v`,`w`] mp_tac) >>
          (impl_tac >- first_assum ACCEPT_TAC) >>
          disch_then (map_every assume_tac o CONJUNCTS) >>
          asm_rewrite_tac[] >> NO_TAC) >>
     TRY (qpat_assum `Rows p cc V rankN pc height need tag boolean edge` mp_tac >>
          SIMP_TAC bool_ss [SimpLHS, LET_THM, Abbr `Rows`, Abbr `Flow`,
                            Abbr `Slots`, Abbr `Check`, Abbr `target`] >>
          disch_then (FIRST o map (fn th => mp_tac th >>
            SIMP_TAC bool_ss [RIGHT_EXISTS_AND_THM, DIFF_EMPTY] >> NO_TAC) o CONJUNCTS)) >>
     qpat_assum `Rows p cc V rankN pc height need tag boolean edge` mp_tac >>
     SIMP_TAC bool_ss [SimpLHS, LET_THM, Abbr `Rows`, Abbr `Slots`] >>
     disch_then (mp_tac o cj 1) >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[])) >>
  qpat_assum `p = pre ++ [AsmLabel l] ++ tail`
    (fn th => once_rewrite_tac[GSYM th]) >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (mk_asm "fetch")
      (CONJUNCTS_THEN2 (mk_asm "layout")
        (qx_choose_then `z` (CONJUNCTS_THEN2 (mk_asm "select") (mk_asm "control")))))) >>
  qabbrev_tac `r = splice_pc (LENGTH pre) 1 0` >>
  qabbrev_tac `pcQ = r o pc` >>
  qabbrev_tac `KQ = {x | x IN V /\ pc x <> LENGTH pre}` >>
  qabbrev_tac `TQ = \x k. OPTION_MAP (\(n,j). (n,r j)) (tag x k)` >>
  mp_tac (CONV_RULE (LAND_CONV (SIMP_CONV bool_ss [RIGHT_EXISTS_AND_THM]))
    (SIMP_RULE bool_ss [LET_THM, RAT_OF_NUM_LES]
    (Q.SPECL [`orig`,`p`,`pre`,`l`,`tail`,`data`,`s`,`j`,`u`,`t`,`cc`,`req`,
             `req_bound`,`V`,`e`,`\x. rat_of_num (rankN x)`,`pc`,`height`,
             `need`,`tag`,`boolean`,`edge`] unused_label_one_actual_root))) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (simp[Abbr `bytes`, Abbr `env0`, Abbr `q`, IgnAsm `p = _`] >> NO_TAC) >>
     TRY (qpat_assum `sym_steps p env0 j (sym_init s) = SymOK u` mp_tac >>
          SIMP_TAC bool_ss [Abbr `bytes`, Abbr `env0`] >> NO_TAC) >>
     TRY (qpat_assum `asm_sym_rel p _ t u` mp_tac >>
          SIMP_TAC bool_ss [Abbr `bytes`] >> NO_TAC) >>
     TRY (qpat_assum `Shape p cc req pc height need tag boolean e t` mp_tac >>
          SIMP_TAC bool_ss [SimpLHS, Abbr `Shape`, RIGHT_EXISTS_AND_THM] >>
          disch_then (FIRST o map ACCEPT_TAC o CONJUNCTS) >> NO_TAC) >>
     TRY (qpat_assum `Open p cc req V {} rankN pc height need tag boolean edge` mp_tac >>
          SIMP_TAC bool_ss [SimpLHS, LET_THM, Abbr `Open`, Abbr `Shape`, Abbr `Flow`,
                            Abbr `Control`, Abbr `target`, RIGHT_EXISTS_AND_THM] >>
          disch_then (FIRST o map ACCEPT_TAC o CONJUNCTS) >> NO_TAC) >>
     TRY (qpat_assum `!x. x IN V ==> Reach edge e x` mp_tac >>
          SIMP_TAC bool_ss [Abbr `Reach`] >> NO_TAC) >>
     TRY (qx_gen_tac `v` >> disch_tac >>
          qmatch_goalsub_rename_tac `need v ==> cc.cc_static` >>
          qpat_assum `Rows p cc V rankN pc height need tag boolean edge` mp_tac >>
          SIMP_TAC bool_ss [SimpLHS, LET_THM, Abbr `Rows`, Abbr `Slots`] >>
          disch_then (qspec_then `v` mp_tac o cj 1) >>
          (impl_tac >- first_assum ACCEPT_TAC) >> POP_ASSUM_LIST (K ALL_TAC) >>
          metis_tac[] >> NO_TAC) >>
     TRY (asm "layout" mp_tac >>
          simp[Abbr `r`, Abbr `q`, RIGHT_EXISTS_AND_THM, IgnAsm `p = _`] >> NO_TAC) >>
     qpat_assum `Open p cc req V {} rankN pc height need tag boolean edge` mp_tac >>
     SIMP_TAC bool_ss [SimpLHS, LET_THM, Abbr `Open`, Abbr `Flow`,
                       Abbr `Control`, Abbr `target`] >>
     disch_then (mp_tac o cj 5) >> POP_ASSUM_LIST (K ALL_TAC) >>
     SIMP_TAC bool_ss [RIGHT_EXISTS_AND_THM, DIFF_EMPTY] >>
     disch_tac >> map_every qx_gen_tac [`v`,`w`] >> disch_tac >>
     first_x_assum (qspecl_then [`v`,`w`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >> asm_rewrite_tac[])) >>
  let
    fun fold_abbr pat = qpat_assum pat (fn th =>
      CONV_TAC (LAND_CONV (PURE_REWRITE_CONV
        [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])))
  in
    map_every fold_abbr [`Abbrev (q = _)`,`Abbrev (r = _)`,
                         `Abbrev (pcQ = _)`,`Abbrev (KQ = _)`]
  end >>
  qabbrev_tac `uQ = sym_with_pc (r u.sym_base.as_pc) u` >>
  disch_then (qx_choose_then `jQ` (qx_choose_then `tQ` (qx_choose_then `eQ`
    (map_every assume_tac o CONJUNCTS)))) >>
  `Shape q cc req pcQ height need TQ boolean eQ tQ` by
    (SIMP_TAC bool_ss [Abbr `Shape`, Abbr `TQ`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `LegalQ = \x (a:bool#(num#num)). edge x (SND a) /\
     if FST a then (EL (pc x) p = AsmOp "JUMP" \/ EL (pc x) p = AsmOp "JUMPI") /\
                    target p pc tag x (SND a)
     else EL (pc x) p <> AsmOp "JUMP" /\ pc (SND a) = pc x+1` >>
  qabbrev_tac `edgeQ = \x y. x IN KQ /\ ?a. LegalQ x a /\ y = z x a` >>
  `!x y. edgeQ x y ==> x IN KQ /\ y IN KQ /\ rankN y < rankN x /\ Control q pcQ TQ x y` by
    (asm "control" mp_tac >>
     SIMP_TAC bool_ss [Abbr `edgeQ`, Abbr `LegalQ`, Abbr `Control`, Abbr `target`,
                      Abbr `KQ`, Abbr `pcQ`, Abbr `TQ`, Abbr `r`,
                      combinTheory.o_THM, RIGHT_EXISTS_AND_THM]) >>
  `FINITE KQ` by
    (`FINITE V` by
       (qpat_assum `Open p cc req V {} rankN pc height need tag boolean edge` mp_tac >>
        SIMP_TAC bool_ss [SimpLHS, LET_THM, Abbr `Open`] >>
        disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     irule SUBSET_FINITE_I >> qexists `V` >> simp[SUBSET_DEF, Abbr `KQ`]) >>
  qpat_assum `Rows p cc V rankN pc height need tag boolean edge` (fn th =>
    qpat_assum `Abbrev (Rows = _)` (fn eq =>
      map_every assume_tac (CONJUNCTS (SIMP_RULE bool_ss [LET_THM,
        REWRITE_RULE [markerTheory.Abbrev_def] eq] th)))) >>
  `!x y name. x IN V /\ edge x y /\ EL (pc x) p = AsmOp name ==>
      IS_SOME (ALOOKUP dup_table name) \/ IS_SOME (ALOOKUP swap_table name) \/
      name = "JUMP" \/ name = "JUMPI" \/ (?m. static_abort_straight name m)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!v. v IN V ==> pc v < LENGTH p /\ Check p cc pc height tag edge v`
       (fn th => qpat_assum `x IN V` (fn hx =>
         qpat_assum `Abbrev (Check = _)` (fn eq =>
           qpat_assum `EL (pc x) p = AsmOp name` (fn fetch =>
             qpat_assum `edge x y` (fn step =>
               let
                 val dispatch = SIMP_RULE (srw_ss())
                   [LET_THM, Excl "MEM", REWRITE_RULE [markerTheory.Abbrev_def] eq, fetch]
                   (CONJUNCT2 (MATCH_MP th hx))
               in
                 POP_ASSUM_LIST (K ALL_TAC) >> assume_tac step >> mk_asm "dispatch" dispatch
               end))))) >>
     Cases_on `name = "INVALID"`
     >- (asm_x "dispatch" mp_tac >> simp[] >> metis_tac[]) >>
     Cases_on `name = "REVERT"`
     >- (asm_x "dispatch" mp_tac >> simp[] >> metis_tac[]) >>
     Cases_on `MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]` >>
     rule_assum_tac (REWRITE_RULE [listTheory.MEM]) >-
       (asm_x "dispatch" mp_tac >> simp[] >> metis_tac[]) >>
     Cases_on `ALOOKUP dup_table name` >> simp[] >>
     Cases_on `ALOOKUP swap_table name` >> simp[] >>
     Cases_on `name = "JUMP"` >> simp[] >>
     Cases_on `name = "JUMPI"` >> simp[] >>
     asm_x "dispatch" mp_tac >> simp[Excl "MEM"] >> metis_tac[]) >>
  `!x. x IN KQ ==> x IN V` by simp[Abbr `KQ`] >>
  (* Slots' indices here are natural numbers, as required by Rows. *)
  `Slots q cc KQ height need TQ boolean` by
    (SIMP_TAC bool_ss [Abbr `Slots`] >>
     qx_gen_tac `x` >> strip_tac >>
     `x IN V` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     qpat_assum `Slots p cc V height need tag boolean` mp_tac >>
     BETA_TAC >>
     disch_then (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[Abbr `TQ`] >>
     rpt gen_tac >> SIMP_TAC bool_ss [Abbr `TQ`, optionTheory.OPTION_MAP_EQ_SOME] >>
     strip_tac >> rename1 `tag x k = SOME old` >> PairCases_on `old` >>
     qpat_x_assum `(l',origin) = _`
       (STRIP_ASSUME_TAC o REWRITE_RULE [pairTheory.PAIR_EQ] o
        BETA_RULE o REWRITE_RULE [pairTheory.UNCURRY]) >>
     qpat_assum `!k l origin. tag x k = SOME(l,origin) ==> _`
       (qspecl_then [`k`,`old0`,`old1`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (K ALL_TAC)
       (CONJUNCTS_THEN2 assume_tac (qx_choose_then `off` (qx_choose_then `dest` strip_assume_tac))))) >>
     asm "layout" (qspecl_then [`x`,`k`,`old0`,`old1`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (fn th => (map_every assume_tac (List.take (CONJUNCTS th,4)) >>
       qspec_then `dest` mp_tac (List.last (CONJUNCTS th)))) >>
     (impl_tac >- (qexists `off` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `new_off` strip_assume_tac o cj 4) >>
     qpat_x_assum `l' = old0` SUBST1_TAC >>
     qpat_x_assum `origin = r old1` SUBST1_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `EL (r old1) q = _` (fn th => rewrite_tac[th]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`new_off`,`r dest`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm "select" (mp_tac o SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]) >>
  disch_then (qx_choose_then `HQ` (qx_choose_then `srcQ` (qx_choose_then `freshQ`
    (qx_choose_then `bnewQ` (mk_asm "choices"))))) >>
  `!x. x IN KQ ==> pcQ x < LENGTH q /\ Check q cc pcQ height TQ edgeQ x` by
    (mp_tac (SIMP_RULE bool_ss [LET_THM, RIGHT_EXISTS_AND_THM]
       (Q.SPECL [`pre`,`l`,`tail`,`cc`,`V`,`pc`,`height`,`tag`,`edge`,`HQ`,`z`]
         unused_label_one_selected_check)) >>
     let
       fun fold pat = qpat_assum pat (fn th =>
         CONV_TAC (LAND_CONV (PURE_REWRITE_CONV
           [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])))
     in
       map_every fold [`Abbrev (p = _)`,`Abbrev (q = _)`,`Abbrev (r = _)`,
                       `Abbrev (pcQ = _)`,`Abbrev (KQ = _)`,`Abbrev (TQ = _)`]
     end >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >-
          (qx_gen_tac `x` >> disch_tac >>
           qpat_assum `!x. x IN V ==> pc x < LENGTH p /\ _`
             (drule_then (mp_tac o CONJUNCT2)) >>
           SIMP_TAC bool_ss [Abbr `Check`, Abbr `target`, LET_THM, RIGHT_EXISTS_AND_THM]) >>
        conj_tac >- asm "fetch" ACCEPT_TAC >>
        let
          fun arm n tt =
            map_every qx_gen_tac [`x`,`a`] >>
            disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "legal")) >>
            asm "choices" (qspec_then `x` mp_tac) >>
            (impl_tac >- first_assum ACCEPT_TAC) >>
            disch_then (qspec_then `a` mp_tac o cj n) >>
            (impl_tac >- asm "legal" ACCEPT_TAC) >> disch_then tt
        in
          conj_tac >- arm 2 (ACCEPT_TAC o cj 1) >>
          arm 3 (fn th => map_every assume_tac (CONJUNCTS th)) >>
          rpt conj_tac >> first_assum ACCEPT_TAC
        end)) >>
     disch_then (mk_asm "checked") >> qx_gen_tac `x` >> disch_tac >>
     conj_tac >- asm "fetch" (drule_then (ACCEPT_TAC o CONJUNCT1)) >>
     asm "checked" (drule_then mp_tac) >>
     SIMP_TAC bool_ss [Abbr `Check`, Abbr `target`, Abbr `edgeQ`, Abbr `LegalQ`,
                       Abbr `TQ`, LET_THM, RIGHT_EXISTS_AND_THM] >>
     asm "fetch" (drule_then (fn th => rewrite_tac[CONJUNCT2 th])) >>
     qpat_assum `x IN KQ` (fn th => SIMP_TAC bool_ss [th])) >>
  `!x y. edgeQ x y ==> Flow q pcQ height TQ boolean x y` by
    (mp_tac (SIMP_RULE bool_ss [LET_THM, RIGHT_EXISTS_AND_THM]
       (Q.SPECL [`pre`,`l`,`tail`,`V`,`pc`,`height`,`tag`,`boolean`,`edge`,
                 `srcQ`,`freshQ`,`bnewQ`,`HQ`,`z`] unused_label_one_selected_flow)) >>
     let
       fun fold pat = qpat_assum pat (fn th =>
         CONV_TAC (LAND_CONV (PURE_REWRITE_CONV
           [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])))
     in
       map_every fold [`Abbrev (p = _)`,`Abbrev (q = _)`,`Abbrev (r = _)`,
                       `Abbrev (pcQ = _)`,`Abbrev (KQ = _)`,`Abbrev (TQ = _)`]
     end >>
     (impl_tac >-
       (conj_tac >- asm "fetch" ACCEPT_TAC >>
        map_every qx_gen_tac [`x`,`a`] >>
        disch_then (CONJUNCTS_THEN2 (mk_asm "keep") (mk_asm "legal")) >>
        asm "choices" (qspec_then `x` mp_tac) >>
        (impl_tac >- asm "keep" ACCEPT_TAC) >>
        disch_then (CONJUNCTS_THEN2 (mk_asm "desc")
          (CONJUNCTS_THEN2 (qspec_then `a` (mp_tac o cj 1)) (mk_asm "selected"))) >>
        (impl_tac >- asm "legal" ACCEPT_TAC) >> disch_tac >>
        asm "legal" (assume_tac o CONJUNCT1) >>
        reverse conj_tac >-
          (reverse conj_tac >-
            (asm "selected" (qspec_then `a` mp_tac) >>
             (impl_tac >- asm "legal" ACCEPT_TAC) >>
             disch_then (map_every assume_tac o CONJUNCTS) >>
             rpt conj_tac >> first_assum ACCEPT_TAC) >>
           `x IN V` by (first_x_assum irule >> asm "keep" ACCEPT_TAC) >>
           rpt strip_tac >>
           qpat_assum `!x y name. x IN V /\ edge x y /\ EL (pc x) p = AsmOp name ==> _`
             irule >>
           qexistsl [`x`,`SND a`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
        qpat_assum `!v w. edge v w ==> _ /\ _ /\ _ /\ Flow p pc height tag boolean v w`
          (drule_then (mp_tac o cj 4)) >>
        asm "desc" mp_tac >>
        SIMP_TAC bool_ss [Abbr `Flow`, LET_THM] >>
        qpat_assum `height (SND a) = HQ x` (fn th => rewrite_tac[th]) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `EL (pc x) p` >> simp[pairTheory.PAIR_EQ] >>
        rename1 `AsmOp name` >>
        Cases_on `ALOOKUP dup_table name` >> simp[pairTheory.PAIR_EQ] >>
        Cases_on `ALOOKUP swap_table name` >> simp[pairTheory.PAIR_EQ] >>
        rpt strip_tac >> metis_tac[])) >>
     disch_then (mk_asm "flowRows") >>
     map_every qx_gen_tac [`x`,`y`] >> disch_tac >>
     `x IN KQ` by (fs[Abbr `edgeQ`]) >>
     asm "fetch" (qspec_then `x` (drule_then
       (mk_asm "rowfetch" o SIMP_RULE bool_ss [combinTheory.o_THM] o CONJUNCT2))) >>
     asm "flowRows" (qspecl_then [`x`,`y`] mp_tac) >>
     (impl_tac >-
       (qpat_x_assum `edgeQ x y` mp_tac >>
        SIMP_TAC bool_ss [Abbr `edgeQ`, Abbr `LegalQ`, Abbr `target`,
                          Abbr `KQ`, LET_THM, RIGHT_EXISTS_AND_THM])) >>
     SIMP_TAC bool_ss [Abbr `Flow`, Abbr `TQ`, Abbr `pcQ`, combinTheory.o_THM,
                       LET_THM, RIGHT_EXISTS_AND_THM] >>
     (* The earlier single rewrite normalized only the worker fetch. *)
     asm "rowfetch" (fn th =>
       rewrite_tac[th, PURE_REWRITE_RULE [combinTheory.o_THM] th])) >>
  (* Restrict the one transported table to occurrences reachable from eQ. *)
  `Rows q cc KQ rankN pcQ height need TQ boolean edgeQ` by
    (SIMP_TAC bool_ss [Abbr `Rows`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!x y. edgeQ x y ==> _ /\ _ /\ _ /\ Control q pcQ TQ x y`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       qpat_assum `!x y. edgeQ x y ==> Flow q pcQ height TQ boolean x y`
         (drule_then ACCEPT_TAC))) >>
  qabbrev_tac `liveSet = {x | x IN KQ /\ Reach edgeQ eQ x}` >>
  qabbrev_tac `liveEdge = \x y. x IN liveSet /\ edgeQ x y` >>
  let
    val normalize = TOP_DEPTH_CONV (FIRST_CONV
      [BETA_CONV, REWR_CONV LET_THM, REWR_CONV DIFF_EMPTY,
       REWR_CONV ratTheory.RAT_OF_NUM_LES])
  in
    qpat_assum `tQ.as_call_ctx = cc` (fn cth =>
      qpat_assum `tQ.as_requests = req` (fn rth =>
        mp_tac (PURE_REWRITE_RULE [cth,rth] (CONV_RULE normalize
          (Q.SPECL [`q`,`uQ`,`tQ`,`KQ`,`eQ`,`\x. rat_of_num (rankN x)`,
                    `pcQ`,`height`,`need`,`TQ`,`boolean`,`edgeQ`]
            pending_rows_rooted_package)))))
  end >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `Rows q cc KQ rankN pcQ height need TQ boolean edgeQ` mp_tac >>
        (* Inactive whole-Rows simplifier:
        SIMP_TAC bool_ss [NoAsms, Abbr `Rows`, Abbr `Slots`, Abbr `Check`,
                          Abbr `Flow`, Abbr `target`, LET_THM]
        *)
        map_every (fn pat => qpat_assum pat (fn th =>
          pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]))
          [`Abbrev (Rows = _)`,`Abbrev (Slots = _)`,`Abbrev (Check = _)`,
           `Abbrev (Flow = _)`,`Abbrev (target = _)`] >>
        CONV_TAC (TOP_DEPTH_CONV (FIRST_CONV [BETA_CONV, REWR_CONV LET_THM])) >>
        disch_then ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> disch_tac >>
        qpat_assum `!x y. edgeQ x y ==> Flow q pcQ height TQ boolean x y`
          (drule_then mp_tac) >>
        qpat_assum `!x y. edgeQ x y ==> _ /\ _ /\ _ /\ Control q pcQ TQ x y`
          (drule_then (mp_tac o cj 4)) >>
        SIMP_TAC bool_ss [Abbr `Control`, Abbr `Flow`, Abbr `target`, LET_THM]) >>
     conj_tac >-
       (qpat_assum `Shape q cc req pcQ height need TQ boolean eQ tQ` mp_tac >>
        (* Inactive contextual simp: SIMP_TAC bool_ss [Abbr `Shape`, RIGHT_EXISTS_AND_THM] *)
        qpat_assum `Abbrev (Shape = _)` (fn th =>
          pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
        BETA_TAC >>
        map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac [th]))
          [`tQ.as_call_ctx = cc`,`tQ.as_requests = req`] >>
        disch_then ACCEPT_TAC) >>
     SIMP_TAC bool_ss [Abbr `TQ`] >>
     conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "live") >>
  qexistsl [`jQ`,`tQ`,`uQ`,`cc`,`req`,`liveSet`,`eQ`,`rankN`,
            `pcQ`,`height`,`need`,`TQ`,`boolean`,`liveEdge`] >>
  ntac 10 (conj_tac >-
    (first_assum ACCEPT_TAC ORELSE
     simp[Abbr `bytes`, IgnAsm `p = _`, IgnAsm `q = _`])) >>
  asm "live" mp_tac >>
  map_every (fn pat => qpat_assum pat (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]))
    [`Abbrev (liveEdge = _)`,`Abbrev (liveSet = _)`,`Abbrev (Reach = _)`,
     `Abbrev (Rows = _)`,`Abbrev (Slots = _)`,`Abbrev (Check = _)`,
     `Abbrev (Open = _)`,`Abbrev (Shape = _)`,`Abbrev (Control = _)`,
     `Abbrev (Flow = _)`,`Abbrev (target = _)`] >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac [th]))
    [`tQ.as_call_ctx = cc`,`tQ.as_requests = req`] >>
  CONV_TAC (TOP_DEPTH_CONV (FIRST_CONV
    [BETA_CONV, REWR_CONV LET_THM, REWR_CONV DIFF_EMPTY])) >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise prune_unused_jumpdests_abort_certificate
