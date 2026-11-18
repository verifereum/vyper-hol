Theory staticAbortOptMergeJumpdestsReplay
Ancestors asmRunBounded[qualified,ignore_grammar] symShuffleSim[qualified,ignore_grammar] numeral[qualified,ignore_grammar] bool[qualified,ignore_grammar] num[qualified,ignore_grammar]
  staticAbortOptMergeJumpdestsOrdinary staticAbortOptMergeJumpdestsPrefix
  asmOptMergeJumpdests asmOptimizer asmSymSem asmSem asmSplice codegenSymRel
  symInstPieces list arithmetic

(* Only a taken transfer whose two destination heads differ needs a bypass. *)
Theorem merge_taken_or_sync[local]:
  let q = MAP (rename_push_label x y) p in
  let I = EL a.sym_base.as_pc p in
  rn_rel x y a b /\ a.sym_base.as_pc < LENGTH p /\
  (I = AsmOp "JUMP" \/ I = AsmOp "JUMPI") /\
  sym_steps p env 1 a = SymOK t ==>
  (?t'. sym_steps q env 1 b = SymOK t' /\ rn_rel x y t t') \/
  (?stk stk'. x <> y /\ a.sym_stack = Lab x 0 :: stk /\
              b.sym_stack = Lab y 0 :: stk' /\
    (I = AsmOp "JUMP" \/
     (I = AsmOp "JUMPI" /\ ?c rest. stk = Val c :: rest /\ c <> 0w)))
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `b.sym_base = a.sym_base /\ a.sym_base.as_stack = [] /\
   LIST_REL (sv_rel x y) a.sym_stack b.sym_stack` by fs[rn_rel_def] >>
  Cases_on `a.sym_stack`
  >- gvs[sym_steps_pos,sym_steps_def,EL_MAP,rename_push_label_def,
         sym_step_def,sym_step_op_def,sym_jump_def,sym_jumpi_def] >>
  rename1 `a.sym_stack = h :: stk` >>
  `?h' stk'. b.sym_stack = h' :: stk' /\ sv_rel x y h h' /\
             LIST_REL (sv_rel x y) stk stk'` by fs[LIST_REL_CONS1] >>
  Cases_on `EL a.sym_base.as_pc p = AsmOp "JUMP"`
  >- (Cases_on `h' = h`
      >- (Cases_on `sym_jump_dest p h` >>
          gvs[sym_steps_pos,sym_steps_def,EL_MAP,rename_push_label_def,
              sym_step_def,sym_step_op_def,sym_jump_def,sym_jump_dest_rename,
              rn_rel_def]) >>
      disj2_tac >> qexistsl [`stk`,`stk'`] >> fs[sv_rel_def] >> metis_tac[]) >>
  `EL a.sym_base.as_pc p = AsmOp "JUMPI"` by fs[] >>
  Cases_on `stk`
  >- gvs[sym_steps_pos,sym_steps_def,EL_MAP,rename_push_label_def,
         sym_step_def,sym_step_op_def,sym_jumpi_def] >>
  rename1 `a.sym_stack = h :: cval :: rest` >>
  Cases_on `cval`
  >- (rename1 `a.sym_stack = h :: Val c :: rest` >>
      `?rest'. stk' = Val c :: rest' /\ LIST_REL (sv_rel x y) rest rest'`
        by fs[LIST_REL_CONS1,sv_rel_val] >>
      Cases_on `c = 0w`
      >- gvs[sym_steps_pos,sym_steps_def,EL_MAP,rename_push_label_def,
             sym_step_def,sym_step_op_def,sym_jumpi_def,sym_set_stack_def,
             rn_rel_def,asm_next_def] >>
      Cases_on `h' = h`
      >- (Cases_on `sym_jump_dest p h` >>
          gvs[sym_steps_pos,sym_steps_def,EL_MAP,rename_push_label_def,
              sym_step_def,sym_step_op_def,sym_jumpi_def,sym_jump_dest_rename,
              rn_rel_def]) >>
      disj2_tac >> qexistsl [`Val c :: rest`,`stk'`] >>
      fs[sv_rel_def] >> metis_tac[]) >>
  gvs[sym_steps_pos,sym_steps_def,EL_MAP,rename_push_label_def,
      sym_step_def,sym_step_op_def,sym_jumpi_def]
QED

(* Before recurring, either consume a nonempty source chunk and one
   destination step, or stop immediately before the short transfer. *)
Theorem merge_replay_chunk[local]:
  let q = MAP (rename_push_label x y) p in
  let d = if next = AsmLabel y then 1 else 3 in
  let I = EL a.sym_base.as_pc p in
  asm_static_wf p /\ p = pre ++ [AsmLabel x; next; third] ++ tail /\
  ((next = AsmLabel y /\ y <> x) \/
   (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
  rn_rel x y a b /\ sym_steps p env (SUC r) a = SymOK e ==>
  (?k u v. 0 < k /\ k <= SUC r /\
     sym_steps p env k a = SymOK u /\ sym_steps q env 1 b = SymOK v /\
     rn_rel x y u v /\ sym_steps p env (SUC r - k) u = SymOK e) \/
  (?stk stk'. r < d /\ a.sym_base.as_pc < LENGTH p /\ x <> y /\
     a.sym_stack = Lab x 0 :: stk /\ b.sym_stack = Lab y 0 :: stk' /\
     (I = AsmOp "JUMP" \/
      (I = AsmOp "JUMPI" /\ ?c rest. stk = Val c :: rest /\ c <> 0w)))
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `p = _` (mk_asm "site") >>
  `a.sym_base.as_pc < LENGTH p` by
    (CCONTR_TAC >> gvs[sym_steps_def]) >>
  `?t. sym_steps p env 1 a = SymOK t /\ sym_steps p env r t = SymOK e` by
    (`SUC r = 1+r` by decide_tac >>
     qpat_assum `sym_steps p env (SUC r) a = _` mp_tac >>
     qpat_assum `SUC r = _` (fn th => once_rewrite_tac[th]) >>
     once_rewrite_tac[sym_steps_add] >>
     Cases_on `sym_steps p env 1 a` >> simp[]) >>
  `~sym_data_label p env x` by
    (`MEM (AsmLabel x) p` by (asm "site" (fn th => simp[th])) >>
     fs[asm_static_wf_def,sym_data_label_def]) >>
  qabbrev_tac `(d:num) = if next = AsmLabel y then 1 else 3` >>
  Q.SUBGOAL_THEN
    `(?v. sym_steps (MAP (rename_push_label x y) p) env 1 b = SymOK v /\
          rn_rel x y t v) \/
     (?stk stk'. x <> y /\ a.sym_stack = Lab x 0 :: stk /\
                 b.sym_stack = Lab y 0 :: stk' /\
       (EL a.sym_base.as_pc p = AsmOp "JUMP" \/
        (EL a.sym_base.as_pc p = AsmOp "JUMPI" /\
         ?c rest. stk = Val c :: rest /\ c <> 0w)))`
    (DISJ_CASES_THEN2 (qx_choose_then `v` strip_assume_tac)
      (qx_choose_then `stk` (qx_choose_then `stk'`
        (map_every assume_tac o CONJUNCTS))))
  >- (Cases_on `EL a.sym_base.as_pc p = AsmOp "JUMP" \/
                EL a.sym_base.as_pc p = AsmOp "JUMPI"`
      >- (irule (SIMP_RULE (srw_ss()) [LET_THM] merge_taken_or_sync) >> simp[]) >>
      disj1_tac >>
      irule (SIMP_RULE (srw_ss()) [LET_THM] merge_rename_nonjump_fetch_ok) >>
      metis_tac[])
  >- (disj1_tac >> qexistsl [`1`,`t`,`v`] >> simp[]) >>
  Cases_on `r < d`
  >- (disj2_tac >> qexistsl [`stk`,`stk'`] >> simp[Abbr `d`] >> metis_tac[]) >>
  `d <= r` by decide_tac >>
  asm "site" assume_tac >>
  drule_all (SIMP_RULE (srw_ss()) [LET_THM] merge_rename_protected_redirect_cut) >>
  disch_then (qx_choose_then `mid` (map_every assume_tac o CONJUNCTS)) >>
  gns[] >>
  `?j. INDEX_OF (AsmLabel y) p = SOME j /\
       sym_steps p env d mid = SymOK (sym_with_pc j mid) /\
       sym_steps p env (r-d) (sym_with_pc j mid) = SymOK e` by
    (simp[Abbr `d`] >> metis_tac[]) >>
  `?v. sym_steps (MAP (rename_push_label x y) p) env 1 b = SymOK v /\
       v.sym_base.as_pc = j /\ rn_rel x y (sym_with_pc j mid) v` by
    (gns[] >> metis_tac[]) >>
  (* Compose before simplification normalizes the order of the counts. *)
  `sym_steps p env (1+d) a = SymOK (sym_with_pc j mid)` by
    (once_rewrite_tac[sym_steps_add] >> gns[]) >>
  `SUC r - (1+d) = r-d` by decide_tac >>
  qexistsl [`1+d`,`sym_with_pc j mid`,`v`] >>
  qpat_x_assum `SUC r - (1+d) = _` (fn th => once_rewrite_tac[th]) >>
  gns[]
QED

Theorem merge_rename_stopped_replay:
  let q = MAP (rename_push_label x y) p in
  let d = if next = AsmLabel y then 1 else 3 in
  let P = \k s. sym_steps p env k s in
  let Q = \k s. sym_steps q env k s in
  asm_static_wf p /\ p = pre ++ [AsmLabel x;next;third] ++ tail /\
  ((next = AsmLabel y /\ y <> x) \/
   (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
  rn_rel x y a b /\ P n a = SymOK e ==>
  (?m f. Q m b = SymOK f /\ rn_rel x y e f) \/
  (?i m r u v stk stk'.
     n = i + SUC r /\ r < d /\
     P i a = SymOK u /\ Q m b = SymOK v /\ rn_rel x y u v /\
     P (SUC r) u = SymOK e /\ u.sym_base.as_pc < LENGTH p /\ x <> y /\
     u.sym_stack = Lab x 0 :: stk /\ v.sym_stack = Lab y 0 :: stk' /\
     (EL u.sym_base.as_pc p = AsmOp "JUMP" \/
      (EL u.sym_base.as_pc p = AsmOp "JUMPI" /\
       ?c rest. stk = Val c :: rest /\ c <> 0w)))
Proof
  rewrite_tac[LET_THM] >> rpt (CHANGED_TAC BETA_TAC) >>
  map_every qid_spec_tac [`e`,`b`,`a`] >> completeInduct_on `n` >>
  Cases_on `n`
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      disj1_tac >> qexistsl [`0`,`b`] >> gns[sym_steps_def]) >>
  rename1 `SUC r` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE (srw_ss()) [LET_THM] merge_replay_chunk) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `k` (qx_choose_then `u` (qx_choose_then `v`
      (map_every assume_tac o CONJUNCTS))))
    (qx_choose_then `stk` (qx_choose_then `stk'`
      (map_every assume_tac o CONJUNCTS))))
  >- (`SUC r - k < SUC r` by decide_tac >>
      first_x_assum (qspec_then `SUC r-k` mp_tac) >>
      simp[] >> disch_then (qspecl_then [`u`,`v`,`e`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (DISJ_CASES_THEN2
        (qx_choose_then `m` (qx_choose_then `f` strip_assume_tac))
        (qx_choose_then `i` (qx_choose_then `m` (qx_choose_then `r'`
          (qx_choose_then `u'` (qx_choose_then `v'` (qx_choose_then `stk`
            (qx_choose_then `stk'` (map_every assume_tac o CONJUNCTS)))))))))
      >- (disj1_tac >> qexistsl [`1+m`,`f`] >>
          once_rewrite_tac[sym_steps_add] >> gns[]) >>
      `sym_steps p env (k+i) a = SymOK u'` by
        (once_rewrite_tac[sym_steps_add] >> gns[]) >>
      `sym_steps (MAP (rename_push_label x y) p) env (1+m) b = SymOK v'` by
        (once_rewrite_tac[sym_steps_add] >> gns[]) >>
      `SUC r = (k+i) + SUC r'` by decide_tac >>
      disj2_tac >> qexistsl [`k+i`,`1+m`,`r'`,`u'`,`v'`,`stk`,`stk'`] >> gns[]) >>
  disj2_tac >> qexistsl [`0`,`0`,`r`,`a`,`b`,`stk`,`stk'`] >>
  simp[sym_steps_def] >> metis_tac[]
QED
