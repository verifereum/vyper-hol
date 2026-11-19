Theory staticAbortOptMergeJumpdestsOrdinary
Ancestors
  asmOwnMergeStep asmOwnMergeCodecopy asmSymPcOwn asmSymPc asmSplice
  asmOptMergeJumpdests asmOptimizer asmSymSem asmSymOwnCode list rich_list

Theorem merge_rename_nonjump_fetch_ok:
  !i. i = a.sym_base.as_pc ==>
  !inst. inst = EL i p ==>
    rn_rel x y a b /\ ~sym_data_label p env x /\ i < LENGTH p /\
    inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" /\
    sym_steps p env 1 a = SymOK t ==>
    ?t'. sym_steps (MAP (rename_push_label x y) p) env 1 b = SymOK t' /\
         rn_rel x y t t'
Proof
  simp[] >> strip_tac >>
  qabbrev_tac `inst = EL a.sym_base.as_pc p` >>
  `sym_step p env inst a = SymOK t` by
    (qpat_x_assum `sym_steps p env 1 a = _` mp_tac >>
     simp[sym_steps_pos,sym_steps_def,Abbr `inst`] >>
     Cases_on `sym_step p env (EL a.sym_base.as_pc p) a` >> simp[]) >>
  (* This list supplies only an instruction-level context, not a fetch. *)
  qabbrev_tac `pf = FILTER (\i. i <> AsmLabel x) p` >>
  `!l. MEM (AsmDataHeader l) pf <=> MEM (AsmDataHeader l) p` by
    simp[Abbr `pf`,MEM_FILTER] >>
  `INDEX_OF (AsmLabel x) pf = NONE` by
    simp[Abbr `pf`,INDEX_OF_eq_NONE,MEM_FILTER] >>
  `~sym_data_label pf env x` by fs[sym_data_label_def] >>
  `sym_step pf env inst a = SymOK t` by metis_tac[sym_step_prog_cong] >>
  `rename_push_label x y inst <> AsmOp "JUMP" /\
   rename_push_label x y inst <> AsmOp "JUMPI"` by
    (Cases_on `inst` >> rw[rename_push_label_def] >> fs[]) >>
  qabbrev_tac `qf = MAP (rename_push_label x y) pf` >>
  `inst <> AsmOp "CODESIZE"` by
    (strip_tac >> gvs[sym_step_def,sym_step_op_def]) >>
  `rename_push_label x y inst <> AsmOp "CODESIZE" /\
   (rename_push_label x y inst = AsmOp "CODECOPY" <=> inst = AsmOp "CODECOPY")` by
    (Cases_on `inst` >> rw[rename_push_label_def] >> fs[]) >>
  `sym_step_own pf env [] inst a = SymOK t /\
   sym_step_own qf env [] (rename_push_label x y inst) b =
     sym_step qf env (rename_push_label x y inst) b` by
    (Cases_on `inst = AsmOp "CODECOPY"`
     >- (`sym_codecopy pf env a = SymOK t` by fs[sym_step_def,sym_step_op_def] >>
         `?dst l d sz stk. a.sym_stack = Val dst :: Lab l d :: Val sz :: stk /\
                           sym_data_label pf env l /\ sym_delta_ok d` by
           (pop_assum mp_tac >> rw[sym_codecopy_def,AllCaseEqs()] >> metis_tac[]) >>
         `l <> x` by metis_tac[] >>
         `?tail. b.sym_stack = Val dst :: Lab l d :: Val sz :: tail` by
           (fs[rn_rel_def,LIST_REL_CONS1,sv_rel_val,sv_rel_def] >> metis_tac[]) >>
         `sym_data_label qf env l` by fs[Abbr `qf`,mem_rename,sym_data_label_def] >>
         gvs[sym_step_own_def,sym_step_op_own_def,sym_step_def,sym_step_op_def,
             sym_codecopy_own_def,sym_codecopy_def,rename_push_label_def]) >>
     simp[sym_step_own_eq]) >>
  `!u v. rn_rel x y u v /\ ~sym_data_label pf env x ==>
         res_rel x y (sym_codecopy_own pf env [] u) (sym_codecopy_own pf env [] v)` by
    simp[codecopy_rel_own] >>
  drule rename_step_own_under >>
  disch_then (qspecl_then [`a`,`b`,`inst`] mp_tac) >>
  gvs[Abbr `qf`] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `sym_step (MAP (rename_push_label x y) p) env (rename_push_label x y inst) b =
     sym_step (MAP (rename_push_label x y) pf) env (rename_push_label x y inst) b` by
    (irule sym_step_prog_cong >> simp[mem_rename]) >>
  `b.sym_base.as_pc = a.sym_base.as_pc` by fs[rn_rel_def] >>
  qexists_tac `out` >>
  simp[sym_steps_pos,sym_steps_def,EL_MAP]
QED
