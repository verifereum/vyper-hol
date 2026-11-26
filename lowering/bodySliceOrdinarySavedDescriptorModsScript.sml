(* Preserve the Slice limit/data descriptor through the two scalar reads. *)
Theory bodySliceOrdinarySavedDescriptorMods
Ancestors
  bodyPtrPrecompileBuiltinsGhost wordArgsPtr exprSimWordArgs bodyPtrDefs loweringPosts
  ptrDiscipline venomState freshWrites arithmetic

Theorem slice_ordinary_saved_descriptor_mods:
  wb_frame cenv es0 es1 sc scs sds /\
  wb_frame cenv es1 es2 sd sds ses /\
  ghost_kept_at lo cenv es0 sc Gc tc scs Gd td /\
  ghost_kept_at lo cenv es1 sd Gd td sds Ge te /\
  sc.cs_next_var <= sd.cs_next_var /\
  sd.cs_next_var <= se.cs_next_var /\
  scs.vs_alloca_next <= sds.vs_alloca_next /\
  sds.vs_alloca_next <= ses.vs_alloca_next /\
  data = Var root /\ not_fresh_at sc root /\
  (!q. limit = Var q ==> not_fresh_at sc q) /\
  (!l. limit <> Label l) /\
  eval_operand limit scs = SOME (n2w (LENGTH bs)) /\
  op_prov Gc limit = NONE /\ op_taint tc limit = {} /\
  lookup_var root scs = SOME p /\
  ptr_covers Gc tc root scs (LENGTH bs) /\
  w2n p + LENGTH bs < dimword (:256) /\
  w2n p + LENGTH bs <= scs.vs_alloca_next ==>
  eval_operand limit ses = SOME (n2w (LENGTH bs)) /\
  op_prov Ge limit = NONE /\ op_taint te limit = {} /\
  lookup_var root ses = SOME p /\
  ptr_covers Ge te root ses (LENGTH bs) /\
  w2n p + LENGTH bs < dimword (:256) /\
  w2n p + LENGTH bs <= ses.vs_alloca_next /\
  not_fresh_at se root
Proof
  strip_tac >>
  `ghost_kept cenv es0 sc Gc tc scs Gd td` by
    (REWRITE_TAC[ghost_kept_def] >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o REWRITE_RULE [ghost_kept_at_def])) >>
  `ghost_kept cenv es1 sd Gd td sds Ge te` by
    (REWRITE_TAC[ghost_kept_def] >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o REWRITE_RULE [ghost_kept_at_def])) >>
  `!q. limit = Var q ==> not_fresh_at sd q` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sc` >> simp[]) >>
  `not_fresh_at sd root` by
    (irule not_fresh_at_mono >> qexists_tac `sc` >> simp[]) >>
  `eval_operand limit sds = SOME (n2w (LENGTH bs)) /\
   op_taint td limit = op_taint tc limit` by
    (drule_all word_operand_frame >> simp[]) >>
  `op_prov Gd limit = NONE` by
    (Cases_on `limit` >> simp[op_prov_def] >>
     `not_fresh_at sc s` by
       (qpat_assum `!q. Var s = Var q ==> _` (qspec_then `s` mp_tac) >> simp[]) >>
     `FLOOKUP Gd s = FLOOKUP Gc s` by
       (irule ghost_kept_provenance >>
        qpat_assum `ghost_kept cenv es0 sc Gc tc scs Gd td` (irule_at Any) >> simp[]) >>
     qpat_assum `FLOOKUP Gd s = FLOOKUP Gc s`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `op_prov Gc (Var s) = NONE`
       (assume_tac o SIMP_RULE (srw_ss()) [op_prov_def]) >>
     first_assum ACCEPT_TAC) >>
  `lookup_var root sds = SOME p` by
    (drule_all wb_frame_vars >> simp[]) >>
  `eval_operand (Var root) sds = SOME p` by
    (simp[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `ptr_covers Gd td root sds (LENGTH bs)` by
    (irule ghost_kept_ptr_covers >>
     qexistsl_tac [`Gc`,`cenv`,`es0`,`scs`,`sc`,`tc`,`p`] >>
     (conj_tac >- (qpat_assum `not_fresh_at sc root` ACCEPT_TAC)) >>
     (conj_tac >- (qpat_assum `eval_operand (Var root) sds = SOME p` ACCEPT_TAC)) >>
     (conj_tac >- (simp[eval_operand_def] >>
       qpat_assum `lookup_var root scs = SOME p` ACCEPT_TAC)) >>
     (conj_tac >- (qpat_assum `ptr_covers Gc tc root scs _` ACCEPT_TAC)) >>
     qpat_assum `ghost_kept cenv es0 sc Gc tc scs Gd td` ACCEPT_TAC) >>
  `eval_operand limit ses = SOME (n2w (LENGTH bs)) /\
   op_taint te limit = op_taint td limit` by
    (drule_all word_operand_frame >> simp[]) >>
  `op_prov Ge limit = NONE` by
    (Cases_on `limit` >> simp[op_prov_def] >>
     `not_fresh_at sd s` by
       (qpat_assum `!q. Var s = Var q ==> _` (qspec_then `s` mp_tac) >> simp[]) >>
     `FLOOKUP Ge s = FLOOKUP Gd s` by
       (irule ghost_kept_provenance >>
        qpat_assum `ghost_kept cenv es1 sd Gd td sds Ge te` (irule_at Any) >> simp[]) >>
     qpat_assum `FLOOKUP Ge s = FLOOKUP Gd s`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `op_prov Gd (Var s) = NONE`
       (assume_tac o SIMP_RULE (srw_ss()) [op_prov_def]) >>
     first_assum ACCEPT_TAC) >>
  `lookup_var root ses = SOME p` by
    (drule_all wb_frame_vars >> simp[]) >>
  `eval_operand (Var root) ses = SOME p` by
    (simp[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `ptr_covers Ge te root ses (LENGTH bs)` by
    (irule ghost_kept_ptr_covers >>
     qexistsl_tac [`Gd`,`cenv`,`es1`,`sds`,`sd`,`td`,`p`] >>
     (conj_tac >- (qpat_assum `not_fresh_at sd root` ACCEPT_TAC)) >>
     (conj_tac >- (qpat_assum `eval_operand (Var root) ses = SOME p` ACCEPT_TAC)) >>
     (conj_tac >- (qpat_assum `eval_operand (Var root) sds = SOME p` ACCEPT_TAC)) >>
     (conj_tac >- (qpat_assum `ptr_covers Gd td root sds _` ACCEPT_TAC)) >>
     qpat_assum `ghost_kept cenv es1 sd Gd td sds Ge te` ACCEPT_TAC) >>
  `not_fresh_at se root` by
    (irule not_fresh_at_mono >> qexists_tac `sc` >> simp[]) >>
  `w2n p + LENGTH bs <= sds.vs_alloca_next` by
    (irule LESS_EQ_TRANS >>
     qexists_tac `scs.vs_alloca_next` >>
     conj_tac
     >- (qpat_assum `w2n p + LENGTH bs <= scs.vs_alloca_next` ACCEPT_TAC)
     >- (qpat_assum `scs.vs_alloca_next <= sds.vs_alloca_next` ACCEPT_TAC)) >>
  `w2n p + LENGTH bs <= ses.vs_alloca_next` by
    (irule LESS_EQ_TRANS >>
     qexists_tac `sds.vs_alloca_next` >>
     conj_tac
     >- (qpat_assum `w2n p + LENGTH bs <= sds.vs_alloca_next` ACCEPT_TAC)
     >- (qpat_assum `sds.vs_alloca_next <= ses.vs_alloca_next` ACCEPT_TAC)) >>
  conj_tac >- (qpat_assum `eval_operand limit ses = SOME (n2w (LENGTH bs))` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `op_prov Ge limit = NONE` ACCEPT_TAC) >>
  conj_tac >- (`op_taint te limit = {}` by
    (qpat_assum `op_taint te limit = op_taint td limit`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `op_taint td limit = op_taint tc limit`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `op_taint tc limit = {}`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >> simp[])) >>
  conj_tac >- (qpat_assum `lookup_var root ses = SOME p` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `ptr_covers Ge te root ses _` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `w2n p + LENGTH bs < dimword (:256)` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `w2n p + LENGTH bs <= ses.vs_alloca_next` ACCEPT_TAC) >>
  qpat_assum `not_fresh_at se root` ACCEPT_TAC
QED
