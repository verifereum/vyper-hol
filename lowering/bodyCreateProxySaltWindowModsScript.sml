(* Salt evaluation preserves the registered proxy row, even though only
   its first 54 bytes are read by CREATE2. *)
Theory bodyCreateProxySaltWindowMods
Ancestors
  bodyPtrDefs loweringPosts loweringStateRelDefs loweringShapeDefs
  exprSimWordArgs memoryReadProps exprPtrUnwrapFrames reasonCopySourcePtr
  venomMemProps venomState
  venomInst venomExecSemantics ptrDiscipline finite_map words list

Theorem create_proxy_salt_window_kept_mods:
  wb_frame cenv ea ew c u t /\
  ghost_kept_at lo cenv ea c Gu tu u G1 tt /\
  u.vs_alloca_next <= t.vs_alloca_next /\
  lookup_var p u = SOME w /\ ptr_covers Gu tu p u 96 /\
  w2n w + 96 <= u.vs_alloca_next /\ not_fresh_at c p /\
  FLOOKUP u.vs_allocas aid = SOME (w2n w,96) /\ aid < c.cs_next_id /\
  (!name b n. local_region cenv ea.scopes u name b n ==>
              regions_disjoint (w2n w) 96 b n) /\
  read_memory (w2n w) 54 u = initcode /\
  (!i. w2n w <= i /\ i < w2n w + 54 ==> i NOTIN tu.t_mem) /\
  eval_operand amount u = SOME aw /\ op_taint tu amount = {} /\
  (!l. amount <> Label l) /\ (!x. amount = Var x ==> not_fresh_at c x) ==>
  lookup_var p t = SOME w /\ ptr_covers G1 tt p t 54 /\
  op_taint tt (Var p) = {} /\ w2n w + 54 <= t.vs_alloca_next /\
  read_memory (w2n w) 54 t = initcode /\
  (!i. w2n w <= i /\ i < w2n w + 54 ==> i NOTIN tt.t_mem) /\
  eval_operand amount t = SOME aw /\ op_taint tt amount = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!name b n. local_region cenv ea.scopes u name b n ==>
              w2n w + 96 <= b \/ b + n <= w2n w` by
    fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
  `read_memory (w2n w) 96 t = read_memory (w2n w) 96 u` by
    (simp[read_memory_eq_mem_bytes_at] >>
     qpat_assum `wb_frame _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     first_assum (drule_all_then ACCEPT_TAC)) >>
  `!s. read_memory (w2n w) 54 s = TAKE 54 (read_memory (w2n w) 96 s)` by
    (gen_tac >> qspecl_then [`w2n w`,`96`,`0`,`54`,`s`] mp_tac read_memory_subwindow >> simp[]) >>
  `read_memory (w2n w) 54 t = initcode` by
    (qpat_assum `!s. read_memory _ 54 s = _` (qspec_then `u` mp_tac) >> simp[]) >>
  `lookup_var p t = SOME w` by drule_all_then ACCEPT_TAC wb_frame_vars >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  `FLOOKUP G1 p = FLOOKUP Gu p /\ op_taint tt (Var p) = op_taint tu (Var p)` by simp[] >>
  `lookup_var p t = lookup_var p u` by simp[] >>
  `ptr_covers G1 tt p t 96` by
    (drule_all copy_ptr_covers_transport >> disch_then (qspec_then `96` mp_tac) >> simp[]) >>
  `ptr_covers G1 tt p t 54` by
    (irule ptr_covers_mono >> qexists_tac `96` >> simp[]) >>
  `op_taint tt (Var p) = {}` by fs[ptr_covers_def] >>
  `!i. w2n w <= i /\ i < w2n w + 54 ==> i NOTIN tt.t_mem` by
    (rpt strip_tac >> `i < w2n w + 96` by decide_tac >>
     `i IN tu.t_mem` by first_assum (drule_all_then ACCEPT_TAC) >>
     qpat_assum `!j. w2n w <= j /\ j < w2n w + 54 ==> j NOTIN tu.t_mem`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `eval_operand amount t = SOME aw /\ op_taint tt amount = {}` by
    (Cases_on `amount` >> gvs[eval_operand_def,op_taint_def] >>
     drule_all_then ACCEPT_TAC wb_frame_vars) >>
  simp[] >> decide_tac
QED
