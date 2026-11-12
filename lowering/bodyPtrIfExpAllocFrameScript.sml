Theory bodyPtrIfExpAllocFrame
Ancestors
  allocationPtr robustCopyTransportPtr bodyPtrDefs ptrDiscipline loweringHalt
  venomState venomExecSemantics venomInst finite_map codegenRel

(* Reuse ignores the requested size: the recorded allocation can have an
   unrelated size k. This effects boundary deliberately has no state_rel. *)
Theorem reused_alloca_memory_effects:
  !id n out s b k tn.
    FLOOKUP s.vs_allocas id = SOME (b,k) ==>
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s =
      OK (update_var out (n2w b) s) /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
      (update_var out (n2w b) s) tn).t_mem = tn.t_mem
Proof
  rpt strip_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      simp[mk_inst_def, exec_alloca_def]) >>
  `new_site_bytes s (update_var out (n2w b) s) = {}` by
    (rw[new_site_bytes_def, update_var_def, pred_setTheory.EXTENSION] >>
     gvs[FLOOKUP_DEF]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, mk_inst_def, range_bytes_def,
       written_taint_def, adopt_reset_def]
QED

Theorem alloca_step_robust_below_frontier:
  !id n out s s1 tn tv v p.
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    val_wf tv v /\
    (!i. p <= i /\ i < p + val_footprint tv v ==> i < s.vs_alloca_next) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v p m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
      s1.vs_memory m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def] >> rpt strip_tac >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- simp[] >>
      qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `tn.t_mem`,
        `tn.t_mem UNION {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n}`,
        `{i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n}`] >>
      simp[] >> metis_tac[arithmeticTheory.NOT_LESS_EQUAL]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule reused_alloca_memory_effects >>
  disch_then (qspecl_then [`n`, `out`, `tn`] strip_assume_tac) >>
  gvs[update_var_def]
QED
