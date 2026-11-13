Theory bodyPtrStructLitFreshAlloc
Ancestors allocationPtr exprSimPtrLiteralBuffer bodyPtrDefs compileEnv
  venomState venomExecSemantics venomInst finite_map words pred_set
  ptrDiscipline exprSimProps loweringHalt

Theorem structlit_fresh_alloca_ghost_inv:
  ghost_inv d ce cx es G tn s /\ local_ptrs_reserved ce sa /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  ~not_fresh_at sa out /\
  (!name entry p sz w. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    w2n w + val_footprint entry.type entry.value <= s.vs_alloca_next) /\
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ghost_inv d ce cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
  simp[] >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  irule literal_ghost_inv_frame >>
  qexistsl [`G`, `s`, `sa`, `tn`,
    `{i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n}`] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  conj_tac
  >- (fs[lookup_var_def] >> rpt gen_tac >> strip_tac >>
      first_x_assum drule_all >> strip_tac >> simp[] >> decide_tac) >>
  rpt strip_tac >> gvs[] >>
  `x <> out` by metis_tac[] >> simp[]
QED

(* Conditional fresh-site ghost preservation only. The caller still owes
   reservation/freshness and live-footprint bounds from its real body frame.
   Code placement, gas admissibility, coverage and narrow-call capacity are
   not consequences of this boundary. The reused branch is in AllocEntry. *)
