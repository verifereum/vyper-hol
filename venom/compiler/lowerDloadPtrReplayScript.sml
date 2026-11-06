Theory lowerDloadPtrReplay
Ancestors lowerDloadPtrPhase ptrDiscipline venomExecSemantics venomState list

Theorem dload_prefix_noninvoke_transport:
  !n fuel C PG xs t0 H0 un0 t H un fuel' C'.
    dload_prefix_match fuel C PG xs n t0 H0 un0 t H un /\
    (!k. k < n ==> (EL k xs).inst_opcode <> INVOKE) ==>
    dload_prefix_match fuel' C' PG xs n t0 H0 un0 t H un
Proof
  Induct >- simp[dload_prefix_match_def] >>
  rpt gen_tac >> simp[Once dload_prefix_match_def] >> strip_tac >>
  `dload_prefix_match fuel' C' PG xs n t0 H0 un0 u J vn` by
    (first_x_assum irule >> conj_tac
     >- (rpt gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
     qexistsl [`C`,`fuel`] >> simp[]) >>
  `step_inst fuel' C' (EL n xs) u = OK v` by
    (`(EL n xs).inst_opcode <> INVOKE` by
       (first_x_assum irule >> simp[]) >>
     gvs[step_inst_non_invoke]) >>
  simp[Once dload_prefix_match_def] >> metis_tac[]
QED

Theorem dload_prefix_extend_mixed:
  dload_prefix_match fuel C PG xs n t0 H0 un0 t H un /\
  n < LENGTH xs /\ (EL n xs).inst_opcode <> INVOKE /\
  step_inst fuel' C' (EL n xs) t = OK v ==>
  dload_prefix_match fuel C PG xs (SUC n) t0 H0 un0
    (v with vs_inst_idx := SUC t.vs_inst_idx)
    (step_prov PG H (EL n xs) v) (step_taint (EL n xs) t v un)
Proof
  strip_tac >> irule dload_prefix_extend >> simp[] >>
  gvs[step_inst_non_invoke]
QED
