(* Generated prologue reads prepend counted and exempt callee outcomes. *)
Theory bodyIntCallPackagePrefix
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasSummaryComposePtr
  fragGasMode fragGasPath gasCount vyperState list rich_list

Theorem gas_marked_exec_path_prefix:
  gas_path ctx func s0 n (OK s1) /\
  gas_marked_exec F (ctx,func) source (es,s1) marks res ee r ==>
  gas_marked_exec F (ctx,func) source (es,s0)
    (REPLICATE n F ++ marks) res ee r
Proof
  rewrite_tac[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
  `s1.vs_gas_readings = DROP n s0.vs_gas_readings` by
    (qpat_assum `gas_path _ _ _ _ (OK _)` (mp_tac o MATCH_MP gas_path_suffix) >>
     simp[gas_count_suffix_def]) >>
  simp[gas_explicit_append] >>
  metis_tac[gas_path_then]
QED

Theorem gas_summary_at_path_prefix:
  gas_path ctx func s0 n (OK s1) /\
  gas_summary_at F (ctx,func) marks source (es,s1) Q R ==>
  gas_summary_at F (ctx,func) (REPLICATE n F ++ marks) source (es,s0) Q R
Proof
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qexistsl [`res`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_path_prefix >> qexists `s1` >> gvs[]
QED

Theorem gas_outcome_path_prefix:
  gas_path ctx func s0 n (OK s1) /\
  gas_outcome F tops (ctx,func) source (es,s1) Q R ==>
  gas_outcome F tops (ctx,func) source (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists `REPLICATE n F ++ marks`
  >- (disj1_tac >> irule gas_summary_at_path_prefix >> metis_tac[]) >>
  disj2_tac >> qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  irule gas_exempt_cert_path_prefix >> metis_tac[]
QED

Theorem gas_marked_exec_zero_suffix:
  gas_marked_exec F (ctx,func) source (es,s0) marks res ee (OK u) /\
  gas_path ctx func u 0 r ==>
  gas_marked_exec F (ctx,func) source (es,s0) marks res ee r
Proof
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >> simp[] >>
  drule_all gas_path_then >> simp[]
QED
