Theory readonlyInvokeCopyFwdValues
Ancestors
  readonlyInvokeCopyFwdRel o1LowerDloadAddressArithmetic
  o1LowerDloadRelocationKernel internalReturnCopyFwdSim o1LowerDloadShared
  venomExecSemantics venomState ptrDiscipline taintAgree codegenRel
  finite_map words list pred_set

Theorem ricf_frame_agree_normalized:
  ricf_frame_agree D X sites PG G tn s t ==>
  taint_agree D X tn s
    (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>)
Proof simp[ricf_frame_agree_def]
QED

Theorem ricf_frame_agree_domains:
  ricf_frame_agree D X sites PG G tn s t ==>
  FDOM t.vs_vars = FDOM s.vs_vars
Proof simp[ricf_frame_agree_def]
QED

Theorem ricf_frame_agree_params:
  ricf_frame_agree D X sites PG G tn s t ==>
  ricf_params_agree sites PG s.vs_params t.vs_params
Proof simp[ricf_frame_agree_def]
QED

Theorem ricf_frame_agree_sites:
  ricf_frame_agree D X sites PG G tn s t ==> ricf_sites_ok sites
Proof simp[ricf_frame_agree_def]
QED

Theorem ricf_frame_agree_cross:
  ricf_frame_agree D X sites PG G tn s t ==>
  ircf_cross tn (ricf_site_triples sites) s t
Proof simp[ricf_frame_agree_def]
QED

Theorem ricf_frame_agree_intro:
  taint_agree D X tn s
    (t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>) /\
  FDOM t.vs_vars = FDOM s.vs_vars /\
  (!v. v IN FDOM s.vs_vars ==>
    ricf_value_agree sites (FLOOKUP G v) (op_taint tn (Var v))
      (s.vs_vars ' v) (t.vs_vars ' v)) /\
  ricf_params_agree sites PG s.vs_params t.vs_params /\
  ricf_sites_ok sites /\ ircf_cross tn (ricf_site_triples sites) s t ==>
  ricf_frame_agree D X sites PG G tn s t
Proof simp[ricf_frame_agree_def]
QED

Theorem ricf_value_agree_inactive:
  (p = NONE \/ !id. p = SOME id ==> id NOTIN FDOM sites) ==>
  (ricf_value_agree sites p m x y <=> word_agree_except m x y)
Proof Cases_on `p` >> simp[ricf_value_agree_def, ld_value_agree_def]
QED

Theorem ricf_frame_agree_operand:
  ricf_frame_agree D X sites PG G tn s t /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
    ricf_value_agree sites (op_prov G op) (op_taint tn op) x y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, op_prov_def, op_taint_def, lookup_var_def] >>
  rpt strip_tac
  >- simp[ricf_value_agree_def, ld_value_agree_def, word_agree_except_def]
  >- (fs[ricf_frame_agree_def, FLOOKUP_DEF, op_taint_def] >> metis_tac[])
  >> fs[ricf_frame_agree_def, taint_agree_def] >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[ricf_value_agree_def, ld_value_agree_def, word_agree_except_def]
QED

Theorem ricf_frame_agree_param:
  ricf_frame_agree D X sites PG G tn s t /\ j < LENGTH s.vs_params ==>
  ricf_value_agree sites (EL j PG) {}
    (EL j s.vs_params) (EL j t.vs_params)
Proof simp[ricf_frame_agree_def, ricf_params_agree_def]
QED

Theorem ricf_value_agree_add:
  ricf_sites_ok sites /\ FLOOKUP sites (db,sz) = SOME (db,sb,sz) /\
  ricf_value_agree sites (SOME (db,sz)) {} x y ==>
  ricf_value_agree sites (SOME (db,sz)) {} (x + z) (y + z)
Proof
  strip_tac >> drule_all ricf_value_agree_relocated >>
  disch_then (fn th => fs[th]) >>
  simp[lower_dload_translate_add]
QED

Theorem ricf_value_agree_sub:
  ricf_sites_ok sites /\ FLOOKUP sites (db,sz) = SOME (db,sb,sz) /\
  ricf_value_agree sites (SOME (db,sz)) {} x y ==>
  ricf_value_agree sites (SOME (db,sz)) {} (x - z) (y - z)
Proof
  strip_tac >> drule_all ricf_value_agree_relocated >>
  disch_then (fn th => fs[th]) >>
  simp[lower_dload_translate_sub]
QED

Theorem ricf_value_agree_comparisons:
  ricf_sites_ok sites /\ FLOOKUP sites (db,sz) = SOME (db,sb,sz) /\
  ricf_value_agree sites (SOME (db,sz)) {} x x' /\
  ricf_value_agree sites (SOME (db,sz)) {} y y' /\
  db <= w2n x /\ w2n x <= db+sz /\
  db <= w2n y /\ w2n y <= db+sz /\
  db+sz < dimword (:256) /\ sb+sz < dimword (:256) ==>
  ((x = y) <=> (x' = y')) /\
  ((w2n x < w2n y) <=> (w2n x' < w2n y')) /\
  ((w2n y < w2n x) <=> (w2n y' < w2n x'))
Proof
  strip_tac >> drule_all ricf_value_agree_relocated >>
  disch_then (fn th => gvs[th]) >>
  metis_tac[lower_dload_translate_comparisons]
QED
