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

Theorem ricf_frame_agree_update_var:
  ricf_frame_agree D X sites PG G tn s t /\
  ricf_value_agree sites p m x y ==>
  ricf_frame_agree D X sites PG (set_prov G [out] p)
    (tn with t_var := set_var_taint tn.t_var [out] m)
    (update_var out x s) (update_var out y t)
Proof
  simp[ricf_frame_agree_def, taint_agree_def, update_var_def,
       set_var_taint_def, ld_shared_agree_def, op_taint_def,
       ircf_cross_def, set_prov_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[] >>
  TRY (gvs[venom_state_component_equality] >> NO_TAC) >>
  Cases_on `v = out` >> gvs[FAPPLY_FUPDATE_THM] >>
  Cases_on `p` >> gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
                       word_agree_except_def] >> metis_tac[]
QED

Theorem ricf_frame_agree_eval_phis:
  !ins s t s1 tn G.
    ricf_frame_agree D X sites PG G tn s t /\ eval_phis s ins = OK s1 ==>
    ?t1. eval_phis t ins = OK t1 /\
      ricf_frame_agree D X sites PG (phis_prov s.vs_prev_bb G ins)
        (tn with t_var := phis_taint s.vs_prev_bb tn ins) s1 t1
Proof
  Induct_on `ins`
  >- (simp[eval_phis_def, phis_taint_def, phis_prov_def] >>
      simp[ricf_frame_agree_def, taint_agree_def, op_taint_def,
           ld_shared_agree_def, ircf_cross_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (qpat_x_assum `eval_phis s (h::ins) = _` mp_tac >>
      simp[Once eval_phis_def, AllCaseEqs()] >> strip_tac >>
      gvs[eval_one_phi_def, AllCaseEqs()] >>
      `?v'. eval_operand val_op t = SOME v' /\
            ricf_value_agree sites (op_prov G val_op)
              (op_taint tn val_op) v v'` by
        (drule_all ricf_frame_agree_operand >> simp[]) >>
      `s.vs_prev_bb = t.vs_prev_bb` by
        (drule ricf_frame_agree_normalized >>
         disch_then (mp_tac o MATCH_MP taint_agree_frame) >>
         disch_then (mp_tac o Q.AP_TERM `\u. u.vs_prev_bb`) >> simp[]) >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `update_var out v' t1` >>
      simp[Once eval_phis_def, eval_one_phi_def] >>
      simp[phis_taint_def, phi_taint_def, phis_prov_def, phi_prov_def] >>
      drule_all ricf_frame_agree_update_var >> gvs[]) >>
  gvs[eval_phis_def, phis_taint_def, phis_prov_def] >>
  simp[ricf_frame_agree_def, taint_agree_def, op_taint_def,
       ld_shared_agree_def, ircf_cross_def]
QED
