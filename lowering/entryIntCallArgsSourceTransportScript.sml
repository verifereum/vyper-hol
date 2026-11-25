(* Source changes leave the selected caller cursors and target witnesses intact. *)
Theory entryIntCallArgsSourceTransport
Ancestors
  entryCreateFocusSpec entryCreateCompletedCut entryCreateBodyCut
  gasExemptScope gasStorage gasContext vyperStorageFootprint vyperState

Theorem intcall_selected_default_context:
  cx_tops cxd = cx_tops cx /\
  (!src H tr. valid_horizon cxd src H tr = valid_horizon cx src H tr) /\
  (!src tr. storage_trace_domain cxd src tr = storage_trace_domain cx src tr) ==>
  (scoped_operand_outcome (DF,lo,explicit,ctx,func,PG)
     (cx_tops cxd) cxd st0 i z source (es,s,G,tn) Q R /\
   create_operand_cut i z explicit ctx func (cx_tops cxd) cxd st0 source (es,s) <=>
   scoped_operand_outcome (DF,lo,explicit,ctx,func,PG)
     (cx_tops cx) cx st0 i z source (es,s,G,tn) Q R /\
   create_operand_cut i z explicit ctx func (cx_tops cx) cx st0 source (es,s))
Proof
  strip_tac >>
  simp[scoped_operand_outcome_def, gas_bad_storage_at_def,
       create_operand_cut_def, create_body_cut_def]
QED

Theorem selected_source_transport[local]:
  old.storage_trace = es.storage_trace /\
  (!obs. source (es with gas_obs := obs) = prior (old with gas_obs := obs)) /\
  (!marks err ee leaf finish'.
    gas_exempt_cert T tops (ctx,func) (ignore_bind prior (return ()))
      (old,s) marks (err,ee) (leaf,finish') ==>
    gas_exempt_cert T tops (ctx,func) (ignore_bind source (return ()))
      (es,s) marks (err,ee) (leaf,finish')) /\
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0
    i z prior (old,s,G,tn) Q R /\
  create_operand_cut i z explicit ctx func tops cx st0 prior (old,s) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0
    i z source (es,s,G,tn) Q R /\
  create_operand_cut i z explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> reverse conj_tac
  >- (qpat_x_assum `create_operand_cut _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[create_operand_cut_def, create_body_cut_def]) >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- fs[gas_bad_storage_at_def] >>
      simp[] >> qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  simp[] >> qexists_tac `H` >> simp[] >> metis_tac[]
QED

Theorem intcall_selected_source_scope:
  ~s.vs_halted /\
  (!obs. source (es with gas_obs := obs) =
         scoped ((es with scopes := scopes) with gas_obs := obs)) /\
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0
    i z scoped (es with scopes := scopes,s,G,tn) Q R /\
  create_operand_cut i z explicit ctx func tops cx st0
    scoped (es with scopes := scopes,s) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0
    i z source (es,s,G,tn) Q R /\
  create_operand_cut i z explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> irule selected_source_transport >>
  qexistsl_tac [`es with scopes := scopes`,`scoped`] >>
  simp[] >> metis_tac[gas_exempt_cert_source_scope]
QED

(* Normalizing a continuation without replacing scopes needs no target step
   and therefore has no nonhalted side condition. *)
Theorem intcall_selected_source_cong:
  (!obs. source (es with gas_obs := obs) = scoped (es with gas_obs := obs)) /\
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0
    i z scoped (es,s,G,tn) Q R /\
  create_operand_cut i z explicit ctx func tops cx st0 scoped (es,s) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0
    i z source (es,s,G,tn) Q R /\
  create_operand_cut i z explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> irule selected_source_transport >>
  qexistsl_tac [`es`,`scoped`] >> simp[] >> rpt strip_tac >>
  irule gasExemptCertTheory.gas_exempt_cert_source_cong >>
  qexists_tac `ignore_bind scoped (return ())` >>
  simp[ignore_bind_def, bind_def]
QED
