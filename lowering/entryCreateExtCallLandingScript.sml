(* Package the selected zero-mark stage without changing its physical or
   ghost endpoint. The stage's compiler supplies the slot geometry. *)
Theory entryCreateExtCallLanding
Ancestors
  entryCreatePathScope entryCreateFocusSpec entryCreateCompletedCut
  gasOutcomeFull createSizePrefixReplay createMarkedPath fragGasOrigin
  abiEncoderProps venomExecSemantics relation list
  gasSummary gasStorage vyperStorageFootprint

Theorem extcall_slot_prefix[local]:
  (!p. slot p ==> ~create_operand_at sr p /\
       ?bb i. lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
              get_instruction bb p.vs_inst_idx = SOME i /\
              i.inst_id IN frag_ids sp sr) ==>
  !s t. RTC (\p q. slot p /\ gas_origin_edge F E ctx func p [] (OK q)) s t ==>
        create_expr_prefix sp sr E ctx func s [] t
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >>
  rpt strip_tac >>
  rename1 `gas_origin_edge F E ctx func p [] (OK q)` >>
  `create_expr_prefix sp sr E ctx func p [] q` by
    (rewrite_tac[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def,create_prefix_step_def] >>
     metis_tac[create_operand_at_def]) >>
  metis_tac[create_expr_prefix_append,APPEND]
QED

Theorem extcall_stage_scoped_landing:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  (!p. slot p ==> ~create_operand_at sr p /\
       ?bb i. lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
              get_instruction bb p.vs_inst_idx = SOME i /\
              i.inst_id IN frag_ids sp sr) /\
  ((?u. r = OK u /\ create_operand_at sr u /\
        RTC (\p q. slot p /\ gas_origin_edge F E ctx func p [] (OK q)) s u) \/
   (exit_result r /\ ?u.
        RTC (\p q. slot p /\ gas_origin_edge F E ctx func p [] (OK q)) s u /\
        slot u /\ gas_origin_edge T E ctx func u [] r)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) [] (r,Gf,tf) /\
       ((?u. r = OK u /\ Q H res (ee with gas_obs := []) Gf tf u) \/
        (exit_result r /\ ?exc. res = INR exc /\
          R H (INR exc) (ee with gas_obs := []) (Gf,tf) r))) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sp sr
    source (es,s,G,tn) Q (\H raw ef gt q. ?exc. raw = INR exc /\ R H (INR exc) ef gt q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_operand_full_scope sp sr E ctx func s [] r` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     drule extcall_slot_prefix >> disch_then drule >> strip_tac
     >- gvs[create_operand_full_scope_def,create_operand_at_def] >>
     irule (SIMP_RULE bool_ss [APPEND]
       (Q.INST [`left` |-> `[]`,`last` |-> `[]`] create_operand_full_scope_terminal)) >>
     fs[create_operand_at_def] >> metis_tac[]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`Gf`,`tf`] >>
      simp[gas_explicit_def]) >>
  disj1_tac >> conj_tac
  >- simp[gas_bad_storage_at_def,gas_explicit_def] >>
  conj_tac >- (simp[create_operand_focus_scope_def] >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G`,`tn`,`s`] >>
  simp[gas_origin_ptr_focus_nil,storage_trace_domain_def]
QED
