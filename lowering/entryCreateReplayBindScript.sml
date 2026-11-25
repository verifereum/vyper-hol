Theory entryCreateReplayBind
Ancestors
  entryCreateFocusSpec entryCreateBodyCut createSizePrefixReplay
  createExprSizeExitDefs gasSummaryCompose vyperStorageFootprint vyperStorageTrace
  fragGasOriginPtr vyperState gasOutcomeFull fragGasPath list

(* Use the geometrical split without imposing any uniform source equation
   on the completed left operand. Each query chooses its own residual tail. *)
Theorem create_operand_cut_bind_replay:
  (!p d k before hit after.
    create_interior_visit a b E ctx fnc (p,d,k) s (before,hit,after) ==>
    create_interior_visit a m E ctx fnc (p,d,k) s (before,hit,after) \/
    ?t d1 k1 front back.
      before = front ++ back /\ create_operand_at m t /\
      create_expr_prefix a m E ctx fnc s (create_cut_marks E front) t /\
      create_interior_visit m b E ctx fnc (p,d1,k1) t (back,hit,after)) /\
  ~s.vs_halted /\
  create_operand_cut a m E ctx fnc tops cx st0 source (es,s) /\
  gas_completed_operand (DF,lo,E,ctx,fnc,PG) tops cx st0 a m source
    (es,s,G0,tn0) Q /\
  (!H r mid G tn t. Q H r mid G tn t ==> ?v. r = INL v) /\
  (!v. storage_trace_frame (next v)) /\
  (!H0 front v mid G tn t.
    valid_horizon cx st0 H0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,ctx,fnc,PG) (s,G0,tn0)
        (create_cut_marks E front) (OK t,G,tn) /\
      Q H (INL v) (mid with gas_obs := []) G tn t) ==>
    create_operand_cut m b E ctx fnc tops cx st0 (next v)
      (mid with gas_obs := [],t)) ==>
  create_operand_cut a b E ctx fnc tops cx st0 (bind source next) (es,s)
Proof
  strip_tac >> simp[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!p d k before hit after. _` drule >> strip_tac
  >- (irule create_cut_bind_left >> simp[] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  `gas_path ctx fnc s (LENGTH (create_cut_marks E front)) (OK t)` by
    (irule create_prefix_gas_path >> simp[] >> metis_tac[]) >>
  drule gas_explicit_append_path >> strip_tac >>
  simp[create_body_cut_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,bind_def] >>
  qabbrev_tac `suffix = gas_explicit (create_cut_marks E back) t.vs_gas_readings ++ tail` >>
  Cases_on `source (es with gas_obs := gas_explicit (create_cut_marks E front)
             s.vs_gas_readings ++ suffix)` >>
  qmatch_asmsub_rename_tac `source _ = (out,mid)` >> disch_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (Cases_on `out` >> gvs[] >>
     `storage_trace_frame (next x)` by simp[] >>
     drule_all storage_trace_frame_prefix >>
     metis_tac[valid_horizon_append]) >>
  qpat_x_assum `gas_completed_operand _ _ _ _ _ _ _ _ _`
    (qspecl_then [`H`,`create_cut_marks E front`,`t`,`suffix`,`out`,`mid`] mp_tac o
     REWRITE_RULE [gas_completed_operand_def]) >>
  simp[GSYM create_operand_at_def] >> reverse strip_tac
  >- (gvs[create_cut_failure_def] >> metis_tac[]) >>
  `?v. out = INL v` by metis_tac[] >>
  `create_operand_cut m b E ctx fnc tops cx st0 (next v)
     (mid with gas_obs := [],t)` by metis_tac[] >>
  qpat_x_assum `create_operand_cut m b _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [create_operand_cut_def]) >>
  disch_then drule >> simp[create_body_cut_def] >>
  disch_then (qspecl_then [`H`,`tail`,`res`,`ee`] mp_tac) >>
  `((mid with gas_obs := []) with gas_obs := suffix) = mid` by
    simp[evaluation_state_component_equality] >>
  qunabbrev_tac `suffix` >> gvs[]
QED
