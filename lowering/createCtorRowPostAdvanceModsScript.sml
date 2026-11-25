(* Project the endpoint fields of a successful singleton constructor post. *)
Theory createCtorRowPostAdvanceMods
Ancestors
  createCtorSavedRows createExprSizeExitDefsMods
  bodyFullExtCallPosList bodyStorageCases exprSimWordArgs exprLoweringProps
  vyperStorageTrace vyperStorageFootprint vyperState list rich_list

Theorem ctor_row_post_advance_mods:
  (?K. valid_horizon cx st0 K ee.storage_trace) /\
  (!K. valid_horizon cx st0 K ee.storage_trace ==>
    extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [sv]
      sa sb es s g h K (INL [v] : value list + exception) ee G tn t) ==>
  expr_sim_inv_mods mods ce cx env ee /\
  return_buf_frame d ce sb t /\
  alloca_history func t /\
  ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!K. valid_horizon cx st0 K ee.storage_trace ==>
    stmt_state_rel K ctx func ce cx ee t /\
    storage_well_formed_on cx ee (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx ee G tn t)
Proof
  rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?K. valid_horizon cx st0 K ee.storage_trace`
    (qx_choosel_then [`K0`] assume_tac) >>
  qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==> _`
    (qspec_then `K0` (drule_then
      (MAP_EVERY assume_tac o CONJUNCTS o
       SIMP_RULE (srw_ss()) [extcall_positional_post_mods_def]))) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >> (gen_tac >> disch_tac >>
      qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==> _`
        (qspec_then `K'` (drule_then
          (MAP_EVERY assume_tac o CONJUNCTS o
           SIMP_RULE (srw_ss()) [extcall_positional_post_mods_def]))) >>
      simp[])
QED
