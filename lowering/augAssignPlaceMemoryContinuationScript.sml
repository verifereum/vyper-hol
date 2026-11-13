(* Counted target traversal with a caller-supplied continuation. *)
Theory augAssignPlaceMemoryContinuation
Ancestors
  augAssignPlaceReadyContinuation augAssignPlaceMemoryTarget augAssignPlaceRhsMemory
  augAssignPlaceWordStoreMemory bodyAugAssignOther gasSummary
  targetPlaceSimMem stmtSimAugAssignPlaceMemory
  vyperInterpreter gasOutcome targetPlaceSimDefs
  gasContext targetPlaceSimCases vyperState vyperStorageFootprint
Libs
  pairLib

Theorem aug_place_target_mem_continuation:
  target_sim_mem ctx func cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p mid t marks.
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      target_post H ctx func cenv cx es sa sp s0 mid (PlaceR p) (Type ty) r t) /\
    t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL p, mid with gas_obs := tail)) /\
    gas_marked_path T ctx func s0 (LENGTH marks) (OK t) ==>
    gas_outcome T (cx_tops cx) (ctx,func) cx st0
      ((k p) : evaluation_state -> 'a evaluation_result) (mid,t) Q R) /\
  (!p. storage_trace_frame ((k p) : evaluation_state -> 'a evaluation_result)) /\
  (!H res ee rr. expr_exit (res : eval_result + exception) rr ==>
    ?ex. res = INR ex /\ R H (INR ex) ee rr) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (eval_target_place cx bt) k) (es,s0) Q R
Proof
  strip_tac >>
  mp_tac aug_place_target_ready_mem_continuation >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >>
      first_x_assum (qspecl_then [`p`, `mid`, `t`, `marks`] mp_tac) >>
      impl_tac
      >- (conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac
          >- (rpt strip_tac >>
              qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
                (qspec_then `H` mp_tac) >>
              impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
              first_assum ACCEPT_TAC) >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> first_assum ACCEPT_TAC
QED
