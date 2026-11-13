(* Counted target traversal with a caller-supplied continuation. *)
Theory augAssignPlaceMemoryContinuation
Ancestors
  augAssignPlaceReadyContinuation augAssignPlaceMemoryTarget augAssignPlaceRhsMemory
  augAssignPlaceWordStoreMemory bodyAugAssignOther gasSummary
  targetPlaceSimMem stmtSimAugAssignPlaceMemory stmtSimAugAssignPlaceStorage
  vyperInterpreter gasOutcome targetPlaceSimDefs
  gasContext targetPlaceSimCases vyperState
Libs
  pairLib

Theorem aug_place_target_mem_continuation:
  target_sim_mem ctx func cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p mid t marks.
    target_post ctx func cenv cx es sa sp s0 mid (PlaceR p) (Type ty) r t /\
    t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL p, mid with gas_obs := tail)) /\
    gas_marked_path T ctx func s0 (LENGTH marks) (OK t) ==>
    gas_outcome T (cx_tops cx) (ctx,func) ((k p) : evaluation_state -> 'a evaluation_result) (mid,t) Q R) /\
  (!res ee rr. expr_exit (res : eval_result + exception) rr ==> ?ex. res = INR ex /\ R (INR ex) ee rr) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_target_place cx bt) k) (es,s0) Q R
Proof
  strip_tac >>
  irule aug_place_target_ready_mem_continuation >> simp[] >>
  metis_tac[]
QED
