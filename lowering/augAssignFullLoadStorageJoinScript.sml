(* One fixed storage-load endpoint, with horizon-guarded query coverage. *)
Theory augAssignFullLoadStorageJoin
Ancestors
  augAssignFullLoadStorageResources augAssignFullLoadStorageStep
  bodyFullTargetDefs bodyPtrDefs ptrSafeRun ptrDiscipline codegenRel
  venomExecSemantics venomInst venomState loweringStateRelDefs
  compileEnv finite_map words pred_set list arithmetic

Theorem augassign_storage_load_joint:
  !DF lo d explicit ctx func PG cenv cx bt es st st0 sa sb sc s0 ty r s G tn
    tr slot tv old x opc i w raw u G1 tn1.
    x = STRING #"%" (toString sb.cs_next_var) /\
    opc = (if tr then TLOAD else SLOAD) /\
    i = mk_inst sb.cs_next_id opc [FST r] [x] /\
    w = (if tr then tload slot s else sload slot s) /\
    raw = update_var x w s /\
    u = (raw with vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G i raw /\
    tn1 = step_taint i s raw tn /\
    eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st) /\
    (!H. valid_horizon cx st0 H st.storage_trace ==>
      target_post H ctx func cenv cx es sa sb s0 st
        (PlaceR (StoragePlace tr slot tv)) (Type ty) r s /\
      target_ptr_ok cenv (PlaceR (StoragePlace tr slot tv)) r G tn s /\
      ghost_inv_at (DF H) lo d cenv cx st G tn s /\
      dead_lo_ok H (DF H) lo cenv cx) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    is_word_type ty /\
    emit_op opc [FST r] sb = (old,sc) /\
    fn_has_code sb sc func /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts
    ==>
    !H. valid_horizon cx st0 H st.storage_trace ==>
      (?cur. read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
        place_type_value cx (StoragePlace tr slot tv) st = (INL tv,st) /\
        evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
        w = typed_val_to_w256 tv cur /\
        eval_operand old u = SOME (typed_val_to_w256 tv cur)) /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G1,tn1) /\
      eval_operand (FST r) u = SOME slot /\
      op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
      ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      (!q. not_fresh_at sb q ==> lookup_var q u = lookup_var q s /\
        FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
    ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
    (rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     drule_all augassign_storage_load_resources >> strip_tac >>
     gvs[]) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    drule >> strip_tac >>
  drule_all augassign_storage_load_resources >> strip_tac >>
  qspec_then `\h. valid_horizon cx st0 h st.storage_trace`
    (drule_all o BETA_RULE) augassign_storage_load_joint_step >>
  disch_then (qspec_then `explicit` strip_assume_tac) >>
  conj_tac
  >- (qexists_tac `cur` >> simp[]) >>
  simp[] >> gvs[]
QED
