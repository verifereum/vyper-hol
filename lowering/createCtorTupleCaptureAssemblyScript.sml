Theory createCtorTupleCaptureAssembly
Ancestors
  createCtorTupleCapture createCtorTuplePhysical createCtorTupleSuccess

(* The physical transport premise is discharged, including widened internal
   calls; captured raw results are not replaced by their delayed reads. *)
Theorem compile_multi_vvs_singleton_outcome:
  expr_body_pre ce cx env e es /\
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_multi_vvs compile_expr ce [e] c1 = ([vv],c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  (!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
  (!l. vv_operand vv <> Label l) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr_results cx [e])
      (\raws. bind (read_results cx raws) (\values. return (raws,values))))
    (es,s_buf)
    (\H res ee t. ?raw value tv.
      res = INL ([raw],[value]) /\
      vv_holds ce cx (lowered_value_type ce e) raw vv ee t /\
      vv_at ce cx (lowered_value_type ce e) c1 c_vvs ee raw vv t /\
      read_result cx raw ee = (INL value,ee) /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv value /\ val_wf tv value /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      alloca_inv t /\ alloca_room ctx func t /\ local_ptrs_reserved ce c_vvs /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      (!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
      (!l. vv_operand vv <> Label l) /\
      (!x w. not_fresh_at c1 x /\ lookup_var x s_buf = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s_buf.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s_buf.vs_allocas aid = SOME (off,sz) /\
        aid < c1.cs_next_id /\
        (!n b sz'. local_region ce es.scopes s_buf n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
        mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s_buf.vs_memory))
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >> irule ctor_capture_singleton_from_boundaries >>
  conj_tac >- ACCEPT_TAC ctor_capture_lowered_transport >>
  metis_tac[]
QED

Theorem compile_multi_vvs_pure_outcome:
  EVERY (\e. ~expr_has_effect e) args /\
  expr_sim_inv ce cx env es /\
  (!e ea. MEM e args /\ expr_sim_inv ce cx env ea ==>
    expr_body_pre ce cx env e ea /\
    expr_vv_sim ctx func ce cx (expr_type e) e ea /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok ea) /\
  compile_multi_vvs compile_expr ce args c1 = (vvs,c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  (!e ca cb vv. MEM e args /\
    compile_expr ce (expr_type e) e ca = (vv,cb) ==>
    (!x. vv_operand vv = Var x ==> not_fresh_at cb x) /\
    (!l. vv_operand vv <> Label l)) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr_results cx args)
      (\raws. bind (read_results cx raws) (\values. return (raws,values))))
    (es,s_buf)
    (\H res ee t. ?raws values.
      res = INL (raws,values) /\
      LENGTH vvs = LENGTH args /\
      LENGTH raws = LENGTH args /\ LENGTH values = LENGTH args /\
      (!i. i < LENGTH args ==>
        vv_holds ce cx (lowered_value_type ce (EL i args))
          (EL i raws) (EL i vvs) ee t /\
        vv_at ce cx (lowered_value_type ce (EL i args)) c1 c_vvs ee
          (EL i raws) (EL i vvs) t /\
        read_result cx (EL i raws) ee = (INL (EL i values),ee) /\
        (?tv. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
          value_has_type tv (EL i values) /\ val_wf tv (EL i values) /\
          type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size tv) /\
        (!x. vv_operand (EL i vvs) = Var x ==> not_fresh_at c_vvs x) /\
        (!l. vv_operand (EL i vvs) <> Label l)) /\
      stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      alloca_inv t /\ alloca_room ctx func t /\ local_ptrs_reserved ce c_vvs /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      (!x w. not_fresh_at c1 x /\ lookup_var x s_buf = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s_buf.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s_buf.vs_allocas aid = SOME (off,sz) /\
        aid < c1.cs_next_id /\
        (!n b sz'. local_region ce es.scopes s_buf n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
        mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s_buf.vs_memory))
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >> irule ctor_capture_pure_from_boundaries >>
  conj_tac >- ACCEPT_TAC ctor_capture_lowered_transport >>
  metis_tac[]
QED

Theorem compile_multi_vvs_singleton_capture:
  expr_body_pre ce cx env e es /\
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_multi_vvs compile_expr ce [e] c1 = ([vv],c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  (!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
  (!l. vv_operand vv <> Label l) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  ?marks. !tail raws values ee H.
    eval_expr_results cx [e]
      (es with gas_obs := gas_explicit marks s_buf.vs_gas_readings ++ tail) =
        (INL raws,ee) /\
    read_results cx raws ee = (INL values,ee) /\
    valid_horizon cx st0 H ee.storage_trace ==>
    ?t raw value tv.
      gas_marked_path F ctx func s_buf (LENGTH marks) (OK t) /\
      gas_marked_exec F (ctx,func)
        (bind (eval_expr_results cx [e])
          (\raws. bind (read_results cx raws) (\values. return (raws,values))))
        (es,s_buf) marks (INL (raws,values)) (ee with gas_obs := []) (OK t) /\
      ee.gas_obs = tail /\ raws = [raw] /\ values = [value] /\
      vv_holds ce cx (lowered_value_type ce e) raw vv (ee with gas_obs := []) t /\
      vv_at ce cx (lowered_value_type ce e) c1 c_vvs
        (ee with gas_obs := []) raw vv t /\
      read_result cx raw (ee with gas_obs := []) = (INL value,ee with gas_obs := []) /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv value /\ val_wf tv value /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      stmt_state_rel H ctx func ce cx (ee with gas_obs := []) t /\
      storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
      alloca_inv t /\ alloca_room ctx func t /\ local_ptrs_reserved ce c_vvs /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      (!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
      (!l. vv_operand vv <> Label l) /\
      (!x w. not_fresh_at c1 x /\ lookup_var x s_buf = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s_buf.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s_buf.vs_allocas aid = SOME (off,sz) /\
        aid < c1.cs_next_id /\
        (!n b sz'. local_region ce es.scopes s_buf n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
        mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s_buf.vs_memory)
Proof
  strip_tac >> drule_all compile_multi_vvs_singleton_outcome >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome _ _ _ _ _ _ _ Q _` >>
  `gas_outcome F (cx_tops cx) (ctx,func) cx st0
     (bind (eval_expr_results cx [e])
       (\raws. bind (read_results cx raws) (\values. return (raws,values))))
     (es,s_buf) Q (\H res ee r. expr_exit res r)` by
    (irule aggregateCountedOutcomeTheory.counted_outcome_conseq >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule ctor_outcome_selected_success >> strip_tac >>
  qexists `marks` >> rpt strip_tac >>
  qpat_x_assum `!tail v ee H. _`
    (qspecl_then [`tail`, `(raws,values)`, `ee`, `H`] mp_tac) >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  simp[Abbr `Q`] >> strip_tac >>
  qexistsl [`t`, `raw`, `value`, `tv`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem compile_multi_vvs_pure_capture:
  EVERY (\e. ~expr_has_effect e) args /\
  expr_sim_inv ce cx env es /\
  (!e ea. MEM e args /\ expr_sim_inv ce cx env ea ==>
    expr_body_pre ce cx env e ea /\
    expr_vv_sim ctx func ce cx (expr_type e) e ea /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok ea) /\
  compile_multi_vvs compile_expr ce args c1 = (vvs,c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  (!e ca cb vv. MEM e args /\
    compile_expr ce (expr_type e) e ca = (vv,cb) ==>
    (!x. vv_operand vv = Var x ==> not_fresh_at cb x) /\
    (!l. vv_operand vv <> Label l)) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  ?marks. !tail raws values ee H.
    eval_expr_results cx args
      (es with gas_obs := gas_explicit marks s_buf.vs_gas_readings ++ tail) =
        (INL raws,ee) /\
    read_results cx raws ee = (INL values,ee) /\
    valid_horizon cx st0 H ee.storage_trace ==>
    ?t. gas_marked_path F ctx func s_buf (LENGTH marks) (OK t) /\
      gas_marked_exec F (ctx,func)
        (bind (eval_expr_results cx args)
          (\raws. bind (read_results cx raws) (\values. return (raws,values))))
        (es,s_buf) marks (INL (raws,values)) (ee with gas_obs := []) (OK t) /\
      ee.gas_obs = tail /\
      LENGTH vvs = LENGTH args /\
      LENGTH raws = LENGTH args /\ LENGTH values = LENGTH args /\
      (!i. i < LENGTH args ==>
        vv_holds ce cx (lowered_value_type ce (EL i args))
          (EL i raws) (EL i vvs) (ee with gas_obs := []) t /\
        vv_at ce cx (lowered_value_type ce (EL i args)) c1 c_vvs
          (ee with gas_obs := []) (EL i raws) (EL i vvs) t /\
        read_result cx (EL i raws) (ee with gas_obs := []) =
          (INL (EL i values),ee with gas_obs := []) /\
        (?tv. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
          value_has_type tv (EL i values) /\ val_wf tv (EL i values) /\
          type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size tv) /\
        (!x. vv_operand (EL i vvs) = Var x ==> not_fresh_at c_vvs x) /\
        (!l. vv_operand (EL i vvs) <> Label l)) /\
      stmt_state_rel H ctx func ce cx (ee with gas_obs := []) t /\
      storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
      alloca_inv t /\ alloca_room ctx func t /\ local_ptrs_reserved ce c_vvs /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      (!x w. not_fresh_at c1 x /\ lookup_var x s_buf = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s_buf.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s_buf.vs_allocas aid = SOME (off,sz) /\
        aid < c1.cs_next_id /\
        (!n b sz'. local_region ce es.scopes s_buf n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
        mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s_buf.vs_memory)
Proof
  strip_tac >> drule_all compile_multi_vvs_pure_outcome >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome _ _ _ _ _ _ _ Q _` >>
  `gas_outcome F (cx_tops cx) (ctx,func) cx st0
     (bind (eval_expr_results cx args)
       (\raws. bind (read_results cx raws) (\values. return (raws,values))))
     (es,s_buf) Q (\H res ee r. expr_exit res r)` by
    (irule aggregateCountedOutcomeTheory.counted_outcome_conseq >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule ctor_outcome_selected_success >> strip_tac >>
  qexists `marks` >> rpt strip_tac >>
  qpat_x_assum `!tail v ee H. _`
    (qspecl_then [`tail`, `(raws,values)`, `ee`, `H`] mp_tac) >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  simp[Abbr `Q`] >> strip_tac >> gvs[] >>
  qexists `t` >> simp[] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH args ==> _` drule >> simp[]
QED
