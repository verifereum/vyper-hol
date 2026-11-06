(* Consumer-normalized continuation boundaries. *)
Theory exprSimSliceOrdinaryEntry
Ancestors
  exprSimSliceOrdinaryContinue vyperAST exprSimSliceMemory exprSimHash
  exprSimProps exprSimWordArgs exprSimCalldataSlice loweringPosts venomState

Theorem slice_bytes_continue_entry:
  expr_type src = BaseT bt /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  expr_sim_case nocalls ctx func cenv cx len /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH bs)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH bs) u.vs_memory = bs /\
  src_base + LENGTH bs < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH bs) r2.vs_memory = bs) /\
  32+n <= sz /\ sz < dimword (:256) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH bs <= bytelike_type_bound (BaseT bt) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (BaseT (BytesT (Dynamic n))) (Slice n)
          [BaseT bt; BaseT (UintT 256); BaseT (UintT 256)] [BytesV bs;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [src;start;len]) ec sc sf u ee tv
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL slice_bytes_continue |> Q.INST
    [`result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [src;start;len]`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[] >> impl_tac >- (rpt strip_tac >> first_x_assum irule >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem slice_string_continue_entry:
  expr_type src = BaseT bt /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  expr_sim_case nocalls ctx func cenv cx len /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH text)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH text) u.vs_memory = MAP (n2w o ORD) text /\
  src_base + LENGTH text < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH text) r2.vs_memory = MAP (n2w o ORD) text) /\
  32+n <= sz /\ sz < dimword (:256) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH text <= bytelike_type_bound (BaseT bt) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (BaseT (StringT n)) (Slice n)
          [BaseT bt; BaseT (UintT 256); BaseT (UintT 256)] [StringV text;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (StringT n)) (Slice n) [src;start;len]) ec sc sf u ee tv
        (LocatedValue (BaseT (StringT n)) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL slice_string_continue |> Q.INST
    [`result` |-> `Builtin (BaseT (StringT n)) (Slice n) [src;start;len]`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[] >> impl_tac >- (rpt strip_tac >> first_x_assum irule >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[]) >>
  simp[]
QED

(* Capture code preserves the source entry frame, including at the adjusted
   instruction index used to enter the next operand. *)
Theorem slice_bytestring_capture_frame:
  compile_bytestring_src src sb = ((sl,data),sc) /\
  eval_operand src t = SOME p /\
  (!x. src = Var x ==> not_fresh_at sb x) /\
  run_inst_seq (emitted_insts sb sc) t = OK u ==>
  wb_frame cenv ec sb t (u with vs_inst_idx := k)
Proof
  strip_tac >> drule_all slice_bytestring_src_run >> strip_tac >>
  gvs[] >>
  `t'.vs_memory = t.vs_memory /\ t'.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `t' = t with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[wb_frame_def, lookup_var_def, locals_kept_mem]
QED

Theorem slice_fixed_capture_frame:
  compile_alloc_buffer 32 sb = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((),sc) /\
  (!x. val_op = Var x ==> not_fresh_at sb x) /\
  eval_operand val_op t = SOME w /\
  stmt_state_rel ctx func cenv cx ec t /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
  run_inst_seq (emitted_insts sb sc) t = OK u ==>
  wb_frame cenv ec sb t (u with vs_inst_idx := k)
Proof
  strip_tac >> drule_all hash_alloc_mstore_frame >> strip_tac >> gvs[] >>
  simp[wb_frame_def, lookup_var_def] >> rpt conj_tac
  >- (rpt strip_tac >> fs[lookup_var_def])
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. aid < _ /\ _ ==> _` irule >>
      qexists_tac `aid` >> simp[]) >>
  irule locals_kept_regions_tail >> qexists_tac `t` >>
  simp[locals_kept_refl] >> rpt strip_tac >> first_x_assum irule >>
  qexists_tac `n` >> simp[]
QED

Theorem slice_source_capture_post_rebase:
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ec.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id <= sc.cs_next_id /\
  expr_post ctx func cenv cx src es sa sb s0 ec v op t /\
  wb_frame cenv ec sb t u /\
  vv_post ctx func cenv cx result ec sc sf u ef tv vv z ==>
  vv_post ctx func cenv cx result es sa sf s0 ef tv vv z
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `wb_frame cenv es sa s0 u` by
    (drule_all wb_frame_trans >> simp[]) >>
  irule vv_post_prefix_frame >>
  simp[] >> qexistsl_tac [`ec`, `sc`, `u`] >> simp[]
QED

Theorem slice_bytestring_source_post_rebase:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ec.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id <= sc.cs_next_id /\
  expr_post ctx func cenv cx src es sa sb s0 ec v op t /\
  compile_bytestring_src op sb = ((sl,data),sc) /\
  eval_operand op t = SOME p /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  run_inst_seq (emitted_insts sb sc) t = OK u /\
  vv_post ctx func cenv cx result ec sc sf
    (u with vs_inst_idx := LENGTH sc.cs_current_insts) ef tv vv z ==>
  vv_post ctx func cenv cx result es sa sf s0 ef tv vv z
Proof
  strip_tac >>
  drule_all slice_bytestring_capture_frame >>
  disch_then (qspec_then `LENGTH sc.cs_current_insts` assume_tac) >>
  irule slice_source_capture_post_rebase >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem slice_fixed_source_post_rebase:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ec.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id <= sc.cs_next_id /\
  expr_post ctx func cenv cx src es sa sb s0 ec v op t /\
  compile_alloc_buffer 32 sb = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; op] sm = ((),sc) /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ eval_operand op t = SOME w /\
  stmt_state_rel ctx func cenv cx ec t /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
  run_inst_seq (emitted_insts sb sc) t = OK u /\
  vv_post ctx func cenv cx result ec sc sf
    (u with vs_inst_idx := LENGTH sc.cs_current_insts) ef tv vv z ==>
  vv_post ctx func cenv cx result es sa sf s0 ef tv vv z
Proof
  strip_tac >>
  drule_all slice_fixed_capture_frame >>
  disch_then (qspec_then `LENGTH sc.cs_current_insts` assume_tac) >>
  irule slice_source_capture_post_rebase >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

(* Sequential normalized entry points; compiler type indices remain general. *)
Theorem slice_bytes_continue_entry_seq:
  expr_type src = BaseT bt /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  ((?s tv t s1 v t1. eval_expr cx start s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==>
    expr_sim_case nocalls ctx func cenv cx len) /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH bs)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH bs) u.vs_memory = bs /\
  src_base + LENGTH bs < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    expr_sim_inv cenv cx env es1 /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH bs) r2.vs_memory = bs) /\
  32+n <= sz /\ sz < dimword (:256) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH bs <= bytelike_type_bound (BaseT bt) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (BaseT (BytesT (Dynamic n))) (Slice n)
          [BaseT bt; BaseT (UintT 256); BaseT (UintT 256)] [BytesV bs;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [src;start;len]) ec sc sf u ee tv
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL slice_bytes_continue_seq |> Q.INST
    [`result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [src;start;len]`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[] >> impl_tac >- (conj_tac >- (first_x_assum ACCEPT_TAC) >>
    rpt strip_tac >> first_x_assum irule >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem slice_string_continue_entry_seq:
  expr_type src = BaseT bt /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_case nocalls ctx func cenv cx start /\
  ((?s tv t s1 v t1. eval_expr cx start s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==>
    expr_sim_case nocalls ctx func cenv cx len) /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = []) /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH text)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH text) u.vs_memory = MAP (n2w o ORD) text /\
  src_base + LENGTH text < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    expr_sim_inv cenv cx env es1 /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH text) r2.vs_memory = MAP (n2w o ORD) text) /\
  32+n <= sz /\ sz < dimword (:256) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH text <= bytelike_type_bound (BaseT bt) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (BaseT (StringT n)) (Slice n)
          [BaseT bt; BaseT (UintT 256); BaseT (UintT 256)] [StringV text;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (StringT n)) (Slice n) [src;start;len]) ec sc sf u ee tv
        (LocatedValue (BaseT (StringT n)) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  mp_tac (SPEC_ALL slice_string_continue_seq |> Q.INST
    [`result` |-> `Builtin (BaseT (StringT n)) (Slice n) [src;start;len]`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[] >> impl_tac >- (conj_tac >- (first_x_assum ACCEPT_TAC) >>
    rpt strip_tac >> first_x_assum irule >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[]) >>
  simp[]
QED
