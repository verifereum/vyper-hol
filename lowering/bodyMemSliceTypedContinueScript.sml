(* Memory-mode typed continuation after capture of a slice source. *)
Theory bodyMemSliceTypedContinue
Ancestors
  bodyMemSliceContinue bodyMemSliceTerminal exprSimSliceOrdinaryContinue
  exprSimSliceOrdinaryFrame exprSimSliceCompose

Theorem slice_bytes_continue_seq_mem:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_mem ctx func cenv cx ty start ec /\
  (!gs v ee. bind (eval_expr cx start) (read_result cx) (ec with gas_obs := gs) =
      (INL v,ee) /\ ee.gas_obs = [] ==>
    expr_sim_mem ctx func cenv cx ty len ee /\
    gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok ee) /\
  gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok ec /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ alloca_history func u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH bs)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH bs) u.vs_memory = bs /\
  src_base + LENGTH bs <= u.vs_alloca_next /\
  src_base + LENGTH bs < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    expr_sim_inv cenv cx env es1 /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH bs) r2.vs_memory = bs) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type result = BaseT (BytesT (Dynamic n)) /\
  lowered_value_type cenv result = expr_type result /\
  sz = type_memory_bytes cenv (lowered_value_type cenv result) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH bs <= bytelike_type_bound (expr_type src) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type result) (Slice n)
          (MAP expr_type [src;start;len]) [BytesV bs;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result ec sc sf u ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      vv_store_bound cx (expr_type result) (lowered_value_type cenv result) ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> ho_match_mp_tac slice_two_read_outcome_seq_mem >> simp[] >>
  conj_tac >- (first_x_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `eval_operand sl r = SOME (n2w (LENGTH bs)) /\
   eval_operand data r = SOME (n2w src_base)` by
    (qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_two_posts_operands) >>
     disch_then drule >>
     disch_then (fn th => conj_tac >> irule th >> fs[] >> metis_tac[])) >>
  `eval_operand sop r = SOME (n2w i)` by
    (qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_post_operands) >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  `mem_bytes_at src_base (LENGTH bs) r.vs_memory = bs` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`start`, `len`, `e1`, `e2`, `sop`, `lop`, `t`, `sd`, `se`,
                    `IntV (&i)`, `IntV (&k)`] >> simp[]) >>
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ee z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result e2 se sf r ee tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    vv_store_bound cx (expr_type result) (lowered_value_type cenv result) ee tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    z.vs_current_bb = sf.cs_current_bb /\ z.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_history func z /\ r.vs_alloca_next <= z.vs_alloca_next)` >>
  qexists_tac `(\res ee r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac >- (BETA_TAC >> rpt strip_tac >> qexists_tac `tv` >>
    simp[] >> metis_tac[slice_two_operand_post_rebase]) >>
  `src_base + LENGTH bs <= r.vs_alloca_next` by decide_tac >>
  drule_all slice_data_bytes_outcome_mem >> simp[]
QED

Theorem slice_string_continue_seq_mem:
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_body_pre cenv cx env start ec /\ expr_body_pre cenv cx env len ec /\
  expr_sim_mem ctx func cenv cx ty start ec /\
  (!gs v ee. bind (eval_expr cx start) (read_result cx) (ec with gas_obs := gs) =
      (INL v,ee) /\ ee.gas_obs = [] ==>
    expr_sim_mem ctx func cenv cx ty len ee /\
    gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok ee) /\
  gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok ec /\
  lower_value compile_expr cenv ty start sc = (sop,sd) /\
  lower_value compile_expr cenv ty len sd = (lop,se) /\
  compile_slice_data sl data sop lop sz se = (out,sf) /\
  fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  stmt_state_rel ctx func cenv cx ec u /\ alloca_history func u /\ ~u.vs_halted /\
  u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand sl u = SOME (n2w (LENGTH text)) /\
  eval_operand data u = SOME (n2w src_base) /\
  (!op z. MEM op [sl;data] /\ op = Var z ==> not_fresh_at sc z /\ not_fresh_at sd z) /\
  (!op l. MEM op [sl;data;sop] ==> op <> Label l) /\
  (!z. sop = Var z ==> not_fresh_at sd z) /\
  (!op z. MEM op [sl;data;sop;lop] /\ op = Var z ==> not_fresh_at se z) /\
  mem_bytes_at src_base (LENGTH text) u.vs_memory = MAP (n2w o ORD) text /\
  src_base + LENGTH text <= u.vs_alloca_next /\
  src_base + LENGTH text < dimword (:256) /\
  (!sd' se' e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
    local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd'.cs_next_id /\
    expr_sim_inv cenv cx env es1 /\
    MAP FDOM ec.scopes = MAP FDOM es1.scopes /\
    expr_post ctx func cenv cx e1 ec sc sd' u es1 v1 op1 r1 /\
    expr_post ctx func cenv cx e2 es1 sd' se' r1 es2 v2 op2 r2 ==>
    mem_bytes_at src_base (LENGTH text) r2.vs_memory = MAP (n2w o ORD) text) /\
  32+n <= sz /\ sz < dimword (:256) /\
  expr_type result = BaseT (StringT n) /\
  lowered_value_type cenv result = expr_type result /\
  sz = type_memory_bytes cenv (lowered_value_type cenv result) /\
  slice_operands_ok (Slice n) [src;start;len] /\
  LENGTH text <= bytelike_type_bound (expr_type src) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc (expr_type result) (Slice n)
          (MAP expr_type [src;start;len]) [StringV text;sv;lv]);
        return (Value v) od) (ec,u)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx result ec sc sf u ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      vv_store_bound cx (expr_type result) (lowered_value_type cenv result) ee tv
        (LocatedValue (expr_type result) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> ho_match_mp_tac slice_two_read_outcome_seq_mem >> simp[] >>
  conj_tac >- (first_x_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `eval_operand sl r = SOME (n2w (LENGTH text)) /\
   eval_operand data r = SOME (n2w src_base)` by
    (qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_two_posts_operands) >>
     disch_then drule >>
     disch_then (fn th => conj_tac >> irule th >> fs[] >> metis_tac[])) >>
  `eval_operand sop r = SOME (n2w i)` by
    (qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_post_operands) >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  `mem_bytes_at src_base (LENGTH text) r.vs_memory = MAP (n2w o ORD) text` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`start`, `len`, `e1`, `e2`, `sop`, `lop`, `t`, `sd`, `se`,
                    `IntV (&i)`, `IntV (&k)`] >> simp[]) >>
  irule slice_gas_outcome_conseq >>
  qexists_tac `(\res ee z. ?tv. res = INL tv /\
    vv_post ctx func cenv cx result e2 se sf r ee tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    vv_store_bound cx (expr_type result) (lowered_value_type cenv result) ee tv
      (LocatedValue (expr_type result) (mk_ptr out LocMemory)) z /\
    z.vs_current_bb = sf.cs_current_bb /\ z.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_history func z /\ r.vs_alloca_next <= z.vs_alloca_next)` >>
  qexists_tac `(\res ee r. expr_exit res r)` >>
  conj_tac >- simp[] >>
  conj_tac >- (BETA_TAC >> rpt strip_tac >> qexists_tac `tv` >>
    simp[] >> metis_tac[slice_two_operand_post_rebase]) >>
  `src_base + LENGTH text <= r.vs_alloca_next` by decide_tac >>
  drule_all slice_data_string_outcome_mem >> simp[]
QED
