(* RHS snapshot boundaries. Active loads use the existing counted unwrap
   contract; composites are materialized only through a typed copy contract. *)
Theory bodyPtrAssignSnapshot
Ancestors
  bodyPtrIfExpWordUnwrap bodyPtrIfExpAllocResources bodyPtrIfExpUnwrapNoop
  bodyPtrIfExpNoopPost bodyPtrAssignUnwrapFrame bodyPtrAssignAllocSourceFrame
  loweringHalt words arithmetic bodyPtrIfExpBytesInputs
  bodyPtrDefs loweringPosts exprLowering compileEnv context fragGasPathPtr
  venomState venomExecSemantics

Theorem snapshot_word_counted_ptr:
  is_word_type (vv_type vv) /\ is_word_type (expr_type e) /\
  compile_snapshot_vv cenv copy vv sm = (saved,sb) /\
  vv_post ctx fn cenv cx e es sa sm s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (expr_type e) raw vv ee G tn s /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?op u G1 tn1.
    saved = StackValue (vv_type vv) op /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v op u /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 u /\
    ghost_inv d cenv cx ee G1 tn1 u /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  Cases_on `unwrap_value cenv vv sm` >>
  gvs[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
  drule_all ifexp_word_unwrap_suffix >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* For the identity unwrap branches only. The universally quantified premise
   is the store primitive's contract, starting AFTER allocation, not a
   materialization contract. In particular no pointer path for allocation
   is postulated here. Active storage/code unwrap is deliberately excluded. *)
Theorem materialize_identity_unwrap_counted_ptr:
  post_value_type cenv e = expr_type e /\ ~is_word_type (expr_type e) /\
  ((?ty op. vv = StackValue ty op) \/
   (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
           p.ptr_location = LocMemory)) /\
  compile_alloc_buffer (type_memory_bytes cenv (expr_type e)) sm = (buf,sc) /\
  compile_store_memory cenv (vv_operand vv) buf.buf_operand
    (expr_type e) (expr_type e) sc = ((),sb) /\
  vv_post ctx fn cenv cx e es sa sm s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_has_code sm sc fn /\ fn_inst_ids_distinct fn /\
  type_memory_bytes cenv (expr_type e) < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ptr_vv_ok cx (expr_type e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
     ptr_buf_ok cenv e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G s) /\
  (!t H tt out.
    buf.buf_operand = Var out /\
    ptr_covers H tt out t (type_memory_bytes cenv (expr_type e)) /\
    expr_post ctx fn cenv cx e es sa sc s0 ee v (vv_operand vv) t /\
    ptr_val_ok cx (expr_type e) v (vv_operand vv) H tt t /\
    ptr_buf_ok cenv e (vv_operand vv) H t /\
    ghost_inv d cenv cx ee H tt t /\ ghost_kept cenv es sa G0 tn0 s0 H tt /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts ==>
    ?u H' tt'.
      gas_path_ptr D 0 ctx fn PG H tt t 0 H' tt' (OK u) /\
      expr_post ctx fn cenv cx e es sa sb s0 ee v buf.buf_operand u /\
      ptr_val_ok cx (expr_type e) v buf.buf_operand H' tt' u /\
      ptr_covers H' tt' out u (type_memory_bytes cenv (expr_type e)) /\
      ghost_inv d cenv cx ee H' tt' u /\ ghost_kept cenv es sa G0 tn0 s0 H' tt' /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts) ==>
  compile_materialize_vv cenv (expr_type e) vv sm = (buf.buf_operand,sb) /\
  ?out u H tt.
    buf.buf_operand = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v buf.buf_operand u /\
    ptr_val_ok cx (expr_type e) v buf.buf_operand H tt u /\
    ptr_covers H tt out u (type_memory_bytes cenv (expr_type e)) /\
    ghost_inv d cenv cx ee H tt u /\ ghost_kept cenv es sa G0 tn0 s0 H tt /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `unwrap_value cenv vv sc = (vv_operand vv,sc)` by
    (gvs[unwrap_value_def, comp_return_def, vv_operand_def]) >>
  conj_tac
  >- gvs[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  drule_all compile_alloc_buffer_vv_source_frame >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all unwrap_value_noop_post >> strip_tac >>
  qpat_x_assum `!t H tt out. _` drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`H'`, `tt'`] >> gvs[] >>
  drule_all gas_path_ptr_then >> simp[]
QED

(* With no delayed-write hazard a composite is not read or copied. R may
   retain the complete semantic and ghost frame without duplicating it. *)
Theorem snapshot_nonword_nocopy_counted_ptr:
  ~is_word_type (vv_type vv) /\
  compile_snapshot_vv cenv F vv sm = (saved,sb) /\
  ~s.vs_halted /\ R sm G tn s ==>
  saved = vv /\ sb = sm /\ R sb G tn s /\
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK s)
Proof
  strip_tac >> gvs[compile_snapshot_vv_def, comp_return_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

(* The store boundary consumes annotation-sized source capacity, not a
   lowered-type ptr_buf_ok assertion. Allocation and unwrap are executed here. *)
Theorem materialize_nonword_counted_ptr:
  post_value_type cenv e = expr_type e /\ ~is_word_type (expr_type e) /\
  ~cenv.ce_is_ctor /\ same_memory_layout cenv (lowered_value_type cenv e) (expr_type e) /\
  expr_body_pre cenv cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  compile_alloc_buffer (type_memory_bytes cenv (expr_type e)) sm = (buf,sc) /\
  unwrap_value cenv vv sc = (src,su) /\
  compile_store_memory cenv src buf.buf_operand (expr_type e) (expr_type e) su = ((),sb) /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  vv_post ctx fn cenv cx e es sa sm s0 ee raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op ==> ptr_buf_ok cenv e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sc fn /\ fn_has_code sc su fn /\ fn_inst_ids_distinct fn /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty ==>
    type_memory_bytes cenv (expr_type e) = type_memory_size ty /\
    type_memory_size ty < 2**64) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ fresh_vars_wrt sm s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!t H tt out.
    buf.buf_operand = Var out /\
    ptr_covers H tt out t (type_memory_bytes cenv (expr_type e)) /\
    expr_post ctx fn cenv cx e es sa su s0 ee v src t /\
    ptr_val_ok cx (expr_type e) v src H tt t /\
    (!w. eval_operand src t = SOME w /\ type_memory_bytes cenv (expr_type e) <> 0 ==>
      ?x b sz. src = Var x /\ FLOOKUP H x = SOME (b,sz) /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv (expr_type e) <= b+sz) /\
    ghost_inv d cenv cx ee H tt t /\ ghost_kept cenv es sa G0 tn0 s0 H tt /\
    ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
    t.vs_inst_idx = LENGTH su.cs_current_insts ==>
    ?u H' tt'.
      gas_path_ptr D 0 ctx fn PG H tt t 0 H' tt' (OK u) /\
      expr_post ctx fn cenv cx e es sa sb s0 ee v buf.buf_operand u /\
      ptr_val_ok cx (expr_type e) v buf.buf_operand H' tt' u /\
      ptr_covers H' tt' out u (type_memory_bytes cenv (expr_type e)) /\
      ghost_inv d cenv cx ee H' tt' u /\ ghost_kept cenv es sa G0 tn0 s0 H' tt' /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts) ==>
  compile_materialize_vv cenv (expr_type e) vv sm = (buf.buf_operand,sb) /\
  ?out u H tt.
    buf.buf_operand = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v buf.buf_operand u /\
    ptr_val_ok cx (expr_type e) v buf.buf_operand H tt u /\
    ptr_covers H tt out u (type_memory_bytes cenv (expr_type e)) /\
    ghost_inv d cenv cx ee H tt u /\ ghost_kept cenv es sa G0 tn0 s0 H tt /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  conj_tac
  >- gvs[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  `?ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty` by
    metis_tac[bodyPtrIfExpBytesInputsTheory.ifexp_arm_annotation_typed] >>
  `type_memory_bytes cenv (expr_type e) < dimword (:256)` by
    (fs[dimword_def] >> decide_tac) >>
  `!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e op G s` by metis_tac[] >>
  drule_all (PURE_REWRITE_RULE
    [ASSUME ``post_value_type cenv e = expr_type e``]
    compile_alloc_buffer_vv_source_fresh_frame) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
   (!x. vv_operand vv = Var x ==> not_fresh_at sc x) /\ not_fresh_at sc out` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[] >> metis_tac[]) >>
  `!ty op. vv = StackValue ty op ==> ptr_buf_ok cenv e op G1 t` by
    metis_tac[] >>
  drule_all assign_unwrap_nonword_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ptr_covers H tt out t' (type_memory_bytes cenv (expr_type e))` by
    metis_tac[] >>
  qpat_x_assum `!t H tt out. _` (qspecl_then [`t'`, `H`, `tt`, `out`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`H'`, `tt'`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  metis_tac[gas_path_ptr_then, ADD]
QED
