Theory bodyPtrIfExpWordUnwrap
Ancestors
  bodyPtrIfExpWord bodyPtrIfExpWordMemory bodyPtrIfExpWordScalar
  bodyPtrDefs loweringPosts exprLowering compileEnv vyperAST context

Theorem ifexp_word_unwrap_suffix:
  is_word_type (expr_type e) /\
  unwrap_value cenv vv sm = (op,sb) /\
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
  ?u G1 tn1. gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v op u /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 u /\
    ghost_inv d cenv cx ee G1 tn1 u /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `vv`
  >- (drule_all ifexp_stack_unwrap_counted >>
      disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
      gvs[] >> qexistsl [`s`,`G`,`tn`] >> simp[]) >>
  drule_all ifexp_word_unwrap_dispatch >> strip_tac >> gvs[vv_operand_def] >>
  rename1 `LocatedValue (expr_type e) p` >>
  `compile_ptr_load F cenv.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb)` by
    metis_tac[] >>
  Cases_on `p.ptr_location` >> gvs[]
  >- (irule ifexp_memory_word_suffix >> metis_tac[])
  >- (irule ifexp_storage_word_suffix >> simp[] >>
      goal_assum (drule_at Any) >> qexistsl [`raw`,`F`] >> simp[] >> metis_tac[])
  >- (irule ifexp_storage_word_suffix >> simp[] >>
      goal_assum (drule_at Any) >> qexistsl [`raw`,`T`] >> simp[] >> metis_tac[]) >>
  irule ifexp_code_word_suffix >> metis_tac[]
QED
