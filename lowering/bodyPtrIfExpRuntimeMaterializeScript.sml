Theory bodyPtrIfExpRuntimeMaterialize
Ancestors bodyPtrIfExpRuntimeSource bodyPtrIfExpRuntimeAllocated
  bodyPtrIfExpRuntimeContent context compileEnv fragExec loweringHalt
  immutableCopyExecution exprSimCopy exprLoweringProps pred_set
  bodyPtrIfExpActiveCopyPost bodyPtrIfExpRuntimeFrame exprSimStorageCopy
  loweringPosts compileEnv venomState finite_map

Theorem ifexp_ensure_memory_runtime_parts[local]:
  compile_ensure_in_memory src LocCode capacity n F imm sb = (dst,sd) /\
  fn_has_code sb sd fn ==>
  ?buf cs. compile_alloc_buffer capacity sb = (buf,cs) /\
    dst = buf.buf_operand /\
    compile_imm_copy_to_memory F imm src buf.buf_operand
      ((capacity+31) DIV 32) 0 cs = ((),sd) /\
    fn_has_code sb cs fn /\ fn_has_code cs sd fn
Proof
  strip_tac >> Cases_on `compile_alloc_buffer capacity sb` >>
  rename1 `compile_alloc_buffer capacity sb = (buf,cs)` >>
  Cases_on `compile_imm_copy_to_memory F imm src buf.buf_operand
    ((capacity+31) DIV 32) 0 cs` >>
  gvs[compile_ensure_in_memory_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  rename1 `compile_imm_copy_to_memory F imm src buf.buf_operand
    ((capacity+31) DIV 32) 0 cs = ((),sd)` >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  `ci_mono cs sd` by
    (mp_tac ci_mono_compile_imm_copy_to_memory >> metis_tac[pairTheory.SND]) >>
  `cs_extends cs sd` by fs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  simp[]
QED

Theorem ifexp_ensure_memory_runtime:
  post_value_type ce e = expr_type e /\
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue tag pp) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue tag pp) ee G tn s /\
  pp.ptr_location = LocCode /\ ~ce.ce_is_ctor /\
  n = (type_memory_bytes ce (expr_type e)+31) DIV 32 /\
  compile_ensure_in_memory pp.ptr_operand pp.ptr_location
    (type_memory_bytes ce (expr_type e)) n F imm sb = (dst,sd) /\
  fn_has_code sb sd fn /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  type_memory_bytes ce (expr_type e) < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb s ==>
  ?out d ty t H tt.
    dst = Var out /\ eval_operand dst t = SOME d /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
    (!m. mem_agree_outside tt.t_mem t.vs_memory m ==> val_in_memory ty v (w2n d) m) /\
    ptr_covers H tt out t (type_memory_bytes ce (expr_type e)) /\
    ghost_inv rty ce cx ee H tt t /\ ghost_kept ce es sa G0 tn0 s0 H tt /\
    (~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v dst t)
Proof
  strip_tac >> drule_all ifexp_runtime_arm_source >> strip_tac >>
  `compile_ensure_in_memory pp.ptr_operand LocCode
    (type_memory_bytes ce (expr_type e)) n F imm sb = (dst,sd)` by metis_tac[] >>
  drule_all ifexp_ensure_memory_runtime_parts >> strip_tac >>
  `compile_alloc_buffer (32*n) sb = (buf,cs) /\
   compile_imm_copy_to_memory F imm pp.ptr_operand buf.buf_operand n 0 cs = ((),sd) /\
   32*n < dimword (:256)` by metis_tac[] >>
  drule_all ifexp_runtime_allocated_execution >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "content"
QED

Resume ifexp_ensure_memory_runtime[content]:
  `32*n = type_memory_size ty /\ n = type_slot_size ty` by metis_tac[] >>
  `w2n d+type_memory_size ty < dimword (:256) /\
   t.vs_memory = (immutable_transfers F F a d (type_slot_size ty) 0 q).vs_memory` by
    metis_tac[] >>
  `!i. w2n d <= i /\ i < w2n d+type_memory_size ty ==> i NOTIN tt.t_mem` by
    (qpat_x_assum `tt.t_mem = _` (fn th => rewrite_tac[th]) >>
     simp[IN_DIFF, GSPECIFICATION] >> metis_tac[]) >>
  drule_all ifexp_runtime_copy_robust >> strip_tac >>
  suspend "semantic"
QED

Resume ifexp_ensure_memory_runtime[semantic]:
  drule_all copy_runtime_contents >> strip_tac >>
  drule_all ifexp_runtime_frame_static >> strip_tac >>
  `LENGTH q.vs_memory <= LENGTH t.vs_memory` by
    (qpat_x_assum `t.vs_memory = (immutable_transfers _ _ _ _ _ _ _).vs_memory`
       (fn th => rewrite_tac[th]) >> irule ifexp_runtime_transfers_length) >>
  `cs.cs_next_id <= sd.cs_next_id` by
    (`ci_mono cs sd` by
       (mp_tac ci_mono_compile_imm_copy_to_memory >> metis_tac[pairTheory.SND]) >>
     fs[ci_mono_def, cs_extends_def]) >>
  `!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x u` by
    (rpt strip_tac >> qpat_x_assum `!x. not_fresh_at cs x ==> _` drule >>
     simp[lookup_var_def]) >>
  suspend "post"
QED

Resume ifexp_ensure_memory_runtime[post]:
  `~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v dst t` by
    (strip_tac >> irule ifexp_allocated_copy_post >>
     simp[] >>
     qexistsl_tac [`buf`, `cs`, `d`, `out`, `raw`, `s`, `sb`, `32*n`, `u`,
       `LocatedValue tag pp`] >>
     simp[copy_static_def, eval_operand_def, lookup_var_def] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         mp_tac (Q.SPECL [`n`, `0`, `q`] ifexp_runtime_transfers_exterior) >>
         simp[] >> disch_then (qspecl_then [`b`, `len`] mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
     conj_tac
     >- (mp_tac (Q.SPECL [`n`, `0`, `q`] ifexp_runtime_transfers_length) >> simp[]) >>
     conj_tac
     >- (drule compile_alloc_buffer_parts >> strip_tac >>
         qpat_x_assum `!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x u`
           (qspec_then `out` mp_tac) >>
         gvs[lookup_var_def]) >>
     qpat_x_assum `val_in_memory ty v (w2n d) t.vs_memory` mp_tac >> simp[]) >>
  qexistsl_tac [`out`, `d`, `ty`, `t`, `H`, `tt`] >>
  simp[venomStateTheory.eval_operand_def] >> metis_tac[]
QED

Finalise ifexp_ensure_memory_runtime
