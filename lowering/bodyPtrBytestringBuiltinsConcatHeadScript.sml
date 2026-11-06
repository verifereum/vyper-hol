(* Compiler cuts for one Concat iteration, before pointer execution dispatch. *)
Theory bodyPtrBytestringBuiltinsConcatHead
Ancestors
  bodyPtrBytestringBuiltinsConcatFrame bodyPtrBytestringBuiltinsConcatBytes
  bodyPtrBytestringBuiltinsEval exprLowering emitHelper compileEnv
  representationCleanPtr valueCopyBytes
Libs monadsyntax

Theorem compile_concat_bytes_cons:
  compile_concat compile_expr cenv (e::es) data_ptr ((T,m)::infos) off_ptr sa =
    ((),sb) ==>
  ?op sm sn.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    (do arg_len <- emit_op MLOAD [op];
        arg_data <- emit_op ADD [op;Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr;offset_op];
        emit_void MCOPY [dst;arg_data;arg_len];
        new_offset <- emit_op ADD [offset_op;arg_len];
        emit_void MSTORE [off_ptr;new_offset]
     od) sm = ((),sn) /\
    compile_concat compile_expr cenv es data_ptr infos off_ptr sn = ((),sb)
Proof
  simp[Once compile_concat_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_concat_fixed_cons:
  compile_concat compile_expr cenv (e::es) data_ptr ((F,m)::infos) off_ptr sa =
    ((),sb) ==>
  ?op sm sn.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr;offset_op];
        emit_void MSTORE [dst;op];
        new_offset <- emit_op ADD [offset_op;Lit (n2w m)];
        emit_void MSTORE [off_ptr;new_offset]
     od) sm = ((),sn) /\
    compile_concat compile_expr cenv es data_ptr infos off_ptr sn = ((),sb)
Proof
  simp[Once compile_concat_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Operand exceptions are handled by the suffix combinator.  On the normal
   branch, expose scratch frames uniformly, so the two scratch allocations
   can be instantiated independently without unfolding the simulation. *)
Theorem concat_operand_eval_suffix:
  expr_body_pre cenv cx env e es /\
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee gt r. expr_exit (INR exc : value + exception) r ==>
    R (INR exc) ee gt r) /\
  (!v ee G tn t.
    expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (expr_type e) v op G tn t /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    (?marks ee0. ee = ee0 with gas_obs := [] /\
      !tail. vyperState$bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,ee0 with gas_obs := tail)) /\
    expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v) /\
    (is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
           value_has_type tv v) /\
    (!aid b sz p n.
      FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
      (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b) /\
      b <= p /\ p+n <= b+sz /\
      (!i. p <= i /\ i < p+n ==> i NOTIN tn0.t_mem) ==>
      FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory /\
      (!i. p <= i /\ i < p+n ==> i NOTIN tn.t_mem)) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x t = SOME w /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x) /\
      !capacity. ptr_covers G0 tn0 x s0 capacity ==>
        ptr_covers G tn x t capacity) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (k v) (ee,t,G,tn) Q R) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx)) k)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> irule expr_sim_ptr_eval_suffix >>
  first_assum (irule_at (Pat `expr_sim_ptr _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v) /\
   (is_word_type (expr_type e) ==>
     ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
          value_has_type tv v)` by
    (irule operand_eval_evidence_semantics >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> metis_tac[]) >>
  first_x_assum irule >> asm_rewrite_tac[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all expr_operand_old_pointer_frame >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all expr_operand_old_allocation_frame >> simp[]) >>
  metis_tac[]
QED

(* Robust operand representations provide actual header/payload cleanliness,
   not merely allocation coverage. *)
Theorem concat_bytes_operand_source:
  is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  ptr_val_ok cx ty v op G tn s /\ eval_operand op s = SOME w ==>
  ?bs.
    (v = BytesV bs \/ ?str. v = StringV str /\ bs = MAP (n2w o ORD) str) /\
    mload (w2n w) s = n2w (LENGTH bs) /\
    mem_bytes_at (w2n w+32) (LENGTH bs) s.vs_memory = bs /\
    (!i. w2n w <= i /\ i < w2n w+32+LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem` by
    (fs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def]) >>
  drule_all bytestring_type_value >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
  >- suspend "bytes"
  >> suspend "string"
QED

Resume concat_bytes_operand_source[bytes]:
  drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV l)
     (w2n w) s.vs_memory` by
    (first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  gvs[valueEncodingTheory.val_in_memory_def,
      valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  rpt strip_tac >> Cases_on `i < w2n w+32` >> metis_tac[arithmeticTheory.NOT_LESS]
QED

Resume concat_bytes_operand_source[string]:
  drule robust_val_in_memory_string_clean >> simp[] >> strip_tac >>
  `val_in_memory (BaseTV (StringT n)) (StringV s')
     (w2n w) s.vs_memory` by
    (first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  gvs[valueEncodingTheory.val_in_memory_def,
      valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  rpt strip_tac >> Cases_on `i < w2n w+32` >> metis_tac[arithmeticTheory.NOT_LESS]
QED

Finalise concat_bytes_operand_source
