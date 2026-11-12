(* Uniform typed hash interface for the runtime MethodId consumer. *)
Theory bodyPtrEnvBuiltinsHashTyped
Ancestors bodyPtrEnvBuiltinsMemoryHashTyped bodyPtrEnvBuiltinsFixedHashTyped
  bodyPtrDefs exprSimDefs exprLoweringProps vyperTypeSystem vyperTyping
  vyperAST vyperValue compileEnv venomState words finite_map list

Theorem method_id_hash_typed_counted:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  ptr_val_ok cx (expr_type e) v arg G tn s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  compile_method_id_hash (expr_type e) arg sm = (op,sh) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct fn /\
  ghost_inv d cenv cx es' G tn s /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sh fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sh) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 32))) result op G' tn' t /\
    ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es' sm G tn s G' tn'
Proof
  strip_tac >> Cases_on `bty` >> gvs[is_bytes_or_string_type_def]
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      irule memory_hash_typed_counted >> simp[] >> metis_tac[]) >>
  rename1 `expr_type e = BaseT (BytesT bd)` >>
  Cases_on `bd` >> Cases_on `v` >> gvs[value_has_type_def]
  >- (drule_at (Pat `expr_type _ = _`) fixed_hash_typed_counted >>
      disch_then irule >> simp[value_has_type_def] >> metis_tac[]) >>
  irule memory_hash_typed_counted >> simp[] >> metis_tac[]
QED
