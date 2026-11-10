(* Consumer boundary after the destination ADD.  Compilation supplies the
   old-source premise; scalar children do not require source-buffer coverage.
   Runtime-code consumers must still retain the caller's ~ce_is_ctor premise. *)
Theory bodyPtrMakeArrayConsumerPost
Ancestors
  bodyPtrMakeArrayDispatch bodyPtrMakeArrayAddFrame exprOperandVar bodyPtrDefs emitHelper
  compileEnv loweringStateRelDefs context exprLowering vyperStorageBackend vyperTypeValues ptrDiscipline loweringPosts venomState

Theorem make_array_located_consumer_post:
  compile_expr cenv (expr_type e) e sa = (LocatedValue ty p,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv (LocatedValue ty p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue ty p) es' G tn s /\
  (~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (vv_operand (LocatedValue ty p)) G s) ==>
  p.ptr_location <> LocCalldata /\
  vv_post ctx func cenv cx e es sa sn s0 es' tv (LocatedValue ty p)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue ty p) es'
    (step_prov PG G (mk_inst sm.cs_next_id ADD [buf; Lit (n2w off)] [out])
      (update_var out w s))
    (step_taint (mk_inst sm.cs_next_id ADD [buf; Lit (n2w off)] [out]) s
      (update_var out w s) tn)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (vv_operand (LocatedValue ty p))
      (step_prov PG G (mk_inst sm.cs_next_id ADD [buf; Lit (n2w off)] [out])
        (update_var out w s))
      ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `!z. vv_operand (LocatedValue ty p) = Var z ==> not_fresh_at sm z`
    by metis_tac[cj 1 compiler_compile_var] >>
  `!z. vv_operand (LocatedValue ty p) = Var z ==> z <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all located_child_after_add_not_calldata >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  simp[] >> conj_tac
  >- (irule binop_source_ptr_vv_ok >> metis_tac[]) >>
  strip_tac >> irule binop_source_ptr_buf_ok >> metis_tac[]
QED

(* These are projections of the actual located-value post, not additional
   source provenance or global storage-liveness assumptions. *)
Theorem make_array_storage_consumer_read:
  vv_post ctx fn cenv cx e es sa sb s0 es' tv (LocatedValue ty p) s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  post_value_type cenv e = expr_type e ==>
  ?a tvt v.
    eval_operand p.ptr_operand s = SOME a /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    well_formed_type_value tvt /\
    read_result cx tv es' = (INL v,es') /\
    slots_in_range (get_storage cx es' tr) (w2n a) tvt /\
    decode_value (get_storage cx es' tr) (w2n a) tvt = SOME v /\
    storage_range_agree (get_storage cx es' tr)
      (if tr then contract_transient s else contract_storage s) a tvt
Proof
  Cases_on `tr` >>
  simp[vv_post_def, vv_holds_def, storage_holds_def] >>
  rpt strip_tac >>
  goal_assum (drule_at Any) >>
  fs[read_storage_slot_eq, AllCaseEqs()] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem make_array_storage_consumer_taint:
  ptr_vv_ok cx t tv (LocatedValue ty p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s = SOME a /\
  evaluate_type (get_tenv cx) t = SOME tvt ==>
  op_taint tn p.ptr_operand = {} /\
  (!k j. w2n a <= w2n k /\ w2n k < w2n a + type_slot_size tvt /\
    j < 32 /\ j IN key_taint (if tr then tn.t_trans else tn.t_stor) k ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n a) tvt (w2n k) j)
Proof
  Cases_on `tr` >>
  simp[ptr_vv_ok_def, key_taint_def, contract_storage_def, contract_transient_def,
    vfmStateTheory.lookup_account_def] >>
  rpt strip_tac >> metis_tac[]
QED
