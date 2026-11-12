(* The counted allocation advances its cursor; raw sequence semantics does not. *)
Theory exprPtrUnwrapCodeCopySemantic
Ancestors
  exprPtrUnwrapAllocation exprSimCopy exprPtrCodeCopyInduction
  exprLoweringProps fragExec instIdxIndep venomExecSemantics venomInst
  compileEnv venomState list exprPtrCodeCopyPost exprSimVVFrame loweringPosts
  context finite_map

Theorem unwrap_code_copy_shifted_run:
  compile_alloc_buffer nb sm = (buf,mid) /\ buf.buf_operand = Var root /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ copy_runtime_frame mid a sb z ==>
  run_inst_seq (emitted_insts sm sb) (s with vs_inst_idx := k) = OK z
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  `root = out` by gvs[] >> fs[] >>
  `run_inst_seq (emitted_insts sm mid) s = OK u` by
    simp[run_inst_seq_def] >>
  `run_inst_seq (emitted_insts sm mid) (s with vs_inst_idx := k) = OK a` by
    (simp[run_inst_seq_inst_idx, mk_inst_def, is_terminator_def,
      exec_result_map_def]) >>
  `sb.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid sb /\
    run_inst_seq (emitted_insts mid sb) a = OK z` by
    fs[copy_runtime_frame_def] >>
  `mid.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm mid` by simp[] >>
  drule_all run_inst_seq_chain >> simp[]
QED

Theorem unwrap_code_copy_endpoint_post:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!ty. evaluate_type (get_tenv cx) t = SOME ty ==>
    type_memory_bytes cenv t = type_memory_size ty) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  compile_alloc_buffer nb sm = (buf,mid) /\ buf.buf_operand = Var root /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ copy_runtime_frame mid a sb z ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op z
Proof
  strip_tac >> drule_all unwrap_code_copy_shifted_run >> disch_tac >>
  irule unwrap_code_same_endpoint_post >> ntac 4 (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  asm_rewrite_tac[vv_post_inst_idx] >> qexistsl [`p`, `t`] >> simp[]
QED
