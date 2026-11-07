(* Reuse an already checked admissible body frame.  The expression fixture
   abbreviates the exact two-literal AST used by ConcatRunProbe. *)
Theory bodyPtrBytestringBuiltinsConcatAdmissionProbe
Ancestors bodyPtrBytestringBuiltinsConcatRunProbe
  bodyPtrBytestringBuiltinsPtrFrame bodyPtrBytestringBuiltinsSourceFrame
  vyperTypeSystem exprSimHypsDefs allocLimits supportedExprTraverse
  exprSimPtrLiteral exprSimSource bodyPtrPreds

Definition concat_admission_expr_def:
  concat_admission_expr =
    Builtin (BaseT (BytesT (Dynamic 2))) (Concat 2)
      [Literal (BaseT (BytesT (Fixed 1))) (BytesL [1w]);
       Literal (BaseT (BytesT (Fixed 1))) (BytesL [2w])]
End

Theorem concat_admission_typed:
  !env. well_typed_expr env concat_admission_expr
Proof
  EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  qexists_tac `Fixed 1` >> simp[]
QED

Theorem concat_admission_syntax:
  int_calls_expr concat_admission_expr = [] /\
  byte_widths_expr concat_admission_expr /\
  ~expr_has_evm_run concat_admission_expr /\
  builtin_args_length_ok (Concat 2) 2 /\
  !cenv. alloc_limits_expr cenv concat_admission_expr
Proof
  EVAL_TAC >> simp[]
QED

Theorem concat_admission_body_pre:
  expr_body_pre order_ptr_env order_ptr_cx order_ptr_tenv
    concat_admission_expr order_ptr_source
Proof
  simp[expr_body_pre_def, order_ptr_sim_inv, concat_admission_typed,
       concat_admission_syntax, order_ptr_call_safety] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  simp[order_ptr_cx_def, order_frame_cx_def,
       gasContextTheory.cx_tops_def, vyperContextTheory.get_tenv_def,
       vyperContextTheory.get_module_code_def] >>
  EVAL_TAC >> simp[]
QED

Theorem literal_body_ptr:
  !cx ann l. body_expr_ptr_ok cx (Literal ann l)
Proof
  simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  irule literal_expr_sim_ptr >> qexists_tac `env` >>
  simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def]
QED

Theorem concat_admission_operand_judgments:
  !cx. body_exprs_ptr_ok cx
    [Literal (BaseT (BytesT (Fixed 1))) (BytesL [1w]);
     Literal (BaseT (BytesT (Fixed 1))) (BytesL [2w])]
Proof
  simp[body_exprs_ptr_ok_def, literal_body_ptr]
QED


Theorem concat_admission_compilation:
  compile_expr order_ptr_env (BaseT (BytesT (Dynamic 2)))
    concat_admission_expr (initial_compile_state "entry") =
  concat_probe_compiled
Proof
  rewrite_tac[concat_admission_expr_def,
              concat_probe_compile_env_independent]
QED

(* The bare execution fixture is not yet a frame witness for this source. *)
Theorem concat_admission_bare_start_not_ghost:
  !d G tn. ~ghost_inv d order_ptr_env order_ptr_cx order_ptr_source G tn
    ((init_venom_state "entry") with vs_alloca_next := 256)
Proof
  rpt gen_tac >> strip_tac >>
  fs[bodyPtrDefsTheory.ghost_inv_def] >>
  qpat_x_assum `!name entry p sz. _` (qspec_then `"arr"` mp_tac) >>
  simp[order_ptr_source_def,
       bodyPtrBytestringBuiltinsPtrRunTheory.order_ptr_env_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_scopes_def,
       vyperStateTheory.lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE,
       bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.lookup_var_def,
       venomStateTheory.init_venom_state_def]
QED
