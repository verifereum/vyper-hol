(* Compiler frontiers for the array base, forced index and suffix. *)
Theory bodyIntCallFamAggSubscriptArraySetup
Ancestors
  exprSimSubscriptArrayEndpoint exprLoweringProps fragExec compileEnv

Theorem intcall_array_compile_cuts:
  compile_expr ce ty obj sa = (bvv,sm) /\
  lower_value compile_expr ce ity idx sm = (iop,sc) /\
  compile_array_subscript base_op iop dyn cnt ws esz sgn
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) sc = (dst,sb) /\
  fn_has_code sa sb func ==>
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id /\
  cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc sb /\
  fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `cs_extends sm sc /\ sm.cs_next_var <= sc.cs_next_var /\
   sm.cs_next_id <= sc.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sc sb` by
    (drule array_subscript_grows >> simp[ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED
