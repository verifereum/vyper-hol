Theory bodyPtrPopFrameContainment
Ancestors
  bodyPtrPopGlobalNoFrame bodyPtrPopFrameProbe

(* The requested all-function opcode exclusion is already proved as
   pop_global_lookup_no_invoke (bodyPtrPopContextContainment); its finite
   computation certificate is pop_global_context_no_invoke.  Universal
   compile-state INVOKE containment is already pop_compile_intcall_fn_invoke
   combined with pop_global_call_decomposition, used by
   pop_global_no_containment.  Keep those interfaces unique. *)
Theorem pop_global_fragment_no_frame:
  !ret_ty sa sb vv func cx es s.
    compile_expr pop_global_package_env ret_ty
      (Pop (BaseT (UintT 256)) pop_global_target) sa = (vv,sb) /\
    fn_has_code sa sb func ==>
    ~stmt_state_rel pop_global_runtime_context func pop_global_package_env cx es s
Proof
  rpt strip_tac >>
  drule pop_stmt_frame_function_lookup >> strip_tac >>
  drule_all pop_global_no_containment >> simp[]
QED
