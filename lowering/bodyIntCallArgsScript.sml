(* Argument typing boundary for the internal-call staging proof.
   Unlike external calls, internal calls require exact parameter types;
   bind_arguments does not license widening at a well-typed call site. *)
Theory bodyIntCallArgs
Ancestors
  vyperTypeSystem exprLowering compileEnv list

Theorem typed_intcall_argument_types:
  well_typed_expr env (Call ty (IntCall id) es drv) /\
  FLOOKUP env.fn_sigs id = SOME sig /\ sig.num_defaults = 0 ==>
  MAP expr_type es = sig.param_types
Proof
  Cases_on `id` >>
  simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >>
  `LENGTH es = LENGTH sig.param_types` by decide_tac >>
  gvs[]
QED

(* Checked exclusion of the candidate narrow-bytes/wide-parameter call.
   This is an interface diagnostic, not a counterexample to body_intcall_case. *)
Theorem typed_intcall_excludes_bytes_argument_widening:
  FLOOKUP env.fn_sigs id = SOME sig /\ sig.num_defaults = 0 /\
  sig.param_types = [BaseT (BytesT (Dynamic 128))] /\
  MAP expr_type es = [BaseT (BytesT (Dynamic 32))] ==>
  ~well_typed_expr env (Call ty (IntCall id) es drv)
Proof
  strip_tac >> strip_tac >>
  drule_all typed_intcall_argument_types >> simp[]
QED

Theorem typed_intcall_staging_capacities:
  well_typed_expr env (Call ty (IntCall id) es drv) /\
  FLOOKUP env.fn_sigs id = SOME sig /\ sig.num_defaults = 0 ==>
  MAP (\e. MAX 32 (type_memory_bytes cenv (expr_type e))) es =
  MAP (\ty. MAX 32 (type_memory_bytes cenv ty)) sig.param_types
Proof
  strip_tac >> drule_all typed_intcall_argument_types >>
  disch_then (fn th => rewrite_tac[GSYM th]) >> simp[MAP_MAP_o, combinTheory.o_DEF]
QED

(* These capacities differ, but the typing boundary above excludes passing
   the narrow one to the wide internal parameter. The memory-param prologue
   merely installs a PtrVar (materialize_internal_params_def); it does not
   perform a parameter-sized copy at entry. *)
Theorem bytes_staging_capacity_diagnostic:
  MAX 32 (type_memory_bytes cenv (BaseT (BytesT (Dynamic 32)))) = 64 /\
  MAX 32 (type_memory_bytes cenv (BaseT (BytesT (Dynamic 128)))) = 160
Proof
  simp[type_memory_bytes_def]
QED
