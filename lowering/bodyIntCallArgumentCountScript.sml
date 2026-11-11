(* Checked probes for the package-entry argument-count interface. *)
Theory bodyIntCallArgumentCount
Ancestors
  supportedProgram compileVyper compileEnv vyperCompiler intCallCallee list words

Theorem empty_struct_supported_zero_abi:
  supported_value_type [StructDecl "E" []] (StructT (NONE,"E")) /\
  abi_size_bound (make_struct_fields_map [StructDecl "E" []])
    (StructT (NONE,"E")) = 0 /\
  abi_embedded_static_size (make_struct_fields_map [StructDecl "E" []])
    (StructT (NONE,"E")) = 0 /\
  ~is_abi_dynamic (make_struct_fields_map [StructDecl "E" []])
    (StructT (NONE,"E"))
Proof
  EVAL_TAC
QED

Theorem empty_struct_tuple_abi_unbounded_count:
  !n. abi_size_bound (make_struct_fields_map [StructDecl "E" []])
        (TupleT (REPLICATE n (StructT (NONE,"E")))) = 0 /\
      LENGTH (REPLICATE n (StructT (NONE,"E"))) = n
Proof
  Induct >> simp[abi_size_bound_def, empty_struct_supported_zero_abi]
QED

Theorem compute_pass_via_stack_true_bound:
  !tys n. LENGTH (FILTER I (compute_pass_via_stack tys n)) <= MAX_STACK_ARGS - n
Proof
  Induct >> simp[compute_pass_via_stack_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  first_x_assum (qspec_then `n + 1` mp_tac) >> simp[]
QED

Theorem staging_charge_argument_count:
  !flags args.
    LENGTH flags = LENGTH args /\
    LENGTH (FILTER I flags) <= MAX_STACK_ARGS /\
    32 * LENGTH (FILTER (\b. ~b) flags) < dimword (:256) ==>
    1 + LENGTH args < dimword (:256)
Proof
  rpt strip_tac >>
  `LENGTH flags = LENGTH (FILTER I flags) +
                  LENGTH (FILTER (\b. ~b) flags)` by
    (rpt (pop_assum kall_tac) >> Induct_on `flags` >>
     simp[] >> Cases >> simp[]) >>
  fs[MAX_STACK_ARGS_def, dimword_def] >> decide_tac
QED
