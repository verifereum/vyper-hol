(* FROZEN OWNER LEAF: proved by its own run, cheat until then.
   Historical obligation C1.5.3.1.3. Packaging preserves multiplicity of
   all instructions. Together with the additive function-charge bound and
   cs_extends on either side of an internal compilation, these bounds
   bound that package's internal_stack_size by unit_alloca_frame. *)
Theory bodyIntCallUnitCharge
Ancestors
  bodyIntCallFunctionCharge compileVyper vyperCompiler moduleLowering
  exprLoweringProps loweringShapeDefs compileEnv venomInst list

Theorem runtime_unit_alloca_charge:
  !tops policy unit exts ints fb ctor st.
    lower_vyper_runtime_unit tops policy = SOME unit /\
    classify_functions tops = (exts,ints,fb,ctor) /\
    compile_generate_runtime
      (build_selectors (type_env tops) exts)
      (MAP (set_external_package_target policy.rpol_target o
        package_external_fn tops F (assign_nkeys tops 0)) exts)
      (MAP (set_internal_package_target policy.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) F 0) ints)
      (set_fallback_package_target policy.rpol_target
        (package_fallback_fn tops F (assign_nkeys tops 0) fb))
      policy.rpol_frontend_dispatch 0 0 []
      (build_dense_entry_info (build_selectors (type_env tops) exts)
        (MAP (set_external_package_target policy.rpol_target o
          package_external_fn tops F (assign_nkeys tops 0)) exts))
      (initial_compile_state "__entry") = ((),st) ==>
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts st))) <=
    unit_alloca_frame unit.cu_context
Proof
  cheat
QED

Theorem deploy_unit_alloca_charge:
  !tops policy bytes unit exts ints fb ctor ce cargs pay nr key trans body rt st.
    lower_vyper_deploy_unit tops policy bytes = SOME unit /\
    classify_functions tops = (exts,ints,fb,ctor) /\
    set_constructor_package_target policy.rpol_target
      (case ctor of
         SOME cf => package_constructor tops F (assign_nkeys tops 0) cf
       | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                  F,F,0n,F,([] : stmt list),NoneT)) =
      (ce,cargs,pay,nr,key,trans,body,rt) /\
    compile_generate_deploy (IS_SOME ctor) (LENGTH bytes)
      (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops)
      cargs 0
      (if IS_SOME ctor then
         MAP (set_internal_package_target policy.rpol_target o
           package_internal_fn tops F (assign_nkeys tops 0) T
             (compute_immutables_len
               (get_struct_fields (make_struct_fields_map tops)) tops)) ints
       else [])
      ce body pay nr key trans (initial_compile_state "__deploy") = ((),st) ==>
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts st))) <=
    unit_alloca_frame unit.cu_context
Proof
  cheat
QED
