(* The raw linked deploy entry without a main constructor. *)
Theory linkedEmptyDeployCode
Ancestors
  ctorDeployLoweringNoCtor compileUnit vyperCompiler bodyInvSplit
  compileVyper compileEnv moduleLowering context venomInst list pair
Theorem lower_vyper_deploy_unit_no_ctor_shape_mods:
  lower_vyper_deploy_unit_mods mods exps rp runtime_bc = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,NONE,imp_ctors) ==>
  unit.cu_context =
    install_immutable_reservation (imm_len_mods mods) (mk_venom_context
      [mk_raw_function "__deploy" [<|bb_label := "__deploy";
        bb_instructions :=
          [mk_inst 0 ALLOCA [Lit (n2w (LENGTH runtime_bc + imm_len_mods mods))] ["%0"];
           mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin";
             Lit (n2w (LENGTH runtime_bc + imm_len_mods mods))] [];
           mk_inst 2 RETURN [Var "%0";
             Lit (n2w (LENGTH runtime_bc + imm_len_mods mods))] []]|>]]
      (SOME "__deploy"))
Proof
  disch_then (CONJUNCTS_THEN2 mp_tac assume_tac) >>
  simp[lower_vyper_deploy_unit_mods_def,set_constructor_package_target_def] >>
  rpt strip_tac >>
  drule no_ctor_lowering_context_shape >> simp[imm_len_mods_def]
QED
