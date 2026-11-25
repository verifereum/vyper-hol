(* Invert successful deploy lowering when a main constructor is present. *)
Theory linkedDeployConstructorRun
Ancestors
  compileUnit bodyInvSplit moduleLowering pair
val _ = Parse.hide "body";

Theorem linked_deploy_constructor_run:
  lower_vyper_deploy_unit_mods mods exps rp runtime_bc = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,SOME cf,imp_ctors) /\
  set_constructor_package_target rp.rpol_target
    (package_constructor_unit mods T (K global_nonreentrant_slot) cf) =
    (ce0,args,pay,nr,key,use_trans,body,ret) ==>
  run_deploy_lowering T rp runtime_bc (imm_len_mods mods) args 0
    (MAP (set_internal_package_target rp.rpol_target o
          package_internal_fn_unit mods T (K global_nonreentrant_slot) T
            (imm_len_mods mods))
      (order_internals_unit (deploy_internal_order_unit (SOME cf)
        (ints ++ imp_ctors)) (ints ++ imp_ctors)))
    ce0 body pay nr key use_trans "__deploy" = SOME unit
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_mods_def, LET_THM, GSYM imm_len_mods_def, AllCaseEqs()]
QED
