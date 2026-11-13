(* Proof-only package maps for structural shadow compilation. *)
Theory gasShadowModuleDefs
Ancestors
  gasShadow gasShadowState moduleLowering list

Definition gas_shadow_external_package_def:
  gas_shadow_external_package
    (lbl,ce,args,min_cds,pay,nr,key,trans,view,body,ret) =
    (lbl,ce,args,min_cds,pay,nr,key,trans,view,MAP gas_shadow_stmt body,ret)
End

Definition gas_shadow_internal_package_def:
  gas_shadow_internal_package
    (lbl,ce,params,rb,nr,key,trans,view,ctor,imm,body,ret) =
    (lbl,ce,params,rb,nr,key,trans,view,ctor,imm,MAP gas_shadow_stmt body,ret)
End

Definition gas_shadow_fallback_package_def:
  gas_shadow_fallback_package (ce,pay,nr,key,trans,view,body,ret) =
    (ce,pay,nr,key,trans,view,MAP gas_shadow_stmt body,ret)
End

Theorem gas_shadow_compile_register_kwarg_vars:
  !xs ce. compile_register_kwarg_vars ce
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) xs) =
    compile_register_kwarg_vars ce xs
Proof
  Induct >> rpt gen_tac
  >- simp[compile_register_kwarg_vars_def] >>
  PairCases_on `h` >> simp[compile_register_kwarg_vars_def]
QED
