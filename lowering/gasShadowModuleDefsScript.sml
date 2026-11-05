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
