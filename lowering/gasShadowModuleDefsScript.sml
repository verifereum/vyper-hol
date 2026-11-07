(* Proof-only package maps for structural shadow compilation. *)
Theory gasShadowModuleDefs
Ancestors
  gasShadow gasShadowCenv gasShadowState moduleLowering list

Definition gas_shadow_external_package_def:
  gas_shadow_external_package
    (lbl,ce,args,min_cds,pay,nr,key,trans,view,body,ret) =
    (lbl,gas_shadow_cenv ce,args,min_cds,pay,nr,key,trans,view,
     MAP gas_shadow_stmt body,ret)
End

Definition gas_shadow_internal_package_def:
  gas_shadow_internal_package
    (lbl,ce,params,rb,nr,key,trans,view,ctor,imm,body,ret) =
    (lbl,gas_shadow_cenv ce,params,rb,nr,key,trans,view,ctor,imm,
     MAP gas_shadow_stmt body,ret)
End

Definition gas_shadow_fallback_package_def:
  gas_shadow_fallback_package (ce,pay,nr,key,trans,view,body,ret) =
    (gas_shadow_cenv ce,pay,nr,key,trans,view,MAP gas_shadow_stmt body,ret)
End
