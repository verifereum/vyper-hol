(* The two package forms preserve the same source environment. *)
Theory runtimeFallbackPackageEnvironment
Ancestors
  compileVyper

val _ = Parse.hide "body";

Theorem same_source_fallback_package_environment:
  set_external_package_target target
    (package_external_fn tops use_trans nkeys
      (mut,nr,rr,name,args,([]:expr list),ret,fbody)) =
    (lbl,ce_ext,pa,mc,pay,nr',key,ut,iv,body,rt) /\
  set_fallback_package_target target
    (package_fallback_fn tops use_trans nkeys
      (SOME (mut,nr,rr,name,args,([]:expr list),ret,fbody))) =
    SOME (ce_fb,pay',nr'',key',ut',iv',body',rt') ==>
  ce_fb = ce_ext
Proof
  simp[package_external_fn_def, package_fallback_fn_def,
       set_external_package_target_def, set_fallback_package_target_def] >>
  rpt strip_tac >> gvs[]
QED
