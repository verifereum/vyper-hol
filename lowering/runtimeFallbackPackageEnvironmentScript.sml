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

(* The fallback shares its compile environment with an empty-argument
   external function packaged from the same source declaration. *)
Theorem fallback_empty_source_external_package:
  set_fallback_package_target target
    (package_fallback_fn tops use_trans nkeys
      (SOME (mut,nr,rr,name,[],([]:expr list),ret,fbody))) =
    SOME (ce,pay,guarded,key,ut,iv,body,rt) ==>
  set_external_package_target target
    (package_external_fn tops use_trans nkeys
      (mut,nr,rr,name,[],([]:expr list),ret,fbody)) =
    ("fn_" ++ name,ce,[],4,pay,guarded,key,ut,iv,body,rt)
Proof
  simp[package_external_fn_def, package_fallback_fn_def,
       set_external_package_target_def, set_fallback_package_target_def,
       build_positional_args_def, min_calldata_size_def] >>
  rpt strip_tac >> gvs[]
QED
