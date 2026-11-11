(* Control and return-type normalization at the internal body boundary. *)
Theory bodyIntCallPackageBodyControl
Ancestors
  bodyIntCallActualEntryFields compileEnv moduleLowering compileVyper list

Theorem internal_entry_body_open:
  compile_internal_function_entry ce params has_rb ctor ilen rt s0 =
    ((ce2,rpc,imm),s1) ==> ~block_is_terminated s1
Proof
  strip_tac >> drule compile_internal_entry_shape >> strip_tac >>
  gvs[block_is_terminated_def] >>
  Cases_on `new` >> gvs[] >>
  Cases_on `s0.cs_current_insts` >> simp[listTheory.LAST_DEF] >>
  `MEM (LAST (h::t)) (h::t)` by
    metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM] >>
  fs[EVERY_MEM] >> Cases_on `t` >> gvs[listTheory.LAST_DEF]
QED

Theorem internal_package_return_option:
  set_internal_package_target target
    (package_internal_fn tops use_trans (nkeys:string->num) ctor ilen
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor',ilen',ss',rt) ==>
  rt = if ret = NoneT then NONE else SOME ret
Proof
  simp[set_internal_package_target_def, package_internal_fn_def,
       pairTheory.ELIM_UNCURRY] >> rpt strip_tac >> simp[]
QED
