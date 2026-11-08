Theory entryBodyEndpointStructure
Ancestors
  entryLocals moduleLowering compileEnv compileVyper intCallCallee

Theorem targeted_external_entry_locals:
  !target tops use_trans keys mut nr rr fname fargs dflts ret fbody
   lbl ce pos mincd pay nr' key ut iv body rt st cenv last.
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut,iv,body,rt) /\
  compile_register_positional_args ce pos 4 st = (cenv,last) ==>
  local_ptrs_reserved cenv last
Proof
  rpt gen_tac >> strip_tac >>
  `ce.ce_vars = (build_compile_env tops External mut fname fargs ret fbody
                  use_trans).ce_vars /\
   MAP FST pos = MAP FST fargs /\ ce.ce_imm_alloca = NONE` by
    (gvs[set_external_package_target_def, package_external_fn_def,
         update_cenv_nonreentrant_def, LET_THM] >>
     rw[update_cenv_ret_abi_def, build_compile_env_imm_alloca,
        build_positional_args_FST]) >>
  qspecl_then [`tops`,`External`,`mut`,`fname`,`fargs`,`ret`,`fbody`,
               `use_trans`] strip_assume_tac build_compile_env_vars >>
  drule compile_register_positional_args_reserved >>
  (impl_tac >- gvs[]) >> simp[]
QED
