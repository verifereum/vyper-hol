(* Checked external raw-return headers determine a bytestring return type. *)
Theory externalRawReturnType
Ancestors
  rawReturnHeader supportedDecls supportedProgram e2eDefs vyperTypeContract
  vyperInterpreter vyperTypeSystem externalReturnPrefix compileVyper
  exprLoweringProps bodySim compileEnv entryStateRel

val _ = Parse.hide "body";

Theorem source_typing_raw_return_type:
  source_typing_ok tops am tx /\ supported_program tops /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,defaults,ret,body) /\
  lookup_raw_return_or_F (NONE : num option) tx.function_name External tops ==>
  ?n. ret = BaseT (BytesT (Dynamic n))
Proof
  strip_tac >>
  drule_all source_typing_ok_raw_external_decl >> strip_tac >>
  fs[source_typing_ok_def] >>
  drule check_contract_function_header >> simp[listTheory.MEM] >>
  disch_then drule >> simp[function_header_ok_def]
QED

Theorem external_package_raw_flag:
  set_external_package_target tgt
    (package_external_fn tops ut0 nkm
      (mut,nr0,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,payable,nr,nkey,ut,iv,body',rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv cenv' ==>
  cenv'.ce_raw_return = rr
Proof
  strip_tac >>
  `cenv0.ce_raw_return = rr` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `ret = NoneT` >>
     simp[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
     strip_tac >> gvs[]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  fs[same_frame_def] >>
  `cenv'.ce_raw_return = cenv.ce_raw_return` by
    (qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
       ce_var_type := _ |> = _` (SUBST1_TAC o SYM) >> simp[]) >>
  `cenv.ce_raw_return = cenv0.ce_raw_return` by
    (qpat_x_assum `cenv = _` SUBST1_TAC >> simp[]) >> simp[]
QED
