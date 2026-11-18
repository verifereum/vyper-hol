(* Successful nondefault raw dispatch exposes the checked source signature and
   the explicit static-head size guard; no canonical calldata is required. *)
Theory dispatchedSelectedFacts
Ancestors defaultDispatchFacts dispatchedSignatureArgs

Theorem dispatched_selected_source_facts:
  supported_program tops /\ source_typing_ok tops am tx /\
  calldata_dispatch tops cd = SOME (tx.function_name,tx.args) /\
  tx.function_name <> "__default__" /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?tvs.
    4 <= LENGTH cd /\
    FIND (\(name,tys). abi_method_id (type_env tops) name tys = cd_selector cd)
      (abi_external_signatures tops) = SOME (tx.function_name,MAP SND args) /\
    OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
    calldata_decode_args cd tvs 0 = SOME tx.args
Proof
  rpt strip_tac >>
  drule default_dispatch_raw_cases >> strip_tac >> gvs[] >>
  `MEM (tx.function_name,tys) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  drule_all dispatched_signature_args >> strip_tac >> gvs[] >>
  metis_tac[]
QED
