(* Raw dispatch facts: the selected signature, not its name, determines placement. *)
Theory defaultDispatchFacts
Ancestors sourceEntryCode runtimeBodyStartDefs checkedSelectorTableProps entryStateRel
  vyperCalldata

Theorem default_dispatch_raw_cases:
  calldata_dispatch tops cd = SOME (name,vals) ==>
  ((LENGTH cd < 4 \/
    FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
      (abi_external_signatures tops) = NONE) /\
   EXISTS is_default_decl tops /\ name = "__default__" /\ vals = []) \/
  (?tys tvs.
    4 <= LENGTH cd /\
    FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
      (abi_external_signatures tops) = SOME (name,tys) /\
    OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
    4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
    calldata_decode_args cd tvs 0 = SOME vals)
Proof
  simp[calldata_dispatch_def] >>
  Cases_on `LENGTH cd < 4` >> simp[]
  >- (Cases_on `EXISTS is_default_decl tops` >> simp[] >> metis_tac[]) >>
  Cases_on `FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops)` >> simp[]
  >- (Cases_on `EXISTS is_default_decl tops` >> simp[] >> metis_tac[]) >>
  PairCases_on `x` >>
  Cases_on `OPT_MMAP (evaluate_type (type_env tops)) x1` >> simp[] >>
  Cases_on `LENGTH cd < 4 + SUM (MAP tv_abi_size x)` >> simp[] >>
  Cases_on `calldata_decode_args cd x 0` >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED
