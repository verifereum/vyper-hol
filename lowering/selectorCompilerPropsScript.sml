(* The checker's collision keys are the method IDs consumed by lowering. *)
Theory selectorCompilerProps
Ancestors
  compileVyper moduleLowering vyperABIEntries vyperTypeBytesCrypto vyperTypeContract
  contractABI selectorDispatch list rich_list arithmetic words
Libs
  proofAuditLib
  fcpLib

val selector_dimindex8 = fcpLib.INDEX_CONV ``dimindex (:8)``
val selector_dimindex256 = fcpLib.INDEX_CONV ``dimindex (:256)``

Theorem function_selector_length[simp]:
  LENGTH (function_selector name tys) = 4
Proof
  simp[function_selector_def, LENGTH_Keccak_256_w64]
QED

Theorem calldata_method_id_bytes:
  w2n (calldata_method_id [a;b;c;d]) =
    FOLDL (\n b. 256 * n + w2n b) 0 [a;b;c;d]
Proof
  mp_tac (Q.ISPEC `a:word8` wordsTheory.w2n_lt) >>
  mp_tac (Q.ISPEC `b:word8` wordsTheory.w2n_lt) >>
  mp_tac (Q.ISPEC `c:word8` wordsTheory.w2n_lt) >>
  mp_tac (Q.ISPEC `d:word8` wordsTheory.w2n_lt) >>
  simp[calldata_method_id_def, FOLDL, w2n_n2w, dimword_def,
       selector_dimindex8, selector_dimindex256,
       LEFT_ADD_DISTRIB] >> rpt strip_tac >>
  `16777216 * w2n a + 65536 * w2n b + 256 * w2n c + w2n d <
    2 ** 256` by (simp[] >> decide_tac) >>
  simp[LESS_MOD] >> decide_tac
QED

Theorem calldata_method_id_four_bytes:
  LENGTH bs = 4 ==>
  w2n (calldata_method_id bs) = FOLDL (\n b. 256 * n + w2n b) 0 bs
Proof
  simp[listTheory.LENGTH_EQ_NUM_compute] >> rpt strip_tac >>
  gvs[calldata_method_id_bytes]
QED

Theorem compute_selector_method_id:
  compute_selector tenv name tys =
    (abi_method_id tenv name tys, "fn_" ++ name,
     selector_has_trailing_zeroes (abi_method_id tenv name tys))
Proof
  simp[compute_selector_def, abi_method_id_def,
       calldata_method_id_four_bytes]
QED

Theorem build_selectors_method_ids:
  MAP FST (build_selectors tenv fns) =
  MAP (\(mut,nr,rr,name,args,dflts,ret,body).
    abi_method_id tenv name (MAP SND args)) fns
Proof
  Induct_on `fns` >> simp[build_selectors_def] >> qx_gen_tac `entry` >>
  PairCases_on `entry` >> simp[build_selectors_def, compute_selector_method_id]
QED

Theorem external_group_method_ids:
  MAP FST (external_group_selectors
    (package_external_group tops target trans nkeys
      (mut,nr,rr,name,args,dflts,ret,stmts))) =
  MAP (\(name,tys). abi_method_id (type_env tops) name tys)
    (abi_function_signatures name args dflts)
Proof
  Cases_on `dflts` >>
  simp[package_external_group_def, package_external_fn_def,
       set_external_package_target_def, external_group_selectors_def,
       compute_selector_method_id, abi_function_signatures_def,
       MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, pairTheory.FORALL_PROD]
QED

val () = proofAuditLib.check_theory "selectorCompilerProps";
