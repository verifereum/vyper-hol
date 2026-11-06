Theory ctorDeployLoweringEntryQuantitativeInputs
Ancestors
 ctorDeployLoweringEntryScalarInputs ctorDeployLoweringFrame ctorSourceInputs
 supportedTypes valueEncoding vyperTypeValues vyperValue vyperTyping vyperABI contractABI words list

Theorem deploy_scalar_memory_size_positive:
 !ty env tv. supported_scalar_type ty /\
 evaluate_type env ty = SOME tv ==> 32 <= type_memory_size tv
Proof
 Cases_on `ty` >>
 simp[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
 Cases_on `b` >>
 simp[supported_word_type_def, supported_string_type_def] >>
 rpt strip_tac >>
 gvs[evaluate_type_def, type_memory_size_def] >>
 rename1 `BytesT bd` >> Cases_on `bd` >>
 gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()]
QED

Theorem deploy_scalar_tuple_memory_cardinality:
 !tys tvs env.
 EVERY supported_scalar_type tys /\
 LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs ==>
 LENGTH tvs <= type_memory_size_list tvs
Proof
 Induct_on `tys` >> Cases_on `tvs` >> simp[type_memory_size_def] >>
 rpt strip_tac >> drule_all deploy_scalar_memory_size_positive >> strip_tac >>
 first_x_assum drule_all >> simp[]
QED

Theorem deploy_scalar_tuple_strict_cardinality:
 !tys tvs env.
 EVERY supported_scalar_type tys /\
 LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
 type_memory_size (TupleTV tvs) < dimword(:256) ==>
 LENGTH tvs < dimword(:256)
Proof
 rpt strip_tac >> drule_all deploy_scalar_tuple_memory_cardinality >>
 gvs[type_memory_size_def]
QED

Theorem deploy_word_memory_size:
 !ty env tv. supported_word_type ty /\
 evaluate_type env ty = SOME tv ==> type_memory_size tv = 32
Proof
 Cases_on `ty` >> simp[supported_word_type_def] >>
 Cases_on `b` >> simp[supported_word_type_def] >> rpt strip_tac >>
 gvs[evaluate_type_def, type_memory_size_def] >>
 rename1 `BytesT bd` >> Cases_on `bd` >>
 gvs[supported_word_type_def, evaluate_type_def, type_memory_size_def, AllCaseEqs()]
QED

Theorem deploy_word_array_strict_cardinality:
 !ty env tv bd n.
 supported_word_type ty /\ evaluate_type env ty = SOME tv /\
 type_memory_size (ArrayTV tv bd) < dimword(:256) /\
 (bd = Fixed n \/ bd = Dynamic n) ==>
 n < dimword(:256)
Proof
 rpt strip_tac >> drule_all deploy_word_memory_size >> strip_tac >>
 gvs[type_memory_size_def]
QED

Theorem deploy_word_empty_array_valid:
 !ty env tv.
 supported_word_type ty /\ evaluate_type env ty = SOME tv ==>
 has_type (Array NONE (vyper_to_abi_type env ty)) (ListV [])
Proof
 rpt strip_tac >> simp[has_type_def]
QED

(* Size coherence is already a field of constructor_bound_source_inputs.
   This boundary deliberately consumes that equality for the actual tv. *)
Theorem deploy_argument_semantic_size_bound:
 !(args : (string # type) list) cenv i tv.
 EVERY (\a. type_memory_bytes cenv (SND a) < 2 ** 64) args /\
 i < LENGTH args /\
 type_memory_size tv = type_memory_bytes cenv (SND (EL i args)) ==>
 type_memory_size tv < dimword(:256)
Proof
 rpt strip_tac >>
 qpat_x_assum `EVERY _ _` mp_tac >> rewrite_tac[EVERY_EL] >>
 disch_then (qspec_then `i` mp_tac) >> simp[] >>
 CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]
QED

Theorem deploy_ctor_argument_semantic_size_bound:
 !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
 sa sb sj st_exit st_epilogue st_final func mut args i tv.
 deploy_ctor_code tops rpolicy runtime_bc dunit
  (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
 lookup_function NONE "__init__" Deploy tops =
  SOME (mut,nr,args,[],NoneT,stmts) /\
 i < LENGTH args /\
 type_memory_size tv = type_memory_bytes cenv (SND (EL i args)) ==>
 type_memory_size tv < dimword(:256)
Proof
 rpt strip_tac >> drule_all deploy_ctor_allocation_bounds >> strip_tac >>
 irule deploy_argument_semantic_size_bound >>
 qexistsl_tac [`args`, `cenv`, `i`] >> simp[]
QED
