Theory abiEncodeNamespaceProbe
Ancestors
  retAbiPlanProps compileEnv exprLowering vyperABI finite_map list

Theorem abi_encode_struct_fields_lookup:
  sfields_tenv_consistent sf tenv /\
  FLOOKUP tenv nsid = SOME (StructArgs args) ==>
  ?fields. FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args
Proof
  simp[sfields_tenv_consistent_def] >> metis_tac[]
QED

Theorem abi_encode_namespace_collision:
  nsid_to_string (SOME 0,"x") = nsid_to_string (NONE,"0.x") /\
  (SOME 0,"x") <> (NONE,"0.x")
Proof
  EVAL_TAC
QED

Theorem abi_encode_namespace_narrowing_failure:
  sfields_tenv_consistent sf tenv /\
  FLOOKUP tenv (SOME 0,"x") = SOME (StructArgs args) /\
  FLOOKUP tenv (NONE,"0.x") = SOME (StructArgs args') ==>
  ~sfields_tenv_consistent (sf \\ nsid_to_string (SOME 0,"x"))
    (tenv \\ (SOME 0,"x"))
Proof
  strip_tac >>
  simp[sfields_tenv_consistent_def, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  disj1_tac >> qexistsl_tac [`(NONE,"0.x")`, `args'`] >>
  simp[GSYM (cj 1 abi_encode_namespace_collision)]
QED

Theorem abi_encode_namespace_narrowing_counterexample:
  sfields_tenv_consistent (FEMPTY |+ ("0.x",([] : (string # type # num) list)))
    (FEMPTY |+ ((SOME 0,"x"),StructArgs []) |+ ((NONE,"0.x"),StructArgs [])) /\
  ~sfields_tenv_consistent ((FEMPTY |+ ("0.x",([] : (string # type # num) list))) \\ nsid_to_string (SOME 0,"x"))
    ((FEMPTY |+ ((SOME 0,"x"),StructArgs []) |+ ((NONE,"0.x"),StructArgs [])) \\ (SOME 0,"x"))
Proof
  `toString (0:num) = "0"` by EVAL_TAC >>
  conj_asm1_tac
  >- (simp[sfields_tenv_consistent_def, finite_mapTheory.FLOOKUP_UPDATE,
           nsid_to_string_def] >> rpt strip_tac >>
      gvs[AllCaseEqs(), nsid_to_string_def] >>
      qexists_tac `(NONE,"0.x")` >> simp[nsid_to_string_def]) >>
  irule abi_encode_namespace_narrowing_failure >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_reachable_alias_evaluation:
  evaluate_type
    (FEMPTY |+ ((SOME 0,"x"),StructArgs [("next",StructT (NONE,"0.x"))])
            |+ ((NONE,"0.x"),StructArgs [("next",StructT (NONE,"0.x"))]))
    (StructT (SOME 0,"x")) = NONE
Proof
  EVAL_TAC
QED

Theorem abi_encode_reachable_alias_consistent:
  sfields_tenv_consistent
    (FEMPTY |+ ("0.x",[("next",StructT (NONE,"0.x"),0:num)]))
    (FEMPTY |+ ((SOME 0,"x"),StructArgs [("next",StructT (NONE,"0.x"))])
            |+ ((NONE,"0.x"),StructArgs [("next",StructT (NONE,"0.x"))]))
Proof
  `toString (0:num) = "0"` by EVAL_TAC >>
  simp[sfields_tenv_consistent_def, finite_mapTheory.FLOOKUP_UPDATE,
       nsid_to_string_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), nsid_to_string_def] >>
  qexists_tac `(NONE,"0.x")` >> simp[nsid_to_string_def]
QED

(* Diagnostic interface ledger (not additional proved theorems):
 * evaluate_type_def, StructT: lookup nsid; evaluate_types (tenv \\ nsid)
 *   (MAP SND args) []; build StructTV if its slot bound holds.
 * type_to_abi_enc_info_def, StructT: when dynamic, lookup the string key;
 *   recursively compile each field with sf \\ nsid_to_string nsid.
 * evaluate_type_ind therefore follows source nsid deletion, not string deletion.
 *
 * Candidate alias-saturation lemma, UNPROVED:
 *   sfields_tenv_consistent sf tenv /\
 *   FLOOKUP tenv a = SOME (StructArgs args) /\
 *   evaluate_types (tenv \\ a) (MAP SND args) [] = SOME tvs
 *   ==>
 *   evaluate_types (DRESTRICT tenv
 *     {k | ~(?fs. FLOOKUP tenv k = SOME (StructArgs fs) /\
 *                  nsid_to_string k = nsid_to_string a)})
 *     (MAP SND args) [] = SOME tvs.
 * Remove struct aliases only: flag aliases must remain available to FlagT.
 * This would recover global correspondence with sf's one-key deletion while
 * justifying the filtered source evaluation; it is not an endpoint premise.
 *
 * Needed supporting interface, UNPROVED: successful evaluation in a submap
 * has a result of the same shape as successful evaluation in the full map;
 * existing cj 1/cj 2 vyper_to_abi_type_submap gives upward stability. For an
 * ancestor alias, correspondence forces identical field type lists. An alias
 * reached below those fields would reproduce their evaluation at strictly
 * smaller evaluated type_value_size; lift through submap stability to get a
 * contradiction. Existing MEM_type_value_size_StructTV/TupleTV expose the
 * strict subvalue descent; ArrayTV requires its elementary constructor-size
 * inequality. Tuple/list induction needs the corresponding member extraction
 * for evaluate_types (including its reversed accumulator).
 * Sibling repetitions are not forbidden: each branch starts with the same
 * ancestor map, so filtering is path-local and does not accumulate across
 * siblings. Zero-bound arrays still evaluate their element before failing.
 * expr_sim_inv_def supplies global consistency and field size agreement,
 * but has no explicit namespace injectivity/reachable-path premise. This
 * audit has NOT established that context_well_typed implies such a premise.
 * The checked reachable-alias example fails evaluation; it is NOT a target
 * counterexample and does NOT prove the proposed saturation lemma.
 *)
