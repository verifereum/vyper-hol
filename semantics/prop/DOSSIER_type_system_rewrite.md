# DOSSIER: type_system_rewrite

PLAN: `semantics/prop/PLAN_type_system_rewrite.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C0.1 | stuck | other | E0004 | "Escalate to plan_oracle for C0 resolution: authorize type_builtin_result_ok repair for AbiEncode branch, adding vyper_abi_size_bound condition" |
| C1 | progressed | plan_incomplete | E0005 | Escalate to plan_oracle: C1 needs decomposition into subcomponents for (1) the vyper_to_abi success lemma and (2) the enc-length-bound lemma, before the 3 success-typing branches are provable. |
| C2.1.a | progressed | other | E0001 | Progress to C2.1.b (HashMapRef proof) or C2.1.c (ArrayRef proof), or C2.2.a (ImmutableVar proof) using the probe evidence |
| C3.1 | progressed | missing_helper | E0026 | Fix C3.1.3: after irule target_path_type_Type_place_leaf_typed, get place_leaf_typed in assumptions, then gvs[place_leaf_typed_def] to expose place_leaf_path_typed, then rest_subs = TL(REVERSE sbs) rewriting + place_leaf_path_typed_def HashMapT case strips first element giving place_leaf_path_typed env vt rest_subs ty pl_tv. Then drule_all place_leaf_path_typed_split_leaf_type works. |
| C3.1.2 | proved | unknown | E0025 |  |
| C3.1.3 | proved | other | E0027 |  |
| C3.1.6 | progressed | other | E0034 |  |
| C3.1.7 | stuck | other | E0041 | Fix the vt=Type contradiction proof at line 2419-2424. Replace PairCases_on p + Cases_on p0 + metis_tac with mp_tac of lookup_global equation + simp[lookup_global_def,...] blast approach. Also verify the HashMapT case (lines 2426-2438) metis_tac[top_level_HashMapRef_assign_no_type_error] works for premise matching. |
| C3.1.7.1 | progressed | tool_limit | E0043 | Test holbuild DISCH_THEN issue by editing 5 cheats and building. If metis_tac works inside Resume blocks, simple replacement will close component. |
| C3.1.7.1.3 | progressed | plan_incomplete | E0044 | "Prove adapter facts: (1) well_formed_vtype (get_tenv cx) (Type t) from runtime_consistent assumptions, (2) evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)) via target_path_type_Type_place_leaf_typed + place_leaf_typed_evaluate_type, (3) leaf_type root_tv (REVERSE sbs) <> NoneTV via assignable_type_evaluate_not_NoneTV. Then caller proof uses r=st (lookup_global_state) + these adapter facts to satisfy drule_all of the boundary theorem." |
| C3.1.7.1.3.1 | progressed | other | E0052 |  |
| C3.1.7.1.3.2 | proved | other | E0053 |  |
| C3.1.7.3 | stuck | plan_incomplete | E0059 | Write boundary lemma assign_target_TopLevelVar_ArrayRef_ordinary_no_type_error for the standard read+write+assign_result path (all non-ArrayTV-Dynamic cases), modeled on assign_target_TopLevelVar_Value_branch_ntr. Then handle AppendOp/PopOp separately." |
| C3.1.7.3.1 | stuck | wrong_statement | E0063 |  |
| C3.1.7.3.2 | proved | other | E0060 |  |
| C3.2 | progressed | other | E0076 | Rewrite Replace_ntr_v2 and Update_ntr_v2 using AppendOp_ordinary_ntr pattern: Cases_on final_tv before expand, per-constructor simp+gvs[AllCaseEqs()], then 4 standard drule subgoals per constructor. This breaks stale checkpoint and avoids variable name mismatches. |

## C0.1

### Current Status

- result: `stuck`
- diagnosis: `other`
- latest episode: `E0004`
- blocker: "CONFIRMED: well_typed_type_builtin_success_type is FALSE. type_builtin_result_ok (AbiEncode _) does not constrain the result dynamic-bytes bound n >= vyper_abi_size_bound. Probes show: n=1 is accepted by type_builtin_result_ok + evaluate_type, but enc of uint256 produces 32 bytes. Since value_has_type (BaseTV (BytesT (Dynamic 1))) requires LENGTH <= 1, the success-typing theorem fails. The correct fix is to add vyper_abi_size_bound condition to type_builtin_result_ok for AbiEncode."
- next: "Escalate to plan_oracle for C0 resolution: authorize type_builtin_result_ok repair for AbiEncode branch, adding vyper_abi_size_bound condition"

### Attempts / Evidence

- `E0004` (stuck, other)
  - Probe type_builtin_result_ok (AbiEncode T) with BytesT (Dynamic 1) for uint256 arg type, then check encoding length -> CONFIRMED counterexample: result_ok accepts n=1, evaluate_type accepts BytesT(Dynamic 1), but enc produces 32 bytes > 1, so value_has_type fails. The ABI encode success typing theorem is FALSE as currently stated. ()

### Evidence refs

- `TO_type_system_rewrite-20260513T185020Z_m0696_t001` (use `read_tool_output` for exact output)

## C1

### Current Status

- result: `progressed`
- diagnosis: `plan_incomplete`
- latest episode: `E0005`
- blocker: "Three ABI encode success-typing cheat branches require two new substantial lemmas that don't exist yet: (1) value_has_type => vyper_to_abi succeeds, and (2) LENGTH(enc ...) <= vyper_abi_size_bound. These helpers are each non-trivial and C1's Risk 2 estimate didn't account for them."
- next: Escalate to plan_oracle: C1 needs decomposition into subcomponents for (1) the vyper_to_abi success lemma and (2) the enc-length-bound lemma, before the 3 success-typing branches are provable.

### Attempts / Evidence

- `E0005` (progressed, plan_incomplete)
  - Fix type_builtin_result_ok definition syntax (corrupted /& and <= in definition), add abi_encode_size_ok helper, use Unicode ∧ for conjunctions that API can't produce as /\ -> Definition compiles, probes pass. vyperTypeSystemTheory and vyperTypeBuiltinsTheory build successfully. Three ABI encode cheats remain. ()
  - Replace cheat proofs for abi_encode, encode_tuple, encode_tuple_nowrap -> Stuck: need value_has_type=>vyper_to_abi_success lemma and LENGTH(enc)<=vyper_abi_size_bound lemma. Neither exists in codebase. contractABI theory has LENGTH_enc_number and head_lengths_leq_LENGTH_enc_tuple which may help. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513Tm0832_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260513Tm0826_t001` (use `read_tool_output` for exact output)

## C2.1.a

### Current Status

- result: `progressed`
- diagnosis: `other` HashMapRef probe: assumptions include all expected typing/context/shape facts. The continuation involves split_hashmap_subscripts, compute_hashmap_slot, read_storage_slot, assign_subscripts, write_storage_slot, assign_result. Key decomposition: from target_runtime_typed derive HashMapType decomposition; show compute_hashmap_slot/split succeed; use assign_operation_runtime_typed for assign_subscripts safety. ArrayRef is similar but with resolve_array_element and special Dynamic array AppendOp/PopOp cases.
- latest episode: `E0001`
- blocker: "None - probe completed successfully"
- next: Progress to C2.1.b (HashMapRef proof) or C2.1.c (ArrayRef proof), or C2.2.a (ImmutableVar proof) using the probe evidence

### Attempts / Evidence

- `E0001` (progressed, other)
  - 1. Fixed lookup_global_stk proof (dependency blocker) by replacing gvs with simp + renaming + PairCases_on pattern from scopes script + universal get_storage_backend subgoal. 2. Probed HashMapRef branch with FAIL_TAC: got 8 assumptions including runtime_consistent, target_runtime_typed, assignable_type, assign_operation_runtime_typed, assign_operation_matches_target_shape, assign_target_assignable_context. Goal: no_type_error_result res. 3. Probed ArrayRef branch: similar assumptions but more complex continuation (resolve_array_element, cases by type_value, special AppendOp/PopOp handling for Dynamic arrays). -> Probe successful - both branches have adequate assumptions. HashMapRef branch needs: derive hashmap type decomposition from target_runtime_typed, show compute_hashmap_slot/split_hashmap_subscripts succeed, show assign_subscripts doesn't TypeError, show write_storage_slot/assign_result work. ArrayRef is more complex with resolve_array_element and special array operations. (`TO_type_system_rewrite-20260513T175918Z_m0140_t001`, `TO_type_system_rewrite-20260513T175918Z_m0142_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260513T175918Z_m0140_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260513T175918Z_m0142_t001` (use `read_tool_output` for exact output)

## C3.1

### Current Status

- result: `progressed`
- diagnosis: `missing_helper`
- latest episode: `E0026`
- blocker: C3.1.3 (target_path_type_HashMapT_split_leaf_runtime) failed: drule_all place_leaf_path_typed_split_leaf_type doesn't work because assumption has place_leaf_typed not place_leaf_path_typed. Fix: unfold place_leaf_typed_def first (= place_leaf_path_typed env loc_vt (REVERSE sbs) ty final_tv), then use REVERSE sbs = first_sub::rest_subs + place_leaf_path_typed_def HashMapT case to get place_leaf_path_typed env vt rest_subs ty pl_tv, THEN apply place_leaf_path_typed_split_leaf_type. Also main theorem proof uses once_rewrite_tac[assign_target_def] instead of simp[Once assign_target_def, bind_def] to avoid timeout.
- next: Fix C3.1.3: after irule target_path_type_Type_place_leaf_typed, get place_leaf_typed in assumptions, then gvs[place_leaf_typed_def] to expose place_leaf_path_typed, then rest_subs = TL(REVERSE sbs) rewriting + place_leaf_path_typed_def HashMapT case strips first element giving place_leaf_path_typed env vt rest_subs ty pl_tv. Then drule_all place_leaf_path_typed_split_leaf_type works.

### Attempts / Evidence

- `E0002` (progressed, missing_helper)
  - Added assignable_type_well_formed lemma (recInduct assignable_type_ind >> rw + Cases_on FLOOKUP for StructT case). Used it to fix AnnAssign vacuous branch instead of broken Cases_on e approach. -> Succeeded: AnnAssign vacuous branch now proves. assignable_type_well_formed is a reusable boundary lemma. (`TO_type_system_rewrite-20260513T185020Z_m0248_t001`)
  - Attempted to revive old Assign proof from commented-out code, adding cheat subgoals for assign_operation_matches_target_shape and assign_target_assignable_context. Built and got goal state for the first cheat subgoal. -> Build reached assign_operation_matches_target_shape cheat in Assign branch, confirming the exact goal shape. But the full proof revival had /| syntax errors and st3/st2 variable reference issues from copy-paste. Reverted to cheat placeholder. (`TO_type_system_rewrite-20260513T185020Z_m0320_t001`)
- `E0003` (stuck, missing_helper)
  - Prove assign_operation_matches_target_shape for BaseTargetV (Replace op) - trivially T from definition -> Succeeded: proved assign_operation_matches_target_shape_BaseTargetV in vyperTypeAssignSoundnessScript.sml (`TO_type_system_rewrite-20260513T185020Z_m0406_t001`)
  - Derive assign_target_assignable_context cx gv st from target_runtime_typed + env_consistent + eval_target success -> Blocked for TopLevelVar: get_module_code cx src = SOME code is needed but not derivable. env_context_consistent only provides get_module_code as antecedent. eval_base_target for TopLevelNameTarget is pure return (no lookup_global). ScopedVar and ImmutableVar cases should be derivable from existing eval_target_assignable + env_consistent. ()
- `E0006` (progressed, missing_helper)
  - Insert FAIL_TAC probe at HashMapRef cheat in assign_target_sound_mutual[sound_TopLevelVar] -> Probed goal state: confirmed all hypotheses available including assign_target_assignable_context, get_module_code, target_runtime_typed. Goal is no_type_error_result res. The branch proof is doable with helper lemmas. (`TO_type_system_rewrite-20260513T211025Z_m0903_t001`)
  - Write helper lemma target_path_type_HashMapT_split connecting target_path_type on HashMapT to subscript/key facts -> Lemma statement compiles but proof is incomplete/broken (confused induction on sbs). Need to rewrite properly using induction on path structure. Also wrote target_path_type_HashMapT_not_nil which compiles. ()
- `E0007` (progressed, missing_helper)
  - Proved target_path_type_HashMapT_split_hashmap_subscripts helper lemma connecting target_path_type on HashMapT to split_hashmap_subscripts success via place_leaf_path_typed_imp_split_hashmap_subscripts + target_path_type_Type_place_leaf_typed + Cases_on REVERSE sbs -> Helper lemma compiles and proves clean. Key: Cases_on REVERSE sbs to expand place_leaf_path_typed_def HashMapT case, then metis_tac with place_leaf_path_typed_imp_split_hashmap_subscripts. ()
  - Fixed well_formed_vtype derivation: construct location_runtime_typed env cx st (TopLevelVar src_id_opt id) (HashMapT t v) from FLOOKUP + location_runtime_typed_def, then irule location_runtime_typed_well_formed_vtype -> Worked. Must construct location_runtime_typed explicitly since irule alone leaves a free loc variable. ()
  - Branch proof: rw[no_type_error_result_def] >> strip_tac, then step-by-step gvs[bind_apply,AllCaseEqs()] to expand monadic do-block -> First gvs layer expands the case split on REVERSE is. Further layers needed for split_hashmap_subscripts, compute_hashmap_slot, evaluate_type, read_storage_slot, assign_subscripts, write_storage_slot. ()
- `E0008` (progressed, missing_helper)
  - Prove well_formed_vtype_split_hashmap_subscripts_well_formed_type: Induct_on value_type then rw/cases on split_hashmap_subscripts_def -> Succeeded after 4 iterations: needed Cases_on subs then Cases_on split result then PairCases_on (`tool_output:TO_type_system_rewrite-20260513T211025Z_m1584_t001`, `tool_output:TO_type_system_rewrite-20260513T211025Z_m1588_t001`)
  - Prove compute_hashmap_slot_subscripts_to_values: Induct_on kts, Cases_on ks, gvs compute_hashmap_slot_def, Cases_on subscript_to_value, irule IH -> Succeeded: key was Cases_on subscript_to_value h before using IH to specialize slot (`tool_output:TO_type_system_rewrite-20260513T211025Z_m1590_t001`)
  - Prove split_hashmap_subscripts_some_imp: ho_match_mp_tac split_hashmap_subscripts_ind -> FAILED: type variable conflict in induction principle (value_type vs fmap). Need Induct_on value_type instead. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m1593_t001`)
  - Prove target_path_type_HashMapT_last_ElementSubscript: target_path_type on HashMapT implies LAST is ValueSubscript -> Partially started but wrong induction strategy; target_path_type_ind needs careful spec_tac usage ()
  - FAIL_TAC probe at HashMapRef cheat to see goal state after two gvs expansions -> Got full goal: 16 assumptions including target_path_type, split_hashmap_subscripts success, runtime_consistent. Do-block shows remaining steps: compute_hashmap_slot, evaluate_type, read_storage_slot, assign_subscripts, write_storage_slot (`tool_output:TO_type_system_rewrite-20260513T211025Z_m1543_t001`)
- `E0009` (progressed, missing_helper)
  - Fix split_hashmap_subscripts_some_imp: change ho_match_mp_tac split_hashmap_subscripts_ind to Induct_on `vt`, change conclusion from SUC(LENGTH kts) = LENGTH subs - LENGTH remaining + 1 to LENGTH kts + LENGTH remaining = LENGTH subs, add first_x_assum drule + simp instead of decide_tac -> Succeeded: lemma builds clean with Induct_on vt approach ()
  - Remove target_path_type_HashMapT_last_ElementSubscript (used unexported target_path_type_ind) -> Removed - lemma was never used elsewhere ()
  - Remove top_level_hashmap_assign_no_type_error (type error: HashMapVarDecl is_transient base_slot id_str should be HashMapVarDecl is_transient kt vt id_str) -> Removed - lemma had cheat and type error in statement ()
  - Prove EVERY ((<>) NONE o subscript_to_value) (REVERSE is) from target_path_type -> FAILED: lemma is FALSE because StructT levels use AttrSubscript where subscript_to_value = NONE. Only HashMapT-level subscripts are guaranteed ValueSubscript. ()
- `E0010` (progressed, missing_helper)
  - Prove target_path_type_HashMapT_last_step and target_path_type_HashMapT_front_path via completeInduct_on LENGTH sbs + Cases_on sbs/t/t' + gvs[target_path_type_def, target_path_step_type_def] -> Lemmas written in source at lines 1830-1852. Not yet build-verified. ()
  - Prove target_path_type_HashMapT_hashmap_prefix_ValueSubscript by Induct_on vt + use target_path_type_HashMapT_last_step/front_path -> Lemma written at lines 1854-1901 but proof body still references removed target_path_type_decompose_last. Needs rewriting. ()
  - EVERY ((<>) NONE o subscript_to_value) (REVERSE is) from target_path_type -> FALSE: paths through StructT use AttrSubscript where subscript_to_value = NONE. Only hashmap-prefix subscripts are ValueSubscript. This was the key insight of E0009. ()
- `E0011` (progressed, missing_helper)
  - Prove target_path_step_type_HashMapT_next_vt: Cases_on sb >> rw[target_path_step_type_def]. Proved clean. -> Succeeded: this helper lemma extracts next_vt = vt from target_path_step_type on HashMapT, needed by last_step and front_path proofs. ()
  - Prove target_path_type_HashMapT_last_step by Induct_on sbs + gen_tac + strip_tac + gvs/Cases_on sbs + drule target_path_step_type_HashMapT_next_vt + fs -> Succeeded: compiles clean. Key was adding target_path_step_type_HashMapT_next_vt and using drule + simp to discharge the sbs <> [] premise. ()
  - Prove target_path_type_HashMapT_front_path by Induct_on sbs + gen_tac + strip_tac + gvs/Cases_on sbs + drule last_step/next_vt + metis_tac target_path_type_def -> Succeeded: compiles clean. Used metis_tac[target_path_type_def] for the inductive step. ()
  - Prove target_path_type_HashMapT_hashmap_prefix_ValueSubscript by Induct_on vt (Type case + HashMapT case) -> FAILED: Type case compiles but HashMapT case fails. Variables h/t collide with type-level t. After renaming with rename1, deriving FRONT sbs <> [] from TL (REVERSE sbs) = h :: rest_subs fails repeatedly. Tried CCONTR_TAC + Cases_on FRONT sbs + various approaches. Also tried Induct_on kts which had a static error referencing non-existent REVERSE_EQ/Nil. ()
  - Induct_on kts approach: Q.SPEC_TAC kts, then Induct, then derive FRONT sbs <> [] by CCONTR_TAC + simp[FRONT_EQ_NIL, REVERSE_EQ Nil] -> FAILED: REVERSE_EQ and Nil are not declared HOL4 theorems. Static error prevents compilation. ()
- `E0012` (progressed, missing_helper)
  - Prove target_path_type_HashMapT_hashmap_prefix_ValueSubscript by Induct_on vt with explicit assumption rewriting and Cases_on for NONE/SOME -> SUCCEEDED. Key: fix NONE-case contradiction by first putting split_hashmap_subscripts equation in assumptions with TL_REVERSE substitution, then Cases_on inner result, then for NONE branch use Cases_on `REVERSE (FRONT sbs)` >> gvs[split_hashmap_subscripts_def]. For SOME branch: PairCases on result, derive kts = t :: x1 explicitly via SOME_11, then use SNOC_LAST_FRONT identity. (`TO_type_system_rewrite-20260513T211025Z_m2096_t001`)
  - Fix HashMapRef branch: step-by-step gvs[bind_apply,AllCaseEqs()] expansion + derive standalone typing facts -> PARTIALLY SUCCEEDED. First gvs expansion works (splits first_sub/rest_subs). But second gvs expansion after split_hashmap_subscripts fails because the existential for split result components can't be discharged. Also compute_hashmap_slot/evaluate_type/read_storage_slot steps still have cheats. (`TO_type_system_rewrite-20260513T211025Z_m2112_t001`)
- `E0013` (progressed, missing_helper)
  - Added place_leaf_path_typed_split_leaf_type helper lemma connecting place_leaf_path_typed to leaf_type through split_hashmap_subscripts result. Not yet build-verified. The lemma provides: evaluate_type env.type_defs final_type = SOME base_tv AND final_tv = leaf_type base_tv remaining AND evaluate_type env.type_defs ty = SOME final_tv -> Written but not yet built. Should enable evaluate_type <> NONE derivation in HashMapRef branch. ()
  - HashMapRef branch still has 3 cheats: compute_hashmap_slot <> NONE, evaluate_type <> NONE, and remaining read/assign/write steps. Step-by-step gvs expansion approach fails because split result variables are bound inside monad. -> Blocked - need to derive all typing facts BEFORE gvs expansion, then let AllCaseEqs() eliminate NONE branches (`TO_type_system_rewrite-20260513T211025Z_m2112_t001`)
- `E0014` (progressed, missing_helper)
  - Fixed place_leaf_path_typed_split_leaf_type: Unicode ∧ for conjunction, Cases_on path before gvs for HashMapT case, drule_all with all 7 args for IH -> SUCCEEDED: lemma now builds clean (`tool_output:TO_type_system_rewrite-20260513T211025Z_m2231_t001`)
  - Rewrote HashMapRef branch proof: derive all typing facts before do-block gvs expansion, then reverse $ gvs[bind_apply,AllCaseEqs(),...] to split TypeError vs success cases, then use read_storage_slot_error + assign_subscripts_no_type_error_runtime_typed + write_storage_slot_no_type_error_from_value_has_type + assign_result_no_type_error_from_successful_assign -> FAILED at by-subgoal extracting split_hashmap_subscripts result variables - the Cases_on + gvs[] approach in the by tactic doesn't close the SOME case properly (`tool_output:TO_type_system_rewrite-20260513T211025Z_m2272_t001`)
  - Added PairCases_on x >> gvs[] >> metis_tac[] to the by-subgoal for split result extraction -> Not yet build-verified ()
- `E0015` (progressed, missing_helper)
  - option_neq_none_imp_is_some + IS_SOME_EXISTS for extracting existential witnesses from option pair result in by-subgoal -> SUCCEEDED: the by-subgoal for split_hashmap_subscripts result now builds clean. Key: mp_tac the ≠ NONE assumption, then simp[option_neq_none_imp_is_some, IS_SOME_EXISTS] converts to ∃x. ... = SOME x, then strip_tac introduces x', then qexistsl[FST x', FST (SND x'), SND (SND x')] + Cases_on x' + Cases_on r + simp[pairTheory.PAIR]. (`TO_type_system_rewrite-20260513T211025Z_m2318_t001`)
  - irule target_path_type_HashMapT_hashmap_prefix_ValueSubscript for EVERY subscript_to_value goal -> FAILED: irule produces subgoals that simp[] can't discharge (variable name/schema mismatch between lemma's kts/remaining and resume's key_types'/remaining_subs'). Changed to drule_all but not yet build-verified. ()
- `E0016` (progressed, missing_helper)
  - drule_all + simp for compute_hashmap_slot: derive LENGTH key_types' <= LENGTH (TL (REVERSE is)) from length sum, then irule compute_hashmap_slot_subscripts_to_values + simp[LENGTH, LENGTH_TAKE_EQ] + DECIDE_TAC -> COMPUTE_HASHMAP_SLOT step now builds. Key: derive inequality first from length sum, then LENGTH_TAKE_EQ + DECIDE_TAC handles MIN. (`TO_type_system_rewrite-20260513T211025Z_m2341_t001`, `TO_type_system_rewrite-20260513T211025Z_m2352_t001`)
  - Step 4: derive well_formed_vtype v from well_formed_vtype (HashMapT t v), then well_formed_type final_type' from split, then env.type_defs = get_tenv cx from runtime_consistent -> All three intermediate facts proved. But evaluate_type (get_tenv cx) final_type' <> NONE from well_formed_type still fails - simp/metis can't connect IS_SOME assumption to <> NONE goal. (`TO_type_system_rewrite-20260513T211025Z_m2377_t001`, `TO_type_system_rewrite-20260513T211025Z_m2387_t001`)
- `E0017` (progressed, missing_helper)
  - Fix evaluate_type <> NONE by Cases_on instead of rw[well_formed_type_def]>>metis_tac[] -> SUCCEEDED: Cases_on evaluate_type result >> gvs[well_formed_type_def] works. NONE case contradicts IS_SOME, SOME case trivial. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m2420_t001`)
  - gvs[bind_apply, AllCaseEqs(), lift_option_type_def, ...] expansion of do-block in resume -> FAILED: gvs doesn't expand the monadic do-block. The do-block remains in the assumption unchanged. Also qpat_x_assum with assign_target pattern doesn't match. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m2428_t001`)
  - Create boundary lemma top_level_HashMapRef_assign_no_type_error -> PARTIAL: Lemma statement compiles, placed after all helper dependencies. Proof skeleton works through lookup_global/expansion/Value-contradiction/split_hashmap_subscripts. Remaining cheats at compute_hashmap_slot and beyond. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m2506_t001`)
- `E0018` (progressed, missing_helper)
  - Boundary lemma approach: push assign_target equation to goal (mp_tac), simp[Once assign_target_def], then expand binds in goal position -> Advances through lookup_global/get_module_code/IS_SOME_EXISTS/expands first set of binds. All typing facts derive. Stuck at expand of toplevel_value case split - need further gvs expansion to reach HashMapRef branch. (`TO_type_system_rewrite-20260513T211025Z_m2552_t001`)
  - Resume inline approach: qpat_x_assum `_ = (INR (Error (TypeError _)),_)` mp_tac after initial gvs[assign_target_def,...] -> Finds the equation but big simp only partially expands do-block - inner binds are behind lambdas and stay unexpanded. Dead end. (`TO_type_system_rewrite-20260513T211025Z_m2547_t001`)
- `E0019` (progressed, missing_helper)
  - Phase 1/Phase 2 restructure: derive all typing facts BEFORE expanding assign_target, then Cases_on tv to handle Value/HashMapRef/ArrayRef separately -> Phase 1 works (metis_tac closes split_hashmap_subscripts, etc.). Phase 2 structure works - Cases_on tv creates 3 subgoals, Value case contradiction via lookup_global_Value_not_HashMapVarDecl works. But existential extraction and ArrayRef case still have cheats. (`TO_type_system_rewrite-20260513T211025Z_m2632_t001`)
  - drule/irule for target_path_type_HashMapT_split_hashmap_subscripts: fails because well_formed_vtype env.type_defs vs well_formed_vtype (get_tenv cx) don't unify in drule despite env.type_defs = get_tenv cx being in assumptions -> Switched to metis_tac which handles the unification. SUCCEEDED. (`TO_type_system_rewrite-20260513T211025Z_m2632_t001`)
  - qexistsl [FST x', FST (SND x'), SND (SND x')] with Cases_on x' >> Cases_on r for existential extraction from IS_SOME_EXISTS -> FAILED: type error - FST applied to SND x' where x' doesn't have right pair decomposition. Need simpler approach: Cases_on the option result directly. (`TO_type_system_rewrite-20260513T211025Z_m2632_t001`)
- `E0020` (progressed, missing_helper)
  - Phase 1: derive typing facts (sbs <> [], split_hashmap_subscripts, compute_hashmap_slot <> NONE, evaluate_type <> NONE). Phase 2: prove lookup_global_HashMapVarDecl_returns_HashMapRef. Phase 3: expand assign_target do-block and dispatch TypeErrors. -> Phase 1 + 2 complete. Phase 3: the AllCaseEqs blast creates quantified v/s'' from bind decomposition; Cases_on `v` works but subsequent Cases_on `a` fails because gvs already resolved v = INL (HashMapRef ...) from lookup_global assumption. ()
  - lookup_global_HashMapVarDecl_returns_HashMapRef: get_module_code + find_var_decl_by_num HashMapVarDecl + lookup_var_slot_from_layout => lookup_global returns (INL (HashMapRef is_t (n2w slot) kt vt), st) -> Succeeded: lemma builds clean with rw[lookup_global_def] + gvs[] (`tool_output:TO_type_system_rewrite-20260513T211025Z_m2763_t001`)
  - Cases_on `v` >> gvs[] to split lookup_global result into INL/INR, then Cases_on `a` for toplevel_value -> Cases_on `v` >> gvs[] works and puts us in HashMapRef branch. But Cases_on `a` fails because gvs already substituted v = INL (HashMapRef ...) from assumption, eliminating `a`. ()
- `E0021` (progressed, missing_helper)
  - probe: FAIL_TAC at HashMapRef branch after Phase 1 typing facts -> Goal is F with do-block equation in assumptions + all typing facts. Do-block = do ... od s'' = (INR (Error (TypeError msg)), st') (`TO_type_system_rewrite-20260513T211025Z_m2808_t001`)
  - gvs[bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def, AllCaseEqs(), option_CASE_rator, sum_CASE_rator, pairTheory.PAIR] to expand do-block in assumptions -> SUCCESS: gvs expands the do-block AND auto-resolves some NONE/TypeError branches. Creates 4 remaining subgoals. (`TO_type_system_rewrite-20260513T211025Z_m2810_t001`)
  - probe with FAIL_TAC after gvs expansion to see all 4 subgoals -> 4 subgoals identified: (1) compute_hashmap_slot NONE - needs bridge x'=LAST is, TAKE length, (2) write+result bind after read/assign success, (3) read_storage_slot TypeError, (4) assign_subscripts TypeError (`TO_type_system_rewrite-20260513T211025Z_m2818_t001`)
  - >- for each subgoal with bridge lemmas but >> >- syntax error -> SYNTAX ERROR: >> >- has wrong precedence. gvs[...] >> >- tac1 fails to type-check. Must use gvs[...] >- (tac1) >- (tac2) directly. (`TO_type_system_rewrite-20260513T211025Z_m2820_t001`)
- `E0022` (progressed, missing_helper)
  - Fix >> >- syntax: replace gvs >> >- tac with gvs >- tac >- tac >- tac >> tac for alternating subgoal handling -> SYNTAX FIX: >> and >- have same precedence, left-associative. Must use gvs >- (tac1) >- (tac2) pattern, not gvs >> >- tac1. Build now passes syntax check. (`TO_type_system_rewrite-20260514T090000Z_m2838_t001`)
  - x' = LAST is by Cases_on is >> gvs[REVERSE_DEF, LAST_DEF, HD] -> FAILED: gvs renames is to h::t' but the by-subgoal still references is. The Cases_on creates h::t' decomposition but the by-subgoal variable context has is already destructed. (`TO_type_system_rewrite-20260514T090000Z_m2860_t001`)
  - metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq] for x' = LAST is -> FAILED: metis cannot find solution. The SNOC decomposition creates circular equation is = SNOC(LAST is)(FRONT is). (`TO_type_system_rewrite-20260514T090000Z_m2864_t001`)
  - drule SNOC_LAST_FRONT_eq >> strip_tac >> gvs[REVERSE_SNOC_eq] -> PARTIAL: drule gives is = SNOC(LAST is)(FRONT is) which is circular. gvs[REVERSE_SNOC_eq] can't eliminate circular variable. (`TO_type_system_rewrite-20260514T090000Z_m2870_t001`)
  - Prove HD_REVERSE_EQ_LAST helper lemma, then use it: `HD(REVERSE is) = LAST is` by metis_tac[HD_REVERSE_EQ_LAST] >> gvs[] -> SUCCEEDED: HD_REVERSE_EQ_LAST bridges x' = LAST is. After gvs, x' is eliminated. Still need LENGTH xs = LENGTH is - 1 for TAKE equality. (`TO_type_system_rewrite-20260514T090000Z_m2878_t001`)
  - After x' = LAST is bridge: `LENGTH xs = LENGTH is - 1` by Cases_on is >> gvs[LENGTH_REVERSE] >> gvs[] -> NOT YET BUILD-VERIFIED. Current code at lines 2295-2300. ()
- `E0023` (stuck, missing_helper)
  - gvs[LENGTH_REVERSE] for subgoal 2 after gvs[AllCaseEqs()] expansion -> Fails - gvs rewrites LENGTH is in some assumptions but can't chain the SUC(LENGTH xs) substitution + LENGTH-TAKE arithmetic to close the F goal ()
  - by-subgoal: LENGTH is = SUC(LENGTH xs) by simp[GSYM LENGTH_REVERSE] -> Times out - simp[GSYM LENGTH_REVERSE] loops ()
  - by-subgoal: LENGTH is = SUC(LENGTH xs) by metis_tac[LENGTH_REVERSE, LENGTH] -> Fails - metis can't find proof with these names ()
  - REVERSE_CONS_IMP_LENGTH helper + irule MATCH_MP in by-subgoal -> by-subgoal never closes despite helper lemma building clean ()
  - qpat_x_assum with MATCH_MP REVERSE_CONS_IMP_LENGTH inline -> Silent failure - assumption not added or pattern match fails ()
- `E0024` (stuck, plan_incomplete)
  - Inline gvs[AllCaseEqs()] expansion of HashMapRef do-block in assumptions with by-subgoal LENGTH bridging -> Dead end after 10+ attempts. By-subgoal pattern can't close LENGTH arithmetic. Variable context inside by-subgoals is incompatible with the arithmetic needed. The inline approach creates fragile subgoals with subtle variable/LENGTH mismatches. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m2945_t001`)
  - Boundary lemma top_level_HashMapRef_assign_no_type_error with goal-position expansion -> Boundary lemma exists with cheat at line 2167. Phase 1-2 helper lemmas (lookup_global_HashMapVarDecl_returns_HashMapRef, target path lemmas) proved clean. Phase 3 (do-block expansion in goal position + TypeError dispatch) still needs the full C3.1.1/C3.1.2/C3.1.3 plan. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m2763_t001`)
- `E0026` (progressed, missing_helper)
  - Added C3.1.3 helper target_path_type_HashMapT_split_leaf_runtime with irule target_path_type_Type_place_leaf_typed + drule_all place_leaf_path_typed_split_leaf_type -> FAILED: drule_all place_leaf_path_typed_split_leaf_type can't match because assumption has place_leaf_typed env (HashMapT kt vt) sbs ty pl_tv, but lemma expects place_leaf_path_typed env vt path ty final_tv. Need intermediate unfolding of place_leaf_typed_def and place_leaf_path_typed_def for HashMapT case. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3108_t001`)
  - Rewrote main theorem (C3.1.6) proof: replaced simp[Once assign_target_def, bind_def] with once_rewrite_tac[assign_target_def] + rewrite_tac[bind_def,...] + CCONTR_TAC approach -> NOT YET TESTED: C3.1.3 must succeed first before the main theorem proof can be attempted ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m3108_t001` (use `read_tool_output` for exact output)

## C3.1.2

### Current Status

- result: `proved`
- diagnosis: `unknown`
- latest episode: `E0025`
- blocker: ""

### Attempts / Evidence

- `E0025` (proved, unknown)
  - target_path_type_HashMapT_assign_target_decomp: fix /= syntax with ∧, then prove decomp lemma using metis_tac[target_path_type_HashMapT_not_nil, target_path_type_HashMapT_split_hashmap_subscripts, etc.] -> Decomp lemma proved and builds clean. All existential facts derived from existing lemmas via metis_tac. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3011_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m3011_t001` (use `read_tool_output` for exact output)

## C3.1.3

### Current Status

- result: `proved`
- diagnosis: `other`
- latest episode: `E0027`
- blocker: "none"

### Attempts / Evidence

- `E0027` (proved, other)
  - rpt strip_tac >> derive env.type_defs = get_tenv cx >> get place_leaf_typed via target_path_type_Type_place_leaf_typed >> gvs[place_leaf_typed_def] >> Cases_on REVERSE sbs >> gvs[place_leaf_path_typed_def] >> drule_all place_leaf_path_typed_split_leaf_type >> strip_tac >> qexists_tac base_tv >> conj_tac >- metis_tac (bridge env.type_defs/get_tenv cx) >> conj_tac >- irule assignable_type_evaluate_not_NoneTV >> metis_tac >> irule evaluate_type_well_formed_type_value >> metis_tac -> C3.1.3 proved. Key fix: gvs[place_leaf_typed_def] then Cases_on REVERSE sbs to expose place_leaf_path_typed, then gvs[place_leaf_path_typed_def] for HashMapT case strips head element giving place_leaf_path_typed env vt t ty pl_tv. Then drule_all place_leaf_path_typed_split_leaf_type works. Also fixed type error in C3.1.6: disch_then (drule_all o write_storage_slot...) to disch_then assume_tac >> drule_all ... (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3162_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m3162_t001` (use `read_tool_output` for exact output)

## C3.1.6

### Current Status

- result: `progressed`
- diagnosis: `other`
- latest episode: `E0034`
- blocker: "assign_target_HashMapRef_branch_no_type_error: Goals 1 and 2 SOLVED. Goals 3 and 4 remain with simple fixes needed: Goal 3 needs metis_tac[] after simp[no_type_error_result_def] to connect assumption 12 (assign_subscripts = INR e) with assumption 15 (assign_subscripts ≠ INR(TypeError msg)) via INR injectivity. Goal 4 needs drule read_storage_slot_error >> simp[no_type_error_result_def] to resolve runtime error constructor mismatch."

### Attempts / Evidence

- `E0028` (progressed, other)
  - rpt strip_tac >> derive env.type_defs + lookup_global + decomp + LENGTH facts >> irule compute_hashmap_slot_subscripts_to_values >> simp[] >> decide_tac -> simp[] times out at 60s with 24 assumptions - too heavy. irule matched but subsequent simp processing all assumptions is too slow (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3180_t001`)
  - irule compute_hashmap_slot_subscripts_to_values >> qexists_tac LENGTH rest_subs - LENGTH remaining >> simp[LENGTH_TAKE_EQ] >> decide_tac -> qexists_tac failed - goal after irule is not existential, it is conjunctive (LENGTH + EVERY antecedents) (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3180_t001`)
- `E0029` (progressed, other)
  - Add compute_hashmap_slot_prefix_some helper lemma (C3.1.4) with clean proof context, replace Step 4 by-subgoal with metis_tac[compute_hashmap_slot_prefix_some] -> compute_hashmap_slot by-subgoal resolved cleanly. Helper lemma proved at line 1823. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3213_t001`)
  - CCONTR_TAC then qpat_x_assum mp_tac then AllCaseEqs blast -> CCONTR_TAC + fs[] substitutes res=INR(Error(TypeError msg)) in assumptions, making qpat_x_assum pattern `assign_target ... = (res,st')` not match (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3192_t001`)
  - Push equation to goal first (no CCONTR_TAC), then rewrite_tac[bind_def]+AllCaseEqs blast -> Goal after once_rewrite_tac[assign_target_def] exceeds 4KB, simp[AllCaseEqs()] times out at 60s (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3220_t001`)
  - Boundary lemma approach: prove assign_target_HashMapRef_branch_no_type_error separately, then main theorem calls it. Kill unused assumptions before CCONTR_TAC+simp[assign_target_def,bind_apply,AllCaseEqs()] -> Boundary lemma placed after main theorem caused forward reference error. Fixed ordering. But simp[assign_target_def,bind_apply,AllCaseEqs()] in the boundary lemma STILL times out at 120s. Killing 11 unused assumptions helped reduce assumption count but the do-block expansion itself is too large for a single simp call. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3227_t001`)
- `E0030` (stuck, other)
  - Remove boundary lemma, prove main theorem directly with once_rewrite_tac[assign_target_def] + simp[bind_def,AllCaseEqs(),...]+TRY dispatch blocks -> Proof failed - 'no theorem proved'. The tactic left unresolved subgoals. The AllCaseEqs approach likely creates TypeError subgoals that the TRY dispatch blocks don't handle. Need to inspect exact residual goals. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3253_t001`)
- `E0031` (progressed, other)
  - Cases_on compute_hashmap_slot instead of simp[IS_SOME_EXISTS] for <> NONE to = SOME conversion -> Succeeded - Cases_on resolves instantly vs simp timeout at 120s. This fixes a key performance blocker. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3286_t001`, `tool_output:TO_type_system_rewrite-20260513T211025Z_m3288_t001`)
  - CCONTR_TAC + gvs[no_type_error_result_def] + mp_tac push equation to goal + once_rewrite_tac[assign_target_def] + simp[bind_apply, lift_option_type_def, ...] -> Goal after expansion attempt shows assign_target... ≠ (INR(Error(TypeError msg)),st') unchanged - once_rewrite_tac may not have fired, or simp re-simplified. Need FAIL_TAC probe RIGHT after once_rewrite_tac (before any simp) to inspect. Syntax error prevented this probe. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3296_t001`)
- `E0032` (progressed, other)
  - gvs[Once assign_target_def, bind_def, ..., AllCaseEqs()] then FAIL_TAC probe -> SUCCESS: gvs with AllCaseEqs on boundary lemma (10 hypotheses) fully expands do-block in one step, auto-resolves error branches, leaves 4 concrete subgoals. Proved the approach works. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3377_t001`)
  - Dispatch 4 subgoals with >- after >> : gvs[...] >> >- (tac1) >- (tac2) >- (tac3) >- (tac4) -> FAILED: >> before >- creates a type error. >> and >- have same precedence/left-associative, so >> tries to apply >- tac1 as a tactic argument, but >- tac1 is not a complete tactic. Must remove >> between gvs and first >-. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3384_t001`, `tool_output:TO_type_system_rewrite-20260513T211025Z_m3386_t001`, `tool_output:TO_type_system_rewrite-20260513T211025Z_m3390_t001`)
  - Cases_on approach: manual step-by-step Cases_on read_storage_slot/assign_subscripts/write_storage_slot after initial gvs without AllCaseEqs -> >= works for first Cases_on pair, but fs[] after Cases_on creates unpredictable subgoal split making >- annotations misalign. AllCaseEqs approach is cleaner. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3349_t001`, `tool_output:TO_type_system_rewrite-20260513T211025Z_m3375_t001`)
- `E0033` (progressed, other)
  - gvs[AllCaseEqs()] >> >- (metis_tac[...]) >- (metis_tac[...]) ... -> Type error: >> before >- is invalid HOL4 syntax due to same precedence/left-associativity. Fixed by removing >>. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3384_t001`, `tool_output:TO_type_system_rewrite-20260513T211025Z_m3390_t001`)
  - gvs[AllCaseEqs()] >- (metis_tac[read_storage_slot_success_type, assign_subscripts_preserves_type_runtime_typed, assign_result_no_type_error_from_successful_assign, no_type_error_result_def]) ... -> metis_tac times out at 120s on all 4 goals with 10-14 assumptions (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3400_t001`)
  - drule read_storage_slot_success_type >> drule assign_subscripts_preserves_type_runtime_typed >> simp[assign_result_no_type_error_from_successful_assign] -> Chained drule creates nested implications in goal, not assumptions. simp can't resolve the quantifier structure. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3400_t001`)
  - irule assign_result_no_type_error_from_successful_assign >> simp[] -> irule creates existential witness subgoal: ∃new old op st st' subs tv. assign_result tv op old subs st = (res,st') ∧ assign_subscripts tv old subs op = INL new. simp[] can't resolve. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3422_t001`)
  - imp_res_tac read_storage_slot_success_type >> imp_res_tac assign_subscripts_preserves_type_runtime_typed >> drule assign_result_no_type_error_from_successful_assign >> disch_then drule >> simp[no_type_error_result_def] -> Goal 1 succeeds but imp_res_tac pollutes with 28+ resolvent assumptions. For Goals 2-4: resolve_then+first_x_assum pattern fails because first_x_assum picks wrong assumption. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3428_t001`)
  - drule_all read_storage_slot_success_type in by-subgoal -> drule_all creates implications even when all antecedents match. Need drule_all_then assume_tac or irule inside by-subgoal instead. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3418_t001`)
- `E0034` (progressed, other)
  - gvs[AllCaseEqs()] with controlled >- dispatch, irule/drule chains for 4 subgoals -> Goals 1-2 solved. Goal 3: after drule_all_then strip_assume_tac assign_subscripts_no_type_error_runtime_typed, simp[no_type_error_result_def] leaves ∀msg. e ≠ TypeError msg which needs metis_tac[] to bridge assumptions 12+15. Goal 4: drule read_storage_slot_error >> simp[no_type_error_result_def] not yet tested since Goal 3 blocked. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3467_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m3467_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260513T211025Z_m3455_t001` (use `read_tool_output` for exact output)

## C3.1.7

### Current Status

- result: `stuck`
- diagnosis: `other`
- latest episode: `E0041`
- blocker: metis_tac[lookup_global_HashMapRef_not_StorageVarDecl, top_level_Type_not_hashmap_decl] fails at line 2423 of vyperTypeStatePreservationScript.sml. After PairCases_on p + Cases_on p0 + gvs[IS_SOME_EXISTS], the pair p is destructured into (StorageVarDecl b'' t'', p1). The lemma lookup_global_HashMapRef_not_StorageVarDecl needs find_var_decl = SOME p and FST p = StorageVarDecl ... as separate premises, but metis_tac can't unify the destructured form with the lemma's pair variable. Fix: either (1) don't destruct p before applying lemma - keep it as a pair, (2) use mp_tac + simp[lookup_global_def,...AllCaseEqs()] blast approach to prove F directly without the lemma, or (3) prove a stronger lemma that takes the already-destructured form.
- next: Fix the vt=Type contradiction proof at line 2419-2424. Replace PairCases_on p + Cases_on p0 + metis_tac with mp_tac of lookup_global equation + simp[lookup_global_def,...] blast approach. Also verify the HashMapT case (lines 2426-2438) metis_tac[top_level_HashMapRef_assign_no_type_error] works for premise matching.

### Attempts / Evidence

- `E0035` (stuck, plan_incomplete)
  - Current approach: gvs[assign_target_def, bind_apply, AllCaseEqs()] upfront then try drule top_level_HashMapRef_assign_no_type_error in HashMapRef branch -> Fails because gvs destroys assign_target cx ... = (res,st') equation. After expansion, assumptions contain expanded monadic do-block but no assign_target equation to match lemma conclusion. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3481_t001`)
- `E0036` (progressed, plan_incomplete)
  - Cases_on `tgt` >> gvs[target_runtime_typed_def, location_runtime_typed_def] >> Cases_on `vt` >> handle Type contradiction + HashMapT derivation + expand monadic do-block -> Probed goal state successfully. After Cases_on tgt + gvs[target_runtime_typed_def, location_runtime_typed_def]: got FLOOKUP with variable vt, target_path_type env vt is (Type ty). After Cases_on vt: (1) Type base_ty - contradiction via lookup_global_Value_not_HashMapVarDecl + top_level_Type_not_hashmap_decl. (2) HashMapT t' v' - need to derive well_formed, decl witnesses, then expand do-block. File corruption prevents clean build. (`TO_type_system_rewrite-20260513T211025Z_m3714_t001`)
- `E0037` (progressed, plan_incomplete)
  - Cases_on `tgt` >> gvs[target_runtime_typed_def, location_runtime_typed_def] >> Cases_on `vt` >> handle Type contradiction + HashMapT derivation + expand monadic do-block -> Probed goal state successfully. After Cases_on tgt + gvs: FLOOKUP with variable vt, target_path_type env vt is (Type ty), lookup_global returns HashMapRef. Type case = contradiction. HashMapT case needs premises + do-block expansion. File corruption from FAIL_TAC insertion prevents build. (`TO_type_system_rewrite-20260513T211025Z_m3714_t001`)
  - gvs[assign_target_def,...] upfront then drule top_level_HashMapRef_assign_no_type_error in HashMapRef branch -> Fails because gvs destroys assign_target equation needed as lemma premise (`TO_type_system_rewrite-20260513T211025Z_m3481_t001`)
- `E0038` (progressed, missing_helper)
  - Cases_on tgt >> gvs[target_runtime_typed_def, location_runtime_typed_def] >> Cases_on vt >> >- (gvs[assign_target_assignable_context_def] >> PairCases_on p >> Cases_on p0 >> gvs[IS_SOME_EXISTS] >> metis_tac[top_level_Type_not_hashmap_decl]) >> ...do-block expansion with 4 subgoals... -> Type case metis_tac[top_level_Type_not_hashmap_decl] fails: the lemma needs runtime_consistent + FLOOKUP=Type + get_module_code + find_var_decl=SOME(HashMapVarDecl...), but after gvs[assign_target_assignable_context_def] and Cases_on p0, we have find_var_decl=SOME(StorageVarDecl...) for the StorageVarDecl case (which hasn't been contradicted yet) and need a bridge lemma. metis_tac can't find the HashMapVarDecl variant. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3765_t001`)
- `E0039` (progressed, missing_helper)
  - Add lookup_global_HashMapRef_not_StorageVarDecl lemma with rw[lookup_global_def,...] + gvs[AllCaseEqs(),...] + Cases_on lookup_var_slot -> Multiple proof attempts failed. rw[lookup_global_def,...] with implicatitive format converts find_var_decl hypothesis to negated goal. FAIL_TAC probe (TO_...m3821) showed after rw the goal becomes find_var_decl ≠ SOME (StorageVarDecl...) instead of F. ()
  - Use mp_tac to push lookup_global equation to goal then simp[lookup_global_def,...,AllCaseEqs()] -> Not yet tried - this is the recommended next approach. simp can expand definitions in goal position but not in assumptions. ()
  - Conjunctive format matching lookup_global_Value_not_HashMapVarDecl pattern with FST p = StorageVarDecl -> Current file has /& instead of /\ syntax error. Not yet tested with correct syntax. ()
- `E0040` (progressed, missing_helper)
  - Fix /& to ==> format in lookup_global_HashMapRef_not_StorageVarDecl + mp_tac proof approach -> Lemma compiles successfully. mp_tac pushes lookup_global equation to goal position, simp[lookup_global_def,...,AllCaseEqs()] expands and AllCaseEqs resolves constructor mismatches. ()
  - Restructure HashMapRef branch in sound_TopLevelVar: use metis_tac[top_level_HashMapRef_assign_no_type_error] instead of inline gvs[assign_target_def,...] expansion -> Code written but not yet build-verified. Added cheat for ArrayRef branch. Key sub-steps: Cases_on tgt + Cases_on vt, derive env.type_defs=get_tenv cx, well_formed_vtype, top_level_HashMap_decl, IS_SOME_EXISTS for slot, then metis_tac[top_level_HashMapRef_assign_no_type_error]. ()
- `E0041` (stuck, other)
  - metis_tac[lookup_global_HashMapRef_not_StorageVarDecl, top_level_Type_not_hashmap_decl] for vt=Type case after PairCases_on p + Cases_on p0 -> Failed: FOL_FIND can't unify the destructured pair (StorageVarDecl b'' t'', p1) with the lemma's pair variable p + FST p premise (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3902_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m3902_t001` (use `read_tool_output` for exact output)

## C3.1.7.1

### Current Status

- result: `progressed`
- diagnosis: `tool_limit`
- latest episode: `E0043`
- blocker: plan_oracle de-risked C3.1.7.1 from Risk 3 to Risk 2 with clear approach: use existing assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error boundary theorem for the 5 non-ArrayTV cheats. The prior DISCH_THEN instrumentation blocker may be resolved in current holbuild - needs testing. The boundary theorem is already proved and available.
- next: Test holbuild DISCH_THEN issue by editing 5 cheats and building. If metis_tac works inside Resume blocks, simple replacement will close component.

### Attempts / Evidence

- `E0042` (stuck, tool_limit)
  - drule assign_result_no_type_error_from_successful_assign >> disch_then drule >> simp[no_type_error_result_def] -> DISCH_THEN assert:predicate not true. Lemma has conjunctive antecedent, drule matches only one. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m4624_t001`)
  - metis_tac[assign_result_no_type_error_from_successful_assign] -> Also triggers DISCH_THEN instrumentation assertion (`tool_output:TO_type_system_rewrite-20260513T211025Z_m4620_t001`)
  - ACCEPT_TAC(MATCH_MP ...) inside fn closure -> Syntax error + DISCH_THEN failure (`tool_output:TO_type_system_rewrite-20260513T211025Z_m4688_t001`)
  - Split lemma assign_result_no_type_error_from_successful_assign_split with separate implication premises, then drule >> disch_then drule -> DISCH_THEN assertion still fires even with split form (`tool_output:TO_type_system_rewrite-20260513T211025Z_m4743_t001`)
  - mp_tac to push assumptions to goal + simp[lemma], avoid drule/disch_then entirely -> Still fails - by-subgoals (irule + goal_assum drule_all for value_has_type) also go through DISCH_THEN (`tool_output:TO_type_system_rewrite-20260513T211025Z_m4746_t001`)
- `E0043` (progressed, tool_limit)
  - Previous session: drule/metis_tac/irule all trigger DISCH_THEN assertion in vyperTypeStatePreservationScript.sml for new theorems -> Blocked by holbuild proof_runtime.sml:749 DISCH_THEN instrumentation issue (`TO_type_system_rewrite-20260513T211025Z_m4746_t001`)
  - Current session: plan_oracle(mode=augment, C3.1.7.1) de-risked component, identified existing boundary theorem as correct consumer -> Component de-risked to Risk 2 with clear approach: use assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error for 5 cheats ()

### Evidence refs

- `TO_type_system_rewrite-20260513T211025Z_m4746_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260513T211025Z_m4743_t001` (use `read_tool_output` for exact output)

## C3.1.7.1.3

### Current Status

- result: `progressed`
- diagnosis: `plan_incomplete`
- latest episode: `E0044`
- blocker: "Callee assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error needs two derived facts that the boundary theorem assign_target_TopLevelVar_Value_branch_ntr requires: (1) evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)) from target_path_type + place_leaf_typed chain, (2) leaf_type root_tv (REVERSE sbs) <> NoneTV from assignable_type. Also need well_formed_vtype env.type_defs (Type t) for step (1). The boundary theorem itself (Value_branch_ntr) is proved. The caller proof structure is clear but the fact-derivation chain is incomplete."
- next: "Prove adapter facts: (1) well_formed_vtype (get_tenv cx) (Type t) from runtime_consistent assumptions, (2) evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)) via target_path_type_Type_place_leaf_typed + place_leaf_typed_evaluate_type, (3) leaf_type root_tv (REVERSE sbs) <> NoneTV via assignable_type_evaluate_not_NoneTV. Then caller proof uses r=st (lookup_global_state) + these adapter facts to satisfy drule_all of the boundary theorem."

### Attempts / Evidence

- `E0044` (progressed, plan_incomplete)
  - Proved assign_target_TopLevelVar_Value_branch_ntr: rw+gvs expands assign_target_def, 3 goals close via metis_tac[assign_result_no_type_error_from_successful_assign_split], spose_not_then+simp[set_global_storage_no_type_error], spose_not_then+simp[assign_subscripts_no_type_error_runtime_typed] -> Boundary theorem fully proved. Changed st to st0 for lookup_global output state to avoid variable name collision. ()
  - Tried mp_tac+impl_tac, irule, drule_all, metis_tac to apply boundary theorem from caller. All fail because: (a) drule_all can't chain env.type_defs=get_tenv cx to produce evaluate_type env.type_defs ty fact, (b) cant derive leaf_type<>NoneTV from assignable_type without explicit chain, (c) well_formed_vtype env.type_defs (Type t) missing for place_leaf_typed chain. -> Caller proof stuck - needs adapter facts before drule_all can succeed ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m4969_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260513T211025Z_m4999_t001` (use `read_tool_output` for exact output)

## C3.1.7.1.3.1

### Current Status

- result: `progressed`
- diagnosis: `other`
- latest episode: `E0052`
- blocker: assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error now builds successfully. Remaining cheats in this file: top_level_HashMapRef_assign_no_type_error (C3.1), sound_TopLevelVar resume (C3.1.7), sound_ImmutableVar (C3.1.7.2), sound_TupleTargetV (C3.1.7.3), sound_assign_targets_cons (C3.1.7.4).

### Attempts / Evidence

- `E0045` (progressed, plan_incomplete)
  - Added target_path_type_Type_evaluate_leaf: well_formed_vtype + target_path_type + evaluate_type t=SOME root_tv => evaluate_type ty = SOME (leaf_type root_tv (REVERSE sbs)). Proof: drule target_path_type_Type_place_leaf_typed >> simp >> strip >> mp_tac place_leaf_typed >> simp[place_leaf_typed_def, place_leaf_path_typed_def] >> strip >> gvs[] -> Lemma added to vyperTypeExprSoundnessScript.sml (not in DISCH_THEN-blocked file). Not yet build-verified. ()
- `E0046` (progressed, plan_incomplete)
  - Added target_path_type_Type_evaluate_leaf lemma to vyperTypeExprSoundnessScript.sml (line 631). Fixed Unicode corruption in /\ by converting to ==> chain. Build verified. -> Compiles in vyperTypeExprSoundnessTheory ()
  - Added target_path_type_Type_evaluate_leaf_not_NoneTV lemma to vyperTypeExprSoundnessScript.sml (line 648). Uses evaluate_leaf + assignable_type_evaluate_not_NoneTV. -> Compiles in vyperTypeExprSoundnessTheory ()
  - Fixed caller at line 2485: first tried by simp[...] (failed - simp can't chain), then fs[...] (worked for fact derivation but drule_all hit DISCH_THEN), now trying mp_tac + simp[assign_target_TopLevelVar_Value_branch_ntr] pattern. -> NOT YET BUILD-VERIFIED - this is the pending edit ()
- `E0047` (progressed, plan_incomplete)
  - Cases_on lookup_global >> Cases_on q >> Cases_on x >- (Value: derive facts then irule/mp_tac+simp/drule+simp to close) -> All by-steps succeed but closing tactic (irule>>simp, mp_tac>>simp, drule_all>>simp) fails to close. Cannot see inner goal state to diagnose. (`TO_type_system_rewrite-20260513T211025Z_m5351_t001`, `TO_type_system_rewrite-20260513T211025Z_m5354_t001`, `TO_type_system_rewrite-20260513T211025Z_m5361_t001`)
  - Prove lookup_global_StorageVarDecl_non_ArrayTV_returns_Value helper first (forall v version), then flat proof with metis_tac to apply boundary lemma -> Helper had wrong statement (forall v instead of exists v was impossible). Abandoned this direction. (`TO_type_system_rewrite-20260513T211025Z_m5359_t001`)
  - Stale checkpoint breaking: tried rw[], gen_tac, T by simp[], rpt strip_tac >> T by simp[] as proof openers -> Checkpoint kept matching proof prefix. The checkpoint issue is annoying but NOT the root cause - the proof logic itself fails. (`TO_type_system_rewrite-20260513T211025Z_m5298_t001`)
- `E0048` (progressed, plan_incomplete)
  - by metis_tac[...] inside >- chains for each intermediate fact (r=st, value_has_type, typ=t, evaluate_type leaf, leaf_type<>NoneTV) then mp_tac boundary_lemma >> simp[] -> All by metis_tac[...] steps fail with DISCH_THEN assertion at proof_runtime.sml:749. This is a known holbuild instrumentation issue for new proofs in vyperTypeStatePreservationScript.sml (L0114). ()
  - mp_tac assign_target_TopLevelVar_Value_branch_ntr >> simp[] after deriving all facts via by metis_tac -> Cannot reach this step because all preceding by metis_tac steps fail first. Previous session confirmed mp_tac+simp also fails (L0099) but that was in stale checkpoint context. ()
  - Various checkpoint-breaking attempts (all_tac, rename theorem, restructure opening) -> Checkpoint keeps matching through line 2473. Need more aggressive restructuring of the Proof block opening. ()
- `E0049` (progressed, plan_incomplete)
  - all_tac >> rpt strip_tac >> Cases_on lookup_global >> Cases_on q >> Cases_on x >> <branches> -> Structure confirmed: 3 INL subgoals (Value, HashMapRef, ArrayRef) + 1 INR subgoal. Checkpoint broken by all_tac >>. Cheat versions pass for all branches. (`TO_type_system_rewrite-20260513T211025Z_m5477_t001`, `TO_type_system_rewrite-20260513T211025Z_m5496_t001`)
  - Replace by metis_tac[lookup_global_state] with gvs[lookup_global_state] / fs[lookup_global_state] / simp[lookup_global_state] -> NONE of fs/gvs/simp can resolve lookup_global_state against assumption 'lookup_global ... = (INL x, r)' because it's an implication lemma that requires matching st' to r in a pair. The simplifier cannot instantiate existential variables in assumption pairs. (`TO_type_system_rewrite-20260513T211025Z_m5490_t001`, `TO_type_system_rewrite-20260513T211025Z_m5488_t001`)
  - mp_tac lookup_global_state >> simp[] to derive r = st -> mp_tac introduces universally quantified res/st' variables that don't match r in context. strip_tac creates fresh variables that don't unify. Need Q.INST specialization. (`TO_type_system_rewrite-20260513T211025Z_m5488_t001`)
  - Contradiction branches: gvs[lookup_global_HashMapRef_not_StorageVarDecl] -> gvs/simp cannot resolve the implication lemma either. Must inline the lemma's proof approach: mp_tac the lookup_global assumption >> simp[lookup_global_def, AllCaseEqs(), ...] >> rpt strip_tac >> gvs[] (`TO_type_system_rewrite-20260513T211025Z_m5490_t001`)
- `E0050` (progressed, other)
  - mp_tac lookup_global_storage_Value_typed >> simp[] >> strip_tac >> mp_tac assign_target_TopLevelVar_Value_branch_ntr >> simp[] -> mp_tac introduces universally quantified res/st' genvars that don't match existing pair-typed assumptions. simp[] cannot unify genvars with concrete pair assumptions like (INL (Value v), r). Created unsolvable implication chain. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m5838_t001`)
  - irule assign_target_TopLevelVar_Value_branch_ntr >> simp[] -> irule successfully matches no_type_error_result conclusion but creates 17 existential subgoals (all variables from boundary lemma). simp[] cannot solve existential witnesses. Need metis_tac or explicit qexistsl. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m5842_t001`)
  - metis_tac[assign_target_TopLevelVar_Value_branch_ntr, lookup_global_storage_Value_typed] -> NOT YET BUILD-VERIFIED. The by/metis_tac approach works (passes THEN1 instrumentation). metis_tac should handle both matching and witness solving. This is the most promising approach. ()
- `E0051` (progressed, other)
  - by+metis_tac for intermediate facts (well_formed_vtype, typ=t, evaluate_type leaf, leaf_type <> NoneTV), then Cases_on lookup_global >> Cases_on q >> Cases_on x for INL, then Cases_on e for INR -> All by+metis_tac steps work. INL branch (Value/HashMapRef/ArrayRef) closes correctly. INR branch fails because stale checkpoint replays old variable names: Cases_on `e` does not match replayed variable y. (`TO_type_system_rewrite-20260513T211025Z_m5866_t001`)
- `E0052` (progressed, other)
  - all_tac >> rpt strip_tac >> by metis_tac[...] for derived facts >> Cases_on lookup_global >> Cases_on q >> Cases_on x for INL branches (Value/HashMapRef/ArrayRef via metis_tac) >> INR branch: imp_res_tac lookup_global_state >> gvs[] >> imp_res_tac assign_target_TopLevelVar_lookup_global_INR_propagate >> gvs[] >> CCONTR_TAC >> gvs[no_type_error_result_def, sumTheory.INR_11] >> metis_tac[lookup_global_StorageVarDecl_non_ArrayTV_no_TypeError] -> Build succeeded. Key insight: imp_res_tac avoids variable-name dependency that by-subgoals have when checkpoint replays with stale names. CCONTR_TAC + gvs with sumTheory.INR_11 properly expands and resolves the no_type_error_result goal for the INR branch. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m5883_t002` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260513T211025Z_m5897_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260513T211025Z_m5903_t001` (use `read_tool_output` for exact output)

## C3.1.7.1.3.2

### Current Status

- result: `proved`
- diagnosis: `other`
- latest episode: `E0053`
- blocker: Lemma target_path_type_Type_evaluate_leaf_not_NoneTV already proved in vyperTypeExprSoundnessScript.sml (lines 648-660) per episode E0046. It is consumed by assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error which now builds successfully.

### Attempts / Evidence

- `E0053` (proved, other)
  - target_path_type_Type_evaluate_leaf_not_NoneTV was added to vyperTypeExprSoundnessScript.sml in episode E0046. It builds and is consumed by the StorageVarDecl boundary theorem. -> Already proved. The lemma exists at vyperTypeExprSoundnessScript.sml:648-660 and is consumed by metis_tac in assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error line 2477. ()

### Evidence refs

- `source:semantics/prop/vyperTypeExprSoundnessScript.sml:648-660` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260513T211025Z_m5903_t001` (use `read_tool_output` for exact output)

## C3.1.7.3

### Current Status

- result: `stuck`
- diagnosis: `plan_incomplete`
- latest episode: `E0059`
- blocker: "gvs[AllCaseEqs()] after Cases_on x1 creates auto-generated variable names that prevent metis_tac/irule from matching against known lemmas. Writing a boundary lemma for the standard read+write+assign_result pattern (analogous to assign_target_TopLevelVar_Value_branch_ntr) would cleanly factor out all non-ArrayTV-Dynamic cases. AppendOp/PopOp length writes still need UintT 256 range derivation."
- next: Write boundary lemma assign_target_TopLevelVar_ArrayRef_ordinary_no_type_error for the standard read+write+assign_result path (all non-ArrayTV-Dynamic cases), modeled on assign_target_TopLevelVar_Value_branch_ntr. Then handle AppendOp/PopOp separately."

### Attempts / Evidence

- `E0054` (progressed, other)
  - Added resolve_array_element_props_local combined lemma + rewrote main theorem with Cases_on x1 then Cases_on bd then Cases_on op step-by-step approach + gvs[AllCaseEqs()] within each branch -> Combined lemma has no_type_error from API escaping /\ to /&/. Three separate single-conclusion lemmas fail because StructTV case needs combined leaf_type+well_formed IH. Main theorem proof untested. (`TO_type_system_rewrite-20260513T211025Z_m6196_t001`, `TO_type_system_rewrite-20260513T211025Z_m6198_t001`, `TO_type_system_rewrite-20260513T211025Z_m6200_t001`)
  - Tried three separate single-conclusion lemmas (leaf_type, ArrayTV_empty_rsubs, well_formed) to avoid conjunction in theorem statement -> leaf_type lemma failed at second strip_tac. well_formed lemma failed at Cases_on bd (No var bd free - StructTV recursive case leaks through TRY without leaf_type IH support). Single-conclusion form loses needed IH cross-conclusion info. (`TO_type_system_rewrite-20260513T211025Z_m6194_t001`)
  - Tried replace_text and edit_lines to write /\ to file -> API consistently escapes /\ to /&/ or /'/ regardless of tool used. Unicode ∧ also corrupted. Existing file has /\ working fine - the escaping happens in tool content parameters only. ()
- `E0055` (progressed, other)
  - Split resolve_array_element_props_local (corrupted /&/ conjunction) into three separate single-conclusion theorems: resolve_array_element_leaf_type_sc, resolve_array_element_ArrayTV_empty_rsubs_sc, resolve_array_element_well_formed_sc. Proofs use ho_match_mp_tac resolve_array_element_ind >> rw[...def...] pattern with Fixed/Dynamic subgoal dispatch via qspecl_then -> Theorems written and file edited. Old _local names replaced with _sc names. BUT: caller references at lines 2521/2523/2527 still use old _local names. Also holbuild not yet tested due to stale checkpoint issues and session ending. ()
- `E0056` (progressed, other)
  - Fixed lookup_storage_def → vfmStateTheory.lookup_storage_def static error at lines 2589/2618. Restructured proof removing all_tac>> prefix to break stale checkpoint. Simplified AppendOp/PopOp write INR branches to use metis_tac[write_storage_slot_no_type_error_from_value_has_type] directly. -> Three _sc helpers proved (resolve_array_element_leaf_type_sc, _ArrayTV_empty_rsubs_sc, _well_formed_sc). Main theorem still fails at AppendOp/PopOp dynamic array write INR subgoals - metis_tac cannot close them without value_has_type derivation for UintT 256 length value. Old proof had explicit arithmetic reasoning for integer range which was removed in simplification. (`TO_type_system_rewrite-20260513T211025Z_m6387_t001`, `TO_type_system_rewrite-20260513T211025Z_m6414_t001`, `TO_type_system_rewrite-20260513T211025Z_m6418_t001`)
- `E0057` (progressed, other)
  - Added all_tac >> before rpt strip_tac to break stale holbuild checkpoint in assign_target_TopLevelVar_ArrayRef_branch_ntr -> Checkpoint STILL matches through line 2486 despite added all_tac >>. Holbuild says 'matched proof prefix through line 2486:3' (`tool_output:TO_type_system_rewrite-20260513T211025Z_m6460_t001`)
  - Inserted FAIL_TAC probes at AppendOp write2, AppendOp write1, PopOp write2, PopOp write1 branches to inspect exact goal state after CCONTR_TAC >> gvs[] -> Probes not reached because checkpoint replays old state. Instrumented log confirms proof reaches the large lambda-case goal but the PairCases_on hasn't been applied yet in the failed fragment. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m6461_t001`)
  - Renamed theorem from assign_target_TopLevelVar_ArrayRef_branch_ntr to assign_target_TopLevelVar_ArrayRef_branch_ntr_v2 to break checkpoint by changing the theorem name key -> Not yet tested - this was the last edit before handoff ()
- `E0058` (progressed, other)
  - Inserted dummy theorem assign_target_ArrayRef_checkpoint_break between _sc helpers and main theorem to force fresh theory-context checkpoint -> Holbuild now resumes from after the _sc helpers, building the dummy theorem fresh ()
  - Renamed theorem from _ntr_v3 back to original assign_target_TopLevelVar_ArrayRef_branch_no_type_error (matching .sig reference) -> Theorem name now matches what callers expect, no dangling _v3 references ()
  - Changed proof prefix from rw[] >> fs[top_level_vtype_well_formed, top_level_Type_storage_decl] to rpt strip_tac >> explicit metis_tac subgoals >> fs[] -> fs[] still eliminates env.type_defs = get_tenv cx which breaks subsequent lemma matching per L0175. irule calls in the expanded goal fail with 'No match' ()
- `E0059` (stuck, plan_incomplete)
  - Replace all irule calls with metis_tac following Value branch pattern -> metis_tac[assign_result_no_type_error_from_successful_assign_split] fails with 'no solution found' - the goal after gvs[AllCaseEqs()] has auto-generated state names that don't match lemma antecedent pattern (`TO_type_system_rewrite-20260513T211025Z_m6607_t001`)
  - Explicit Cases_on read_storage_slot/write_storage_slot/assign_subscripts before gvs -> Same fundamental problem - gvs[AllCaseEqs()] still creates unfathomable goal state with auto-generated names (`TO_type_system_rewrite-20260513T211025Z_m6615_t001`)
  - Use rpt(FIRST[simp,metis_tac,CCONTR_TAC,drule]) after gvs -> Not yet built - latest approach that avoids positional dispatch ()
  - Insert FAIL_TAC probes to diagnose exact goal structure -> Confirmed: after Cases_on x1, gvs produces multiple subgoals with auto-named variables. The success path goal has no 'assign_subscripts = INL' assumption in the form the lemma expects (`TO_type_system_rewrite-20260513T211025Z_m6609_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260513T211025Z_m6607_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260513T211025Z_m6609_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260513T211025Z_m6615_t001` (use `read_tool_output` for exact output)

## C3.1.7.3.1

### Current Status

- result: `stuck`
- diagnosis: `wrong_statement`
- latest episode: `E0063`
- blocker: "Confirmed: assign_target_TopLevelVar_ArrayRef_ordinary_no_type_error is structurally wrong for ArrayRef. gvs[AllCaseEqs()] on case(ao,final_tv) creates 32 goals. The Cases_on op approach in _branch_no_type_error (line 2590) already works for Replace/Update. Plan oracle confirmed: neutralize this helper, prove AppendOp/PopOp dynamic boundary lemmas instead."

### Attempts / Evidence

- `E0061` (progressed, other)
  - gvs[Once assign_target_def,...,AllCaseEqs()] directly (like HashMapRef) -> Fails: AllCaseEqs expands compiled pair case, creates too many subgoals ()
  - Cases_on op then per-op gvs[AllCaseEqs()] -> Fails: same pair case explosion, predicate not true error ()
  - 2-phase: gvs outer bind, then Cases_on final_tv + gvs inner chain -> Works! gvs with type_value_CASE_rator+assign_operation_CASE_rator+well_formed_type_value_def fully decomposes all 32 goals into 4 standard patterns. But FIRST[4 alternatives] fails on contradiction goals. ()
  - FIRST with 4 monadic path alternatives after gvs expansion -> All 32 goals unsolved: contradiction goals from ArrayTV Dynamic + PopOp/AppendOp branches not handled by any of the 4 path alternatives ()
- `E0062` (stuck, wrong_statement)
  - gvs[Once assign_target_def,...,AllCaseEqs()] with exclusion hypotheses op≠PopOp/∀v.op≠AppendOp v, then FIRST[4 monadic alternatives] -> 32 goals instead of 4; FIRST fails on contradiction goals where gvs instantiated final_tv=ArrayTV Dynamic but universal exclusion ∀v. op≠AppendOp v wasn't instantiated by gvs (`tool_output:TO_type_system_rewrite-20260513T211025Z_m6966_t002`)
- `E0063` (stuck, wrong_statement)
  - gvs[Once assign_target_def,...,AllCaseEqs()] with exclusion hypotheses op!=PopOp/forall v. op!=AppendOp v, then FIRST[4 monadic alternatives] -> 32 goals instead of 4; FIRST fails on contradiction goals where universal exclusion wasn't instantiated (`tool_output:TO_type_system_rewrite-20260513T211025Z_m6966_t002`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m6966_t002` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260513T211025Z_m6953_t001` (use `read_tool_output` for exact output)

## C3.1.7.3.2

### Current Status

- result: `proved`
- diagnosis: `other`
- latest episode: `E0060`
- blocker: ""

### Attempts / Evidence

- `E0060` (proved, other)
  - Added storage_array_append_len_value_has_type and storage_array_pop_len_value_has_type local lemmas using rewrite_tac[value_has_type_def, NUM_OF_INT, INT_POS] + decide_tac/metis_tac pattern from vht_uint_bound -> Both lemmas build successfully (confirmed by checkpoint after storage_array_pop_len_value_has_type). Proof uses integerTheory.NUM_OF_INT + integerTheory.INT_POS to handle Num (&n) rewriting, with metis_tac[LESS_TRANS] for the 2^256 transitivity step that decide_tac cannot handle. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m6707_t001` (use `read_tool_output` for exact output)

## C3.2

### Current Status

- result: `progressed`
- diagnosis: `other`
- latest episode: `E0076`
- blocker: assign_target_ArrayRef_Replace_ntr_v2 and Update_ntr_v2 fail at by-subgoal referencing final_tv after AllCaseEqs expansion + stale holbuild checkpoint replay. The gvs blast pattern works for PopOp_ordinary_ntr (proven) but Replace/Update have stale checkpoints replaying old variable bindings. Must rewrite both lemmas using the PROVEN AppendOp_ordinary_ntr pattern (Cases_on final_tv BEFORE expanding assign_target_def) which produces per-constructor subgoals with concrete type names in by-subgoals, and breaks the stale checkpoint by having a different proof structure.
- next: Rewrite Replace_ntr_v2 and Update_ntr_v2 using AppendOp_ordinary_ntr pattern: Cases_on final_tv before expand, per-constructor simp+gvs[AllCaseEqs()], then 4 standard drule subgoals per constructor. This breaks stale checkpoint and avoids variable name mismatches.

### Attempts / Evidence

- `E0064` (progressed, other)
  - Cases_on get_storage_backend BEFORE expanding assign_target_def, then simp[Once assign_target_def, ..., AllCaseEqs()] resolves the monadic binds correctly for AppendOp -> AppendOp boundary lemma PROVED successfully with 4 subgoals (success, 2x write INR, check fail). Key: Cases_on before simp creates equation in assumptions that AllCaseEqs matches. (`TO_type_system_rewrite-20260513T211025Z_m7196_t001`)
  - Wrote assign_target_TopLevelVar_ArrayRef_ordinary_no_type_error boundary lemma for the _ branch (read_storage_slot + assign_subscripts + write_storage_slot + assign_result) -> Written but not yet build-tested. Uses bind_def + AllCaseEqs in one blast which should work since the _ branch has no get_storage_backend. ()
  - Rewriting _branch_no_type_error to use boundary lemmas via irule -> Identified correct structure: Cases_on op, then Cases_on resolve_array_element, then irule appropriate boundary lemma. Currently half-rewritten - file won't build. (`TO_type_system_rewrite-20260513T211025Z_m7228_t001`)
- `E0065` (progressed, other)
  - Delete broken ordinary_no_type_error lemma (AllCaseEqs destructures final_tv creating N*M goals), prove PopOp by modeling on AppendOp proof pattern: Cases_on get_storage_backend BEFORE expanding assign_target_def, then AllCaseEqs -> ordinary_no_type_error deleted successfully. PopOp proof Goals 1 and 2 now pass. Goal 3 (default_value write INR) fails because gvs[assign_operation_runtime_typed_def] renames pop_elem_tv to elem_tv', breaking metis_tac chain of default_value_has_type_thm + write_storage_slot_no_type_error_from_value_has_type ()
  - Pre-derive value_has_type pop_elem_tv (default_value pop_elem_tv) before AllCaseEqs expansion using drule evaluate_type_ArrayT_cases then drule default_value_has_type_thm -> gvs renames pop_elem_tv to elem_tv' after assign_operation_runtime_typed_def expansion, making backtick terms with pop_elem_tv not match ()
  - Goal 2 w2n < 2^256: simp[wordsTheory.w2n_lt] fails because dimword(:256) not computed to 2^256 by simp alone -> Fixed with ASSUME_TAC (INST_TYPE [...]] wordsTheory.w2n_lt) >> POP_ASSUM mp_tac >> simp[] ()
  - Goal 3 metis_tac[default_value_has_type_thm, write_storage_slot_no_type_error_from_value_has_type] -> Fails because elem_tv' != pop_elem_tv in assumption context after gvs; metis can't unify them without evaluate_type_ArrayT_cases ()
- `E0066` (progressed, other)
  - Replace qpat_x_assum callback with drule evaluate_type_ArrayT_cases in PopOp Goal 3 -> PopOp proof now passes all 5 goals. Key fix: drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] unifies elem_tv' with pop_elem_tv, then drule default_value_has_type_thm >> simp[] gives value_has_type (`tool_output:TO_type_system_rewrite-20260513T211025Z_m7380_t001`, `tool_output:TO_type_system_rewrite-20260513T211025Z_m7386_t001`)
  - Fix branch_no_type_error Replace case: change drule_all_then to metis_tac, change evaluate_type env.type_defs to get_tenv cx -> Stale holbuild checkpoint replays old gvs[AllCaseEqs()] expansion, creating 5 subgoals with huge goal state (>4KB). metis_tac times out. Need to break stale checkpoint first (insert all_tac >> or dummy local theorem before the proof). (`tool_output:TO_type_system_rewrite-20260513T211025Z_m7411_t001`)
- `E0067` (progressed, other)
  - Restructure assign_target_TopLevelVar_ArrayRef_branch_no_type_error: add all_tac >> prefix to break stale checkpoint, use evaluate_type (get_tenv cx) after fs[] rewrites, Cases_on resolve_array_element BEFORE expanding assign_target_def, use irule read_storage_slot_success_type + drule chains instead of metis_tac on >4KB goal state -> Edit made to Replace/Update cases (lines 2660-2753). AppendOp/PopOp cases (lines 2754+) still need restructuring. Not yet build-tested. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m7421_t001`)
- `E0068` (progressed, other)
  - Create assign_target_TopLevelVar_ArrayRef_ordinary_branch_ntr[local] boundary lemma for the ordinary read+assign+write+assign_result path (handles ALL type_value constructors for Replace/Update via resolve_array_element result as premise). Uses drule_all_then assume_tac read_storage_slot_success_type instead of irule read_storage_slot_success_type to avoid existential witness issues. -> Boundary lemma written and inserted into file, but conjunction syntax corrupted by API (/¥/ instead of /\). Must rewrite statement to use ==> chains. Also inserted assign_target_ArrayRef_checkpoint_break3[local] dummy theorem to break stale holbuild checkpoint. Main theorem NOT yet rewritten to use the boundary lemma. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m7446_t001`)
- `E0069` (progressed, other)
  - Replace corrupted /\ boundary lemma with two separate theorems (Replace_ntr, Update_ntr) using ==> chains, rewrite main theorem to use metis_tac[boundary_lemma] -> Boundary lemmas written and main theorem simplified from 280 to 100 lines. Build failed: assign_target_ArrayRef_Replace_ntr missing get_module_code premise. After AllCaseEqs() expansion, get_module_code = NONE subgoal has no facts to resolve. Added get_module_code premise to Replace_ntr but not yet Update_ntr. Also realized AppendOp/PopOp ordinary sub-branches in main theorem incorrectly reference Replace-specific boundary lemma. (`TO_type_system_rewrite-20260513T211025Z_m7491_t001`)
- `E0070` (progressed, other)
  - Replace two operation-specific boundary lemmas with single polymorphic assign_target_ArrayRef_ordinary_ntr -> Build fails: by-subgoals reference final_tv after AllCaseEqs substitution. AllCaseEqs substitutes final_tv -> BaseTV v11, then by-subgoal value_has_type final_tv current_val creates a FRESH final_tv that differs. Also, polymorphic op with AllCaseEqs on case(ao,final_tv) pair creates N*M subgoals. ()
  - Fix by-subgoals to avoid referencing final_tv -> Not yet implemented. The fix: use drule_all_then assume_tac read_storage_slot_success_type >> simp[] instead of by-subgoals. ()
- `E0071` (progressed, other)
  - AllCaseEqs() without Excl (PopOp pattern): gvs[Once assign_target_def,...,AllCaseEqs()] - creates big disjunction over all final_tv constructors plus ArrayTV Dynamic branches that gvs cannot reduce. Over 13 subgoals remain unsolved. -> Big disjunction over final_tv constructors created by AllCaseEqs expanding type_value_case and bound_case inside case(ao,final_tv) pair. assign_operation_distinct doesn't prevent this expansion because AllCaseEqs expands everything together. (`tool_output:TO_type_system_rewrite-20260514T195458Z_m7882_t001`)
  - AllCaseEqs()+Excl type_value_case_eq+bound_case_eq (Update_ntr pattern) WITH type_value_CASE_rator+bound_CASE_rator in simp: produced big disjunction over final_tv constructors in goal after Cases_on read_storage_slot -> type_value_CASE_rator pre-creates case final_tv of ... expression that AllCaseEqs()+Excl cannot prevent expansion of. Excl only prevents adding type_value_case_eq to simp set, but the CASE_rator already introduced the case form. (`tool_output:TO_type_system_rewrite-20260514T195458Z_m7969_t001`)
  - Cases_on final_tv BEFORE simp (AppendOp pattern): variable name clash between v:base_type from Cases_on and v:value from Replace v -> Type error: BaseTV v where v:base_type conflicts with Replace v where v:value. gvs[AllCaseEqs()] then further expands base_type creating UintT n sub-cases. (`tool_output:TO_type_system_rewrite-20260514T195458Z_m7967_t001`)
- `E0072` (progressed, other)
  - Replace_ntr: PopOp pattern full gvs[...type_value_CASE_rator, bound_CASE_rator, prod_CASE_rator, AllCaseEqs()] -> Fails: AllCaseEqs expands _ wildcard to 7 final_tv constructors creating huge disjunction. drule on 4KB goal fails. ()
  - Replace_ntr: simp without type_value_CASE_rator/bound_CASE_rator, then Cases_on monadic operations -> Fails: even without explicit CASE_rator, the pair case (ao,final_tv) produces case final_tv of 7 constructors after prod_CASE_rator or built-in pair case handling. ()
  - Replace_ntr: avoid prod_CASE_rator, use pair_case_eq + assign_operation_case_eq + assign_operation_distinct to resolve pair case to equalities -> Not yet tested. pairTheory.pair_case_eq exists (grep confirms). assign_operation_case_eq exists in vyperStateTheory. This should convert the pair case to if-then-else with equality tests that assign_operation_distinct simplifies to F, leaving just the _ wildcard body. ()
- `E0073` (progressed, other)
  - gvs blast with type_value_CASE_rator+bound_CASE_rator+AllCaseEqs() (Update_ntr pattern) -> Produces massive disjunction for Replace/Update because no exclusion premise to collapse identical-but-variably-named branches (`tool_output:TO_type_system_rewrite-20260514T195458Z_m8136_t001`)
  - Excl type_value_case_eq + bound_case_eq to prevent AllCaseEqs re-expansion -> prod_CASE_rator already creates case expressions before Excl runs; Excl cannot undo (`tool_output:TO_type_system_rewrite-20260514T195458Z_m8153_t001`)
  - Cases_on intermediate read_storage_slot/assign_subscripts results after simp expansion -> Cases_on 'q' fails because q not free in goal - it's bound inside nested case expression within implication antecedent (`tool_output:TO_type_system_rewrite-20260514T195458Z_m8171_t001`)
  - metis_tac with array_ref_ordinary_branch_success/write_error/assign_error/no_type_error helpers after Cases_on final_tv -> metis can't match because the assumption is a nested case expression, not individual function-result assumptions (`tool_output:TO_type_system_rewrite-20260514T195458Z_m8168_t001`)
- `E0074` (progressed, other)
  - Replace_ntr_v2 uses Cases_on final_tv + per-constructor mp_tac+simp+Cases_on read_storage_slot+Cases_on q -> Stale holbuild checkpoint replays wrong variable bindings for Cases_on q (q not free in replayed goal). all_tac prefix doesn't break checkpoint match. ()
  - PopOp_ordinary_ntr uses single gvs[Once assign_target_def, ..., prod_CASE_rator, AllCaseEqs()] blast producing 4 clean subgoals -> PROVED successfully. This pattern avoids Cases_on intermediate results entirely. ()
- `E0075` (progressed, other)
  - gvs[Once assign_target_def,...,AllCaseEqs()] WITHOUT assign_operation_CASE_rator or Dynamic exclusion premise -> massive disjunction on final_tv constructors (>4KB goal) -> AllCaseEqs expands pair case (ao,final_tv) into N final_tv constructors because without assign_operation_CASE_rator the case(ao,final_tv) expression isn't resolved by assign_operation_distinct (`tool_output:TO_type_system_rewrite-20260514T195458Z_m8240_t001`)
  - Added (!etv n. final_tv ≠ ArrayTV etv (Dynamic n)) premise + gvs blast -> still massive disjunction, same root cause -> Dynamic exclusion helps with PopOp-specific pair arms but doesn't prevent AllCaseEqs from expanding final_tv constructors in the _ wildcard branch (`tool_output:TO_type_system_rewrite-20260514T195458Z_m8293_t001`)
  - Cases_on intermediate results (read_storage_slot etc.) after simp without AllCaseEqs -> type errors -> Cases_on q after Cases_on read_storage_slot produces wrong variable bindings (r=state not r=value), causing type mismatch in assign_subscripts (`tool_output:TO_type_system_rewrite-20260514T195458Z_m8309_t001`)
  - Final approach: gvs[...assign_operation_CASE_rator,...AllCaseEqs()] without Dynamic exclusion -> NOT YET TESTED -> PopOp_ordinary_ntr (PROVED) includes assign_operation_CASE_rator in its simp set. Replace/Update previous attempts were missing it. This is the likely key difference. ()
- `E0076` (progressed, other)
  - gvs[Once assign_target_def,...,assign_operation_CASE_rator,...,AllCaseEqs()] blast matching PopOp_ordinary_ntr pattern -> Fails at by-subgoal with DISCH_THEN assertion - stale checkpoint replays old variable bindings for final_tv after AllCaseEqs substitution assigns final_tv -> BaseTV v11 but by-subgoal creates FRESH final_tv (`TO_type_system_rewrite-20260514T195458Z_m8323_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260514T195458Z_m8323_t001` (use `read_tool_output` for exact output)
