# DOSSIER: type_system_rewrite

PLAN: `semantics/prop/PLAN_type_system_rewrite.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C0.1 | stuck | other | E0004 | "Escalate to plan_oracle for C0 resolution: authorize type_builtin_result_ok repair for AbiEncode branch, adding vyper_abi_size_bound condition" |
| C1 | progressed | plan_incomplete | E0005 | Escalate to plan_oracle: C1 needs decomposition into subcomponents for (1) the vyper_to_abi success lemma and (2) the enc-length-bound lemma, before the 3 success-typing branches are provable. |
| C2.1.a | progressed | other | E0001 | Progress to C2.1.b (HashMapRef proof) or C2.1.c (ArrayRef proof), or C2.2.a (ImmutableVar proof) using the probe evidence |
| C3.1 | progressed | missing_helper | E0022 | Build-verify subgoal 1 (LENGTH xs = LENGTH is - 1 via Cases_on is >> gvs[LENGTH_REVERSE], then gvs[] closure). Then fix subgoal 2: replace FAIL_TAC probe with actual write_storage_slot/assign_result/assign_subscripts dispatch. |

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
- latest episode: `E0022`
- blocker: "HashMapRef branch subgoal 1 (compute_hashmap_slot NONE): `x' = LAST is` bridge now works via HD_REVERSE_EQ_LAST + gvs variable elimination. Remaining: derive `LENGTH xs = LENGTH is - 1` (from REVERSE is = LAST is::xs + LENGTH_REVERSE via Cases_on is >> gvs[LENGTH_REVERSE]), then gvs[] should close via contradiction with compute_hashmap_slot NONE vs ≠ NONE. After subgoal 1, subgoals 2-4 need handling: (2) write_storage_slot/assign_result do-block (FAIL_TAC probe currently), (3) read_storage_slot TypeError via drule read_storage_slot_error, (4) assign_subscripts TypeError via drule_all assign_subscripts_no_type_error_runtime_typed."
- next: Build-verify subgoal 1 (LENGTH xs = LENGTH is - 1 via Cases_on is >> gvs[LENGTH_REVERSE], then gvs[] closure). Then fix subgoal 2: replace FAIL_TAC probe with actual write_storage_slot/assign_result/assign_subscripts dispatch.

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

### Evidence refs

- `TO_type_system_rewrite-20260514T090000Z_m2878_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260514T090000Z_m2860_t001` (use `read_tool_output` for exact output)
