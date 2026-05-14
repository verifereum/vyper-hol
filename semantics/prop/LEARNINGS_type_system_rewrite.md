# LEARNINGS_type_system_rewrite

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='' tags=
shape: HOL4 monadic definitions transformed by SRULE [bind_def, FUN_EQ_THM, option_CASE_rator, etc.]
pattern: SRULE-transformed monadic definitions (from cv_auto_trans) may not fully reduce with simp[]. Use Cases_on the monadic result pairs instead of trying to simp through the SRULE form. Model on existing working proofs in the same theory (e.g., vyperLookupStorageScopesScript.sml).
works_when: Proving independence/irrelevance of a context field (like cx.stk or st.scopes) from a monadic function
evidence:
- source:semantics/prop/vyperLookupStorageScopesScript.sml:90-125
- tool_output:TO_type_system_rewrite-20260513T175918Z_m0051_t001
- tool_output:TO_type_system_rewrite-20260513T175918Z_m0070_t001

## L0002 scope='' tags=
shape: ADT constructors in HOL4 Theorem proofs
pattern: For var_decl_info and similar ADTs, use Cases_on not PairCases_on. PairCases_on only works for product types. Use PairCases_on only after confirming the type is a pair/prod.
works_when: Case-splitting on HOL4 algebraic data type constructors
evidence:
- tool_output:TO_type_system_rewrite-20260513T175918Z_m0070_t001 - PairCases_on failed on var_decl_info type

## L0003 scope='' tags=
shape: HOL4 monadic record update independence proof
pattern: When proving f (cx with field := val) = f cx for monadic f, add quantified subgoals for sub-functions using cx fields (e.g. get_storage_backend for all st'), rather than unfolding everything. Model on vyperLookupStorageScopesScript.sml.
works_when: Proving cx-field independence for monadic functions
evidence:
- tool_output:TO_type_system_rewrite-20260513T175918Z_m0118_t001
- source:semantics/prop/vyperLookupStorageScopesScript.sml:90-125

## L0004 scope='' tags=
shape: well_typed_expr implies well_formed_type
pattern: well_typed_expr env e includes well_formed_type env.type_defs (expr_type e) for most constructors but not all (Name). Prove a general helper lemma well_typed_expr_implies_well_formed_type once, use everywhere needing evaluate_type != NONE.
works_when: Deriving evaluate_type != NONE from well_typed_expr in statement soundness branches
evidence:
- tool_output:TO_type_system_rewrite-20260513T185020Z_m0174_t001
- source:semantics/prop/vyperTypeSystemScript.sml:453-510

## L0005 scope='' tags=
shape: assignable_type_not_NoneT for expr_type != NoneT
pattern: assignable_type tenv ty ==> ty <> NoneT. Use metis_tac[assignable_type_not_NoneT]. Combined with evaluate_type_not_NoneT_imp_not_NoneTV gives assignable_type_evaluate_not_NoneTV.
works_when: Proving non-NoneT side condition for assignable types
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:243-247

## L0006 scope='' tags=
shape: assignable_type tenv ty ==> well_formed_type tenv ty
pattern: recInduct assignable_type_ind >> rw[assignable_type_def, well_formed_type_def] >> Cases_on `FLOOKUP tenv (string_to_num id)` >> gvs[] >> Cases_on `x` >> gvs[]
works_when: Teniv is env.type_defs, ty is expr_type e, assignable_type comes from type_stmt hypothesis
evidence:
- tool_output:TO_type_system_rewrite-20260513T185020Z_m0247_t001
- tool_output:TO_type_system_rewrite-20260513T185020Z_m0248_t001

## L0007 scope='' tags=
shape: assign_operation_matches_target_shape for BaseTargetV
pattern: assign_operation_matches_target_shape (BaseTargetV loc sbs) op = T (trivially true from definition). Use simp[assign_operation_matches_target_shape_def] or irule assign_operation_matches_target_shape_BaseTargetV.
works_when: Proving the shape side condition for non-tuple assignment targets (Replace, Update, AppendOp, PopOp on BaseTargetV)
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:886-894 - definition showing BaseTargetV case is T
- tool_output:TO_type_system_rewrite-20260513T185020Z_m0406_t001 - build confirms lemma compiles clean in vyperTypeAssignSoundnessTheory

## L0010 scope='' tags=
shape: ABI encode result typing requires vyper_abi_size_bound lower bound (C1)
pattern: type_builtin_result_ok for AbiEncode must require n >= vyper_abi_size_bound tenv target_ty where n is the BytesT(Dynamic n) bound. C0.1 probes confirmed: vyper_abi_size_bound FEMPTY (TupleT [BaseT (UintT 256)]) = 32 and enc of Uint 256 is 32 bytes, but old predicate accepted n=1 making success-typing theorem FALSE.
works_when: Proving ABI encode success-typing; updating type_builtin_result_ok for AbiEncode
evidence:
- tool_output:TO_type_system_rewrite-20260513T204155Z_m0746_t001

## L0012 scope='' tags=
shape: ABI encode success typing needs two missing lemmas (C1)
pattern: To prove well_typed_type_builtin_success_type for AbiEncode/encode_tuple/encode_tuple_nowrap, need: (1) value_has_type tv v ∧ evaluate_type tenv typ = SOME tv ⇒ ∃av. vyper_to_abi tenv typ v = SOME av, and (2) vyper_to_abi tenv typ v = SOME av ⇒ LENGTH (enc (vyper_to_abi_type tenv typ) av) ≤ vyper_abi_size_bound tenv typ. contractABITheory has LENGTH_enc_number and head_lengths_leq_LENGTH_enc_tuple.
works_when: Proving ABI encode success-typing branches after type_builtin_result_ok repair
evidence:
- episode:E0005

## L0013 scope='' tags=
shape: HOL4 Definition with numeric comparison on RHS
pattern: Extract numeric comparisons (<=, >=, <) into separate helper Definitions before using in main Definition. HOL4 Definition parser treats '=' specially and confuses nearby comparisons.
works_when: Defining predicates with numeric bounds in HOL4 Definition blocks
evidence:
- episode:E0005

## L0014 scope='' tags=
shape: assign_target_sound_mutual hypotheses provide get_module_code for TopLevelVar
pattern: In assign_target_sound_mutual, the assign_target_assignable_context hypothesis for TopLevelVar already provides get_module_code cx src = SOME code and find_var_decl_by_num witnesses. The evaluator's lift_option_type bind also extracts get_module_code. Do NOT claim get_module_code is unavailable for C3 branches - it's a C5 concern (deriving it from target_runtime_typed), not a C3 concern (using it as a hypothesis).
works_when: Proving TopLevelVar branches of assign_target_sound_mutual (both no_type_error and preservation)
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m0903_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:909-926
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1760-1777

## L0016 scope='' tags=
shape: lookup_global HashMapRef connects to env.toplevel_vtypes HashMapT
pattern: When lookup_global returns INL (HashMapRef is_t bs kt vt), runtime_consistent env cx st + FLOOKUP env.toplevel_vtypes (src,n) = SOME vt_loc, then vt_loc = HashMapT kt vt. Key lemmas: lookup_global_HashMapRef_imp_HashMapVarDecl (lookup_global returning HashMapRef implies find_var_decl_by_num returns HashMapVarDecl with matching types), then use top_level_Type_not_hashmap_decl to rule out Type case, giving HashMapT.
works_when: Proving typing environment consistency for TopLevelVar HashMapRef branches in assign_target_sound_mutual and similar theorems
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1768-1792
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1223-1232 (top_level_Type_not_hashmap_decl)

## L0017 scope='' tags=
shape: TopLevelVar branch proof pattern in assign_target_sound_mutual
pattern: For TopLevelVar cases: (1) drule_at Any lookup_global_success_get_module_code to extract get_module_code from lookup_global result. (2) Use assign_target_assignable_context_def to pull out IS_SOME witnesses for evaluate_type and lookup_var_slot_from_layout. (3) gvs[bind_apply, AllCaseEqs()] to step through monadic evaluator do-block. (4) For INR TypeError cases: use specialized no-TypeError lemmas (top_level_storage_value_assign_subscripts_no_type_error, write_storage_slot_no_type_error_from_value_has_type). (5) For INL success cases: assign_result_no_type_error_from_successful_assign.
works_when: Proving no_type_error_result for TopLevelVar branches (Value, HashMapRef, ArrayRef) in assign_target_sound_mutual
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1888-1927 (working Value branch proof)
- tool_output:TO_type_system_rewrite-20260513T211025Z_m0903_t001 (HashMapRef goal state)

## L0018 scope='' tags=
shape: lookup_global result implies var_decl_info constructor (Value vs HashMapRef)
pattern: When lookup_global returns Value v, FST p cannot be HashMapVarDecl (use lookup_global_Value_not_HashMapVarDecl). Symmetrically, when lookup_global returns HashMapRef, FST p cannot be StorageVarDecl. Proof: Cases_on p >> Cases_on the var_decl_info, then mp_tac the lookup_global equation, simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def, option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator, toplevel_value_CASE_rator, type_value_CASE_rator, AllCaseEqs()] >> rpt strip_tac >> gvs[]. The key addition is AllCaseEqs() which resolves the nested type_value and toplevel_value case splits that rw/gvs alone cannot.
works_when: Proving that a lookup_global result shape constrains the find_var_decl_by_num var_decl_info constructor
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1137_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1262-1273
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1906-1914

## L0019 scope='' tags=
shape: place_leaf_path_typed to split_hashmap_subscripts success
pattern: ho_match_mp_tac place_leaf_path_typed_ind >> rw[] >> gvs[place_leaf_path_typed_def, split_hashmap_subscripts_def] >> Cases_on `split_hashmap_subscripts vt path` >> gvs[] >> PairCases_on `x` >> gvs[]
works_when: Proving split_hashmap_subscripts vt path <> NONE from place_leaf_path_typed env vt path ty final_tv. The induction aligns place_leaf_path_typed and split_hashmap_subscripts recursion on HashMapT vt.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1268_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1272_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1270_t001
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:295-297
- source:semantics/vyperStateScript.sml:488-495
- source:semantics/prop/vyperTypeSystemScript.sml:287-291

## L0020 scope='' tags=
shape: Cases_on vt with >- to separate Type vs HashMapT cases when using drule_all
pattern: Cases_on `vt` >> gvs[] >- (drule_all top_level_Type_not_hashmap_decl >> strip_tac >> gvs[]) >> (* HashMapT case *) drule_all top_level_HashMap_decl >> strip_tac >> gvs[var_decl_info_11]
works_when: Proving vt = HashMapT t v from FLOOKUP env.toplevel_vtypes = SOME vt + find_var_decl_by_num = SOME (HashMapVarDecl ...). The Type case is contradictory (top_level_Type_not_hashmap_decl), the HashMapT case follows from top_level_HashMap_decl + injectivity.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1190_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1920-1926

## L0021 scope='' tags=
shape: well_formed_vtype (HashMapT kt vt) implies well_formed_vtype vt
pattern: From well_formed_vtype_def: well_formed_vtype tenv (HashMapT kt vt) = well_formed_type tenv kt /\ hashmap_key_type kt /\ well_formed_vtype tenv vt. So well_formed_vtype tenv (HashMapT kt vt) imp well_formed_vtype tenv vt via gvs[well_formed_vtype_def].
works_when: Need to derive well_formed_vtype for the value type component of a HashMapT declaration, e.g. to apply target_path_type_Type_place_leaf_typed on the inner vt after stripping a subscript.
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:287-291

## L0022 scope='' tags=
shape: target_path_type on HashMapT implies split_hashmap_subscripts on inner vt succeeds
pattern: Prove target_path_type_HashMapT_split_hashmap_subscripts: well_formed_vtype env.type_defs (HashMapT kt vt) + target_path_type env (HashMapT kt vt) sbs (Type ty) ==> split_hashmap_subscripts vt (TL (REVERSE sbs)) <> NONE. Proof: target_path_type_Type_place_leaf_typed gives place_leaf_typed, unfold place_leaf_typed_def then Cases_on REVERSE sbs to expand place_leaf_path_typed_def HashMapT case, then place_leaf_path_typed_imp_split_hashmap_subscripts.
works_when: Need to derive split_hashmap_subscripts success for the hashmap value type after stripping one subscript level
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1778-1791
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:295-297
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:621-629

## L0023 scope='' tags=
shape: well_formed_vtype from location_runtime_typed for TopLevelVar
pattern: To derive well_formed_vtype env.type_defs vt when location_runtime_typed uses FLOOKUP env.toplevel_vtypes: first construct location_runtime_typed by simp[location_runtime_typed_def] >> gvs[], then irule location_runtime_typed_well_formed_vtype >> goal_assum drule_all. Do NOT use irule first then try to case-split the free loc variable.
works_when: Deriving well_formed_vtype for top-level types in branch proofs where FLOOKUP env.toplevel_vtypes is already in assumptions
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:467-483
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1954-1959

## L0024 scope='' tags=
shape: split_hashmap_subscripts induction
pattern: Use Induct_on value_type instead of ho_match_mp_tac split_hashmap_subscripts_ind for lemmas about split_hashmap_subscripts. The function's induction principle has type variable conflicts with value_type. After Induct_on vt, use rw[split_hashmap_subscripts_def], Cases_on subs for HashMapT case, then Cases_on split result + PairCases_on.
works_when: Proving properties of split_hashmap_subscripts by induction on the value_type argument
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1574_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1593_t001

## L0025 scope='' tags=
shape: compute_hashmap_slot success from ValueSubscript list
pattern: compute_hashmap_slot slot kts ks <> NONE when LENGTH kts = LENGTH ks and EVERY ((<>) NONE o subscript_to_value) ks. Proof: Induct_on kts >> Cases_on ks, gvs compute_hashmap_slot_def, Cases_on subscript_to_value h, irule IH.
works_when: Proving compute_hashmap_slot succeeds when all subscripts are ValueSubscripts with matching key count
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1590_t001

## L0026 scope='' tags=
shape: well_formed_vtype through split_hashmap_subscripts
pattern: well_formed_vtype tenv vt + split_hashmap_subscripts vt subs = SOME (final_type, kts, remaining) implies well_formed_type tenv final_type. Proof: Induct_on vt >> rw split_hashmap_subscripts_def. Type case is direct from well_formed_vtype_def. HashMapT case: Cases_on subs (vacuous for []), Cases_on split result, PairCases_on, drule IH.
works_when: Deriving evaluate_type success for the final type in a hashmap assignment target path
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1588_t001

## L0027 scope='' tags=
shape: split_hashmap_subscripts lemmas by induction on value_type
pattern: Use Induct_on `vt` >- rw[split_hashmap_subscripts_def] >> rw[split_hashmap_subscripts_def] >> Cases_on `subs` >> ... for lemmas about split_hashmap_subscripts. The function's induction principle has type variable conflicts. After Induct_on vt, the Type case solves by rw, and the HashMapT case needs Cases_on subs then Cases_on the recursive split result + PairCases_on.
works_when: Proving properties of split_hashmap_subscripts by induction on the value_type argument
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1695_t001
- episode:E0009

## L0028 scope='' tags=
shape: HashMapRef branch do-block expansion in assign_target proofs
pattern: Do NOT use CCONTR_TAC or try to reference bound variables inside the monadic do-block. Instead: (1) prove all needed helper lemmas BEFORE the branch expansion using only free variables from the branch context, (2) expand the do-block step-by-step with gvs[bind_apply, AllCaseEqs(), lift_option_type_def, return_def, raise_def], (3) rely on AllCaseEqs to eliminate NONE/TypeError branches when helper facts + assumptions contradict them.
works_when: Proving no_type_error_result for the HashMapRef branch of assign_target
evidence:
- episode:E0007
- episode:E0009

## L0029 scope='' tags=
shape: HashMapT level subscripts are ValueSubscript but not ALL subscripts
pattern: target_path_step_type_HashMapT_ValueSubscript: at HashMapT level forces ValueSubscript. But paths through StructT levels have AttrSubscript where subscript_to_value = NONE. So EVERY subscript_to_value (REVERSE sbs) is FALSE in general. Only the hashmap-prefix subscripts (determined by split_hashmap_subscripts key_types length) are guaranteed ValueSubscript.
works_when: Proving subscript_to_value properties for HashMapT-level subscripts in assignment target paths
evidence:
- episode:E0009

## L0030 scope='' tags=
shape: split_hashmap_subscripts_some_imp length fact
pattern: split_hashmap_subscripts vt subs = SOME (final_type, kts, remaining) ==> LENGTH kts + LENGTH remaining = LENGTH subs. This gives the length agreement needed for compute_hashmap_slot: the hashmap prefix has LENGTH kts + 1 subscripts.
works_when: Deriving length facts for compute_hashmap_slot argument agreement in HashMapRef branch proofs
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1695_t001

## L0031 scope='' tags=
shape: target_path_type decomposition on HashMapT
pattern: target_path_type_HashMapT_last_step: target_path_type env (HashMapT kt vt) sbs final_vt with sbs <> [] ==> target_path_step_type env (HashMapT kt vt) (LAST sbs) vt. target_path_type_HashMapT_front_path: target_path_type env (HashMapT kt vt) sbs final_vt with sbs <> [] ==> target_path_type env vt (FRONT sbs) final_vt. The LAST element corresponds to the first (root) step; FRONT is the remainder.
works_when: Decomposing target_path_type on HashMapT to extract root-level step and remaining path. LAST sbs is always ValueSubscript at HashMapT root level.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1830-1852
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:262-288

## L0032 scope='' tags=
shape: HashMapRef evaluator computes hashmap key subscripts as prefix of REVERSE is
pattern: In the HashMapRef branch, the evaluator does: REVERSE is split into first_sub + rest_subs, then split_hashmap_subscripts vt rest_subs, then hashmap_subs = first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining_subs) rest_subs. This prefix contains exactly the subscripts at HashMapT levels, which are all ValueSubscript. The suffix may contain AttrSubscript at StructT levels.
works_when: Proving compute_hashmap_slot success for HashMapRef assignment branches. Need: (1) length agreement from split_hashmap_subscripts_some_imp, (2) EVERY subscript_to_value on hashmap_subs via target_path_type_HashMapT_hashmap_prefix_ValueSubscript.
evidence:
- source:semantics/vyperStateScript.sml:888-905
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1854-1901

## L0033 scope='' tags=
shape: target_path_type list ordering convention
pattern: In target_path_type env loc_vt (sb::sbs) final_vt, sbs are processed recursively first (inner steps closer to root), then sb is applied last (outer step closer to leaf). So the LAST element of the list corresponds to the FIRST step from the root type loc_vt. REVERSE gives root-to-leaf order matching the evaluator.
works_when: Any proof relating target_path_type to evaluator REVERSE ordering, especially HashMapRef/ArrayRef branches.
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:283-288

## L0034 scope='' tags=
shape: target_path_step_type on HashMapT forces next_vt = vt
pattern: target_path_step_type_HashMapT_next_vt: target_path_step_type env (HashMapT kt vt) sb next_vt ==> next_vt = vt. Proved by Cases_on sb >> rw[target_path_step_type_def]. Use this to simplify target_path_type decomposition on HashMapT: the step goes from HashMapT kt vt to exactly vt.
works_when: Decomposing target_path_type on HashMapT into LAST step + FRONT path; needed by last_step and front_path lemmas
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1810_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1812-1818
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:262-268

## L0035 scope='' tags=
shape: target_path_type on HashMapT decomposition into LAST step + FRONT path
pattern: target_path_type_HashMapT_last_step: target_path_type env (HashMapT kt vt) sbs final_vt with sbs <> [] ==> target_path_step_type env (HashMapT kt vt) (LAST sbs) vt. Proved by Induct_on sbs + gen_tac + strip_tac + gvs/Cases_on sbs + drule target_path_step_type_HashMapT_next_vt + fs. Similarly target_path_type_HashMapT_front_path: sbs <> [] ==> target_path_type env vt (FRONT sbs) final_vt. Proved by Induct_on sbs + gen_tac + strip_tac + gvs/Cases_on sbs + drule last_step/next_vt + metis_tac[target_path_type_def].
works_when: Decomposing a target_path_type assumption on HashMapT to extract the outermost step (LAST sbs) and inner path (FRONT sbs), matching evaluator's root-to-leaf order
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1810_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1830-1869

## L0036 scope='' tags=
shape: Induct_on sbs variable naming for target_path_type/step_type lemmas
pattern: After Induct_on `sbs`, the induction step introduces h (head) and uses sbs for the tail. Do NOT use Cases_on `t` or `t'` which will conflict with HOL4 type variables or unexpected names. Use Cases_on `sbs` after the initial gen_tac+strip_tac to further destruct the tail when needed, and rename with rename1 to avoid collisions with type-level variables (especially `t` from HashMapT t vt).
works_when: Proving target_path_type/step_type structural lemmas by list induction where variable names may collide with Vyper type variables (t, t')
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1810_t001

## L0037 scope='' tags=
shape: Proving list decomposition identities involving LAST/FRONT/TL/REVERSE
pattern: Use SNOC_LAST_FRONT + REVERSE_SNOC instead of manual FRONT_DEF/LAST_DEF/TL_DEF case splits. Key identity: sbs ≠ [] ⟹ sbs = SNOC (LAST sbs) (FRONT sbs) (SNOC_LAST_FRONT); REVERSE (SNOC x l) = x :: REVERSE l (REVERSE_SNOC); TL (LAST sbs :: REVERSE (FRONT sbs)) = REVERSE (FRONT sbs). Clean 2-step decomposition without Cases_on REVERSE.
works_when: Need to decompose REVERSE sbs into (LAST sbs, REVERSE (FRONT sbs)) or TL (REVERSE sbs) = REVERSE (FRONT sbs). Also for recursive FRONT (FRONT sbs).
evidence:
- episode:E0011

## L0038 scope='' tags=
shape: completeInduct_on variable shadowing when induction variable is universally quantified in the theorem
pattern: completeInduct_on `LENGTH sbs` on a variable under ∀ in the theorem adds its own ∀sbs wrapper. After rpt strip_tac, theorem's sbs becomes sbs'. Tactics referencing sbs operate on the completeInduct variable. AVOID: use Induct_on a datatype variable or restructure proof instead.
works_when: Theorem has universally quantified list variable where you want to induct on LENGTH
evidence:
- episode:E0011

## L0039 scope='' tags=
shape: List identity: l <> [] ==> TL (REVERSE l) = REVERSE (FRONT l)
pattern: Prove SNOC_LAST_FRONT_eq (!l. l <> [] ==> l = SNOC (LAST l) (FRONT l)) and REVERSE_SNOC_eq (!x xs. REVERSE (SNOC x xs) = x :: REVERSE xs) as local lemmas. Then use: qsuff_tac `REVERSE l = LAST l :: REVERSE (FRONT l)` >- simp[] >> metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq]. The qsuff_tac + metis_tac pattern avoids circular substitution issues.
works_when: HOL4 theories where SNOC_LAST_FRONT/REVERSE_SNOC are not available (not in standard list/rich_list lib)
evidence:
- episode:E0011

## L0040 scope='' tags=
shape: NONE/SOME contradiction from conditional definition inside assumption
pattern: When gvs[def] can't rewrite inside an implication antecedent, derive the rewritten equation as an explicit assumption first: `eq' = ...` by (qpat_x_assum `eq = ...` mp_tac >> simp[helper_lemma]). Then Cases_on the inner result, and for NONE case use Cases_on the list argument >> gvs[def] to get the NONE = SOME contradiction.
works_when: Proving contradiction from split_hashmap_subscripts or similar conditional pattern-matching definitions where the equation is in assumptions but needs rewriting with side conditions
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2096_t001
- episode:E0012

## L0041 scope='' tags=
shape: Monadic do-block (od) type-soundness proof with gvs expansion
pattern: For proving no-TypeError in monadic do-blocks: (1) Derive ALL typing/option-success facts as standalone subgoals BEFORE any gvs expansion. (2) Only then do gvs[bind_apply,AllCaseEqs(),lift_option_type_def,return_def,raise_def]. (3) If variables are bound inside the monad, use Cases_on/strip_tac in a by-subgoal to extract them into assumptions first. Don't derive facts about monad-bound variables after partial expansion.
works_when: Proving no-type-error result for evaluator/assign_target do-blocks where TypeError comes from NONE cases in bind chains
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2112_t001
- episode:E0007

## L0042 scope='' tags=
shape: place_leaf_path_typed through split_hashmap_subscripts to leaf_type
pattern: place_leaf_path_typed_split_leaf_type: place_leaf_path_typed env vt path ty final_tv + split_hashmap_subscripts vt path = SOME (final_type, kts, remaining) ==> ?base_tv. evaluate_type env.type_defs final_type = SOME base_tv AND final_tv = leaf_type base_tv remaining. Proof: Induct_on vt with Cases_on split result + PairCases_on. For Type case, direct from place_leaf_path_typed_def. For HashMapT case, recursive call.
works_when: Deriving evaluate_type <> NONE and leaf_type alignment for the final_type in HashMapRef assign_target branch after split_hashmap_subscripts succeeds
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1997-2018
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:290-298
- source:semantics/vyperStateScript.sml:488-495
- episode:E0013

## L0043 scope='' tags=
shape: Monadic do-block no-TypeError proof: derive all facts before gvs expansion
pattern: For proving no_TypeError in monadic do-blocks: derive ALL typing/option-success facts as standalone subgoals BEFORE any gvs expansion. Only then do gvs[bind_apply,AllCaseEqs(),lift_option_type_def,return_def,raise_def]. The AllCaseEqs() should eliminate all None/TypeError branches because the derived facts contradict them. Do NOT try to derive facts about monad-bound variables after partial expansion.
works_when: Proving no_type_error_result for evaluator/assign_target do-blocks where TypeError comes from NONE cases in bind chains
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2112_t001
- episode:E0007
- episode:E0012
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2042-2083 - ScopedVar branch working proof pattern as model

## L0044 scope='' tags=
shape: compute_hashmap_slot LENGTH alignment from split_hashmap_subscripts_some_imp
pattern: compute_hashmap_slot slot (kt :: kts) (first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining_subs) rest_subs) <> NONE when: (1) subscript_to_value first_sub <> NONE (from target_path_step_type_HashMapT_ValueSubscript on LAST sbs), (2) EVERY ((<>) NONE o subscript_to_value) (TAKE (LENGTH kts) rest_subs) (from target_path_type_HashMapT_hashmap_prefix_ValueSubscript), (3) LENGTH kts + 1 = LENGTH (first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining_subs) rest_subs) (arithmetic from split_hashmap_subscripts_some_imp: LENGTH kts + LENGTH remaining = LENGTH rest_subs, so LENGTH kts + 1 = 1 + LENGTH rest_subs - LENGTH remaining = LENGTH hashmap_subs). Then irule compute_hashmap_slot_subscripts_to_values.
works_when: Proving compute_hashmap_slot <> NONE for HashMapRef assignment branch
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1778-1788 - compute_hashmap_slot_subscripts_to_values
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1790-1802 - split_hashmap_subscripts_some_imp
- source:semantics/vyperStateScript.sml:888-905 - evaluator HashMapRef branch showing hashmap_subs construction
- episode:E0013

## L0045 scope='' tags=
shape: place_leaf_path_typed through split_hashmap_subscripts to leaf_type and evaluate_type
pattern: place_leaf_path_typed_split_leaf_type: place_leaf_path_typed env vt path ty final_tv + split_hashmap_subscripts vt path = SOME (final_type, key_types, remaining) implies exists base_tv where evaluate_type env.type_defs final_type = SOME base_tv and final_tv = leaf_type base_tv remaining and evaluate_type env.type_defs ty = SOME final_tv. Proof: Induct_on vt then Cases_on path to split Type vs HashMapT cases, then Cases_on split result + PairCases_on for recursive case, then drule_all for IH.
works_when: Deriving evaluate_type <> NONE and leaf_type alignment for the final_type in HashMapRef assign_target branch after split_hashmap_subscripts succeeds
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1997-2018
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2231_t001
- episode:E0014

## L0048 scope='' tags=
shape: well_formed_type => evaluate_type <> NONE
pattern: Cases_on `evaluate_type tenv ty` >> gvs[well_formed_type_def]. NONE case: IS_SOME NONE = F contradicts well_formed_type assumption. SOME case: evaluate_type tenv ty <> NONE trivially. Do NOT use simp/metis - they cannot connect IS_SOME assumption to <> NONE goal.
works_when: Deriving evaluate_type <> NONE from well_formed_type assumption
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2393_t001
- episode:E0016

## L0049 scope='' tags=
shape: Monadic do-block in assumption cannot be expanded by gvs[bind_apply, AllCaseEqs()]
pattern: When a monadic do-block (from assign_target_def, evaluate_def, etc.) appears as an ASSUMPTION equation, gvs[bind_apply, AllCaseEqs(), lift_option_type_def, ...] will NOT expand it. Instead: (1) create a standalone boundary lemma where the equation is the conclusion, then simp can expand it; or (2) push the assumption to the goal with mp_tac first, then simp[bind_def, lift_option_type_def, ...] on the goal. NEVER try gvs expansion on assumed do-blocks.
works_when: Proving no-TypeError or preservation for a monadic do-block branch where the do-block result is already in assumptions from a prior case split
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2428_t001
- episode:E0007
- episode:E0012
- episode:E0017
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2112-2176 - boundary lemma approach

## L0051 scope='' tags=
shape: drule/irule failing for lemma with env.type_defs when hypothesis has (get_tenv cx)
pattern: When env.type_defs = get_tenv cx is in assumptions but a lemma antecedent uses env.type_defs directly, drule/irule fails because (get_tenv cx) and env.type_defs are syntactically different. Use metis_tac which handles unification through equality. Or explicitly derive well_formed_vtype env.type_defs (HashMapT kt vt) by fs[] first, then drule works on the env.type_defs form.
works_when: Applying typing lemmas (target_path_type_HashMapT_split_hashmap_subscripts, etc.) when runtime_consistent provides env.type_defs = get_tenv cx
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2620_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2632_t001
- episode:E0019

## L0052 scope='' tags=
shape: Existential extraction from option pair/triple result in by-subgoal
pattern: When proving ?x y z. f a = SOME (x,y,z) from f a <> NONE: use Cases_on `f a` >> gvs[] instead of IS_SOME_EXISTS + qexistsl. NONE case contradicts <> NONE assumption. SOME case gives the result directly. Then PairCases_on the pair to extract components if needed. Do NOT use IS_SOME_EXISTS + qexistsl[FST x', FST(SND x'), SND(SND x')] which has fragile type decomposition.
works_when: Extracting components from option-wrapped pair/triple results where <> NONE assumption is available
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2632_t001
- episode:E0019
- episode:E0015

## L0053 scope='' tags=
shape: Monadic do-block no-TypeError proof: case-split on lookup result before expanding body
pattern: When proving no_TypeError for assign_target TopLevelVar branch: (1) Case-split on lookup_global cx src n st result FIRST, getting INR/INL(Value)/INL(HashMapRef)/INL(ArrayRef) subgoals. (2) Contradict INR/Value/ArrayRef cases. (3) Only expand the HashMapRef do-block for the HashMapRef subgoal, using pre-derived typing facts for each TypeError step. Do NOT use AllCaseEqs on the full assign_target body before case-splitting.
works_when: Proving no_type_error_result for TopLevelVar branches where lookup_global determines the tv constructor
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2721_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2708_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2714_t001
- episode:E0019
- episode:E0018
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1262-1274 - lookup_global_Value_not_HashMapVarDecl
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1276-1288 - lookup_global_ArrayRef_not_HashMapVarDecl
- source:semantics/vyperStateScript.sml:413-439 - lookup_global_def showing HashMapVarDecl+slot returns HashMapRef
- source:semantics/vyperStateScript.sml:863-939 - assign_target_def showing tv <- lookup_global bind

## L0054 scope='' tags=
shape: lookup_global ArrayRef contradicts HashMapVarDecl hypothesis
pattern: When lookup_global returns INL(ArrayRef is_t bs etv ebd) but find_var_decl_by_num returns SOME(HashMapVarDecl...), the result is F. Proved via rw[lookup_global_def, bind_def, etc.] >> gvs[AllCaseEqs(), var_decl_info_CASE_rator, type_value_CASE_rator] >> Cases_on lookup_var_slot_from_layout. Symmetric to lookup_global_Value_not_HashMapVarDecl.
works_when: Proving contradiction when lookup_global result shape doesn't match the declaration type
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1276-1288 - lookup_global_ArrayRef_not_HashMapVarDecl lemma

## L0055 scope='' tags=
shape: lookup_global with HashMapVarDecl declaration returns HashMapRef toplevel_value
pattern: lookup_global_HashMapVarDecl_returns_HashMapRef: get_module_code cx src = SOME code => find_var_decl_by_num n code = SOME (HashMapVarDecl is_t kt vt, id) => lookup_var_slot_from_layout cx is_t src id = SOME slot => lookup_global cx src n st = (INL (HashMapRef is_t (n2w slot) kt vt), st). Proof: rw[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs(), var_decl_info_CASE_rator, prod_CASE_rator, option_CASE_rator, type_value_CASE_rator, LET_THM] >> gvs[].
works_when: Proving that lookup_global returns a HashMapRef when the declaration is HashMapVarDecl. Used to eliminate Value/ArrayRef/INR branches in assign_target no-TypeError proofs for TopLevelVar HashMapRef.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2125-2135
- episode:E0020
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2763_t001

## L0056 scope='' tags=
shape: AllCaseEqs blast on assign_target TopLevelVar do-block + Cases_on v resolves branches
pattern: For proving no_type_error_result of assign_target TopLevelVar: (1) Pre-derive ALL typing facts (split_hashmap_subscripts, compute_hashmap_slot, evaluate_type success, well_formed_type). (2) Derive lookup_global result via lookup_global_HashMapVarDecl_returns_HashMapRef. (3) rw[no_type_error_result_def] >> CCONTR_TAC >> gvs[] >> push assign_target equation to goal >> simp[Once assign_target_def + full AllCaseEqs blast] >> rpt strip_tac >> gvs[]. (4) Cases_on `v` >> gvs[] - gvs auto-resolves v from lookup_global assumption. INR case: gvs[] resolves s''=st. INL case: already in the right toplevel_value branch (HashMapRef if that's the declared type). (5) Expand remaining binds in goal position, dispatch TypeErrors.
works_when: Proving no_type_error_result for TopLevelVar branches of assign_target where lookup_global determines the toplevel_value constructor
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2773_t001
- episode:E0020

## L0057 scope='' tags=
shape: gvs expansion of monadic do-block in assumptions after case split
pattern: When a monadic do-block result is in assumptions (from prior gvs[def, bind_apply, AllCaseEqs()]), use a SECOND gvs[bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def, AllCaseEqs(), option_CASE_rator, sum_CASE_rator, pairTheory.PAIR] to expand the remaining do-block IN assumptions. This creates subgoals for each TypeError branch. The NONE/TypeError branches are auto-resolved if contradicted by typing facts already in assumptions. Use >- to handle remaining subgoals individually.
works_when: Proving no_TypeError for a monadic do-block branch after a case split, where typing facts are already derived as assumptions. The do-block equation must be in assumptions (not goal position).
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2810_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2818_t001
- episode:E0021

## L0058 scope='' tags=
shape: Bridge gvs-expansion variables to typing-fact variables via REVERSE decomposition
pattern: After gvs[AllCaseEqs()] expands a do-block containing REVERSE sbs = x'::xs (from lift_option_type case REVERSE sbs), the variables x' and xs don't match typing facts that use LAST sbs and TL(REVERSE sbs). Bridge with: `x' = LAST sbs` by (qpat_x_assum `REVERSE sbs = _ :: _` mp_tac >> Cases_on `sbs` >> gvs[REVERSE_DEF, LAST_DEF, HD]) and `TAKE (LENGTH xs - LENGTH remaining) xs = TAKE (LENGTH key_types) xs` by (DECIDE_TAC after deriving LENGTH xs = LENGTH key_types + LENGTH remaining from the length sum assumption).
works_when: Proving compute_hashmap_slot or similar function is not NONE after gvs expansion where the expansion introduces x'/xs but typing facts use LAST/TL(REVERSE)
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2818_t001
- episode:E0021

## L0059 scope='' tags=
shape: Bridge gvs-expansion variable x' to LAST is via helper lemma
pattern: When gvs expands REVERSE is = x'::xs in assumptions, bridge x' = LAST is by proving HD_REVERSE_EQ_LAST helper: !l. l <> [] ==> HD(REVERSE l) = LAST l. Proof: qsuff_tac REVERSE l = LAST l :: REVERSE(FRONT l) >- simp[] >> metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq]. Then use `HD(REVERSE is) = LAST is` by metis_tac[HD_REVERSE_EQ_LAST] >> gvs[] which eliminates x' = LAST is via variable elimination.
works_when: Proving x' = LAST is when REVERSE is = x'::xs is in assumptions and is ≠ [] is available. gvs expansion creates x'/xs but typing facts reference LAST is.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2878_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1918-1924
- episode:E0022

## L0060 scope='' tags=
shape: by-subgoal MUST be completely self-contained - cannot reference assumptions that gvs has renamed/duplicated
pattern: When a by-subgoal (t1 by tac) needs to derive a fact from assumptions, and gvs has already renamed/duplicated variables, the by-subgoal CANNOT see the original assumption names. Instead: (1) derive ALL facts as standalone Theorem helper lemmas BEFORE the main proof, (2) use MATCH_MP/irule with the helper lemma directly, not by-subgoal. For LENGTH bridging, prove REVERSE_CONS_IMP_LENGTH (!l h t. REVERSE l = h::t ==> LENGTH l = SUC(LENGTH t)) as a standalone theorem, then use qpat_x_assum + MATCH_MP + assume_tac inline (NOT inside a by-subgoal).
works_when: Proving intermediate facts inside mutual theorem resumes where by-subgoals have different variable context from the displayed goal
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2945_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2943_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2860_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1926-1932 - REVERSE_CONS_IMP_LENGTH helper lemma
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1918-1924 - HD_REVERSE_EQ_LAST helper lemma pattern that works for by-subgoals when the fact is simple enough for metis_tac inside the by-subgoal but the variable bridge needs the standalone lemma first

## L0061 scope='' tags=
shape: Proving no-TypeError for monadic evaluator do-block branch (HashMapRef, ArrayRef, ImmutableVar, etc.)
pattern: ALWAYS use a boundary lemma where the assign_target/evaluate equation is the GOAL conclusion, not an assumption. simp[bind_def, AllCaseEqs()] can expand binds in goals but NOT in assumptions. Create small packaged helper lemmas for all path/split/typing facts BEFORE the main proof, then expand the do-block once in goal position. The resume simply calls drule boundary_lemma.
works_when: Proving no_type_error_result for evaluator branches where the function result ends up as an assumption after prior gvs/case-split
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2547_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2552_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2153-2167
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2042-2083
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2945_t001

## L0062 scope='' tags=
shape: Existential conjunction lemma packaging path decomposition facts for HashMapT assignment target
pattern: Use target_path_type_HashMapT_assign_target_decomp to package: REVERSE sbs decomposition, split_hashmap_subscripts success/length, EVERY subscript_to_value for hashmap prefix - all from well_formed_vtype + target_path_type on HashMapT. Proof: derive sbs <> [] via target_path_type_HashMapT_not_nil, then Cases_on split result, derive length via split_hashmap_subscripts_some_imp, derive EVERY via target_path_type_HashMapT_hashmap_prefix_ValueSubscript, then qexistsl [LAST sbs, TL(REVERSE sbs), ...]. Write statement using nested ==> not /\.
works_when: Proving HashMapRef assignment branch no-TypeError where REVERSE sbs is consumed by the evaluator. The decomp lemma bridges the gap between typing facts (LAST, TL(REVERSE), split_hashmap_subscripts) and the evaluator's monadic bind variables (x'/xs from case REVERSE sbs of x::xs).
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2153-2187
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2990_t003
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2945_t001

## L0063 scope='' tags=
shape: Expanding large HOL definitions (assign_target_def, evaluate_def) with many assumptions in context
pattern: Use once_rewrite_tac[def] instead of simp[Once def] when the definition is large and there are many assumptions. simp processes all assumptions which can be exponentially slow. once_rewrite_tac only rewrites occurrences in the goal. Follow with targeted simp[bind_def, lift_option_type_def, ...] for monadic expansions.
works_when: Proving theorems where assign_target_def or other large definitions need expanding in the goal/antecedent and there are 10+ assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3070_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3060_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2187-2264
- episode:E0025
- episode:E0007
- episode:E0012
- episode:E0018
- episode:E0021
- episode:E0024
- episode:E0022
- episode:E0020
- episode:E0019
- episode:E0007

## L0064 scope='' tags=
shape: Deriving LENGTH (TAKE n l) = n from n <= LENGTH l assumption
pattern: Use `LENGTH (TAKE n l) = n` by metis_tac[LENGTH_TAKE_EQ] or by (Cases_on `n` >> imp_res_tac LENGTH_TAKE_EQ >> simp[]). Do NOT use simp[LENGTH_TAKE_EQ] which processes all assumptions and times out.
works_when: Proving LENGTH facts about TAKE where the bound is already in assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3053_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3062_t001
- episode:E0025

## L0065 scope='' tags=
shape: drule fails when lemma antecedent uses env.type_defs but hypothesis uses (get_tenv cx)
pattern: When env.type_defs = get_tenv cx is in assumptions but a lemma antecedent uses env.type_defs, drule/irule fails on syntactic mismatch. Derive the matching form first: `well_formed_vtype env.type_defs (...) by metis_tac[]` then drule works. Per L0051.
works_when: Applying typing lemmas (target_path_type_*, split_hashmap_subscripts_*, etc.) when runtime_consistent provides env.type_defs = get_tenv cx
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3046_t001
- episode:E0025
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2620_t001

## L0066 scope='' tags=
shape: place_leaf_typed vs place_leaf_path_typed relationship in HOL4
pattern: place_leaf_typed env loc_vt sbs ty final_tv = place_leaf_path_typed env loc_vt (REVERSE sbs) ty final_tv (place_leaf_typed_def). To use place_leaf_path_typed_split_leaf_type, first gvs[place_leaf_typed_def] to expose place_leaf_path_typed, then rewrite REVERSE sbs into first_sub::rest_subs, then gvs[place_leaf_path_typed_def] for HashMapT case strips first element to give place_leaf_path_typed env vt rest_subs ty final_tv.
works_when: Proving leaf typing facts after target_path_type_Type_place_leaf_typed gives place_leaf_typed but you need place_leaf_path_typed for place_leaf_path_typed_split_leaf_type. This occurs in HashMapRef assignment branch helper proofs.
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:300-303
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:295-298
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3108_t001
- episode:E0026

## L0067 scope='' tags=
shape: place_leaf_typed to place_leaf_path_typed bridge for split_leaf_type
pattern: To use place_leaf_path_typed_split_leaf_type from target_path_type_Type_place_leaf_typed: (1) irule target_path_type_Type_place_leaf_typed to get ?pl_tv. place_leaf_typed env loc_vt sbs ty pl_tv; (2) gvs[place_leaf_typed_def] to expose place_leaf_path_typed env loc_vt (REVERSE sbs) ty pl_tv; (3) Cases_on `REVERSE sbs` (empty case contradicts sbs ne []); (4) gvs[place_leaf_path_typed_def] strips constructor case (e.g. HashMapT gives place_leaf_path_typed env vt t ty pl_tv); (5) drule_all place_leaf_path_typed_split_leaf_type. For env.type_defs vs get_tenv cx mismatches, use metis_tac[] to bridge.
works_when: Proving leaf typing facts after target_path_type_Type_place_leaf_typed returns place_leaf_typed but you need place_leaf_path_typed for place_leaf_path_typed_split_leaf_type
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3162_t001
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:300-303
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:295-298
- episode:E0027
- episode:E0026
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2187-2228

## L0070 scope='' tags=
shape: Helper lemma compute_hashmap_slot_prefix_some for HashMapRef branch
pattern: compute_hashmap_slot_prefix_some: LENGTH kts + LENGTH remaining = LENGTH rest_subs ==> EVERY ((<>) NONE o subscript_to_value) (first_sub :: TAKE (LENGTH kts) rest_subs) ==> compute_hashmap_slot base_slot (kt::kts) (first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining) rest_subs) <> NONE. Proof: decide_tac for LENGTH identity, irule compute_hashmap_slot_subscripts_to_values + fs[LENGTH] + decide_tac + asm_rewrite_tac[].
works_when: Proving compute_hashmap_slot <> NONE for HashMapRef assignment branch where split_hashmap_subscripts and target_path_type provide LENGTH and EVERY facts.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1823-1839
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3213_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3180_t001
- episode:E0029
- episode:E0028

## L0071 scope='' tags=
shape: HOL4 monadic do-block expansion for multi-branch definitions (e.g. assign_target_def TopLevelVar with 3 tv cases)
pattern: Do NOT use simp[assign_target_def, bind_apply, AllCaseEqs()] in a single blast for multi-branch monadic do-blocks (3+ branches). It creates too many simultaneous subgoals and either times out or leaves unresolved goals. Instead: (1) Push the equation to goal with mp_tac. (2) Use the known result (e.g. lookup_global returns HashMapRef) to eliminate branches BEFORE expanding nested binds. (3) Expand binds incrementally: use simp[bind_def,lift_option_type_def,return_def,raise_def] WITHOUT AllCaseEqs first to unfold the monad, then use Cases_on or IF_CASES_TAC for each case split one at a time, dispatching with >- after each. (4) Only use AllCaseEqs() AFTER the case variable has been narrowed to one branch. If this still fails, insert FAIL_TAC probes to inspect the exact residual goal state.
works_when: Proving no_type_error_result or similar for monadic do-blocks with multiple case-expression branches (Value/HashMapRef/ArrayRef in TopLevelVar, etc.) where a single simp[AllCaseEqs()] blast creates more than ~8 simultaneous subgoals
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3220_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3253_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3227_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2114-2158 - ScopedVar works with Once+AllCaseEqs because single branch
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2370-2438 - sound_TopLevelVar resume works with AllCaseEqs because fewer assumptions after mutual theorem strips
- source:semantics/vyperStateScript.sml:873-905 - assign_target_def showing 3-case tv split in TopLevelVar branch

## L0072 scope='' tags=
shape: FAIL_TAC probe for debugging incomplete tactic dispatch
pattern: When TRY blocks or other dispatch tactics leave unresolved subgoals silently (no error, just incomplete proof), insert `>> FAIL_TAC "probe"` BEFORE the TRY block to see the exact goal state. Remove the probe after identifying the mismatch. This is critical for monadic do-block TypeError dispatch where the drule target may not syntactically match the goal term.
works_when: Debugging proof failures where tactic completes but leaves unresolved subgoals, especially with TRY/ORELSE dispatch blocks for TypeError branches in monadic evaluator proofs
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3253_t001 - proof failed with 'no theorem proved' but no goal state shown

## L0073 scope='' tags=
shape: Converting option <> NONE to = SOME in heavy assumption context
pattern: When needing ?x. f a = SOME x from f a <> NONE in a context with 20+ assumptions, use Cases_on `f a` >> gvs[] to split NONE/SOME cases, rather than simp[optionTheory.IS_SOME_EXISTS] which processes all assumptions and times out. NONE case contradicts <> NONE assumption via gvs. SOME case gives the named result directly. Then rename1 to give the result a useful name.
works_when: Converting option <> NONE facts to = SOME form in proof contexts with many assumptions where simp is too slow
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3286_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3288_t001
- episode:E0031

## L0074 scope='' tags=
shape: Proving no-TypeError for monadic do-block branches with many assumptions
pattern: For standalone theorems about assign_target/evaluate do-blocks with 20+ assumptions: (1) Create a separate BOUNDARY LEMMA with minimal sufficient hypotheses (only the = SOME facts needed for the specific branch), place BEFORE the main theorem. (2) Prove boundary lemma with gvs[Once assign_target_def, bind_def, lift_option_type_def, ...] - FEWER assumptions means simp/gvs finishes fast. (3) Main theorem derives the boundary lemma's hypotheses from the full preamble and calls drule boundary_lemma. This mirrors the working resume proofs which have fewer assumptions after mutual theorem stripping.
works_when: Proving no_type_error_result or preservation for monadic evaluator branches where inline expansion with full assumption set times out. ALWAYS use boundary lemma when assumption count exceeds ~15.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2114-2158
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2338
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3296_t001
- episode:E0031

## L0075 scope='' tags=
shape: FAIL_TAC probe placement for debugging monadic expansion
pattern: When debugging once_rewrite_tac[def] + simp[...] sequences, insert FAIL_TAC probe RIGHT AFTER once_rewrite_tac (before any simp), not after the subsequent simp call. This shows whether the definition actually rewrites. Use >> between once_rewrite_tac and FAIL_TAC, and ensure FAIL_TAC is on its own line to avoid parse errors with subsequent simp calls.
works_when: Debugging whether a once_rewrite_tac[definition] actually fires in the goal position, especially when the subsequent simp might undo or obscure the rewrite
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3298_t001
- episode:E0031

## L0077 scope='' tags=
shape: HashMapRef branch step-by-step do-block expansion in assign_target
pattern: After narrowing to the HashMapRef case in assign_target, expand the do-block step-by-step: (1) case REVERSE is of x::xs -> lift_option_type none case contradicts sbs ne [], (2) split_hashmap_subscripts SOME case from assumption, (3) compute_hashmap_slot SOME case from assumption, (4) evaluate_type SOME case from assumption, (5) read_storage_slot -> INR case use drule read_storage_slot_error + gvs[], INL case continue, (6) assign_subscripts -> INR(TypeError) use irule assign_subscripts_no_type_error_runtime_typed + read_storage_slot_success_type, INL case continue, (7) write_storage_slot no TypeError via assign_subscripts_preserves_type_runtime_typed + write_storage_slot_no_type_error_from_value_has_type, (8) assign_result via assign_result_no_type_error_from_successful_assign.
works_when: Proving no_type_error_result for HashMapRef branch of assign_target TopLevelVar, where the do-block has known successful option computations but read/assign/write may error
evidence:
- source:semantics/vyperStateScript.sml:888-905
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2114-2158
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3328_t001

## L0078 scope='' tags=
shape: HOL4 gvs[AllCaseEqs()] after Once assign_target_def with >- dispatch
pattern: When gvs[Once assign_target_def, bind_def, ..., AllCaseEqs()] produces multiple subgoals, chain >- blocks DIRECTLY after gvs without >>: gvs[...] >- (tac1) >- (tac2) ... NEVER write gvs[...] >> >- (tac) because >> and >- have the SAME precedence and are LEFT-ASSOCIATIVE, making >> try to apply >- tac as a tactic argument, which is ill-typed.
works_when: Proving monadic do-block branches where gvs[AllCaseEqs()] produces multiple subgoals that need individual dispatch. The key: no >> between the gvs call and the first >-.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3384_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3390_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2114-2158 - working ScopedVar proof with reverse $ gvs[...] >- (...) >- (...) pattern without >>
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3377_t001 - successful gvs+AllCaseEqs expansion showing 4 clean subgoals from boundary lemma with 10 hypotheses

## L0079 scope='' tags=
shape: Boundary lemma eliminates simp/gvs timeout for large monadic do-block expansion
pattern: gvs[Once assign_target_def, bind_def, ..., AllCaseEqs()] with 10 hypotheses (boundary lemma) completes instantly and auto-resolves TypeError/None branches. With 20+ hypotheses (main theorem), it times out at 120s. Solution: create a boundary lemma with minimal =SOME hypotheses (only the facts needed for the specific branch), prove it with gvs[AllCaseEqs()], then main theorem derives boundary lemma hypotheses and calls drule.
works_when: Proving no_type_error_result for monadic evaluator branches where inline expansion with full assumption set times out. ALWAYS use boundary lemma when assumption count exceeds ~15.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3377_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3227_t001 - timeout with 20+ assumptions
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2250-2304 - boundary lemma with 10 hypotheses

## L0080 scope='' tags=
shape: HashMapRef branch 4 subgoals after gvs[AllCaseEqs()] in assign_target boundary lemma
pattern: After gvs[Once assign_target_def, bind_def, ..., AllCaseEqs()] in assign_target_HashMapRef_branch_no_type_error, exactly 4 subgoals remain: (1) Full success: assign_result final_tv op current_val remaining s4 = (res,st') [solve: metis_tac[read_storage_slot_success_type, assign_subscripts_preserves_type_runtime_typed, assign_result_no_type_error_from_successful_assign]]; (2) write_storage_slot INR: no_type_error_result (INR e) [solve: metis_tac[read_storage_slot_success_type, assign_subscripts_preserves_type_runtime_typed, write_storage_slot_no_type_error_from_value_has_type, no_type_error_result_def]]; (3) assign_subscripts INR: no_type_error_result (INR (Error e)) [solve: derive value_has_type then irule assign_subscripts_no_type_error_runtime_typed]; (4) read_storage_slot INR: no_type_error_result (INR e) [solve: metis_tac[read_storage_slot_error, no_type_error_result_def]].
works_when: Proving the assign_target_HashMapRef_branch_no_type_error boundary lemma for C3.1.6.4/C3.1.6 specifically.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3377_t001 - instrumented log with all 4 subgoals
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2250-2304 - boundary lemma source

## L0081 scope='' tags=
shape: Closing gvs[AllCaseEqs()] subgoals in monadic do-block no-TypeError proofs
pattern: After gvs[Once assign_target_def, bind_def, ..., AllCaseEqs()] produces N subgoals from a monadic do-block expansion: (1) For success-path goals with no_type_error_result res where the result lemma has multi-antecedent form, use drule lemma >> disch_then drule >> simp[no_type_error_result_def]. (2) For INR error goals, first derive value_has_type facts via irule inside by-subgoals (irule read_storage_slot_success_type >> simp[] etc), then CCONTR_TAC >> gvs[] >> imp_res_tac specific_no_TypeError_lemma >> gvs[]. (3) NEVER use irule on no_type_error_result goals directly. (4) NEVER use imp_res_tac with multi-antecedent lemmas in this context - it pollutes.
works_when: Proving no_type_error_result for monadic do-block branches after gvs[AllCaseEqs()] expansion, where the success/error paths have known lemma solutions but tactical selection is tricky
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2114-2158 - ScopedVar proof model with drule>>disch_then drule>>simp
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3422_t001 - irule existential witness failure
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3428_t001 - imp_res_tac pollution failure
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3400_t001 - metis_tac timeout failure
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3384_t001 - >> before >- syntax error

## L0082 scope='' tags=
shape: HOL4 monadic do-block subgoal dispatch after gvs[AllCaseEqs()]
pattern: After gvs[Once assign_target_def, bind_def, ..., AllCaseEqs()] creates N subgoals from monadic do-block: (1) Derive value_has_type via drule_all_then assume_tac read_storage_slot_success_type >> simp[]. (2) Bridge env.type_defs = get_tenv cx via metis_tac[]. (3) Use drule_all_then assume_tac or metis_tac[specific_lemma] for remaining facts. (4) Close with drule >> disch_then drule >> simp[no_type_error_result_def] (success path) or metis_tac[error_classification_lemma] (error paths). NEVER use irule on multi-antecedent lemmas or imp_res_tac in this context.
works_when: Proving no_type_error_result for monadic do-block branches where gvs[AllCaseEqs()] creates clean subgoals with <15 assumptions each
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3455_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3467_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2114-2158 - working ScopedVar proof model

## L0083 scope='' tags=
shape: env.type_defs vs get_tenv cx bridging in assign_target proofs
pattern: When runtime_consistent env cx st gives env.type_defs = get_tenv cx, lemmas using env.type_defs won't match assumptions using (get_tenv cx). Fix: derive the env.type_defs form first via `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)` by metis_tac[], then apply the lemma with drule_all_then or metis_tac.
works_when: Applying typing lemmas (assign_subscripts_preserves_type_runtime_typed, assign_subscripts_no_type_error_runtime_typed, etc.) in boundary lemmas where env.type_defs = get_tenv cx is available
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3461_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3463_t001

## L0084 scope='' tags=
shape: Closing no_type_error_result goals for INR error cases in monadic do-blocks
pattern: For no_type_error_result (INR e) where e comes from a classified error function: (1) Use drule error_classification_lemma (e.g., drule read_storage_slot_error for read_storage_slot errors). This pushes ∃m. e = Error (RuntimeError m) as antecedent. (2) simp[no_type_error_result_def] then resolves the constructor inequality. For INR (TypeError msg) cases that should be impossible: drule_all_then strip_assume_tac no_type_error_lemma gives ∀msg. f ... ≠ INR(TypeError msg), combine with f ... = INR e via metis_tac[].
works_when: Proving no_type_error_result for INR error branches in assign_target/evaluate do-blocks where the error source is a classified function (read_storage_slot always gives RuntimeError, assign_subscripts can't give TypeError under runtime typing)
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3455_t001 - Goal 4 with read_storage_slot INR
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3467_t001 - Goal 3 with assign_subscripts INR

## L0085 scope='' tags=
shape: Using standalone assignment no-TypeError lemmas inside mutual theorem resumes
pattern: When a standalone assignment-target no-TypeError theorem (e.g. top_level_HashMapRef_assign_no_type_error) exists and the resume needs to close a HashMapRef branch: (1) Do NOT expand assign_target_def upfront for all branches - it destroys the assign_target equation. (2) Instead, case-split on lookup_global result BEFORE any assign_target expansion. (3) For branches with a proved boundary lemma: derive the lemma's premises from assign_target_assignable_context_def + target_runtime_typed_def + runtime_consistent, then drule the lemma. (4) For branches that need inline expansion (Value): scope the gvs[assign_target_def,...] to only that branch's subgoal.
works_when: Integrating proved standalone no-TypeError theorems into assign_target_sound_mutual resumes where upfront gvs expansion would destroy the assign_target equation needed by drule
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3481_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3478_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2355-2422
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2308-2353

## L0086 scope='' tags=
shape: drule read_storage_slot_error needs rpt strip_tac before simp
pattern: After drule read_storage_slot_error, the goal becomes (∃m. e = Error (RuntimeError m)) ⇒ no_type_error_result (INR e). simp[no_type_error_result_def] alone cannot resolve the existential. Add rpt strip_tac first to unpack the existential witness, then simp[no_type_error_result_def] resolves the constructor inequality (RuntimeError ≠ TypeError).
works_when: Closing no_type_error_result goals where the error error_type variable e comes from read_storage_slot via drule read_storage_slot_error
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3478_t001

## L0087 scope='' tags=
shape: metis_tac[] bridges INR injectivity gap after simp[no_type_error_result_def]
pattern: When simp[no_type_error_result_def] leaves goal ∀msg. e ≠ TypeError msg but assumptions contain assign_subscripts ... = INR e and ∀msg. assign_subscripts ... ≠ INR(TypeError msg), metis_tac[] bridges the INR injectivity gap to derive e ≠ TypeError msg from the two assumptions. simp alone cannot combine the equation and inequality across different assumption forms.
works_when: Closing monadic do-block subgoals where the error variable e appears in both an equation and a universal inequality with INR wrapper
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3476_t001

## L0088 scope='' tags=
shape: Integrating a proved boundary lemma into a mutual theorem resume that uses upfront gvs[function_def]
pattern: When a resume does gvs[function_def, AllCaseEqs()] upfront (destroying the equation a boundary lemma needs), restructure: (1) Do NOT expand function_def upfront. (2) Case-split on the discriminating variable (e.g., vt from target_runtime_typed) BEFORE any definition expansion. (3) For branches with a proved boundary lemma: derive lemma premises from context definitions (assign_target_assignable_context_def, target_runtime_typed_def, runtime_consistent), then metis_tac[boundary_lemma]. (4) For branches needing inline expansion: scope the gvs[function_def,...] to ONLY that branch subgoal.
works_when: Proving no-type-error/preservation branches inside mutual theorem resumes where one branch has a standalone proved theorem and other branches need inline expansion. The upfront gvs expansion destroys equations needed by boundary lemmas.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3481_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2355-2423
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3475_t001

## L0089 scope='' tags=
shape: metis_tac vs drule/irule for standalone no-TypeError theorems with type-variable mismatch
pattern: When applying top_level_HashMapRef_assign_no_type_error or similar theorems where the conclusion has type variables (kt, vt, etc.) that must be unified, use metis_tac[theorem_name] instead of drule/irule. metis_tac handles higher-order unification of type variables, while drule creates unresolved existential subgoals and irule creates witness subgoals it cannot resolve.
works_when: Applying standalone assignment no-TypeError theorems where the theorem has universally quantified type variables that need instantiation from the current goal context
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3475_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3481_t001

## L0090 scope='' tags=
shape: Resume proof that uses boundary lemma referencing assign_target/f_eval equation as premise
pattern: DO NOT use upfront gvs[f_def, AllCaseEqs()] which consumes the equation. Instead: (1) decompose typing assumptions to get needed type-level info (e.g. Cases_on 'vt'), (2) for boundary-lemma branch: derive premises from context defs without expanding f_def, then apply lemma directly, (3) for inline-expansion branch: use gvs[Once f_def, bind_def, ...] or controlled expansion scoped to just that subgoal.
works_when: Resume proof where some branches can use boundary lemmas needing the original equation and other branches need inline definition expansion
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3526_t003
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2114-2158
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2308-2353
- episode:E0035

## L0091 scope='' tags=
shape: HashMapRef branch in TopLevelVar resume: FLOOKUP returns vt, lookup_global returns HashMapRef b c t v
pattern: After gvs[assign_target_def,...] >> Cases_on tv in TopLevelVar resume: (1) First resolve tgt/Cases_on vt to get FLOOKUP variable vt. Variable names after gvs: vt from FLOOKUP, b' from BaseTarget. (2) Cases_on vt splits: Type base_ty (contradiction via lookup_global_Value_not_HashMapVarDecl + top_level_Type_not_hashmap_decl) and HashMapT t' v' (derive premises then inline do-block expansion). (3) For HashMapT: derive env.type_defs=get_tenv cx, well_formed_vtype via location_runtime_typed_well_formed_vtype, top_level_HashMap_decl for find_var_decl, IS_SOME_EXISTS for slot, then lookup_global_HashMapVarDecl_returns_HashMapRef, then target_path_type_HashMapT_assign_target_decomp + compute_hashmap_slot_prefix_some + target_path_type_HashMapT_split_leaf_runtime, then expand do-block with gvs[bind_def,ignore_bind_def,return_def,raise_def,lift_option_type_def,lift_sum_def,type_check_def,assert_def,check_def,option_CASE_rator,sum_CASE_rator,pairTheory.PAIR,LET_THM,AllCaseEqs()] yielding 4 subgoals.
works_when: Proving no_type_error_result for HashMapRef branch of assign_target TopLevelVar case in the mutual assign_target_sound_mutual proof
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3714_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2250-2306
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2308-2353
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2160-2170 - lookup_global_HashMapVarDecl_returns_HashMapRef
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1223-1243 - top_level_Type_not_hashmap_decl + top_level_HashMap_decl
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:246-260 - location_runtime_typed_def (TopLevelVar case is just FLOOKUP)

## L0092 scope='' tags=
shape: HashMapRef branch in TopLevelVar resume after upfront gvs expansion
pattern: After upfront gvs[assign_target_def,...] >> Cases_on tv, the HashMapRef branch has: lookup_global cx src_id_opt (string_to_num id) st = (INL(HashMapRef b c t v),s'') + get_module_code cx src_id_opt = SOME ts + runtime_consistent + FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME vt + target_path_type env vt is (Type ty) + assignable_type env.type_defs ty + assign_operation_runtime_typed env ty op + assign_target_assignable_context cx (BaseTargetV(TopLevelVar src_id_opt id) is) st. Must Cases_on tgt >> gvs[target_runtime_typed_def, location_runtime_typed_def] >> Cases_on vt >> gvs[]. Type case: contradiction. HashMapT case: derive premises then expand do-block inline.
works_when: Proving no_type_error_result for HashMapRef branch of assign_target TopLevelVar inside the mutual sound_TopLevelVar resume after upfront gvs[assign_target_def,...]
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3714_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2355-2484
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2250-2306 - boundary lemma with 4 subgoal pattern

## L0093 scope='' tags=
shape: C2 prerequisite CHEATs for HashMapRef branch proof closure
pattern: assign_subscripts_preserves_type_runtime_typed, assign_subscripts_no_type_error_runtime_typed, top_level_storage_value_assign_subscripts_no_type_error, and assign_operation_runtime_typed_leaf_no_type_error are still CHEATs. The boundary lemma assign_target_HashMapRef_branch_no_type_error (line 2250) also depends on these. Proving the HashMapRef do-block branches requires these lemmas to be proved first (C2). Without C2, some of the 4 subgoals from gvs[AllCaseEqs()] won't close.
works_when: Determining whether HashMapRef branch proofs can close or if C2 must be completed first
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2250-2306
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1190-1240 - CHEAT list

## L0094 scope='' tags=
shape: lookup_global return shape determines var_decl_info constructor (need converse lemmas)
pattern: For each lookup_global return shape, need a lemma that the OTHER declaration types are impossible. Existing: lookup_global_Value_not_HashMapVarDecl (Value + HashMapVarDecl = F), lookup_global_ArrayRef_not_HashMapVarDecl (ArrayRef + HashMapVarDecl = F). MISSING: lookup_global_HashMapRef_not_StorageVarDecl (HashMapRef + StorageVarDecl = F). All follow same proof pattern: rw[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs(), option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator, type_value_CASE_rator, toplevel_value_CASE_rator, LET_THM] >> gvs[].
works_when: Deriving contradictions in assign_target_sound_mutual branches where lookup_global result shape doesn't match the expected declaration type. After Cases_on vt + Cases_on p0 from assign_target_assignable_context.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1262-1273
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1276-1288
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3765_t001
- episode:E0038

## L0095 scope='' tags=
shape: Proving lookup_global result shape constrains var_decl_info constructor
pattern: For contradiction lemmas where lookup_global returns a specific toplevel_value (HashMapRef, ArrayRef, Value) but find_var_decl implies a different var_decl_info: use EITHER (1) CONJUNCTIVE format (conjunction //\) matching lookup_global_Value_not_HashMapVarDecl + same proof chain, OR (2) mp_tac to push the lookup_global equation to goal position then simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs(), *_CASE_rator, LET_THM] + rpt strip_tac + gvs[]. DO NOT use rw with implicative format - it converts find_var_decl hypothesis to a negated goal.
works_when: Proving that lookup_global returning a specific toplevel_value constructor contradicts a find_var_decl_by_num result of a different var_decl_info constructor
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1262-1274
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3821_t001
- episode:E0039

## L0096 scope='' tags=
shape: lookup_global contradiction lemma with implicative format
pattern: For lemmas proving F from lookup_global returning wrong constructor vs find_var_decl type: use ==> format + mp_tac approach (push lookup_global equation to goal, simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def, option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator, type_value_CASE_rator, toplevel_value_CASE_rator, LET_THM, AllCaseEqs()] + rpt strip_tac + gvs[]). DO NOT use rw - it converts find_var_decl hypothesis to negated goal.
works_when: Proving contradiction between lookup_global return shape and find_var_decl_by_num var_decl_info constructor
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1302
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1276-1288
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3864_t001

## L0099 scope='' tags=
shape: Mutual theorem resume with standalone boundary lemma needing the original equation
pattern: When a resume uses standalone boundary lemmas that need the original function equation (e.g. assign_target ... = (res, st')), do NOT do upfront gvs[f_def, AllCaseEqs()] - it expands the equation into a monadic do-block in assumptions, making it impossible for drule/metis_tac to match. Instead: (1) case-split on the discriminating variable FIRST (e.g. Cases_on lookup_global result to get Value/HashMapRef/ArrayRef), (2) for branches with standalone theorems: keep the original equation intact, derive premises from context definitions without expanding f_def, then invoke the theorem, (3) for branches needing inline expansion: scope gvs[Once f_def,...] within that subgoal only.
works_when: Mutual theorem resumes where some branches have proven standalone theorems needing the original function equation, and other branches need inline definition expansion
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3937_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3481_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2377
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2323-2368
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2265-2280
- episode:E0041

## L0100 scope='' tags=
shape: Mutual theorem resume with standalone boundary lemma needing original function equation
pattern: When a resume uses standalone boundary lemmas that need the original function equation (e.g. assign_target ... = (res, st')), do Cases_on the discriminating variable FIRST (e.g. vt from location_runtime_typed) BEFORE expanding the function definition. Then scope gvs[function_def,...] to ONLY the subgoals that need inline expansion. For subgoals with proved boundary lemmas: keep the original equation intact, derive premises from context definitions, then invoke the boundary lemma directly.
works_when: Mutual theorem resumes where some branches have proven standalone theorems needing the original function equation, and other branches need inline definition expansion. The discriminating variable comes from expanding the type/runtime-typed hypothesis.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3937_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4016_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2323-2368
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:258-259
- episode:E0041
- episode:E0035

## L0101 scope='' tags=
shape: Boundary lemma for assign_target TopLevelVar Value branch with lookup_global result as hypothesis
pattern: Create assign_target_TopLevelVar_Value_branch_no_type_error taking lookup_global=(INL(Value v)) + value_has_type root_tv v as premises. Push assign_target equation to goal with mp_tac then simp[Once assign_target_def] then gvs[bind_def,AllCaseEqs()] to expand do-block. Dispatch subgoals: assign_result success, set_global INR, assign_subscripts INR, evaluate_type NONE, find_var_decl NONE, get_module_code NONE.
works_when: Proving no_type_error_result for TopLevelVar assign_target when lookup_global returns Value (StorageVarDecl with non-ArrayTV evaluate_type)
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2323-2377
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2114-2158 - ScopedVar boundary lemma model
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2250-2306 - HashMapRef boundary lemma model
- source:semantics/vyperStateScript.sml:873-886 - assign_target TopLevelVar Value branch do-block definition

## L0102 scope='' tags=
shape: Boundary lemma for assign_target TopLevelVar branch where lookup_global result is deterministic from declaration alone
pattern: Take lookup_global result as premise. After simp[Once assign_target_def], use AllCaseEqs() to select the branch matching the lookup_global result. Subgoals: assign_result (drule assign_result_no_type_error_from_successful_assign), storage write (drule set_global/write_storage_slot no-type-error), assign_subscripts (drule assign_subscripts_no_type_error_runtime_typed), option failures (contradiction with premises).
works_when: lookup_global's return value is fully determined by the declaration type (e.g. HashMapVarDecl → HashMapRef, ArrayTV StorageVarDecl → ArrayRef). No read_storage_slot contingencies.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2265-2321 - assign_target_HashMapRef_branch_no_type_error working proof
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4025_t002 - HashMapRef branch proven in resume by metis_tac[top_level_HashMapRef_assign_no_type_error]

## L0103 scope='' tags=
shape: Boundary lemma for assign_target TopLevelVar branch where lookup_global result is contingent on read_storage_slot
pattern: Do NOT take lookup_global result as premise. Instead take runtime_consistent + context witnesses. Inside: simp[Once assign_target_def] then handle ALL cases of the lookup_global/monadic expansion. For INR errors: not TypeError (RuntimeError). For ArrayRef: use ArrayRef boundary lemma. For HashMapRef: contradiction with StorageVarDecl declaration. For Value v: derive value_has_type from lookup_global_storage_Value_typed, then handle assign_subscripts/set_global/assign_result.
works_when: lookup_global calls read_storage_slot which can fail. The no_type_error_result conclusion holds even on INR because read_storage_slot only raises RuntimeError, never TypeError.
evidence:
- source:semantics/vyperStateScript.sml:413-439 - lookup_global_def showing StorageVarDecl reads storage when not ArrayTV
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1352-1380 - lookup_global_storage_Value_typed deriving value_has_type from lookup_global Value result

## L0104 scope='' tags=
shape: lookup_global state preservation for boundary lemmas
pattern: After expanding assign_target_def with gvs[Once assign_target_def, ..., AllCaseEqs()], the inner lookup_global call produces state variable s'' that equals st. Use imp_res_tac lookup_global_state to derive this, NOT metis_tac with hardcoded variable names.
works_when: Proving no_type_error_result for TopLevelVar assignment targets where set_global or read_storage_slot state needs to be reconciled
evidence:
- source:semantics/prop/vyperStatePreservationScript.sml:91
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4249_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4221_t001

## L0105 scope='' tags=
shape: TopLevelVar assignment boundary lemma premise interface
pattern: Boundary lemmas for TopLevelVar no-TypeError proofs need target_runtime_typed + assign_operation_runtime_typed + assign_operation_matches_target_shape as premises. Without target_runtime_typed, the set_global TypeError contradiction path breaks because top_level_storage_value_assign_success_no_type_error and assign_subscripts_preserves_type_runtime_typed both require it.
works_when: Writing any boundary lemma that proves no_type_error_result for assign_target on TopLevelVar targets
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4261_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1517

## L0106 scope='' tags=
shape: lookup_global result case-split for TopLevelVar StorageVarDecl
pattern: For TopLevelVar with StorageVarDecl + non-ArrayTV root_tv: lookup_global deterministically returns (INL (Value v), st). Case-split on lookup_global result: INR is RuntimeError (not TypeError), HashMapRef contradicts StorageVarDecl (use lookup_global_HashMapRef_not_StorageVarDecl), ArrayRef contradicts non-ArrayTV (need new lemma or expand lookup_global_def), Value routes to top_level_storage_value_assign_success_no_type_error.
works_when: Proving no_type_error_result for assign_target TopLevelVar StorageVarDecl branch when root_tv is not ArrayTV
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2357-2398
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2265-2321
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1517-1544

## L0107 scope='' tags=
shape: lookup_global result shape for StorageVarDecl with all-SOME preconditions
pattern: For StorageVarDecl + non-ArrayTV evaluate_type + all lift_option_type preconditions as SOME, lookup_global_def's StorageVarDecl branch goes: lift_option_type succeeds → evaluate_type case-split: ArrayTV → ArrayRef, non-ArrayTV → read_storage_slot + return(Value). So lookup_global returns INL(ArrayRef) iff ArrayTV, INL(Value v) iff read_storage succeeds, INR(Error(RuntimeError)) iff read_storage fails. Use lookup_global_StorageVarDecl_non_ArrayTV_no_TypeError to rule out TypeError, lookup_global_ArrayRef_not_StorageVarDecl to rule out ArrayRef+non-ArrayTV, lookup_global_HashMapRef_not_StorageVarDecl to rule out HashMapRef.
works_when: Proving properties of assign_target TopLevelVar+StorageVarDecl+non-ArrayTV branches
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2354-2374
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1303
- source:semantics/vyperStateScript.sml:413-440 (lookup_global_def)

## L0108 scope='' tags=scoping,universal_quantifier,metis,free_variables
shape: HOL4 free variables in != conditions become fixed after strip_tac, blocking metis instantiation
pattern: When a theorem needs root_tv <> ArrayTV elem_tv bd for ANY elem_tv/bd (not specific ones), write (!elem_tv bd. root_tv <> ArrayTV elem_tv bd) in the theorem statement. After strip_tac this becomes ∀elem_tv bd. root_tv ≠ ArrayTV elem_tv bd in assumptions, which metis_tac can instantiate. NEVER use root_tv ≠ ArrayTV elem_tv bd with free elem_tv/bd at top-level ∀.
works_when: Proving contradiction lemmas via metis_tac where the != condition must match multiple universally-quantified cases (e.g., lookup_global_ArrayRef_not_StorageVarDecl needs root_tv ≠ ArrayTV for any element type, not just specific free variables)
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4542_t001 - metis_tac fails with fixed free variables
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4551_t001 - universal quantifier in assumptions works with metis_tac

## L0109 scope='' tags=lookup_global,contradiction_lemma,pair_format,metis
shape: Contradiction lemma for lookup_global result shape must use same pair format as caller assumptions
pattern: For lemmas proving F from lookup_global returning wrong constructor vs find_var_decl type, use find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ, id) direct pair form (like lookup_global_ArrayRef_not_StorageVarDecl), NOT FST p = StorageVarDecl... form. The direct pair form matches what strip_tac produces from the theorem's find_var_decl assumptions.
works_when: Writing contradiction lemmas for lookup_global result shapes that will be applied via metis_tac in proofs where find_var_decl_by_num = SOME (Constructor, id_str) is already in assumptions
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1303 - lookup_global_ArrayRef_not_StorageVarDecl with direct pair form (works)
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1306-1318 - lookup_global_HashMapRef_not_StorageVarDecl originally FST p form (failed), now fixed to direct pair form

## L0110 scope='' tags=assign_result,no_type_error,drule,metis
shape: assign_result_no_type_error_from_successful_assign application pattern
pattern: assign_result_no_type_error_from_successful_assign takes assign_subscripts tv old subs op = INL new /\ assign_result tv op old subs st = (res,st'). Use metis_tac[assign_result_no_type_error_from_successful_assign] not drule+disch_then, because drule cannot match the conjoined premises across different assumption forms.
works_when: Proving no_type_error_result for the success path of assign_target where assign_subscripts succeeded and assign_result follows
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4606_t001 - drule+disch_then fails on Goal 1
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1190-1203 - lemma statement showing conjoined premises

## L0111 scope='' tags=
shape: Applying a lemma with conjunctive antecedent (P /\ Q ==> R) where P and Q are separate assumptions
pattern: Use first_x_assum (fn th1 => qpat_x_assum `Q_pattern` (fn th2 => ACCEPT_TAC (MATCH_MP lemma (CONJ th1 th2)))) to manually CONJ the two separate assumptions and MATCH_MP the result. For drule-style, prove a helper lemma with SEPARATE implication antecedents (P ==> Q ==> R) so drule+disch_then drule works natively.
works_when: The lemma has a conjunctive antecedent and no single assumption matches the full conjunction
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1190-1203
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2280-2336
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4624_t001

## L0115 scope='' tags=
shape: assign_result_no_type_error_from_successful_assign_split: separated implication form for safe proof application
pattern: assign_result_no_type_error_from_successful_assign_split: assign_subscripts tv old subs op = INL new ==> assign_result tv op old subs st = (res, st') ==> no_type_error_result res. Separated implication (vs conjunction) allows drule >> disch_then drule application. However, drule itself still triggers DISCH_THEN in holbuild-instrumented theories. The split form is useful for pure simp rewriting if both antecedents are in assumptions.
works_when: Applying the assign_result no-TypeError lemma where the two antecedents (assign_subscripts success + assign_result equation) are separate assumptions. If drule is unavailable (holbuild instrumentation), use simp with this lemma as a conditional rewrite.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1205-1218
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1190-1203 - original conjunctive form

## L0116 scope='' tags=
shape: 5 non-ArrayTV constructor cheats in sound_TopLevelVar reduce to single boundary theorem
pattern: assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error packages the full lookup-global analysis for Type/StorageVarDecl: HashMapRef contradicts StorageVarDecl, ArrayRef contradicts non-ArrayTV, Value branch handled by assign_target_TopLevelVar_Value_branch_no_type_error. Each non-ArrayTV constructor only needs !elem_tv bd. root_tv <> ArrayTV elem_tv bd (trivially true by discrimination). Collapse all non-ArrayTV into one block instead of per-constructor handling.
works_when: Replacing cheats for BaseTV, TupleTV, StructTV, FlagTV, NoneTV cases in sound_TopLevelVar Type/StorageVarDecl branch
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2494-2539
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2623-2631
- episode:E0043

## L0119 scope='' tags=
shape: holbuild stale checkpoint preventing proof edits from taking effect
pattern: When holbuild shows 'matched proof prefix through line X' and replays stale state, add all_tac >> before the first real tactic to break the prefix match. Reordering gvs args or renaming theorem does NOT break checkpoint matching - only structural prefix change works.
works_when: Holbuild checkpoint matching on rewritten proofs that share gvs/rw prefix with old version
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4888_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4894_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4898_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2428-2434
- source:semantics/prop/STATE_type_system_rewrite.md:Do_Not_Retry section on fs[] addition still matching checkpoint
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451 - current proof with all_tac >> rw[] >> prefix
- source:semantics/prop/LEARNINGS_type_system_rewrite.md - L0114 checkpoint instrumentation learning
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2427-2450 - current proof state after adding all_tac >> prefix
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407 - rename to assign_target_TopLevelVar_Value_branch_ntr to further break old checkpoint associations
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2419 - added lookup_var_slot_from_layout hypothesis needed for Goal 2
- source:semantics/prop/PLAN_type_system_rewrite.md - C3.1.7.1.3 component description
- source:semantics/prop/STATE_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2450
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2493-2498 - caller assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error updated to use _ntr name
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2584-2591 - 5 metis_tac replacements in sound_TopLevelVar Resume still untested
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2426 - Value branch lemma with added lookup_var_slot_from_layout hypothesis and full proof
- source:semantics/prop/STATE_type_system_rewrite.md - existing Do Not Retry entries on DISCH_THEN instrumentation blocker
- source:semantics/prop/LEARNINGS_type_system_rewrite.md - existing L0114 learning
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2427-2451 - current proof with all_tac >> rw[] >> gvs >- pattern
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2415-2426 - theorem statement with lookup_var_slot_from_layout hypothesis added
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2434-2450 - proof body with 3-goal dispatch
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2493-2498 - caller updated to use _ntr name
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2584-2591 - 5 metis_tac replacements in sound_TopLevelVar Resume
- source:semantics/prop/STATE_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/DOSSIER_type_system_rewrite.md
- source:semantics/prop/PLAN_type_system_rewrite.md - C3.1.7.1.3 active component
- source:semantics/prop/STATE_type_system_rewrite.md - existing Do Not Retry and Reflection sections
- source:semantics/prop/LEARNINGS_type_system_rewrite.md - existing L0114 and other learnings
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451 - current proof state
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2415-2426 - theorem with lookup_var_slot_from_layout added
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2427-2451 - proof with all_tac >> rw[] >> gvs >- dispatch
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2493-2498 - caller updated
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2584-2591 - 5 metis_tac replacements untested
- source:semantics/prop/STATE_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/DOSSIER_type_system_rewrite.md
- source:semantics/prop/PLAN_type_system_rewrite.md
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2427-2451
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2415-2426
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2495
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2584-2591
- source:semantics/prop/STATE_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/DOSSIER_type_system_rewrite.md
- source:semantics/prop/PLAN_type_system_rewrite.md
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2427-2451
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2415-2426
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2495
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2584-2591
- source:semantics/prop/STATE_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/DOSSIER_type_system_rewrite.md
- source:semantics/prop/PLAN_type_system_rewrite.md

## L0120 scope='' tags=
shape: Cases_on `lookup_global` then passing result to boundary theorem
pattern: After Cases_on `lookup_global cx src n st`, the pair is destructured to (q,r). Cases_on `q` splits INL/INR. For INL(Value v) case, prove `r = st` by metis_tac[lookup_global_state] then gvs[] before applying any boundary theorem that expects the state variable to match.
works_when: Boundary theorem uses `st` or `st0` for lookup_global's output state, but Cases_on names it `r`
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m4969_t001
- source:semantics/prop/vyperStatePreservationScript.sml:91-107 - lookup_global_state theorem proving st'=st for lookup_global output state

## L0121 scope='' tags=
shape: Type t place_leaf chain derivation for assignment boundary theorems
pattern: To derive evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)) and leaf_type root_tv (REVERSE sbs) <> NoneTV from runtime_consistent + FLOOKUP = SOME (Type t) + target_path_type + assignable_type + StorageVarDecl facts: (1) gvs[top_level_vtype_well_formed] gives well_formed_vtype env.type_defs (Type t); (2) gvs[top_level_Type_storage_decl] gives typ = t; (3) gvs[target_path_type_Type_place_leaf_typed] Skolemizes ?final_tv. place_leaf_typed; (4) gvs[place_leaf_typed_def, place_leaf_path_typed_def] resolves base_tv = root_tv + evaluate_type ty fact; (5) gvs[assignable_type_evaluate_not_NoneTV] derives leaf_type <> NoneTV. Useful as standalone adapter lemma consumed via simp[adapter_lemma].
works_when: Proving assignment no-TypeError boundary theorems for TopLevelVar Type/StorageVarDecl cases where place_leaf_typed chain is needed but not directly available from assumptions
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1267
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1227-1236
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:621-629
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:290-298
- source:semantics/prop/vyperTypeSystemScript.sml:270-273
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5035_t002

## L0122 scope='' tags=
shape: Proving evaluate_type leaf equation from target_path_type + well_formed_vtype
pattern: target_path_type_Type_evaluate_leaf bridges: well_formed_vtype env.type_defs (Type t) + target_path_type env (Type t) sbs (Type ty) + evaluate_type env.type_defs t = SOME root_tv => evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)). Add in vyperTypeExprSoundnessScript.sml (not in DISCH_THEN-blocked files). Proof: drule target_path_type_Type_place_leaf_typed >> simp >> strip >> mp_tac place_leaf_typed >> simp[place_leaf_typed_def, place_leaf_path_typed_def] >> strip >> gvs[].
works_when: Need to derive evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)) for TopLevelVar StorageVarDecl Type branches. Caller uses simp[target_path_type_Type_evaluate_leaf, top_level_vtype_well_formed, top_level_Type_storage_decl] where top_level_* lemmas bridge from runtime_consistent + FLOOKUP to well_formed_vtype + typ=t.
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-645
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1267
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1227-1236
- episode:E0045

## L0124 scope='' tags=
shape: Type path evaluate_type leaf equation adapter for assignment boundary theorems
pattern: target_path_type_Type_evaluate_leaf: well_formed_vtype env.type_defs (Type t) ==> target_path_type env (Type t) sbs (Type ty) ==> evaluate_type env.type_defs t = SOME root_tv ==> evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)). Add in vyperTypeExprSoundnessScript.sml. Proof: drule target_path_type_Type_place_leaf_typed >> simp >> strip >> pop_assum mp_tac >> simp[place_leaf_typed_def, place_leaf_path_typed_def] >> strip >> gvs[].
works_when: Proving evaluate_type leaf equation for Type StorageVarDecl TopLevelVar assignment boundary theorems where place_leaf_typed chain is needed. Caller uses fs[target_path_type_Type_evaluate_leaf, top_level_vtype_well_formed, top_level_Type_storage_decl]
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-646
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5128_t001
- episode:E0046

## L0125 scope='' tags=
shape: Leaf type non-NoneTV adapter for assignable Type paths
pattern: target_path_type_Type_evaluate_leaf_not_NoneTV: well_formed_vtype env.type_defs (Type t) ==> target_path_type env (Type t) sbs (Type ty) ==> evaluate_type env.type_defs t = SOME root_tv ==> assignable_type env.type_defs ty ==> leaf_type root_tv (REVERSE sbs) <> NoneTV. Proof: rpt strip_tac >> drule target_path_type_Type_evaluate_leaf >> simp[] >> metis_tac[assignable_type_evaluate_not_NoneTV].
works_when: Proving leaf_type <> NoneTV for assignment boundary theorems where assignable_type is available
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:648-660
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5138_t001
- episode:E0046

## L0126 scope='' tags=
shape: fs[existential-conclusion lemma] decomposes assumptions needed by downstream boundary lemmas
pattern: When a lemma like top_level_Type_storage_decl has an existential conclusion (?is_transient typ. vdi = StorageVarDecl is_transient typ /\ typ = t), fs[lemma] destructs the existentials and rewrites vdi, destroying the original find_var_decl_by_num ... = SOME (StorageVarDecl ..., ...) assumption. If a boundary lemma needs the ORIGINAL form, use a NON-EXISTENTIAL adapter instead (e.g., top_level_Type_storage_decl_type_eq: find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ, id) ==> typ = t) which derives just typ=t without decomposing the pair. Add adapter in a dependency theory file where drule/metis_tac work, then consume via simp[adapter] in the blocked file.
works_when: Applying boundary lemmas that need assumptions like find_var_decl_by_num = SOME (Constructor, id) after deriving intermediate facts from existential-conclusion lemmas in the same proof context
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5150_t001 - fs[top_level_Type_storage_decl] before boundary lemma application failed
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2504 - failing theorem
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660 - existing adapter lemmas that work with simp but don't derive typ=t directly without decomposition
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1227-1236 - top_level_Type_storage_decl original existential form

## L0128 scope='' tags=
shape: assign_target TopLevelVar lookup_global INR error propagation
pattern: When lookup_global cx src (string_to_num id) st = (INR e, st), assign_target cx (BaseTargetV (TopLevelVar src id) is) op st = (INR e, st). Proved as assign_target_TopLevelVar_lookup_global_INR_propagate in vyperTypeExprSoundnessScript.sml via simp[assign_target_def, bind_def, return_def, LET_THM, pairTheory.PAIR].
works_when: Proving no-TypeError for TopLevelVar assign_target when lookup_global returns INR
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:707-714
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5240_t001

## L0129 scope='' tags=
shape: holbuild stale checkpoint workaround
pattern: Stale holbuild checkpoints persist across edits and replay old variable bindings, breaking proofs that depend on specific variable names. Workaround strategies: (1) try holbuild --skip-checkpoints flag; (2) restructure proof opening to avoid prefix match (different initial tactic); (3) use suspend/Resume as sole subgoal tactic (not inside >- chains). The Proof block change may need to differ SIGNIFICANTLY from the stale prefix - even changing strip_tac to rw[] can leave enough prefix match.
works_when: holbuild reports 'matched proof prefix through' and replays stale state with wrong variable names
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5243_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5256_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5269_t001

## L0130 scope='' tags=
shape: target_path_type evaluate_type leaf equation derivation
pattern: well_formed_vtype env.type_defs (Type t) + target_path_type env (Type t) sbs (Type ty) + evaluate_type env.type_defs t = SOME root_tv => evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)). Proved as target_path_type_Type_evaluate_leaf. Also: + assignable_type => leaf_type ... <> NoneTV, proved as target_path_type_Type_evaluate_leaf_not_NoneTV. Chain: top_level_vtype_well_formed gives well_formed_vtype, top_level_Type_storage_decl gives typ=t, then gvs[] rewrites evaluate_type(get_tenv cx)(typ) to evaluate_type(env.type_defs)(t).
works_when: Deriving evaluate_type leaf equation from target_path_type + Type vtype + StorageVarDecl context
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5128_t001

## L0131 scope='' tags=
shape: Closing a goal with irule/mp_tac+simp from a boundary lemma after Cases_on splits where the boundary lemma uses differently-named state variables
pattern: When a boundary lemma has state variable names that differ from the current goal (e.g., lemma uses st0 while goal has r=st), do NOT rely on irule/mp_tac+simp to handle the unification. Instead: (1) use suspend/Resume to see the exact goal state, (2) manually specialize the boundary lemma with Q.INST before applying, or (3) use match_mp_tac which does higher-order matching and can handle variable renaming, or (4) prove an adapter lemma that bridges the naming gap.
works_when: Boundary lemma variable names don't match current assumptions due to Cases_on introducing fresh names or intermediate equalities like r=st
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5361_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5348_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5354_t001
- episode:E0047

## L0134 scope='' tags=
shape: fs/gvs cannot forward-chain implicative lemmas against pair-structured assumptions
pattern: When an assumption is 'f x = (a, b)' (pair-structured) and a lemma says 'f x = (res, st') ==> P st', neither fs, gvs, nor simp can instantiate st' := b. Must use mp_tac to specialize the lemma and strip_tac to discharge antecedent, or restructure the Cases_on to expose the pair components individually.
works_when: Thy lemma is implicational with variables bound in the antecedent that need instantiation from pair-structured assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5490_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5488_t001

## L0140 scope='' tags=
shape: Single-call fs[huge_list_of_lemmas] may resolve env.type_defs vs get_tenv cx matching issue in HOL4
pattern: When fs[gvs] processes env.type_defs = get_tenv cx, it rewrites env.type_defs → get_tenv cx in all derived facts. This prevents subsequent lemmas using env.type_defs from matching. UNTESTED APPROACH: put ALL lemmas in a SINGLE fs[...] call - fs processes theorems sequentially, adding each conclusion to assumptions before full variable elimination. So fs[top_level_vtype_well_formed, top_level_Type_storage_decl, target_path_type_Type_evaluate_leaf, ...] may add well_formed_vtype env.type_defs (Type t) (with env.type_defs form) and evaluate_type env.type_defs ty = SOME ... BEFORE doing the env.type_defs→get_tenv cx substitution.
works_when: Deriving intermediate facts in vyperTypeStatePreservationScript.sml where env.type_defs = get_tenv cx is in assumptions and upstream adapter lemmas use env.type_defs in their pattern. The single-call approach lets fs chain all derivations sequentially before the final substitution pass.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486 - failing proof where multi-step fs[] approach fails due to env.type_defs rewriting
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660 - adapter lemmas using env.type_defs in their statement
- episode:E0049 - latest episode showing the env.type_defs matching issue after gvs[] rewrites env.type_defs→get_tenv cx in assumptions
- episode:E0045 - target_path_type_Type_evaluate_leaf lemma proven in upstream file with env.type_defs form, consumed via simp in downstream where matching fails after gvs substitution
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236 - top_level_vtype_well_formed and top_level_Type_storage_decl lemmas that add env.type_defs facts to assumptions
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451 - working boundary lemma assign_target_TopLevelVar_Value_branch_ntr uses env.type_defs in statement and is consumed via metis_tac in its own proof (has checkpoint) but would need mp_tac+simp for new proofs without checkpoint
- episode:E0047
- episode:E0048
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5395_t004 - by metis_tac inside >- chains fails with DISCH_THEN assertion
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001 - by subgoal fails in HashMapRef proof
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001 - all by metis_tac variants fail in new proofs due to DISCH_THEN
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5361_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5354_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5348_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5679_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t001
- source:semantics/prop/PLAN_type_system_rewrite.md
- source:semantics/prop/DOSSIER_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/STATE_type_system_rewrite.md
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- episode:E0049
- episode:E0047
- episode:E0048
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- episode:E0049
- episode:E0045
- episode:E0047
- episode:E0048
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- episode:E0049
- episode:E0045
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- episode:E0049
- episode:E0045
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- episode:E0049
- episode:E0047
- episode:E0048
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- episode:E0045
- episode:E0046
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- source:semantics/prop/PLAN_type_system_rewrite.md
- source:semantics/prop/DOSSIER_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/STATE_type_system_rewrite.md
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- episode:E0049
- episode:E0045
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- episode:E0049
- episode:E0047
- episode:E0048
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- episode:E0045
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- episode:E0049
- episode:E0047
- episode:E0048
- episode:E0045
- episode:E0046
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/PLAN_type_system_rewrite.md
- source:semantics/prop/DOSSIER_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/STATE_type_system_rewrite.md
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- episode:E0049
- episode:E0045
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- episode:E0049
- episode:E0047
- episode:E0048
- episode:E0045
- episode:E0046
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5348_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5351_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5354_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5359_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5361_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- episode:E0049
- episode:E0047
- episode:E0048
- episode:E0045
- episode:E0046
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/PLAN_type_system_rewrite.md
- source:semantics/prop/DOSSIER_type_system_rewrite.md
- source:semantics/prop/LEARNINGS_type_system_rewrite.md
- source:semantics/prop/STATE_type_system_rewrite.md
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5348_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5351_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5354_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5359_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5361_t001
- episode:E0049
- episode:E0047
- episode:E0048
- episode:E0045
- episode:E0046
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1260-1236
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1290-1333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1335-1380
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1382-1410
- source:semantics/prop/vyperStatePreservationScript.sml:91-107
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2453-2486
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5765_t002
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5761_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5748_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5755_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5369_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5512_t001

## L0142 scope='' tags=
shape: Boundary lemma with many variables applied to goal with matching assumptions
pattern: For boundary lemmas with 5+ antecedent variables, use metis_tac[boundary_lemma, supporting_lemmas] instead of mp_tac>>simp[] or irule>>simp[]. mp_tac creates unspecialized genvars that simp cannot resolve against concrete pair assumptions. irule creates too many existential subgoals. metis_tac handles both assumption matching and existential witness solving automatically.
works_when: Goal is no_type_error_result or similar, and a boundary lemma has the right conclusion but many antecedents matching existing assumptions. Verified in vyperTypeStatePreservationScript.sml.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5838_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5842_t001
- episode:E0050
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451

## L0143 scope='' tags=
shape: INR exception branch in assign_target TopLevelVar proofs
pattern: For INR branches where lookup_global returns INR e, use assign_target_TopLevelVar_lookup_global_INR_propagate (vyperTypeExprSoundnessScript.sml:709) to directly get assign_target = (INR e, st). Then Cases_on e splits exception type. Only Error/TypeError needs contradiction (via lookup_global_StorageVarDecl_non_ArrayTV_no_TypeError for StorageVarDecl). Other exceptions (AssertException, BreakException, ContinueException, ReturnException) are trivially not TypeError - just simp[no_type_error_result_def].
works_when: Proving no_type_error_result res for assign_target when lookup_global returns INR
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2368-2387
- episode:E0050

## L0144 scope='' tags=
shape: by/metis_tac/irule work fine in vyperTypeStatePreservationScript.sml proofs
pattern: The DISCH_THEN instrumentation at proof_runtime.sml:749 does NOT block by/metis_tac/irule/drule in proofs resumed from failed-prefix checkpoints. The 38+ episode diagnosis claiming all THEN1-based tactics fail was WRONG. by+metis_tac works fine. When a tactic fails with THEN1 assertion, check the actual tactic error first (e.g., mp_tac genvars, irule existential explosion) before blaming instrumentation.
works_when: Working in vyperTypeStatePreservationScript.sml with proofs resumed from failed-prefix checkpoints
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5840_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5842_t001
- episode:E0050

## L0145 scope='' tags=
shape: HOL4 holbuild stale checkpoint with wrong variable names in resumed proof
pattern: When holbuild says matched proof prefix through line N and replays from checkpoint with different variable names, add all_tac >> at the very start of the Proof block to break the prefix match. Then re-verify all proof steps work with fresh variable names. Do NOT try to rename the auto-generated variables; instead restructure the proof to not depend on specific auto-generated names (use named lemmas, metis_tac, or Cases_on after gvs[] gives you the actual name).
works_when: Holbuild checkpoint matches an old proof prefix and replays with different variable bindings from the old execution, causing Cases_on or other variable-dependent tactics to fail
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5866_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2469-2498
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- episode:E0051
- episode:E0050

## L0146 scope='' tags=
shape: HOL4 INR exception branch in assign_target TopLevelVar proofs using propagate lemma
pattern: For INR branches where lookup_global returns (INR y, r): (1) derive r=st via metis_tac[lookup_global_state], (2) use assign_target_TopLevelVar_lookup_global_INR_propagate to get assign_target = (INR y, st), (3) combine with lookup_global_StorageVarDecl_non_ArrayTV_no_TypeError (for StorageVarDecl) or similar TypeError-exclusion lemma to show no_type_error_result. Avoid manual Cases_on y + err decomposition; use metis_tac[assign_target_TopLevelVar_lookup_global_INR_propagate, lookup_global_..._no_TypeError, lookup_global_state, no_type_error_result_def].
works_when: Proving no_type_error_result for assign_target TopLevelVar when lookup_global returns INR error
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2368-2380
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5866_t001
- episode:E0051

## L0147 scope='' tags=
shape: INR branch of assign_target TopLevelVar proofs via propagate lemma + contradiction lemma
pattern: For INR branches where lookup_global returns (INR y, r): use metis_tac[assign_target_TopLevelVar_lookup_global_INR_propagate, lookup_global_StorageVarDecl_non_ArrayTV_no_TypeError, lookup_global_state, no_type_error_result_def] instead of manual Cases_on auto-named exception variable. The propagate lemma maps lookup_global INR directly to assign_target INR. lookup_global_state gives r=st. The contradiction lemma rules out TypeError. If metis times out, split: `r = st` by metis_tac[lookup_global_state], then metis_tac[...rest].
works_when: Proving no_type_error_result for assign_target TopLevelVar when lookup_global returns INR error, especially in proofs with stale checkpoint risk where auto-generated variable names are unreliable
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2368-2387
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5866_t001
- episode:E0051
- episode:E0050

## L0148 scope='' tags=
shape: INR branch closure for assign_target TopLevelVar proofs using imp_res_tac + CCONTR_TAC
pattern: For INR branches where lookup_global returns (INR y, r): imp_res_tac lookup_global_state >> gvs[] >> imp_res_tac assign_target_TopLevelVar_lookup_global_INR_propagate >> gvs[] >> CCONTR_TAC >> gvs[no_type_error_result_def, sumTheory.INR_11] >> metis_tac[contradiction_lemma]. This avoids auto-generated variable names from Cases_on which are fragile under holbuild checkpoints.
works_when: Proving no_type_error_result for assign_target TopLevelVar when lookup_global returns INR error. Avoids both variable-name fragility and FOL timeout from single metis_tac call with 4+ lemmas.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5903_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5886_t001
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:709-714
- episode:E0052

## L0150 scope='' tags=
shape: resolve_array_element TypeError only from non-IntV subscript at ArrayTV level
pattern: resolve_array_element raises Error(TypeError ...) only when at an ArrayTV level the subscript is NOT ValueSubscript(IntV _). The check/assert calls for bounds (Fixed/Dynamic oob) raise RuntimeError. target_path_step_type on Type(ArrayT elem_ty len) forces sb = ValueSubscript(IntV _) (vyperTypeExprSoundnessScript.sml:269-270). So under target_path_type env (Type (ArrayT ...)) sbs ..., resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) (REVERSE sbs) st never returns TypeError. Prove resolve_array_element_no_type_error as helper before the ArrayRef boundary lemma.
works_when: Proving no_type_error_result for assign_target TopLevelVar ArrayRef branch, or any context where resolve_array_element is called on a typed target path through ArrayTV type
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:269-270
- source:semantics/vyperStateScript.sml:816-836
- source:semantics/vyperStateScript.sml:906-938
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:102-121

## L0151 scope='' tags=
shape: ArrayRef branch of assign_target TopLevelVar has 3 sub-cases after resolve_array_element
pattern: After resolve_array_element succeeds with (elem_slot, final_tv, remaining_subs), the ArrayRef branch does case (ao, final_tv) of: (1) PopOp + ArrayTV pop_elem_tv (Dynamic _) => pop from dynamic array (check non-empty, read last, write default, write decremented length), (2) AppendOp v + ArrayTV app_elem_tv (Dynamic n) => append to dynamic array (check capacity, write new element, write incremented length), (3) _ => ordinary assignment (read_storage_slot + assign_subscripts + write_storage_slot + assign_result). The ordinary case is same as the Value branch (lines 2407-2451). Pop/Append need assign_operation_runtime_typed to provide dynamic array typing.
works_when: Proving no_type_error_result for assign_target TopLevelVar ArrayRef branch
evidence:
- source:semantics/vyperStateScript.sml:906-938
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2388-2405

## L0152 scope='' tags=
shape: ArrayRef branch assign_target gvs expansion produces too many subgoals
pattern: For the ArrayRef branch of assign_target TopLevelVar, gvs[Once assign_target_def, AllCaseEqs()] creates >4KB goal with unapplied lambda-case on type_value (final_tv). Fix: (1) Push assign_target equation to goal with mp_tac, (2) simp[Once assign_target_def] for TopLevelVar, (3) Cases_on resolve_array_element result type instead of AllCaseEqs, (4) PairCases_on to destructure (elem_slot, final_tv, remaining_subs), (5) Cases_on final_tv + Cases_on bd for ArrayTV sub-cases, (6) dispatch each sub-case individually. OR split into separate boundary sub-lemmas for ordinary/PopOp/AppendOp.
works_when: Proving no_type_error_result for assign_target TopLevelVar ArrayRef branch where the evaluator does case (ao, final_tv) of PopOp/AppendOp/ordinary
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m5993_t001
- source:semantics/vyperStateScript.sml:906-938
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451 - working Value branch as contrast with only 3 subgoals from AllCaseEqs

## L0153 scope='' tags=
shape: resolve_array_element no-TypeError under target_path_step_type ArrayT constraint
pattern: resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) sbs st cannot return INR(TypeError) when the subscripts at ArrayTV levels are all ValueSubscript(IntV _). target_path_step_type env (Type (ArrayT elem_ty len)) sb next_vt forces sb = ValueSubscript(IntV _). So under target_path_type env (Type t) sbs (Type ty) where t contains ArrayT, resolve_array_element's TypeError clause (line 833-834 of vyperStateScript.sml) is unreachable. The check/assert calls for bounds only raise RuntimeError.
works_when: Proving no_type_error_result for ArrayRef assignment target paths where target_path_type constrains the subscripts through ArrayT levels
evidence:
- source:semantics/vyperStateScript.sml:833-834 - TypeError clause for non-IntV subscript
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:269-270 - target_path_step_type forces ValueSubscript(IntV _) at ArrayT level
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:102-121 - resolve_array_element_error

## L0155 scope='' tags=
shape: mp_tac + simp[Once assign_target_def] for resolve_array_element ArrayRef branch
pattern: For the ArrayRef branch of assign_target TopLevelVar: (1) qpat_x_assum assign_target equation mp_tac pushes it to goal, (2) simp[Once assign_target_def + bind/return/raise/lift defs] expands the do-block IN THE GOAL where simp can work, (3) lookup_global assumption matches ArrayRef so AllCaseEqs resolves the tv branch, (4) goal becomes case resolve_array_element ... of (lambda on final_tv), (5) Cases_on the resolve result + Cases_on q (INL/INR) + PairCases_on the triple + Cases_on final_tv dispatches each branch individually. The key difference from gvs blast: the lambda-case is beta-reduced AFTER PairCases_on destructure.
works_when: Proving no_type_error_result for ArrayRef branch of assign_target TopLevelVar where AllCaseEqs blast creates unresolvable lambda-case due to opaque resolve_array_element result
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6038_t001
- source:semantics/vyperStateScript.sml:906-938

## L0156 scope='' tags=
shape: resolve_array_element_error not in vyperTypeStatePreservationTheory scope
pattern: resolve_array_element_error is proved in vyperTypeAssignSoundnessScript.sml (line 102-121) but that theory is NOT an ancestor of vyperTypeStatePreservation. Need to either: (1) add vyperTypeAssignSoundness to the Ancestors list, or (2) prove a local copy of the lemma in vyperTypeStatePreservationScript.sml. The proof pattern uses ho_match_mp_tac resolve_array_element_ind >> rw[resolve_array_element_def, bind_apply, check_def, assert_def, return_def, raise_def, AllCaseEqs(), bound_CASE_rator] >> gvs[].
works_when: Need to classify resolve_array_element INR errors as RuntimeError (not TypeError) in vyperTypeStatePreservation proofs
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6042_t001
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:102-121

## L0157 scope='' tags=
shape: Cases_on order for resolve_array_element result in ArrayRef assign_target proofs
pattern: After Cases_on the resolve_array_element pair result (q,r): first Cases_on q (gives INL/INR), THEN for the INL case PairCases_on the inner triple to get (elem_slot,final_tv,remaining_subs). Do NOT try PairCases_on on the original pair (q,r) because q may be a sum type.
works_when: Destructuring the resolve_array_element result in ArrayRef assign_target proofs after the initial Cases_on split
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6040_t001

## L0158 scope='' tags=
shape: Stale holbuild checkpoint for ArrayRef assign_target branch proof
pattern: For assign_target_TopLevelVar_ArrayRef_branch_ntr: (1) Cases_on resolve_array_element result, (2) Cases_on q for INL/INR, (3) INR: drule resolve_array_element_error_local + Cases_on g + gvs[no_type_error_result_def], (4) INL: PairCases_on triple + step-by-step Cases_on final_tv (NOT AllCaseEqs) + for each constructor dispatch with 4-subgoal ordinary pattern (read_storage_slot success/write/assign_subscripts/assign_result). Insert all_tac >> before second Cases_on to break stale checkpoint. For ArrayTV Dynamic: Cases_on bd then Cases_on op separately.
works_when: Proving no_type_error_result for assign_target TopLevelVar ArrayRef branch where evaluator's case (ao, final_tv) of expression has multiple branches
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2409-2448
- source:semantics/vyperStateScript.sml:906-938
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6086_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2295-2351
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2388-2407

## L0159 scope='' tags=
shape: ArrayRef branch of assign_target TopLevelVar after resolve_array_element = 3 evaluator sub-cases
pattern: After resolve_array_element succeeds with (elem_slot, final_tv, remaining), assign_target ArrayRef does case (ao, final_tv): (1) (PopOp, ArrayTV _ Dynamic) => pop do-block: check non-empty + read last + write default + write decremented length + ret. (2) (AppendOp v, ArrayTV _ Dynamic n) => append do-block: check capacity + write new element + write incremented length + return NONE. (3) _ => ordinary read_storage_slot + assign_subscripts + write_storage_slot + assign_result. The ordinary case matches ALL BaseTV/TupleTV/StructTV/FlagTV/NoneTV/ArrayTV(Fixed)/ArrayTV(Dynamic)+Replace/Update. Prove with step-by-step Cases_on final_tv then scoped gvs[AllCaseEqs()] per branch.
works_when: Proving no_type_error_result for assign_target TopLevelVar ArrayRef branch
evidence:
- source:semantics/vyperStateScript.sml:906-938
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6096_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2295-2351

## L0160 scope='' tags=
shape: check b str always raises RuntimeError never TypeError in Vyper evaluator
pattern: check b str = assert b (Error (RuntimeError str)). So check failures produce INR (Error (RuntimeError msg)), never INR (Error (TypeError msg)). For no_type_error_result proofs: check INR branches resolve by simp[no_type_error_result_def] after extracting the RuntimeError form. No CCONTR_TAC needed.
works_when: Proving no_type_error_result for evaluator branches using check (e.g., array bounds checks in AppendOp/PopOp)
evidence:
- source:semantics/vyperStateScript.sml:177
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:38-42

## L0162 scope='' tags=
shape: HOL4 conjunction /\ in SML term quotations written via tool API
pattern: The API tools (replace_text, edit_lines) escape /\ to /&/ or /'/ in content parameters, breaking HOL4 syntax. Workaround: (1) use write_file for full file content, (2) restructure theorem to use nested ==> instead of /\, or (3) use CONJ in ML-level theorem construction. The existing codebase has /\ working fine - the corruption happens in tool content parameters only.
works_when: Writing HOL4 theorem statements with conjunction via tool API
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6196_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6198_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6200_t001

## L0164 scope='' tags=
shape: HOL4 conjunction in SML term quotations written via tool API
pattern: API tools (replace_text, edit_lines, append_file) escape backslash-slash to /&/ in content parameters. Workaround: (1) use nested implication (==>) instead of conjunction in theorem statements - logically equivalent and avoids backslash entirely, (2) use write_file for full file content which may preserve backslash correctly. Nested implication is the cleanest solution: change P / Q / R to P ==> Q ==> R in theorem statement, and change rpt conj_tac to rpt strip_tac in proof. For extraction of individual conclusions, use drule_all or first_x_assum drule to specialize the nested implications.
works_when: Writing HOL4 theorem statements with conjunction via tool API where backslash gets corrupted
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6198_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6200_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2409-2443

## L0165 scope='' tags=
shape: HOL4 conjunction //\ in SML term quotations written via tool API - use separate single-conclusion theorems
pattern: API tools (replace_text, edit_lines, append_file) escape /\ to /&/ in content parameters. Instead of trying to write /\, split the combined lemma into separate single-conclusion theorems (no /\ needed). For resolve_array_element specifically: leaf_type, ArrayTV_empty_rsubs, and well_formed_type_value preservation each have independent induction proofs with no cross-conclusion dependency because resolve_array_element only recurses on ArrayTV+ValueSubscript(IntV), not on StructTV. The previous claim that a combined conjunction lemma is needed was wrong.
works_when: Writing HOL4 theorem statements with conjunction via tool API where backslash gets corrupted. Especially for resolve_array_element properties which were previously claimed to need combined IH.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6198_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6200_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6265_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2409-2482 - three separate _sc theorems replacing corrupted combined _local lemma
- source:semantics/vyperStateScript.sml:816-836 - resolve_array_element_def showing recursion only on ArrayTV+IntV subs, StructTV is base case
- episode:E0055

## L0166 scope='' tags=
shape: resolve_array_element single-conclusion lemmas for assignment ArrayRef branch
pattern: Split resolve_array_element properties into separate single-conclusion theorems: leaf_type preservation (leaf_type tv subs = leaf_type final_tv rsubs), ArrayTV empty remaining (!etv ebd. final_tv = ArrayTV etv ebd ==> rsubs = []), and well_formed_type_value preservation. Each uses ho_match_mp_tac resolve_array_element_ind >> rw[resolve_array_element_def, bind_apply, ignore_bind_apply, check_def, assert_def, return_def, raise_def, AllCaseEqs(), bound_CASE_rator, leaf_type_def/well_formed_type_value_def, BETA_THM]. For StructTV BaseTV cases: these are BASE CASES (not recursive), so single-conclusion form works fine. For ArrayTV Fixed/Dynamic: first_x_assum (qspecl_then [`0`/`1`, `s''`] mp_tac) >> impl_tac >- simp[ADD_COMM] >> disch_then drule >> strip_tac >> gvs[].
works_when: Proving assignment ArrayRef branch properties of resolve_array_element. Previously claimed to need combined conjunction IH but that was WRONG - resolve_array_element only recurses on ArrayTV+ValueSubscript(IntV), StructTV is a base case.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2409-2482
- source:semantics/vyperStateScript.sml:816-836 - resolve_array_element_def showing recursion only on ArrayTV+IntV subs, StructTV is base case
- episode:E0055
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6265_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6267_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6269_t001

## L0167 scope='' tags=
shape: resolve_array_element induction proofs must use simp[Once resolve_array_element_def] not rw[resolve_array_element_def]
pattern: For ALL induction proofs over resolve_array_element (leaf_type, well_formed_type_value, ArrayTV_empty_rsubs, error classification, state preservation): use simp[Once resolve_array_element_def] AFTER pushing the resolve_array_element equation to goal position with mp_tac. Do NOT use rw[resolve_array_element_def, bind_apply, ...] which eagerly normalizes address expressions (n2w(elem_offset + Num idx * type_slot_size tv)) via ADD_COMM, creating IH-vs-goal mismatch where IH has 'Num idx * type_slot_size tv + 1' but goal has '1 + Num idx * type_slot_size tv'. The working reference proof is resolve_array_element_state in vyperStatePreservationScript.sml (lines 135-151).
works_when: Proving any property of resolve_array_element by induction where the recursive call's base address includes arithmetic (elem_offset + Num idx * type_slot_size elem_tv)
evidence:
- source:semantics/prop/vyperStatePreservationScript.sml:135-151
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6302_t002
- source:semantics/vyperStateScript.sml:816-836
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2409-2482 - broken rw version needing fix
- source:semantics/prop/vyperScopePreservationScript.sml:281-297 - another working Once-pattern example
- source:semantics/prop/vyperExprNoControlScript.sml:337-367 - another working Once-pattern example
- source:semantics/prop/vyperStatePreservationScript.sml:135-151 - canonical working example with FIRST dispatch for Fixed/Dynamic
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2388-2407 - resolve_array_element_error_local also works with rw but should adopt Once for consistency

## L0168 scope='' tags=
shape: resolve_array_element induction proof with simp[Once] + FIRST dispatch
pattern: For ALL induction proofs over resolve_array_element: ho_match_mp_tac resolve_array_element_ind >> rw[] >> qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >> simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >> rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, type_check_def, assert_def, AllCaseEqs()]) >> rpt strip_tac >> gvs[] >> gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >> imp_res_tac get_storage_backend_state >> gvs[] >> FIRST [first_x_assum (qspec_then `0` mp_tac) >> simp[] >> disch_then drule >> simp[], first_x_assum (qspec_then `1` mp_tac) >> simp[] >> disch_then drule >> simp[]]. The FIRST dispatch handles Fixed case (elem_offset=0) and Dynamic case (elem_offset=1).
works_when: Proving any property of resolve_array_element by induction where the recursive call's base address includes arithmetic that ADD_COMM would normalize differently
evidence:
- source:semantics/prop/vyperStatePreservationScript.sml:135-151
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6333_t002
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6353_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6355_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2409-2467 - current _sc helper theorems with Once pattern (untested due to checkpoint)

## L0169 scope='' tags=
shape: Dynamic array append/pop write_storage_slot INR subgoals need explicit value_has_type derivation
pattern: For write_storage_slot INR subgoals in AppendOp/PopOp dynamic array branches: (1) well_formed_type_value (BaseTV (UintT 256)) is trivial. (2) value_has_type (BaseTV (UintT 256)) (IntV (&(w2n(lookup_storage slot storage) +/- 1))) requires: 0i <= &(w2n(lookup_storage slot storage) +/- 1) and Num(&(w2n(lookup_storage slot storage) +/- 1)) < 2**256. Prove these with simp[integerTheory.INT_OF_NUM] + arithmetic + decide_tac. For AppendOp: w2n(..storage) < n < dimword(:256). For PopOp: w2n(..storage) <= n < dimword(:256) and 0 < w2n(..storage). Then simp[value_has_type_def] >> metis_tac[write_storage_slot_no_type_error_from_value_has_type].
works_when: Proving no_type_error_result for AppendOp/PopOp dynamic array write_storage_slot INR branches where the written value is an IntV of a modified storage length
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6414_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2580-2645 - pre-edit proof with explicit arithmetic reasoning (removed in this session)

## L0170 scope='' tags=
shape: AppendOp/PopOp dynamic array write needs explicit value_has_type for modified uint256 length
pattern: For write_storage_slot writing BaseTV(UintT 256) IntV of modified array length in AppendOp/PopOp branches: (1) For AppendOp: check gives w2n(lookup_storage slot storage) < n, Dynamic n means n is valid array size <= dimword(:256), so w2n(...) + 1 < 2^256. Derive value_has_type with simp[value_has_type_def, integerTheory.INT_OF_NUM] + decide_tac for range. (2) For PopOp: check gives w2n(...) > 0, so w2n(...) - 1 >= 0, and w2n(...) < dimword(:256), so w2n(...)-1 < 2^256. Then metis_tac[write_storage_slot_no_type_error_from_value_has_type] closes.
works_when: Proving no_type_error_result for AppendOp/PopOp dynamic array write_storage_slot INR branches where the written value is IntV of a modified array storage length
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6414_t001
- source:semantics/vyperStateScript.sml:906-938
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2581-2627

## L0172 scope='' tags=
shape: value_has_type (BaseTV (UintT 256)) (IntV i) for dynamic array length writes
pattern: To prove value_has_type (BaseTV (UintT 256)) (IntV &(stored_len +/- 1)) for AppendOp/PopOp: (1) From well_formed_type_value (ArrayTV elem_tv (Dynamic n)): n < dimword(:256) = 2^256. (2) From check: stored_len < n (AppendOp) or 0 < stored_len (PopOp). (3) AppendOp: stored_len + 1 <= n < 2^256, so simp[value_has_type_def, integerTheory.INT_OF_NUM] >> decide_tac. (4) PopOp: stored_len >= 1 means stored_len - 1 >= 0 and stored_len - 1 < 2^256, so simp[value_has_type_def] >> decide_tac. Then metis_tac[write_storage_slot_no_type_error_from_value_has_type].
works_when: Proving no_type_error_result for AppendOp/PopOp dynamic array write_storage_slot INR branches where written value is IntV of modified array storage length
evidence:
- source:semantics/prop/vyperTypingScript.sml:77-78 - value_has_type_def for UintT
- source:semantics/prop/vyperTypingScript.sml:41-44 - well_formed_type_value_def: Dynamic n gives n < dimword(:256)
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6414_t001 - metis failure for UintT 256 value_has_type
- episode:E0057

## L0173 scope='' tags=
shape: Deriving leaf_type <> NoneTV after resolve_array_element via equality chaining
pattern: When resolve_array_element_leaf_type_sc gives leaf_type tv subs = leaf_type final_tv rsubs and you already have leaf_type tv subs <> NoneTV in assumptions, use metis_tac[resolve_array_element_leaf_type_sc] (NOT fs[resolve_array_element_leaf_type_sc] >> NO_TAC) to chain the equalities and derive leaf_type final_tv rsubs <> NoneTV.
works_when: Proving leaf_type final_tv rsubs <> NoneTV inside ArrayRef branch of assign_target where leaf_type(ArrayTV...)(REVERSE sbs) <> NoneTV is available from target_path_type_Type_evaluate_leaf_not_NoneTV
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6476_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2509-2511
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2409-2427

## L0174 scope='' tags=
shape: Holbuild stale theory-context checkpoint workaround: insert dummy local theorem
pattern: When holbuild reports 'theorem-context checkpoint after X' and replays stale variable names, insert a trivial dummy [local] theorem AFTER theorem X but BEFORE the failing theorem. This forces holbuild to create a fresh theory-context checkpoint after the dummy. Renaming the failing theorem does NOT work because checkpoints are at theory-context level not theorem-name level.
works_when: Stale holbuild checkpoint at theory-context boundary causing auto-generated variable name mismatches in resumed proofs
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6488_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6506_t001
- episode:E0057
- episode:E0056
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2449-2469
- episode:E0051
- episode:E0049
- episode:E0047
- episode:E0045
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6517_t001
- episode:E0050
- episode:E0052

## L0175 scope='' tags=
shape: fs[top_level_vtype_well_formed, top_level_Type_storage_decl] corrupts env.type_defs matching in assignment proofs
pattern: Using fs[top_level_vtype_well_formed, top_level_Type_storage_decl] at proof start rewrites env.type_defs to get_tenv cx in ALL assumptions via variable elimination. This destroys matching for downstream lemmas like target_path_type_Type_evaluate_leaf that use env.type_defs in their antecedent pattern. Solution: use rpt strip_tac + individual metis_tac calls to derive intermediate facts BEFORE gvs/fs rewrites env.type_defs. Or use single fs[] call that processes all needed lemmas sequentially before elimination per L0140.
works_when: Proving assignment boundary lemmas where env.type_defs = get_tenv cx is in assumptions and upstream adapter lemmas use env.type_defs in their antecedent
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6517_t001
- episode:E0049
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2484-2491

## L0176 scope='' tags=
shape: ArrayRef branch proof: use rename1 before Cases_on on auto-generated constructor components
pattern: After Cases_on x1 where x1 is a type_value, the ArrayTV constructor introduces auto-generated names (e.g. b' for the bound component). Use rename1 ArrayTV etv' abd >> Cases_on abd instead of Cases_on b' to avoid dependency on auto-generated names that differ between checkpoint replays and fresh execution.
works_when: Proving ArrayRef branch assignment target theorems where Cases_on on type_value constructors introduces auto-generated variable names
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6488_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2531-2533

## L0177 scope='' tags=
shape: Dummy local theorem breaks holbuild stale theory-context checkpoint
pattern: When holbuild replays stale state from a theory-context checkpoint, insert a trivial Theorem dummy: T Proof simp[] QED AFTER the last proved theorem but BEFORE the failing theorem. This forces holbuild to create a fresh theory-context checkpoint. Renaming the failing theorem does NOT work (checkpoints are theory-level not theorem-level).
works_when: Holbuild shows 'theorem-context checkpoint after X' and replays stale variable bindings despite proof edits
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6547_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6506_t001
- episode:E0058
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2469-2473 - dummy theorem assign_target_ArrayRef_checkpoint_break

## L0178 scope='' tags=
shape: ArrayRef branch assign_target no-TypeError proof after gvs[AllCaseEqs()] expansion
pattern: For each subgoal from gvs[AllCaseEqs()] in the ArrayRef branch: (1) success path: metis_tac[assign_result_no_type_error_from_successful_assign_split], (2) write_storage INR: metis_tac[assign_subscripts_preserves_type_runtime_typed] to get value_has_type then metis_tac[write_storage_slot_no_type_error_from_value_has_type], (3) assign_subscripts INR: spose_not_then strip_assume_tac >> metis_tac[assign_subscripts_no_type_error_runtime_typed, ...], (4) read_storage_slot INR: metis_tac[read_storage_slot_error]. NEVER use irule after gvs expansion.
works_when: Proving no_type_error_result for assign_target ArrayRef branch where gvs[AllCaseEqs()] has expanded the monadic do-block into 4 subgoals per type_value/operation case
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2648-2668
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6558_t001
- episode:E0058
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2520-2621 - current failing irule-based proof that needs conversion to metis_tac pattern

## L0179 scope='' tags=
shape: Monadic do-block proof for assign_target with nested bind/lift_sum/write_storage_slot
pattern: Do NOT use gvs[AllCaseEqs()] on monadic do-block goals after Cases_on a type_value variable. Instead: (1) extract boundary lemma for standard read+write+assign_result path modeled on assign_target_TopLevelVar_Value_branch_ntr, (2) handle special operations (AppendOp/PopOp) in separate boundary sub-lemmas with targeted Cases_on per intermediate result + drule/simp.
works_when: Proving no_type_error_result for assign_target where the goal contains case x1 of ... with nested monadic binds after simp[Once assign_target_def]
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6609_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2604-2646
- episode:E0059
- episode:E0058
- episode:E0057
- episode:E0056
- episode:E0054
- episode:E0031 (original 'NEVER use irule after gvs[AllCaseEqs()]' learning)

## L0180 scope='' tags=
shape: value_has_type for UintT 256 IntV of array length (append/pop count)
pattern: After gvs[assign_operation_runtime_typed_def, AllCaseEqs(), ...], the AppendOp length write needs: value_has_type (BaseTV (UintT 256)) (IntV &(w2n k + 1)). Derive from: w2n k < n (from check), n < dimword(:256) (from well_formed_type_value_def ArrayTV Dynamic case), so w2n k + 1 < 2^256. For IntV: 0 <= &(w2n k + 1) and Num(&(w2n k + 1)) = w2n k + 1 < 2^256 by integer_arith. PopOp is similar with w2n k - 1.
works_when: ArrayTV (Dynamic n) with AppendOp/PopOp length write branches
evidence:
- episode:E0056
- episode:E0057
- source:semantics/prop/vyperTypingScript.sml:34-52 (well_formed_type_value_def)

## L0181 scope='' tags=
shape: ArrayRef assign_target branch has 3 evaluator sub-cases requiring separate boundary lemmas
pattern: After resolve_array_element succeeds, ArrayRef branch of assign_target_def does case (ao, final_tv): (1) PopOp + ArrayTV Dynamic => pop do-block, (2) AppendOp v + ArrayTV Dynamic n => append do-block, (3) _ => ordinary read+write+assign_result. Extract separate boundary lemmas for each: ordinary_ntr (like Value branch), append_ntr, pop_ntr. Do NOT use single gvs[AllCaseEqs()] blast across all cases.
works_when: Proving no_type_error_result for assign_target TopLevelVar ArrayRef branch
evidence:
- source:semantics/vyperStateScript.sml:906-938
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2609-2653
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6653_t001
- episode:E0059
- episode:E0054
- episode:E0031

## L0182 scope='' tags=
shape: value_has_type (BaseTV (UintT 256)) (IntV (&n)) for storage array length writes
pattern: Use rewrite_tac[value_has_type_def, integerTheory.NUM_OF_INT, integerTheory.INT_POS] >> rpt strip_tac >> decide_tac for sub-range reasoning + metis_tac[arithmeticTheory.LESS_TRANS] for the 2^256 bound. decide_tac alone cannot handle 2^256 as a concrete number. Pattern from vht_uint_bound in vyperBuiltinTypingScript.sml.
works_when: Proving value_has_type (BaseTV (UintT 256)) (IntV (&(stored_len +/- 1))) for dynamic array AppendOp/PopOp length writes where stored_len < n and n < dimword(:256) = 2^256
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6707_t001
- source:semantics/prop/vyperBuiltinTypingScript.sml:1100-1106
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2475-2500 - proved storage_array_append/pop_len_value_has_type lemmas

## L0183 scope='' tags=
shape: ArrayRef ordinary boundary lemma for assign_target TopLevelVar
pattern: The ordinary ArrayRef boundary lemma MUST use strong exclusion hypotheses: op <> PopOp /\ (!v. op <> AppendOp v). With these, the case (op, final_tv) in assign_target_def resolves entirely to the _ branch (ordinary read+write+assign_result path), producing exactly 4 subgoals from gvs[AllCaseEqs()]: (1) assign_result success, (2) write_storage_slot INR, (3) assign_subscripts INR, (4) read_storage_slot INR. This matches the HashMapRef pattern. Weak conditional exclusions (op=PopOp => final_tv<>ArrayTV Dynamic) do NOT work because AllCaseEqs/Cases_on must still split on both op and final_tv.
works_when: Proving no_type_error_result for the ordinary (non-PopOp/non-AppendOp) branch of assign_target TopLevelVar ArrayRef where the _ branch in assign_target_def fires
evidence:
- source:semantics/vyperStateScript.sml:906-938 - ArrayRef branch showing case (ao, final_tv) of PopOp+Dynamic/AppendOp+Dynamic/_
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2295-2351 - HashMapRef 4-subgoal pattern as model
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6760_t001 - weak exclusion timeout
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6762_t001 - Cases_on explosion timeout

## L0184 scope='' tags=
shape: ArrayRef assign_target gvs expansion produces too many subgoals from nested case (op, final_tv)
pattern: For ArrayRef branches: use Cases_on `final_tv` >> gvs[CaseEq "type_value", bind_def, lift_sum_def, return_def, raise_def, AllCaseEqs(), no_type_error_result_def] to split into ~21 goals. Then for each goal, derive assign_subscripts = INL new_val via Cases_on `assign_subscripts ...` >> gvs[return_def, raise_def], then chain through read_storage_slot_success_type, assign_subscripts_preserves_type_runtime_typed, etc.
works_when: Proving ArrayRef branch of assign_target, where case (ao, final_tv) of ... creates nested 2D case split. Strong exclusion hypotheses (op<>PopOp / !v.op<>AppendOp v) prevent Dynamic-array special branches.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6808_t001
- source:semantics/vyperStateScript.sml:906-938
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2311-2351
