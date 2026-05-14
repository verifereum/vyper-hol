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

## L0011 scope='' tags=
shape: HOL4 conjunction in source written through API
pattern: When the API corrupts /\ to /¥ or /&, use Unicode ∧ instead. HOL4 accepts ∧ in Definition and Theorem statement contexts. The 'No rule for [==>]' error was from missing theorem conclusion, not from ∧.
works_when: Writing HOL4 conjunction operators through API tools that corrupt backslashes
evidence:
- episode:E0005

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

## L0015 scope='' tags=
shape: Theorem statements written through API with conjunction
pattern: The API corrupts /\ (backslash-conjunction) to /¥. Use only nested ==> in theorem statements to avoid Unicode corruption. HOL4 accepts !x. P x ==> Q x ==> R x as equivalent to !x. P x /\ Q x ==> R x.
works_when: Writing new theorem statements through replace_text/edit_lines/write_file
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m0991_t001
- tool_output:TO_type_system_rewrite-20260513T211025Z_m1009_t001
- episode:E0005 (from prior session LEARNINGS)

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

## L0046 scope='' tags=
shape: HOL4 existential witness from option pair result in by-subgoal
pattern: When proving exists x y z. f a = SOME (x,y,z) from f a <> NONE + Cases_on f a >> gvs[], the SOME case gives f a = SOME x' where x' is a pair. Need PairCases_on x' >> gvs[] then explicitly witness: qexistsl [x0,x1,x2] >> simp[]. Do NOT rely on metis_tac[] or gvs[] alone to close the existential goal.
works_when: Extracting components from an option-wrapped pair result in a by-subgoal, especially split_hashmap_subscripts results
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2272_t001

## L0047 scope='' tags=
shape: HOL4 existential witness from option pair result in by-subgoal
pattern: When proving ?x y z. f a = SOME (x,y,z) from f a ≠ NONE in a by-subgoal: qpat_x_assum `f a ≠ NONE` mp_tac >> simp[option_neq_none_imp_is_some, optionTheory.IS_SOME_EXISTS] >> rpt strip_tac >> qexistsl [`FST x'`, `FST (SND x')`, `SND (SND x')`] >> Cases_on `x'` >> Cases_on `r` >> simp[pairTheory.PAIR]. Do NOT use Cases_on the option result directly - it fails to substitute the ≠ NONE in assumptions.
works_when: Extracting components from an option-wrapped pair/triple result where the NONE case contradicts a ≠ NONE assumption. The IS_SOME_EXISTS bridge converts ≠ NONE to ∃, making the existential trivial.
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2318_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1760-1764
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2197-2205

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
