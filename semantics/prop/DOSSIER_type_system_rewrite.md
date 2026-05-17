# DOSSIER: type_system_rewrite

PLAN: `semantics/prop/PLAN_type_system_rewrite.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C0.1 | stuck | other | E0004 | "Escalate to plan_oracle for C0 resolution: authorize type_builtin_result_ok repair for AbiEncode branch, adding vyper_abi_size_bound condition" |
| C1 | progressed | plan_incomplete | E0005 | Escalate to plan_oracle: C1 needs decomposition into subcomponents for (1) the vyper_to_abi success lemma and (2) the enc-length-bound lemma, before the 3 success-typing branches are provable. |
| C1.1 | proved |  | E0151 |  |
| C1.2 | stuck | unknown | E0156 |  |
| C2.1.a | progressed | other | E0001 | Progress to C2.1.b (HashMapRef proof) or C2.1.c (ArrayRef proof), or C2.2.a (ImmutableVar proof) using the probe evidence |
| C3.1 | stuck | other | E0099 | "Rewrite assign_target_TopLevelVar_no_type_error Type branch using irule approach: (1) Save env.type_defs=get_tenv cx with pop_assum mk_asm before any fs/gvs, (2) expand assignable_context via mp_tac+simp+strip_tac+PairCases_on+Cases_on (getting code, p, p0=StorageVarDecl/HashMapVarDecl), (3) Cases_on evaluate_type/Cases_on lookup_var_slot for witnesses, (4) For each Cases_on x subgoal: FIRST use irule boundary_theorem to see exact required premises, then derive each individually. If irule produces a premise gap, prove an adapter lemma." |
| C3.1.2 | proved |  | E0025 |  |
| C3.1.3 | proved |  | E0027 |  |
| C3.1.4 | proved |  | E0100 |  |
| C3.1.5 | proved |  | E0101 |  |
| C3.1.6 | progressed | other | E0034 |  |
| C3.1.7 | stuck | other | E0041 | Fix the vt=Type contradiction proof at line 2419-2424. Replace PairCases_on p + Cases_on p0 + metis_tac with mp_tac of lookup_global equation + simp[lookup_global_def,...] blast approach. Also verify the HashMapT case (lines 2426-2438) metis_tac[top_level_HashMapRef_assign_no_type_error] works for premise matching. |
| C3.1.7.1 | progressed | tool_limit | E0043 | Test holbuild DISCH_THEN issue by editing 5 cheats and building. If metis_tac works inside Resume blocks, simple replacement will close component. |
| C3.1.7.1.3 | progressed | plan_incomplete | E0044 | "Prove adapter facts: (1) well_formed_vtype (get_tenv cx) (Type t) from runtime_consistent assumptions, (2) evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)) via target_path_type_Type_place_leaf_typed + place_leaf_typed_evaluate_type, (3) leaf_type root_tv (REVERSE sbs) <> NoneTV via assignable_type_evaluate_not_NoneTV. Then caller proof uses r=st (lookup_global_state) + these adapter facts to satisfy drule_all of the boundary theorem." |
| C3.1.7.1.3.1 | progressed | other | E0052 |  |
| C3.1.7.1.3.2 | proved |  | E0053 |  |
| C3.1.7.3 | stuck | plan_incomplete | E0059 | Write boundary lemma assign_target_TopLevelVar_ArrayRef_ordinary_no_type_error for the standard read+write+assign_result path (all non-ArrayTV-Dynamic cases), modeled on assign_target_TopLevelVar_Value_branch_ntr. Then handle AppendOp/PopOp separately." |
| C3.1.7.3.1 | stuck | wrong_statement | E0063 |  |
| C3.1.7.3.2 | proved |  | E0060 |  |
| C3.2 | progressed | other | E0085 |  |
| C3.3 | proved |  | E0086 |  |
| C3.4 | proved |  | E0087 |  |
| C3.5 | proved |  | E0089 |  |
| C3.6 | proved |  | E0106 |  |
| C4 | progressed | unknown | E0105 |  |
| C4.2 | stuck | missing_helper | E0160 | "Rewrite ecrecover_no_type_error proof using EL-index approach or BuiltinTyping simp pattern. All boundary lemmas are proved. Consumer just needs correct variable connection." |
| C4.2.1 | proved |  | E0161 |  |
| C4.2.2 | progressed | other | E0162 |  |
| C5.2 | stuck | plan_incomplete | E0113 |  |
| C5.2.1 | proved |  | E0114 |  |
| C5.2.2 | proved |  | E0115 |  |
| C5.2.3 | proved |  | E0116 |  |
| C5.2.4 | proved |  | E0120 |  |
| C5.2.6 | progressed | plan_incomplete | E0121 | Move to C5.2.7 checkpoint then C5.3 |
| C5.2.7 | progressed | plan_incomplete | E0122 | Move to C5.3 (AnnAssign lemmas, Risk 1, no dependency on TopLevelVar gap). Then escalate C5 architectural gap via plan_oracle. |
| C5.3 | proved |  | E0123 |  |
| C5.4 | stuck | risk_mismatch | E0124 |  |
| C5.4.1 | proved |  | E0125 |  |
| C5.4.2 | proved |  | E0126 |  |
| C5.4.3 | proved |  | E0130 |  |
| C5.4.5 | proved |  | E0132 |  |

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

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0151`
- blocker: 

### Attempts / Evidence

- `E0133` (progressed, plan_incomplete)
  - Proved [local,simp] iff rewrite lemmas for value_has_type at all BaseTV/FlagTV constructors. Also proved is_int_type_imp_IntV. Main theorem proof still uses one-shot gvs which explodes. -> Boundary lemmas proved. Main theorem proof structure wrong - needs per-bop-case handling. ()
- `E0134` (progressed, plan_incomplete)
  - Tried multiple proof structures for well_typed_binop_no_type_error: (1) gvs[type predicates] then mp_tac + simp[evaluate_binop_def] + IF_CASES_TAC - closes 52/56 goals, 4 remain with msg ≠ 'binop'. (2) gvs then fs[evaluate_binop_def] - fs can't split if-then-else in assumptions. (3) simp instead of gvs for type predicates - doesn't eliminate impossible cases. -> 52/56 goals closed by mp_tac+simp+IF_CASES_TAC; 4 remaining goals have 'msg ≠ binop' conclusion suggesting possible counterexamples or proof-engineering artifacts from gvs variable elimination ()
- `E0135` (progressed, plan_incomplete)
  - Rewrote well_typed_binop_no_type_error to use structured type/value resolution then simp[evaluate_binop_def] instead of gvs+fs approach. Key insight: error = RuntimeError string | TypeError string, so INR(RuntimeError _) ≠ INR(TypeError msg) automatically. After gvs resolves type constructors from well_typed_binop_def and value constructors from value_has_type iff lemmas, simp[evaluate_binop_def] on the ∀msg conclusion directly rewrites if-then-else in the conclusion (not stuck in assumption like fs). IF_CASES_TAC splits remaining conditionals. Build not yet verified. -> Proof rewritten but not yet verified by holbuild - session ended before build test. ()
  - Previous approach: gvs[type predicates] >> fs[evaluate_binop_def] >> rpt(IF_CASES_TAC >> fs[]) -> Closed 52/56 goals. 4 remaining with msg ≠ 'binop' conclusion - gvs variable elimination moves ≠ to assumption, creating F-goal; fs cannot split if-then-else in assumptions; IF_CASES_TAC only works on conclusion. ()
  - Proved [local,simp] iff lemmas for value_has_type at BaseTV/FlagTV constructors (vht_BaseTV_UintT, etc.) -> Helpers proved and in source. These let gvs derive value constructors from value_has_type when type_value is known. ()
- `E0136` (progressed, plan_incomplete)
  - FAIL_TAC probe after Cases_on bop >> gvs[well_typed_binop_def] >> TRY type resolution -> 31 remaining goals; base_type b still free; need per-operator approach (`TO_type_system_rewrite-20260516T153850Z_m18171_t001`)
- `E0137` (progressed, plan_incomplete)
  - Tried multiple proof structures for well_typed_binop_no_type_error: (1) gvs[well_typed_binop_def] then Cases_on for type resolution then simp[evaluate_binop_def] - gvs variable elimination creates F-goals from ∀msg inequality, (2) TRY block chains with gvs - rpt(TRY...) loops/times out, Cases_on is_int_type ty doesn't work when some bop cases don't have is_int_type, (3) Current broken attempt: Cases_on is_int_type ty forces case split on all 31 subgoals but many don't have is_int_type ty -> None of these approaches work because gvs with the ∀msg. ... ≠ INR(TypeError msg) conclusion does variable elimination creating F-goals that can't be simplified. The fundamental issue is: gvs strips ∀msg, creates equation from negation, moves to assumption, sets goal to F. Then evaluate_binop_def with if-then-else in assumptions can't be split by simp/fs. Must avoid gvs for the final evaluate_binop step. ()
  - Per-operator approach using vyperEvalBinopScript lemmas (22 proved lemmas giving INL results) - NEVER ATTEMPTED despite 4+ sessions of L0613/L0621/L0624 explicitly recommending it -> Not attempted - tunnel vision on one-shot gvs/simp approaches instead ()
- `E0138` (progressed, plan_incomplete)
  - disch_tac + gvs[well_typed_binop_def] + type resolution TRY Cases_on + gen_tac >> simp[evaluate_binop_def] -> Major progress: disch_tac prevents gvs variable elimination on ∀msg. After Cases_on bop >> gvs[well_typed_binop_def] >> gvs[evaluate_type_def, type_to_int_bound_def, is_int_type_def, ...] >> TRY Cases_on t1/t2/ty/b/b' for type resolution >> TRY Cases_on result_tv/tv1/tv2 for value resolution via vht_* lemmas >> gen_tac >> simp[evaluate_binop_def, binop_negate_def], 42 of 56 goals close. 14 remaining goals have if-then-else in conclusion (Div/Mod/UnsafeDiv with divisor=0 check). simp cannot split these conditionals. (`tool_output:TO_type_system_rewrite-20260516T153850Z_m18372_t001`, `tool_output:TO_type_system_rewrite-20260516T153850Z_m18367_t001`)
  - gvs-based approach with Cases_on v1/v2 -> Cases_on v1 >> gvs[] caused 2031-goal explosion because v1 has many constructors and gvs expands every case. Must resolve type variables first, then let vht_* lemmas determine value constructors. (`tool_output:TO_type_system_rewrite-20260516T153850Z_m18339_t001`)
- `E0139` (progressed, plan_incomplete)
  - fs[value_has_type_def] for value resolution (instead of gvs[value_has_type_def, evaluate_binop_def]) then gvs[evaluate_binop_def, binop_negate_def] at end -> Key fix: fs preserves forall-msg in conclusion, avoiding unsolvable msg!=binop goals. But gvs at end cannot split if-then-else under forall-msg. 14 remaining goals: forall-msg. (if i'=0 then INR(RuntimeError) else bounded_int_op...) != INR(TypeError msg). Both branches trivially != TypeError. ()
  - rpt strip_tac >> CASE_TAC >> simp[] after gvs -> strip_tac strips forall-msg and does variable elimination creating F-goal - the L0629 pitfall confirmed again ()
  - COND_CASES_TAC >> simp[] after gvs (not yet tested) -> Not yet tested - handoff came before build completed. COND_CASES_TAC should split if-then-else in conclusion even under forall-msg. ()
- `E0140` (progressed, plan_incomplete)
  - CCONTR_TAC approach: gen_tac >> disch_tac >> gen_tac >> CCONTR_TAC >> Cases_on bop >> gvs[well_typed_binop_def] >> gvs[evaluate_type_def,...] >> TRY Cases_on type vars >> gvs >> fs[value_has_type_def] for value resolution >> gvs[evaluate_binop_def, binop_negate_def, AllCaseEqs()] -> FAIL_TAC probe confirmed 56 goals with correct shape (all value constructors resolved, goal is F with evaluate_binop = INR(TypeError msg) assumption). But gvs[evaluate_binop_def, binop_negate_def, AllCaseEqs()] fails with 'no theorem proved' - likely tactic timeout or AllCaseEqs() blowup on 56 goals. (`TO_type_system_rewrite-20260516T153850Z_m18467_t001`, `TO_type_system_rewrite-20260516T153850Z_m18480_t001`)
- `E0141` (progressed, plan_incomplete)
  - CCONTR_TAC + gvs[evaluate_binop_def, binop_negate_def] (with and without AllCaseEqs()) -> FAIL_TAC probe confirmed 56 correct goals after CCONTR_TAC + type/value resolution. gvs[evaluate_binop_def] on 56 goals fails - likely tactic timeout. AllCaseEqs() made it worse. Without AllCaseEqs() still failed. (`TO_type_system_rewrite-20260516T153850Z_m18502_t001`, `TO_type_system_rewrite-20260516T153850Z_m18498_t001`)
  - pop_assum (mp_tac o REWRITE_RULE[evaluate_binop_def]) approach -> Never actually tested - replace_text failed due to whitespace mismatch in the same session. Approach is theoretically sound: rewrite evaluate_binop_def in the specific assumption, push to goal, split conditionals. ()
- `E0142` (progressed, plan_incomplete)
  - disch_tac+gen_tac + simp[evaluate_binop_def, binop_negate_def] + rpt(COND_CASES_TAC >- simp[]) + pairarg_tac + COND_CASES_TAC + simp[] -> Closes 42/56 goals after initial simp. After COND_CASES_TAC, splits conditionals for Div/Mod/UnsafeDiv/Exp. Remaining 14 goals: 10 are bounded_int_op/wrapped_int_op/bounded_decimal_op ≠ INR(TypeError msg) (should close by [local,simp] helpers) and 4 are msg ≠ 'binop' from ShL/ShR let-binding residue. Final simp[] does NOT close all 14 goals. (`tool_output:TO_type_system_rewrite-20260516T153850Z_m18545_t001`, `tool_output:TO_type_system_rewrite-20260516T153850Z_m18546_t001`, `tool_output:TO_type_system_rewrite-20260516T153850Z_m18555_t001`)
  - Added int_bound_bits_def to simp set -> Same 14 goals remain - int_bound_bits_def doesn't help (`tool_output:TO_type_system_rewrite-20260516T153850Z_m18545_t001`)
  - Added pairarg_tac + simp[] between COND_CASES_TAC rounds for ShL/ShR let bindings -> Still 14 goals remain - pairarg_tac doesn't eliminate all let issues, final build still fails (`tool_output:TO_type_system_rewrite-20260516T153850Z_m18557_t001`)
- `E0143` (progressed, plan_incomplete)
  - Inversion lemma + Excl + vht_ArrayTV_exists + binop_negate_INL/INR approach for well_typed_binop_no_type_error -> Fixed broken vht_ArrayTV (was wrong iff, now correct forward-only). Fixed broken binop_negate_no_type_error (was FALSE, replaced with binop_negate_INL/INR). Fixed is_bool_type_inv proof. Main theorem still fails to close - proof structure with one-shot simp[evaluate_binop_def] + COND_CASES_TAC leaves residual goals. (`TO_type_system_rewrite-20260516T153850Z_m18824_t001`)
  - Same one-shot approach from E0138-E0142 with Excl + inversion lemmas -> Same fundamental issue: after type+value resolution, expanding evaluate_binop_def across all bop cases simultaneously leaves residual conditional goals that simp cannot close. Need per-operator decomposition. (`TO_type_system_rewrite-20260516T153850Z_m18816_t001`)
- `E0144` (progressed, plan_incomplete)
  - Read full evaluate_binop_def (413 lines), all 22 evaluate_binop_* lemmas in vyperEvalBinopScript.sml, well_typed_binop_def (21 bop cases), is_Unsigned_def (has [simp]), and current well_typed_binop_no_type_error proof attempt. Confirmed build fails. Did NOT implement per-operator helper approach - session used for investigation only. -> Full source read completed. Confirmed is_Unsigned_def has [simp] so it should resolve. Confirmed 22 evaluate_binop_* lemmas exist. The per-operator helper approach is the correct next step but was not attempted this session. ()
- `E0145` (progressed, plan_incomplete)
  - Implemented per-operator no-TypeError helper approach for well_typed_binop_no_type_error: added ~40 [local] helpers (binop_no_type_error_Add, binop_no_type_error_Div, etc.), each trivially provable by simp[evaluate_binop_def] (+ COND_CASES_TAC for conditional branches). Main theorem dispatches by irule to matching helper after type/value resolution. -> Helpers written and main theorem rewritten. Build attempted but output truncated/unclear - many holbuild parse warnings about 'expected QED' from single-line Proof...QED format. Need to verify build result and potentially reformat Proof/QED to separate lines. ()
  - Also confirmed: ShL/ShR return INR(RuntimeError) for negative shift, NOT TypeError. L0651 potential counterexample was wrong - the theorem IS true. All TypeError in evaluate_binop comes from value-mismatch fallback branches only. -> Key insight: TypeError in evaluate_binop_def ONLY appears in value-mismatch fallback branches (| _ => INR(TypeError 'binop')). All real-error branches (div-by-zero, shift-negative, overflow) return INR(RuntimeError _). Since RuntimeError != TypeError by constructor distinctness, the theorem is unconditionally true for all well-typed inputs. ()
- `E0146` (progressed, plan_incomplete)
  - Fixed single-line Proof/QED format (replace_all Proof simp[evaluate_binop_def] QED -> multi-line). Fixed conditional helpers needing rpt gen_tac before COND_CASES_TAC. All per-operator helpers now compile. Main theorem still fails: irule approach has 62 unresolved goals because inversion lemmas were in TRY(fs[inv] >> NO_TAC) which reverts their effect; CCONTR_TAC approach with gvs[evaluate_binop_def] also fails - 'no theorem proved'. -> Per-operator helpers compile; root cause of main theorem failure identified: inversion lemmas (is_int_type_inv etc.) are applied inside TRY that reverts them, leaving type variables unresolved. ()
- `E0147` (progressed, other)
  - Replaced simp[evaluate_binop_def] with gvs[evaluate_binop_def, Excl bounded_int_op_def, Excl bounded_decimal_op_def, Excl wrapped_int_op_def, AllCaseEqs(), LET_THM] to expand evaluate_binop in assumptions without expanding bounded/wrapped ops -> Reduced remaining goals from 86 to 37 after excluding bounded/wrapped definitions from gvs. The equation bounded_int_op (Unsigned n) (i+i') = INL v now appears in assumptions correctly. But imp_res_tac bounded_int_op_INL still leaves 37 goals unsolved - the inversion lemma matching or subsequent gvs[] closure needs investigation. (`TO_type_system_rewrite-20260516T153850Z_m19481_t001`)
  - Used FAIL_TAC probe to see remaining goals after TRY blocks for bounded_int_op_INL/bounded_decimal_op_INL/wrapped_int_op_INL -> 37 remaining goals with shape: assumptions include bounded_int_op/wrapped_int_op/bounded_decimal_op equations, goal is value_has_type for the result. Typical case: bounded_int_op (Unsigned n) (i+i') = INL v with goal exists i. v = IntV i / 0 <= i / Num i < 2**n (`TO_type_system_rewrite-20260516T153850Z_m19479_t001`)
- `E0148` (progressed, other)
  - Ported helper lemmas from vyperTypeSoundnessHelpersScript.sml: int_div_lt_imp (mangled statement), decimal_mul_word_bound, int_shift_right_nonneg/neg_bounds/within_bound/unsigned_within_bound, int_bitwise_eq_BITWISE/nat_bound, int_shift_left_unsigned/signed_within_bound (references nonexistent int_bitwiseTheory.int_shift_left_bound), wrapped_int_op_INL_Unsigned/Signed. Inserted 270 lines at lines 728-999. -> Helpers inserted but have CRITICAL syntax bug: / used instead of /\ for conjunction in all theorem statements and some SML tactic terms. Also int_div_lt_imp has wrong statement, int_shift_left helpers reference nonexistent theorem. Build not tested. ()
- `E0149` (progressed, other)
  - Fixed all / vs /\ syntax bugs in helper lemmas lines 728-999: replaced / with /\ in theorem statements, fixed int_div_lt_imp to match original statement, deleted int_div_lt_imp_simple, deleted broken int_shift_left_unsigned_within_bound and int_shift_left_signed_within_bound (referenced nonexistent int_bitwiseTheory.int_shift_left_bound), fixed wrapped_int_op_INL_Unsigned/Signed statements -> All syntax fixes applied. Most helpers compile (int_div_lt_imp, decimal_mul_word_bound, shift_right helpers, int_bitwise helpers all proved). But wrapped_int_op_INL_Unsigned proof fails: drule wrapped_int_op_INL >> simp >> disch_then approach doesn't work correctly for getting the existential result out of the INL inversion. (`TO_type_system_rewrite-20260516T153850Z_m20076_t001`)
- `E0150` (progressed, plan_incomplete)
  - Fixed wrapped_int_op_INL_Unsigned/Signed proofs: replaced drule wrapped_int_op_INL >> simp >> disch_then with imp_res_tac wrapped_int_op_INL >> gvs[within_int_bound_def]. Both now compile. -> INL inversion helpers now compile. Main well_typed_binop_success_type proof still has 26 remaining goals at FAIL_TAC probe. Rewrote TRY blocks with per-family dispatch: wrapped_int_op specialized lemmas, decimal_mul_word_bound, ExpMod via w2n_lt, flag bitwise via int_bitwise_nat_bound, ShL via int_mod/signed_int_mod, ShR via int_shift_right bounds. (`TO_type_system_rewrite-20260516T153850Z_m20089_t001`)
  - Replaced after-gvs TRY blocks for well_typed_binop_success_type with per-family handlers for: bounded_int_op_INL, bounded_decimal_op_INL, wrapped_int_op_INL_Unsigned/Signed, decimal_mul_word_bound, ExpMod w2n_lt, flag bitwise (int_and/or/xor via int_bitwise_nat_bound), ShL (int_mod/signed_int_mod_within_bound), ShR (int_shift_right_within_bound/unsigned_within_bound). -> Edit applied but NOT yet built. Known syntax issues: flag bitwise term quotations for $/\, $\/, and XOR lambda need proper HOL4 backtick syntax. ShL/ShR irule approach may fail because gvs already expanded within_int_bound_def in the goals, so goals are 0 <= expr /\ Num expr < 2**n rather than within_int_bound form. ()
- `E0151` (proved, )
  - Fix int_shift_right_unsigned_Num_bound (gvs resolved conjunction, conj_tac failed) then use Num_int_lt + INT_LT_LE for Num monotonicity; fix w2n_word_exp_lt_256 (irule match failure with 2**256 vs dimword) by changing lemma to use dimword(:256); remove FAIL_TAC probe from well_typed_binop_success_type -> All three C1.1 theorems proved cheat-free: well_typed_binop_no_type_error, well_typed_binop_success_type, well_typed_update_binop_no_type_error. Build passes. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m20217_t002` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m20238_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m20264_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m20269_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m20290_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `stuck`
- diagnosis: `unknown`
- latest episode: `E0156`
- blocker: fs[]/gvs[] consume value_has_type (BaseTV (UintT 256)) sv/lv via [local,simp] iff lemma vht_BaseTV_UintT before boundary lemma evaluate_slice_BytesT_no_type_error can use them. Need Excl approach or proof restructuring.

### Attempts / Evidence

- `E0152` (progressed, missing_helper)
  - slice_no_type_error: Cases_on vs/ts decomposition + evaluate_type_BaseT + gvs resolves types + Cases_on fv + gvs[value_has_type_def] + expand evaluate_slice with AllCaseEqs/dest_NumV_def -> All type resolution works. Stuck on closing dest_NumV(IntV i)=NONE branch: AllCaseEqs splits dest_NumV into NONE/SOME but NONE branch has 0≤i ∧ i<0 contradiction that neither gvs nor intLib.ARITH_TAC closes (`TO_type_system_rewrite-20260516T153850Z_m21673_t001`, `TO_type_system_rewrite-20260516T153850Z_m21669_t001`, `TO_type_system_rewrite-20260516T153850Z_m21660_t001`)
  - Tried simp[dest_NumV_def] after imp_res_tac vht_BaseTV_UintT instead of gvs to avoid case split -> simp resolves if-then-else using 0≤i assumption but still leaves dest_NumV(IntV i)=NONE from prior AllCaseEqs expansion - ordering issue (`TO_type_system_rewrite-20260516T153850Z_m21671_t001`)
- `E0153` (progressed, missing_helper)
  - dest_NumV_IntV_SOME boundary lemma: 0 <= i ==> dest_NumV (IntV i) = SOME (Num i), proved with intLib.ARITH_TAC for ~(i<0) then simp[dest_NumV_def] -> Proved successfully as local simp lemma. Key: intLib.ARITH_TAC closes ~(i < 0:int) from 0 <= i, then simp resolves the if-then-else in dest_NumV_def (`TO_type_system_rewrite-20260516T153850Z_m21708_t001`)
  - value_has_type_UintT_imp_dest_NumV_SOME: boundary lemma deriving dest_NumV = SOME from value_has_type (BaseTV (UintT n)) sv, uses vht_BaseTV_UintT + gvs[] -> Added but not yet build-tested. Should work since vht_BaseTV_UintT gives sv=IntV i, 0<=i and dest_NumV_IntV_SOME [simp] closes dest_NumV ()
  - slice_no_type_error: Cases_on all 3 values then gvs[vht_*] then simp[gvs evaluate_slice_def] -> 1458 subgoal case explosion from Cases_on value constructors. gvs with vht iff lemmas doesn't close impossible cases properly. Probe at tool_output:TO_type_system_rewrite-20260516T153850Z_m21746_t001 shows goal with [NoneV; NoneV; NoneV] - impossible values (`TO_type_system_rewrite-20260516T153850Z_m21746_t001`)
  - slice_no_type_error: imp_res_tac vht_BaseTV_UintT then gvs[] then simp[evaluate_builtin_def, evaluate_slice_def, ...] -> gvs[] leaves fv/sv/lv as free variables because vht iff rewrites create existential equations that gvs doesn't substitute. simp then can't resolve case patterns in evaluate_slice_def (`TO_type_system_rewrite-20260516T153850Z_m21730_t001`)
  - slice_no_type_error: imp_res_tac value_has_type_UintT_imp_dest_NumV_SOME then gvs[] then Cases_on fv only -> Not fully tested yet - this approach adds dest_NumV facts before expanding evaluate_slice, and only case-splits the first value (BytesV), avoiding the 1458-subgoal explosion ()
- `E0154` (progressed, missing_helper)
  - Prove evaluate_slice boundary lemmas taking concrete constructor args (BytesV bs, IntV i, IntV j), then use irule in consumer proofs -> Both boundary lemmas evaluate_slice_BytesV_no_type_error and evaluate_slice_StringV_no_type_error PROVED successfully using rw[evaluate_slice_def, LET_THM] + Cases_on. Consumer proofs still failing at witness extraction step - drule on vht iff lemmas fails because prior gvs[] consumed the value_has_type assumptions by [local,simp] vht rule rewrites. (`TO_type_system_rewrite-20260516T153850Z_m21828_t001`, `TO_type_system_rewrite-20260516T153850Z_m21834_t001`)
  - Cases_on fv >> gvs[vht_BaseTV_BytesT_Dynamic] to extract BytesV witness in consumer proof -> gvs fires vht iff for value_has_type, partially resolves to existential witnesses (bs, i, i' appear in assumptions) but does NOT substitute fv -> BytesV bs into evaluate_builtin assumption. fv remains as free variable. Subsequent gvs/rules can't close the evaluate_builtin assumption pattern. (`TO_type_system_rewrite-20260516T153850Z_m21828_t001`)
  - drule vht_BaseTV_BytesT_Dynamic >> strip_tac after gvs steps for witness extraction -> Fails with FIRST_ASSUM error - the value_has_type assumption was already consumed/rewritten by prior gvs[] which fired the [local,simp] vht rule. drule can't find a matching assumption. (`TO_type_system_rewrite-20260516T153850Z_m21834_t001`)
- `E0155` (progressed, missing_helper)
  - slice_no_type_error: gvs[evaluate_type_def, LET_THM, AllCaseEqs()] then drule vht_BaseTV_BytesT_Dynamic then irule evaluate_slice_BytesV_no_type_error -> drule fails because gvs consumed value_has_type assumptions via [local,simp] vht iff lemmas. fv/sv/lv remain as free variables in evaluate_builtin assumption. FIRST_ASSAM error. (`TO_type_system_rewrite-20260516T153850Z_m21857_t002`, `TO_type_system_rewrite-20260516T153850Z_m21843_t002`)
  - slice_no_type_error: gvs[Excl vht_BaseTV_BytesT_Dynamic, Excl vht_BaseTV_UintT, Excl vht_BaseTV_BytesT_Fixed] to preserve value_has_type, then Cases_on fv >> gvs[vht_BaseTV_BytesT_Dynamic] for witness extraction -> Fixed n' case survives because Excl prevents gvs from firing vht_BaseTV_BytesT_Fixed to close impossible cases. Two subgoals remain after Cases_on bd but only one handled by >-. (`TO_type_system_rewrite-20260516T153850Z_m21937_t001`)
  - slice_no_type_error: simp[evaluate_type_def, LET_THM, AllCaseEqs()] instead of gvs to avoid consuming value_has_type, then Cases_on fv >> gvs[vht_BaseTV_BytesT_Dynamic] -> simp doesn't resolve evaluate_type to concrete typed_values (x, x' remain as abstract Skolem variables). Cases_on fv >> gvs[vht_BaseTV_BytesT_Dynamic] can't match because value_has_type has abstract type argument, not concrete BaseTV (BytesT (Dynamic n)). First subgoal not solved. (`TO_type_system_rewrite-20260516T153850Z_m21942_t001`)
  - slice_no_type_error: after gvs[evaluate_type_def, LET_THM, AllCaseEqs()] let gvs fully consume value_has_type, then manually substitute fv/sv/lv and irule boundary lemma -> gvs DOES resolve types to concrete typed_values AND fires vht iff lemmas on value_has_type. bs/i/i' witnesses appear as assumptions. BUT gvs does NOT substitute fv=BytesV bs into evaluate_builtin assumption. fv/sv/lv remain free. irule evaluate_slice_BytesV_no_type_error fails because goal has [fv;sv;lv] not [BytesV bs;IntV i;IntV i']. (`TO_type_system_rewrite-20260516T153850Z_m21940_t001`)
- `E0156` (stuck, unknown)
  - Fix slice_no_type_error proof: resolve abstract type variables from evaluate_type_BaseT_SOME, then use boundary lemma evaluate_slice_BytesT_no_type_error to derive contradiction on F goal -> 6+ attempts failed. Core issue: fs[]/gvs[] with [local,simp] iff lemmas (vht_BaseTV_UintT, vht_BaseTV_BytesT_Fixed/Dynamic) consume value_has_type assumptions needed as boundary lemma premises. After fs[], UintT value_has_type is decomposed to sv=IntV i + bounds, and metis_tac cannot reconstruct it because 2^256 vs literal 11579...936 is opaque to FOL. Also tried: irule (fails on F goal shape), metis_tac[vht_BaseTV_UintT] (times out due to 2^256 gap), direct Cases_on (combinatorial explosion 729 subgoals). (`TO_type_system_rewrite-20260516T153850Z_m22074_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260516T153850Z_m22074_t001` (use `read_tool_output` for exact output)

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

- result: `stuck`
- diagnosis: `other`
- latest episode: `E0099`
- blocker: "assign_target_TopLevelVar_no_type_error Type branch: metis_tac on boundary theorems fails after expanding assign_target_assignable_context via mp_tac+simp+strip_tac+PairCases_on+Cases_on. The boundary theorems (assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error, top_level_HashMapRef_assign_no_type_error) are fully proved. The problem is pure proof-engineering: after expanding assignable_context, variable names change and/or fs[] eliminates env.type_defs=get_tenv cx, breaking metis matching. The irule diagnostic approach (identified in STATE/L0398) has NEVER been executed despite being the most promising approach across 10+ sessions."
- next: "Rewrite assign_target_TopLevelVar_no_type_error Type branch using irule approach: (1) Save env.type_defs=get_tenv cx with pop_assum mk_asm before any fs/gvs, (2) expand assignable_context via mp_tac+simp+strip_tac+PairCases_on+Cases_on (getting code, p, p0=StorageVarDecl/HashMapVarDecl), (3) Cases_on evaluate_type/Cases_on lookup_var_slot for witnesses, (4) For each Cases_on x subgoal: FIRST use irule boundary_theorem to see exact required premises, then derive each individually. If irule produces a premise gap, prove an adapter lemma."

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
- `E0090` (progressed, missing_helper)
  - Prove top_level_HashMapRef_assign_no_type_error by deriving branch lemma premises: env.type_defs=get_tenv cx, lookup_global=HashMapRef, decomp, split_leaf_runtime, compute_hashmap_slot, then drule_all branch lemma -> First attempt: drule_all split_leaf_runtime AFTER Cases_on/gvs failed because gvs substituted first_sub→LAST sbs, rest_subs→TL(REVERSE sbs), making the rest_subs variable unavailable for drule_all. Second attempt: reordered split_leaf_runtime BEFORE Cases_on/gvs, not yet build-verified. ()
- `E0091` (progressed, missing_helper)
  - Fix drule_all in top_level_HashMapRef_assign_no_type_error: change >> gvs[] >> drule_all to >- gvs[] >> metis_tac -> SUCCEEDED: top_level_HashMapRef_assign_no_type_error now builds clean. Key fix: (1) use >- gvs[] instead of >> gvs[] to scope substitution to NONE case, (2) use metis_tac instead of drule_all to avoid DISCH_THEN instrumentation assertion. ()
  - Write sound_TopLevelVar resume proof with Cases_on vt + branch lemmas -> FAILED at static error: assign_target_preserves_runtime_consistent_result not yet declared (defined later in file). Need to use cj 1 assign_target_preserves_state_well_typed_mutual instead. ()
- `E0092` (progressed, missing_helper)
  - gvs[assign_target_assignable_context_def, assign_target_assignable_def, IS_SOME_EXISTS, FORALL_AND_THM, pairTheory.FORALL_PROD, PULL_EXISTS] in sound_TopLevelVar resume block to expand predicate and dispatch to boundary theorems -> FAILED: gvs cannot expand assign_target_assignable_context in assumptions - it remains opaque (assumption 6 unchanged). Without expansion, get_module_code/find_var_decl_by_num facts never appear, and metis_tac[top_level_Type_storage_decl] fails with FOL_FIND no solution. Confirmed across 5+ attempts and 3 sessions. ()
  - Rebuild to confirm boundary theorem top_level_HashMapRef_assign_no_type_error is proved -> Build failed at sound_TopLevelVar resume. The boundary theorem IS proved but the resume cannot invoke it because gvs destroys the equation needed for premise matching. ()
- `E0093` (progressed, other)
  - fs[assign_target_assignable_context_def, assign_target_assignable_def, GSYM EXISTS_PROD, PULL_EXISTS] >> FAIL_TAC probe (Type branch) -> SUCCEEDED: fs expands assign_target_assignable_context in assumptions. Goal shows get_module_code, find_var_decl_by_num with case expression, etc. FIRST_ASSAM issue was from pairarg_tac, NOT from fs. (`tool_output:TO_type_system_rewrite-20260515T192259Z_m11231_t001`)
  - fs[...] >> Cases_on `p` >> gvs[] >> FAIL_TAC probe -> SUCCEEDED: Cases_on p >> gvs[] destructures the pair (q=FST p, r=SND p) without triggering FIRST_ASSAM error. Pairarg_tac was the FIRST_ASSAM trigger. (`tool_output:TO_type_system_rewrite-20260515T192259Z_m11233_t001`)
  - UNDISCH_TAC `assign_target_assignable_context cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) st` >> simp[...] -> FAILED: UNDISCH_TAC takes term not frag list, holbuild quotation parsing can't handle it. Type error: Can't unify term with 'a frag list. (`tool_output:TO_type_system_rewrite-20260515T192259Z_m11229_t001`)
  - fs[...] >> Cases_on `p` >> gvs[] >> Cases_on `q` >> fs[IS_SOME_EXISTS] >> metis_tac[top_level_Type_storage_decl] >> ... full Type+HashMapT branch proof -> PARTIALLY FAILED: fs+Cases_on approach works for expansion. Full proof compiles further but FOL_FIND 'no solution found' at a metis_tac call inside the Type/StorageVarDecl branch. Likely env.type_defs rewritten to get_tenv cx by fs[IS_SOME_EXISTS] or variable name mismatches after Cases_on p. (`tool_output:TO_type_system_rewrite-20260515T192259Z_m11235_t001`)
- `E0094` (progressed, missing_helper)
  - fs[assign_target_assignable_context_def, assign_target_assignable_def, GSYM EXISTS_PROD, PULL_EXISTS] >> Cases_on p >> fs[] >> Cases_on q >> imp_res_tac top_level_Type_storage_decl >> fs[IS_SOME_EXISTS] >> metis_tac[boundary_theorems] -> metis_tac fails with FOL_FIND 'no solution found' after fs expansion changes assumption variable names/shapes (`TO_type_system_rewrite-20260515T192259Z_m11275_t001`)
  - Same approach but with FAIL_TAC probe at StorageVarDecl branch -> FAIL_TAC probe confirmed proof reaches the right branch but holbuild instrumented log doesn't show intermediate goal state (`TO_type_system_rewrite-20260515T192259Z_m11266_t002`)
- `E0095` (progressed, missing_helper)
  - fs[assign_target_assignable_context_def, assign_target_assignable_def, GSYM EXISTS_PROD, PULL_EXISTS] >> Cases_on p >> fs[] >> Cases_on q >> imp_res_tac top_level_Type_storage_decl >> fs[IS_SOME_EXISTS] >> metis_tac[assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error, type_value_distinct, assign_target_TopLevelVar_ArrayRef_branch_no_type_error, lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef] -> fs expands assign_target_assignable_context in assumptions correctly. Cases_on p >> fs[] destructures pair (q=FST p, r=SND p). Cases_on q splits StorageVarDecl/HashMapVarDecl. But after fs[IS_SOME_EXISTS], metis_tac fails with FOL_FIND 'no solution found' because the expansion changed variable names/assumption shapes, breaking metis matching with boundary theorems. The boundary theorems are ALL proved - this is purely a tactic-matching issue. (`TO_type_system_rewrite-20260515T192259Z_m11275_t001`, `TO_type_system_rewrite-20260515T192259Z_m11231_t001`)
  - For HashMapT branch: fs[assign_target_assignable_context_def, ...] >> Cases_on p >> fs[] >> Cases_on q >> fs[IS_SOME_EXISTS] >> simp[assign_target_assignable_def] >> metis_tac[top_level_HashMapRef_assign_no_type_error] -> Same FOL_FIND failure - fs expansion changes assumption shapes making metis_tac unable to match top_level_HashMapRef_assign_no_type_error premises. (`TO_type_system_rewrite-20260515T192259Z_m11235_t001`)
- `E0096` (progressed, missing_helper)
  - Wrote adapter bridge lemmas TopLevelVar_Type_assignable_context_imp_StorageVarDecl_facts and TopLevelVar_HashMapT_assignable_context_imp_HashMapVarDecl_facts to isolate fs[assign_target_assignable_context_def] expansion damage inside their proofs, outputting clean existential witnesses. Rewrote wrapper assign_target_TopLevelVar_no_type_error to use drule_all bridge_lemma >> strip_tac instead of fs expansion in body. -> Bridge lemma approach is correct per STATE/L0359. Wrapper structure compiles ( Cases_on vt, drule_all, strip_tac, metis_tac pattern). BUT // conjunction in bridge lemma conclusions got corrupted to /@ by API (lines 3270-3272, 3296-3299) - syntax error prevents build. ()
- `E0097` (progressed, missing_helper)
  - Cases_on evaluate_type + Cases_on lookup_var_slot + gvs[IS_SOME_EXISTS] to extract witnesses -> Cases_on introduces witnesses but gvs[IS_SOME_EXISTS] over-destructures type_value (e.g. BaseTV b'), then Cases_on x fails because x was eliminated. The variable x from the option decomposition gets resolved by gvs. (`tool_output:TO_type_system_rewrite-20260515T192259Z_m11479_t001`)
  - mp_tac to push IS_SOME assumptions to goal position, then simp[IS_SOME_EXISTS] + strip_tac to introduce witnesses -> Written to file but NOT build-verified. Key insight: simp[IS_SOME_EXISTS] is a goal-position rewrite that converts IS_SOME(P) to ?x. P = SOME x. Must push IS_SOME facts to goal via qhdtm_x_assum IS_SOME mp_tac first. ()
- `E0098` (progressed, missing_helper)
  - Current proof: Cases_on vt >- (mp_tac assignable_context + simp[assign_target_assignable_context_def, assign_target_assignable_def] + rpt strip_tac + PairCases_on p + gvs[FST,SND] + Cases_on p0 + gvs[] + Cases_on evaluate_type + gvs[IS_SOME_DEF] + Cases_on lookup_var_slot + gvs[IS_SOME_DEF] + by metis_tac derived facts + fs[] + Cases_on type_value + metis_tac[boundary_theorems]) -> Build fails at THEN1 first subgoal not solved. After expansion through assignable_context and gvs/fs, metis_tac cannot match boundary theorem premises (env.type_defs vs get_tenv cx, variable name changes after Cases_on). The error is: HOL_ERR first subgoal not solved by second tactic. (`TO_type_system_rewrite-20260515T192259Z_m11950_t002`)
  - Previous sessions tried: (1) fs[gvs] expansion in wrapper body - variable names break metis; (2) adapter bridge lemmas with /\ conclusions - API corrupts /\ to /&; (3) IS_SOME_EXISTS goal-position rewrite - over-destructures type_value; (4) mp_tac+simp[IS_SOME_EXISTS] for witness extraction - not yet build-verified -> All approaches fail at the same point: after expanding assignable_context, the derived witnesses have variable names that don't match boundary theorem premises. The CORRECT approach (adapter bridge lemma with ==> chain conclusion) was identified in L0394 but never properly executed due to API /\ corruption and stale checkpoints. (`TO_type_system_rewrite-20260515T192259Z_m11275_t001`, `TO_type_system_rewrite-20260515T192259Z_m11333_t001`)
- `E0099` (stuck, other)
  - mp_tac assignable_context + simp[assign_target_assignable_context_def, assign_target_assignable_def] + strip_tac + PairCases_on p + gvs[FST,SND] + Cases_on p0 + gvs[] + Cases_on evaluate_type + gvs[IS_SOME_DEF] + Cases_on lookup_var_slot + gvs[IS_SOME_DEF] + by metis_tac derived facts + fs[] + Cases_on x + metis_tac[boundary_theorems] -> THEN1 first subgoal not solved: metis_tac cannot match boundary theorem premises after expansion changes variable names. fs[] at line 3301 may eliminate env.type_defs=get_tenv cx. ()

### Evidence refs

- `TO_type_system_rewrite-20260515T192259Z_m11981_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260515T192259Z_m11275_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260515T192259Z_m11231_t001` (use `read_tool_output` for exact output)

## C3.1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0025`
- blocker: 

### Attempts / Evidence

- `E0025` (proved, )
  - target_path_type_HashMapT_assign_target_decomp: fix /= syntax with ∧, then prove decomp lemma using metis_tac[target_path_type_HashMapT_not_nil, target_path_type_HashMapT_split_hashmap_subscripts, etc.] -> Decomp lemma proved and builds clean. All existential facts derived from existing lemmas via metis_tac. (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3011_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m3011_t001` (use `read_tool_output` for exact output)

## C3.1.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0027`
- blocker: 

### Attempts / Evidence

- `E0027` (proved, )
  - rpt strip_tac >> derive env.type_defs = get_tenv cx >> get place_leaf_typed via target_path_type_Type_place_leaf_typed >> gvs[place_leaf_typed_def] >> Cases_on REVERSE sbs >> gvs[place_leaf_path_typed_def] >> drule_all place_leaf_path_typed_split_leaf_type >> strip_tac >> qexists_tac base_tv >> conj_tac >- metis_tac (bridge env.type_defs/get_tenv cx) >> conj_tac >- irule assignable_type_evaluate_not_NoneTV >> metis_tac >> irule evaluate_type_well_formed_type_value >> metis_tac -> C3.1.3 proved. Key fix: gvs[place_leaf_typed_def] then Cases_on REVERSE sbs to expose place_leaf_path_typed, then gvs[place_leaf_path_typed_def] for HashMapT case strips head element giving place_leaf_path_typed env vt t ty pl_tv. Then drule_all place_leaf_path_typed_split_leaf_type works. Also fixed type error in C3.1.6: disch_then (drule_all o write_storage_slot...) to disch_then assume_tac >> drule_all ... (`tool_output:TO_type_system_rewrite-20260513T211025Z_m3162_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m3162_t001` (use `read_tool_output` for exact output)

## C3.1.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0100`
- blocker: 

### Attempts / Evidence

- `E0100` (proved, )
  - Expanded assign_target_assignable_context via mp_tac+simp+strip_tac+PairCases_on+Cases_on, then used gvs[IS_SOME_EXISTS] to resolve slot witness, then derived variable-name consistency (t=kt, v=vt) between context-expansion witnesses and FLOOKUP witnesses using drule_all top_level_HashMap_decl + metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ, var_decl_info_11], and finally called metis_tac[top_level_HashMapRef_assign_no_type_error] -> HashMapT branch proved. Key insight: after expanding assignable_context, the find_var_decl witnesses (b,t,v,p1) from context expansion differ from FLOOKUP's (kt,vt). Use top_level_HashMap_decl to get consistent find_var_decl (with kt,vt matching FLOOKUP), then prove variable equality via option/pair/datatype injectivity. After fs[] substitution, metis_tac correctly matches boundary theorem premises. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260515T192259Z_m12256_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m12258_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m12261_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m12265_t001` (use `read_tool_output` for exact output)

## C3.1.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0101`
- blocker: 

### Attempts / Evidence

- `E0101` (proved, )
  - Cases_on vt dispatch to Type and HashMapT specialized wrappers -> Built successfully. Proof: rpt strip_tac >> Cases_on vt >- metis_tac[assign_target_TopLevelVar_Type_no_type_error] >> metis_tac[assign_target_TopLevelVar_HashMapT_no_type_error] ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260515T192259Z_m12265_t001` (use `read_tool_output` for exact output)

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
- diagnosis: `n/a`
- latest episode: `E0053`
- blocker: 

### Attempts / Evidence

- `E0053` (proved, )
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
- diagnosis: `n/a`
- latest episode: `E0060`
- blocker: 

### Attempts / Evidence

- `E0060` (proved, )
  - Added storage_array_append_len_value_has_type and storage_array_pop_len_value_has_type local lemmas using rewrite_tac[value_has_type_def, NUM_OF_INT, INT_POS] + decide_tac/metis_tac pattern from vht_uint_bound -> Both lemmas build successfully (confirmed by checkpoint after storage_array_pop_len_value_has_type). Proof uses integerTheory.NUM_OF_INT + integerTheory.INT_POS to handle Num (&n) rewriting, with metis_tac[LESS_TRANS] for the 2^256 transitivity step that decide_tac cannot handle. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260513T211025Z_m6707_t001` (use `read_tool_output` for exact output)

## C3.2

### Current Status

- result: `progressed`
- diagnosis: `other`
- latest episode: `E0085`
- blocker: "C3.2 ArrayRef branch helper lemmas all proved. Remaining sound_TopLevelVar cheat is a broader C3 obligation needing all sub-branch lemmas (Value, HashMapRef, ImmutableVar) in addition to ArrayRef."

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
- `E0077` (progressed, other)
  - Renamed Replace_ntr_v2 to _v3 and Update_ntr_v2 to _v3 with all_tac >> prefix to break stale holbuild checkpoint. Removed assign_operation_CASE_rator from gvs set to match proven PopOp_ordinary_ntr pattern. Updated one caller reference (Replace) but Update caller at line 3140 still needs v2->v3 update. -> Edits made but not yet build-tested. Two key changes: (1) all_tac >> prefix breaks stale checkpoint, (2) removed assign_operation_CASE_rator which was not present in the proven PopOp proof. ()
- `E0078` (progressed, other)
  - Replace_ntr_v4: gvs[Once assign_target_def, ..., prod_CASE_rator, AllCaseEqs(), Excl type_value_case_eq, Excl bound_case_eq, Excl int_bound_case_eq] then by-subgoals with value_has_type final_tv current_val -> FAILS: Excl prevents AllCaseEqs from expanding case final_tv expression, leaving case final_tv of BaseTV v11 => ... | TupleTV v12 => ... in goal conclusion. By-subgoal value_has_type final_tv current_val cannot match because current_val is bound inside each case branch. The drule_all_then assume_tac read_storage_slot_success_type can't find read_storage_slot in assumptions (it's inside the case body). (`TO_type_system_rewrite-20260514T195458Z_m8500_t002`)
- `E0079` (progressed, other)
  - Reviewed build output for assign_target_ArrayRef_Replace_ntr: gvs blast with type_value_CASE_rator+bound_CASE_rator+prod_CASE_rator+AllCaseEqs() produces big disjunction over final_tv constructors. by-subgoals like value_has_type final_tv current_val fail because AllCaseEqs substitutes final_tv to BaseTV v11 in assumptions but by-subgoal creates fresh final_tv. -> Identified root cause: prod_CASE_rator creates nested pair case that AllCaseEqs expands to N*M constructor cross-product. assign_operation_distinct eliminates PopOp/AppendOp pair-arms but gvs still expands type_value case creating disjunction. by-subgoals referencing final_tv after this expansion are impossible. ()
- `E0080` (progressed, other)
  - Rewrite all 4 ArrayRef ordinary-branch lemmas to use simp[AllCaseEqs()] + rpt strip_tac + gvs[] + TRY(metis_tac[helper]) pattern -> Replace_ntr and Update_ntr_v4 passed build. AppendOp_ordinary_ntr and PopOp_ordinary_ntr rewritten but not independently tested (build reached main theorem first). ()
  - Rewrite main theorem assign_target_TopLevelVar_ArrayRef_branch_no_type_error to use gvs[sum_CASE_rator, pairTheory.PAIR] instead of Cases_on q to avoid auto-generated variable names -> FAILED: gvs[sum_CASE_rator, pairTheory.PAIR] does not split sum assumptions into subgoals. PairCases_on a fails because a doesn't exist after gvs consumes the equality. The sum_CASE_rator only rewrites case expressions, not bare sum-typed variables. ()
  - Fix stale checkpoint by changing Cases_on g to Cases_on y -> PARTIAL: Fixed one occurrence but stale checkpoint at different point mismatched variables. Need to use all_tac >> prefix to break stale checkpoint matching. ()
- `E0081` (progressed, other)
  - Unified 4 boundary lemmas (Replace_ntr, Update_ntr_v4, AppendOp_ordinary_ntr, PopOp_ordinary_ntr) with identical proof bodies into one parameterized assign_target_ArrayRef_ordinary_ntr[local] taking op as universally quantified variable + Dynamic exclusion premise -> Edit made, NOT build-tested. Main theorem still references old lemma names. ()
- `E0082` (progressed, other)
  - Cases_on resolve + gvs[sum_CASE_rator, pairTheory.PAIR] + PairCases_on a -> PairCases_on fails: gvs consumes variable 'a' so it's not free. Checkpoint replays with different names (q,r instead of a). (`TO_type_system_rewrite-20260514T195458Z_m8731_t002`)
  - Unified boundary lemma assign_target_ArrayRef_ordinary_ntr with gvs blast + metis_tac[4 helpers] pattern -> PROVEN. The boundary lemma works when resolve_array_element result is given as premise. But main theorem can't connect without Cases_on. ()
  - Attempts to avoid Cases_on by metis_tac[boundary_lemma] from main theorem premises -> metis_tac cannot bridge because boundary lemma needs resolve_array_element triple result which isn't in main theorem assumptions ()
- `E0083` (progressed, other)
  - Proved resolve_array_element_error_not_TypeError: leaf_type tv subs <> NoneTV => resolve_array_element ... = (INR (Error e), st') => e <> TypeError msg. Used resolve_array_element_ind with bind_apply/AllCaseEqs expansion. IH instantiations with qspec_then `0`/`1` for elem_offset witnesses. get_storage_backend always returns INL. -> PROVED. Lemma compiles successfully after adding missing QED. (`tool_output:TO_type_system_rewrite-20260514T195458Z_m8997_t001`)
  - Created assign_target_TopLevelVar_ArrayRef_resolve_error_no_type_error boundary lemma that handles the INR resolve_array_element case in the ArrayRef branch. Expands assign_target_def once, then uses drule resolve_array_element_error_not_TypeError + simp[no_type_error_result_def]. -> Not yet build-verified; the lemma is written but the 4th INR branch (PopOp) still has the old drule pattern ()
  - Replace INR branches in main theorem: metis_tac[assign_target_TopLevelVar_ArrayRef_resolve_error_no_type_error] instead of drule+gvs approach. Replaced 3 of 4 branches (Replace, Update, AppendOp). -> PopOp branch at line 2987-2989 still has old drule resolve_array_element_error_sc >> drule resolve_array_element_error_not_TypeError >> simp pattern ()
- `E0084` (progressed, other)
  - Fixed assign_target_TopLevelVar_ArrayRef_resolve_error_no_type_error: added Cases_on e before drule to destruct exception ADT, then drule_all resolves both antecedents -> Lemma now proves clean (`TO_type_system_rewrite-20260514T195458Z_m9089_t001`)
  - Fixed assign_target_TopLevelVar_ArrayRef_branch_no_type_error: replaced metis_tac with explicit Cases_on x1 per type_value constructor; used IMP_RES_TAC + metis_tac[] for Dynamic cases -> Main theorem now builds clean, vyperTypeStatePreservationTheory succeeds (`TO_type_system_rewrite-20260514T195458Z_m9151_t001`)
- `E0085` (progressed, other)
  - Fixed assign_target_TopLevelVar_ArrayRef_resolve_error_no_type_error by adding Cases_on e to destruct exception ADT, then drule_all resolves both antecedents -> Lemma proved clean (`TO_type_system_rewrite-20260514T195458Z_m9089_t001`)
  - Fixed assign_target_TopLevelVar_ArrayRef_branch_no_type_error with explicit Cases_on x1 per type_value constructor + IMP_RES_TAC + metis_tac[] for Dynamic cases -> Main theorem builds clean, vyperTypeStatePreservationTheory succeeds (`TO_type_system_rewrite-20260514T195458Z_m9151_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260514T195458Z_m9151_t001` (use `read_tool_output` for exact output)

## C3.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0086`
- blocker: 

### Attempts / Evidence

- `E0086` (proved, )
  - reverse $ gvs[Once assign_target_def, bind_def, ..., AllCaseEqs(), get_immutables_def, set_immutable_def, set_address_immutables_def, LET_THM, no_type_error_result_def] >- (rpt strip_tac >> mp_tac assign_subscripts_no_type_error_runtime_typed >> impl_tac >- simp[] >> simp[]) >> rpt strip_tac >> drule assign_result_no_type_error_from_successful_assign >> disch_then drule >> simp[no_type_error_result_def] -> Build succeeded. Adding set_address_immutables_def+LET_THM to the gvs blast resolved the set_address_immutables INR subgoal (turns out it always returns INL via return()). The blast produces exactly 2 subgoals: (1) assign_subscripts INR TypeError, closed by mp_tac assign_subscripts_no_type_error_runtime_typed + impl_tac >- simp[] + simp[]; (2) success path, closed by drule assign_result_no_type_error_from_successful_assign >> disch_then drule >> simp[no_type_error_result_def]. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260514T195458Z_m9545_t002` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260514T195458Z_m9556_t001` (use `read_tool_output` for exact output)

## C3.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0087`
- blocker: 

### Attempts / Evidence

- `E0087` (proved, )
  - rpt gen_tac >> strip_tac x3 >> conj for preservation via irule cj 1 >> unfold assign_target_def + monads + assign_operation_matches_target_shape_def, Cases_on tgt >> drule IH for assign_targets >> impl_tac with LIST_REL3 construction via evaluate_type_TupleT_cases + values_have_types_LIST_REL + LIST_REL3_from_LIST_REL2 >> qexists_tac EL n tys + EL n tvs -> Fixed type error: EL n l (assignment_target) → EL n tys (type). Build succeeds, sound_TupleTargetV proved. (`TO_type_system_rewrite-20260514T195458Z_m9729_t002`, `TO_type_system_rewrite-20260514T195458Z_m9731_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260514T195458Z_m9729_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260514T195458Z_m9731_t001` (use `read_tool_output` for exact output)

## C3.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0089`
- blocker: 

### Attempts / Evidence

- `E0088` (progressed, unknown)
  - INL branch: qpat_x_assum kill head IH, drule tail IH, disch_tac, pop_assum qspecl_then env/t, metis_tac[target_assignment_values_assignable_def, no_type_error_result_def] -> INL branch SOLVED. Key: kill head IH via qpat_x_assum, then first_x_assum finds tail IH, drule matches equation, disch_tac pops result, qspecl_then specializes env/t, metis_tac closes with target_assignment_values_assignable_def + no_type_error_result_def (`tool_output:TO_type_system_rewrite-20260515T171247Z_m10775_t001`)
  - INR branch: various approaches to apply head IH (first_x_assum qspecl_then, qpat_x_assum drule, qhdtm_x_assum) -> All fail: first_x_assum picks wrong IH, qpat_x_assum with drule gets No match from MATCH_MP, qhdtm_x_assum fails Q_TAC for assign_targets constant. Root cause: both IHs have same universal structure (∀3vars. f args = result ⟹ ∀... ⟹ ...) so first_x_assum/first_assum pick the wrong one. (`tool_output:TO_type_system_rewrite-20260515T171247Z_m10784_t001`)
- `E0089` (proved, )
  - INR branch of sound_assign_targets_cons: kill tail IH with qpat_x_assum kall_tac, specialize head IH with qspecl_then st/INR exc/s1 then env/h/ty, impl_tac with metis_tac[Replace_from_value_has_type, Replace_from_typed], strip_tac, gvs do-block expansion -> SOLVED. Key insight: do NOT use `by` block for the INR IH application — inline the tactic directly. The `by` block caused stale checkpoint interference where the goal state showed the outer `no_type_error_result res` instead of the inner `no_type_error_result (INR exc)`. Also, use metis_tac directly in impl_tac instead of explicit conj_tac chains which mismatched the conjunction structure. (`tool_output:TO_type_system_rewrite-20260515T192259Z_m10834_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260515T192259Z_m10834_t001` (use `read_tool_output` for exact output)

## C3.6

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0106`
- blocker: 

### Attempts / Evidence

- `E0102` (proved, )
  - Verified assign_target_sound_mutual fully built: all 5 Resume blocks proved (sound_ScopedVar, sound_TopLevelVar, sound_TupleTargetV, sound_ImmutableVar, sound_assign_targets_cons), Finalise present, vyperTypeStatePreservationTheory builds successfully, assign_target_sound_mutual exported in .sig -> C3.6 TopLevelVar resume integration is complete - all resume blocks proved, no cheats in file ()
- `E0106` (proved, )
  - Inline expand assign_target_assignable_context in Resume proof with gvs/Cases_on -> Failed: auto-generated variable names (b', t') from gvs destructuring prevent metis_tac from matching universally-quantified variables in top_level_Type_storage_decl ()
  - Add rename1 after gvs[IS_SOME_EXISTS] to fix variable names -> Still failed: Cases_on root_tv had wrong constructor routing (>- targeted BaseTV not ArrayTV) ()
  - Use metis_tac for ArrayTV case combined with boundary lemma -> Timeout: metis combining assign_target_TopLevelVar_ArrayRef_branch_no_type_error with lookup_global lemma timed out ()
  - Derive lookup_global fact as subgoal then metis with single boundary lemma -> Worked for ArrayTV case ()
  - Use drule_all top_level_HashMap_decl + gvs with injectivity for HashMapT branch, derive assign_target_assignable explicitly -> Succeeded: vyperTypeStatePreservationTheory builds clean with zero cheats ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260515T192259Z_m13447_t003` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m13481_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m13509_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m13520_t001` (use `read_tool_output` for exact output)

## C4

### Current Status

- result: `progressed`
- diagnosis: `unknown`
- latest episode: `E0105`
- blocker: "C4 wrappers all proved (assign_target_no_type_error, assign_targets_no_type_error, assign_target_update_no_type_error, assign_target_append_no_type_error). Downstream vyperTypeStmtSoundnessTheory fails at Assign branch because C5 bridge lemmas (assign_operation_matches_target_shape, assign_target_assignable_context, assign_operation_runtime_typed) are needed to connect statement-level assumptions to C4 premises."

### Attempts / Evidence

- `E0103` (progressed, unknown)
  - Read vyperTypeAssignSoundnessScript.sml cheats (lines 313-365): assign_target_no_type_error, assign_target_update_no_type_error, assign_target_append_no_type_error. These are legacy wrappers with old-style premises (assign_target_assignable, well_typed_atarget) that need bridging to C3's strengthened premises (assign_operation_matches_target_shape, assign_target_assignable_context). -> C4 cheats identified but not the build blocker. Build fails at stmt soundness assignment branches which need C5 bridge lemmas first. ()
- `E0104` (progressed, unknown)
  - Rewrote assign_target_no_type_error with C3 premises, proved with imp_res_tac (cj 1 assign_target_sound_mutual) >> gvs[] -> Works - direct projection from C3 mutual theorem ()
  - Rewrote assign_targets_no_type_error with EVERY (assign_target_assignable_context cx st) gvs - WRONG: arg order is cx gv st, partial application cx st misplaces gv -> Type error: EVERY expects (alpha -> bool) but assign_target_assignable_context cx st has wrong type ()
  - Tried MEM form (!gv. MEM gv gvs => ...) with REWRITE_RULE/GSYM EVERY_MEM conversion -> REWRITE_RULE and SIMP_RULE couldn't convert the universal+implication form to EVERY ()
  - Proved assign_target_update_no_type_error by building assign_operation_runtime_typed from well_typed_binop + value_runtime_typed, then imp_res_tac -> Should work - builds assign_operation_runtime_typed internally from decomposed premises ()
  - Proved assign_target_append_no_type_error similarly by building assign_operation_runtime_typed from evaluate_type + value_has_type -> Should work - same pattern as update wrapper ()
- `E0105` (progressed, unknown)
  - Fixed assign_targets_no_type_error EVERY lambda: EVERY (λgv. assign_target_assignable_context cx gv st) gvs matching C3 arg order cx gv st -> Build passes for vyperTypeAssignSoundnessTheory (`tool_output:TO_type_system_rewrite-20260515T192259Z_m13043_t002`, `tool_output:TO_type_system_rewrite-20260515T192259Z_m13049_t001`)
  - Verified all 4 C4 theorems build: assign_target_no_type_error, assign_targets_no_type_error, assign_target_update_no_type_error, assign_target_append_no_type_error -> vyperTypeAssignSoundnessTheory built, no cheats in file (`tool_output:TO_type_system_rewrite-20260515T192259Z_m13049_t001`, `tool_output:TO_type_system_rewrite-20260515T192259Z_m13050_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260515T192259Z_m13043_t002` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m13049_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m13050_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m13050_t002` (use `read_tool_output` for exact output)

## C4.2

### Current Status

- result: `stuck`
- diagnosis: `missing_helper` "List destruct with gvs[LIST_REL_CONS1] for 4+ element lists produces unpredictable tail variable names. Need either: (1) EL-index approach using LIST_REL_EL_EQN, or (2) single-pass Cases_on on values with simp (not gvs), matching the working BuiltinTyping pattern at lines 253-261."
- latest episode: `E0160`
- blocker: "ecrecover_no_type_error list destruct: after Cases_on vs >> gvs[LIST_REL_CONS1] for 4-element lists, auto-generated variable names for tails are unpredictable. Need EL-index approach (LIST_REL_EL_EQN) or single-pass value-destruct approach (Cases_on vs >> Cases_on h >> simp, like BuiltinTyping file pattern) instead of trying to predict gvs-generated tail names."
- next: "Rewrite ecrecover_no_type_error proof using EL-index approach or BuiltinTyping simp pattern. All boundary lemmas are proved. Consumer just needs correct variable connection."

### Attempts / Evidence

- `E0157` (progressed, missing_helper)
  - Fix slice_no_type_error BytesT case using Excl approach: fs[evaluate_builtin_def, Excl "vht_BaseTV_UintT"] then metis_tac[evaluate_slice_BytesT_no_type_error] -> BytesT slice proof works. Excl prevents vht_BaseTV_UintT from consuming value_has_type assumptions, preserving them for the boundary lemma. This was the key insight that unblocked the 6+ attempt stalemate. (`TO_type_system_rewrite-20260516T153850Z_m22112_t001`)
  - Add evaluate_slice_StringT_no_type_error boundary lemma and fix slice_string_no_type_error with same Excl pattern: fs[evaluate_builtin_def, Excl "vht_BaseTV_UintT", Excl "vht_BaseTV_StringT"] then metis_tac[evaluate_slice_StringT_no_type_error] -> StringT slice proof works after adding the boundary lemma and using evaluate_type_BaseT_SOME instead of evaluate_type_BaseT. The old proof used imp_res_tac + gvs + Cases_on + irule pattern but gvs consumed assumptions. (`TO_type_system_rewrite-20260516T153850Z_m22120_t001`)
  - Fix make_array_no_type_error: Cases_on o' + gvs[evaluate_builtin_def] handles NONE case. SOME x case needs Cases_on evaluate_type + evaluate_type_ArrayT_cases for NONE contradiction. -> Currently being fixed. NONE case of MakeArray works. SOME x case with evaluate_type NONE needs imp_res_tac evaluate_type_ArrayT_cases >> gvs[] to derive contradiction from ty = ArrayT x bd. Build not yet verified after latest edit. (`TO_type_system_rewrite-20260516T153850Z_m22144_t001`)
- `E0158` (progressed, missing_helper)
  - make_array_no_type_error: Cases_on o' >> gvs[evaluate_builtin_def] auto-solves NONE branch. SOME x branch: Cases_on evaluate_type (get_tenv cx) x >> gvs[] + gvs[evaluate_type_def, AllCaseEqs()] for NONE contradiction from ty = ArrayT x bd -> make_array_no_type_error fully proved. Key: gvs[well_typed_builtin_app_def] expands ty = ArrayT x bd; Cases_on o' splits; gvs[evaluate_builtin_def] solves NONE; for SOME x, Cases_on evaluate_type + gvs[evaluate_type_def, AllCaseEqs()] derives contradiction from evaluate_type NONE when ty = ArrayT x bd implies evaluate_type exists (`TO_type_system_rewrite-20260516T153850Z_m22198_t001`)
  - ecrecover_no_type_error: Tried direct Cases_on vs with >> (wrong subgoal control); tried boundary lemma evaluate_ecrecover_no_type_error with hardcoded [BaseTV (UintT 256)] (too narrow - BECAUSE last 3 args can be BytesT Fixed 32 OR UintT 256); tried Cases_on v/v'/h/h' (wrong auto-generated variable names after gvs/fs) -> Failed 5+ attempts. Root causes: (1) gvs destroys != INR(TypeError) goal via variable elimination; (2) ECRecover typing has disjunction EVERY (UintT 256 OR BytesT Fixed 32) for last 3 args, making simple boundary lemma too narrow; (3) list destruct with >> is fragile since variable names differ across subgoals; (4) auto-generated variable names from gvs/fs expansion are unreliable; (5) The evaluate_ecrecover_no_type_error boundary lemma I added needs to handle BOTH UintT and BytesT patterns (`TO_type_system_rewrite-20260516T153850Z_m22189_t001`, `TO_type_system_rewrite-20260516T153850Z_m22244_t001`, `TO_type_system_rewrite-20260516T153850Z_m22257_t001`, `TO_type_system_rewrite-20260516T153850Z_m22262_t001`, `TO_type_system_rewrite-20260516T153850Z_m22279_t001`)
- `E0159` (progressed, missing_helper)
  - Fix ecrecover_no_type_error: rewrote boundary lemma evaluate_ecrecover_no_type_error using ecrecover_arg_to_num abstraction (handles both UintT 256 and BytesT Fixed 32). Added ecrecover_arg_Uint256_not_none and ecrecover_arg_BytesT32_not_none helper lemmas. All three boundary lemmas proved successfully. -> Boundary lemmas for ECRecover proved and working. Consumer proof ecrecover_no_type_error failed 8+ times trying to connect LIST_REL value_has_type + well_typed_builtin_app to boundary lemma assumptions. (`TO_type_system_rewrite-20260516T153850Z_m22329_t001`, `TO_type_system_rewrite-20260516T153850Z_m22331_t001`, `TO_type_system_rewrite-20260516T153850Z_m22333_t001`, `TO_type_system_rewrite-20260516T153850Z_m22335_t001`, `TO_type_system_rewrite-20260516T153850Z_m22337_t001`)
  - Fix ecadd_no_type_error: replaced stale Cases_on v' with explicit list destruct (LENGTH + Cases_on vs/ts elements) -> Code written but build never reached ecadd due to ecrecover blocking first ()
  - Fix ecmul_no_type_error: same pattern as ecadd fix -> Code written but build never reached ecmul due to ecrecover blocking first ()
- `E0160` (stuck, missing_helper)
  - ecrecover_no_type_error: tried Cases_on vs >> gvs[LIST_REL_CONS1] >> Cases_on t >> gvs[LIST_REL_CONS1] >> ... for 4-element list. After 3 levels of destruct, auto-generated tail variable names (t, t', t'') from gvs don't match expected pattern. gvs renames tails unpredictably based on assumption simplification. Tried explicit variable names t, t', t'', t''' but actual names after gvs are different (t, xs, etc.) -> 8+ attempts across 2 sessions. Root cause: gvs[LIST_REL_CONS1] auto-generates variable names for list tails that depend on full assumption state, making them unpredictable. Cases_on `t''` fails because gvs renamed the tail to something else. (`TO_type_system_rewrite-20260516T153850Z_m22390_t001`, `TO_type_system_rewrite-20260516T153850Z_m22395_t001`)
  - Rewrote ecrecover_no_type_error to take typing predicates directly (like slice_no_type_error) instead of well_typed_builtin_app_def. Avoids gvs[well_typed_builtin_app_def] destroying the ≠ TypeError goal. -> Consumer proof rewritten. List destruct still fails: Cases_on `t''` cannot find t'' free in goal after gvs[LIST_REL_CONS1] renamed tails. (`TO_type_system_rewrite-20260516T153850Z_m22395_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260516T153850Z_m22390_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260516T153850Z_m22395_t001` (use `read_tool_output` for exact output)

## C4.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0161`
- blocker: 

### Attempts / Evidence

- `E0161` (proved, )
  - Carry forward existing boundary lemmas at lines 1511-1539 -> All three lemmas already present and proved in source ()

### Evidence refs

- `TO_type_system_rewrite-20260516T153850Z_m22429_t002` (use `read_tool_output` for exact output)

## C4.2.2

### Current Status

- result: `progressed`
- diagnosis: `other` C4.2.2 ECRecover target is proved but downstream ecadd/ecmul need boundary lemma extraction for value_has_type ArrayTV decomposition
- latest episode: `E0162`
- blocker: 

### Attempts / Evidence

- `E0162` (progressed, other)
  - Added list_el_decomp_4 local helper + fixed ecrecover_no_type_error inline proof using simp[list_el_decomp_4] instead of match_mp_tac LIST_EQ >> simp[]. Derived per-element EL-index typing facts, converter non-NONE facts before list decomposition, then fs[EL] + Cases_on v0 + metis_tac[evaluate_ecrecover_no_type_error]. -> ecrecover_no_type_error proved successfully (list_el_decomp_4 + list_el_decomp_2 helpers added). ecadd_no_type_error proof still needs fixing. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m22675_t002` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m22730_t001` (use `read_tool_output` for exact output)

## C5.2

### Current Status

- result: `stuck`
- diagnosis: `plan_incomplete`
- latest episode: `E0113`
- blocker: Cannot derive assign_target_assignable_context for TopLevelVar in Assign INR sub-case because env_context_consistent does not provide get_module_code from FLOOKUP toplevel_vtypes. This is an architectural gap in env_context_consistent_def that needs to be fixed before the assignable context can be derived for TopLevelVar targets.

### Attempts / Evidence

- `E0107` (progressed, unknown)
  - recInduct base_target_value_shape_ind >> rw[] >> gvs[base_target_value_shape_def] >> metis_tac[type_place_target_NameTarget/AttributeTarget/SubscriptTarget] -> Helper lemma well_typed_target_ScopedVar_imp_var_assignable compiles. Build progresses past it into assign_target_INL_imp_assign_target_assignable_context. Output keeps truncating at TopLevelVar case - build may be timing out or just taking long. (`tool_output:TO_type_system_rewrite-20260515T192259Z_m13850_t001`, `tool_output:TO_type_system_rewrite-20260515T192259Z_m13855_t001`)
- `E0108` (progressed, unknown)
  - CCONTR_TAC >> strip_tac >> assign_target expansion >> gvs[AllCaseEqs()] >> simp[optionTheory.IS_SOME_EXISTS] >> metis_tac[optionTheory.IS_SOME_EXISTS] -> metis_tac[optionTheory.IS_SOME_EXISTS] failed with 'no solution found' in both StorageVarDecl and HashMapVarDecl branches. The issue is that after simp[IS_SOME_EXISTS] converts IS_SOME constraints to existentials, metis_tac cannot figure out the witness instantiation. (`tool_output:TO_type_system_rewrite-20260515T192259Z_m13863_t001`)
  - Edited: replace IS_SOME by ?slot witness extraction with CCONTR_TAC >> gvs[optionTheory.IS_SOME_EXISTS] + assign_target expansion, then simp[] to close -> Edited both StorageVarDecl and HashMapVarDecl branches. NOT YET BUILD-TESTED. ()
- `E0109` (progressed, unknown)
  - metis_tac[well_typed_target_ScopedVar_imp_var_assignable] in ScopedVar case after gvs[target_runtime_typed_def, well_typed_atarget_def, location_runtime_typed_def] -> metis_tac fails with 'no solution found' - probably variable name/pattern mismatch between goal state and lemma, not a logical issue since type_place_target_NameTarget biconditional provides var_assignable directly (`tool_output:TO_type_system_rewrite-20260515T192259Z_m13938_t002`)
  - CCONTR_TAC + gvs[optionTheory.IS_SOME_EXISTS] pattern for IS_SOME goals in TopLevelVar StorageVarDecl/HashMapVarDecl lookup_var_slot_from_layout branches -> Edited but not build-tested due to broken file from FAIL_TAC probe edit ()
- `E0110` (progressed, other)
  - irule well_typed_target_ScopedVar_imp_var_assignable >> simp[] inside backtick subgoal for FLOOKUP env.var_assignable (string_to_num v) = SOME T -> irule produces subgoals but simp[] cannot close the first one. Likely variable name mismatch after gvs destructures assumptions. (`TO_type_system_rewrite-20260515T192259Z_m14025_t001`)
  - metis_tac[well_typed_target_ScopedVar_imp_var_assignable] after gvs[target_runtime_typed_def, well_typed_atarget_def, location_runtime_typed_def] -> metis_tac fails with 'no solution found' - pattern instantiation issue, not a logical gap (`TO_type_system_rewrite-20260515T192259Z_m13938_t002`)
- `E0111` (progressed, other)
  - Replace FAIL_TAC probe + metis_tac[well_typed_target_ScopedVar_imp_var_assignable] with fs[] instead of gvs[] then metis_tac; add env_scopes_consistent intermediate step; use drule chain through env_scopes_consistent_var_assignable_imp + lookup_scopes_find_containing_scope -> metis_tac still fails with 'no solution found' after fs[target_runtime_typed_def, target_value_shape_def, well_typed_atarget_def, well_typed_target_def]. Replaced with cheat for FLOOKUP step. Build result unclear - output truncated, found FIRST_ASSUM error from TopLevelVar branch. ()
  - Build vyperTypeAssignSoundnessTheory to check after removing FAIL_TAC probe -> Build output too large to see full result. Error at FIRST_ASSUM in TopLevelVar HashMapVarDecl branch likely. ScopedVar proof still has cheat for FLOOKUP step. ()
- `E0112` (progressed, other)
  - irule target_runtime_typed_ScopedVar_imp_assignable_context >> conj_tac -> conj_tac fails - irule produces 2 subgoals not a conjunction (`TO_type_system_rewrite-20260515T192259Z_m14274_t001`)
  - metis_tac[target_runtime_typed_ScopedVar_imp_assignable_context] after fs[runtime_consistent_def] -> FIRST_ASSAM exception - metis_tac cannot match lemma antecedents against post-fs assumptions (`TO_type_system_rewrite-20260515T192259Z_m14276_t001`)
  - drule_all_then assume_tac target_runtime_typed_ScopedVar_imp_assignable_context after fs[runtime_consistent_def] -> FIRST_ASSAM exception - drule_all cannot find matching assumption after fs restructured env_consistent (`TO_type_system_rewrite-20260515T192259Z_m14278_t001`)
  - qpat_x_assum + MATCH_MP target_runtime_typed_ScopedVar_imp_assignable_context (latest edit, untested) -> Not yet build-tested ()
- `E0113` (stuck, plan_incomplete)
  - Use assign_operation_matches_target_shape_Replace_from_typed for shape (works for both BaseTargetV and TupleTargetV) -> Shape can be derived - this lemma takes target_runtime_typed + evaluate_type + value_has_type, all available in the goal ()
  - Try assign_target_INL_imp_assignable_context_stmt for context -> Wrong: INR sub-case has assign_target returning INR, and the bridge lemma requires INL success ()
  - Try irule assign_operation_matches_target_shape_BaseTargetV -> Fails: gv might be TupleTargetV ()
  - Derive get_module_code from env_context_consistent + FLOOKUP toplevel_vtypes -> Impossible: env_context_consistent only has implications requiring get_module_code as precondition, never concluding it. All clauses go: get_module_code + bare_globals => toplevel_vtypes, or get_module_code + toplevel_vtypes => declaration_facts ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260515T192259Z_m14656_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260515T192259Z_m14754_t001` (use `read_tool_output` for exact output)

## C5.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0114`
- blocker: 

### Attempts / Evidence

- `E0114` (proved, )
  - Define assignment_value_static_assignable_context using case + if-then-else to avoid /\ corruption -> Definition compiles successfully via holbuild. The /\ corruption issue was worked around by using single-equation case expression with if-then-else encoding of conjunction instead of multi-clause pattern matching with /\. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T092459Z_m14874_t001` (use `read_tool_output` for exact output)

## C5.2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0115`
- blocker: 

### Attempts / Evidence

- `E0115` (proved, )
  - Add ScopedVar, ImmutableVar, TupleTargetV simp lemmas for assignment_value_static_assignable_context -> All three lemmas proved. Key issues: (1) had to change definition from case-expression to multi-clause ∧ form to get proper rewrite rules, (2) TupleTargetV lemma needed metis_tac[ETA_AX] because simp eta-expands the function in EVERY ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T092459Z_m14906_t001` (use `read_tool_output` for exact output)

## C5.2.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0116`
- blocker: 

### Attempts / Evidence

- `E0116` (proved, )
  - ho_match_mp_tac target_runtime_typed_ind >> rpt strip_tac then Cases_on `loc` with ScopedVar using metis, ImmutableVar using simp, TopLevelVar using irule/iffLR on assignment_value_static_assignable_context_TopLevelVar -> Proof succeeds. Key: (1) changed definition from if-then-else to conjunction form matching assign_target_assignable_context, (2) added iff-based TopLevelVar rewrite lemma, (3) Cases_on loc BEFORE expanding assign_target_assignable_context so ScopedVar boundary lemma can match intact target_runtime_typed assumption, (4) used iffLR for biconditional TopLevelVar lemma, (5) impossible goals close by gvs[target_runtime_typed_def], (6) list goals use metis_tac[] with IHs. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T092459Z_m15317_t001` (use `read_tool_output` for exact output)

## C5.2.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0120`
- blocker: 

### Attempts / Evidence

- `E0119` (progressed, other)
  - Restore build by replacing failing Assign INR sub-proofs with cheat. Then identify C5.2.4 proof approach: prove INL => assignment_value_static_assignable_context first, then use iff with assign_target_assignable_context for TopLevelVar. Key insight: assign_target_assignable for TopLevelVar is trivially T, so assign_target_assignable_context reduces to just the static context existential. -> Build restored for both vyperTypeStmtSoundnessTheory and vyperTypeAssignSoundnessTheory. C5.2.4 approach validated but not yet executed. Next session should add assign_target_TopLevelVar_INL_imp_static_context lemma and prove it via controlled expansion of assign_target_def (NOT global). (`TO_type_system_rewrite-20260516T092459Z_m15707_t001`, `TO_type_system_rewrite-20260516T092459Z_m15708_t001`)
- `E0120` (proved, )
  - Prove assign_target_TopLevelVar_INL_imp_assignable_context: INL success implies assignable context for TopLevelVar -> Proved. Key tactic insights: (1) Use metis_tac for existential witnesses from universally-quantified helper theorems (irule/drule leave unresolved quantifiers). (2) Use PairCases_on p instead of Cases_on FST p to preserve pair structure for drule/irule matching. (3) Use metis_tac for IS_SOME facts from specialized helper lemmas instead of drule+simp which leaves ∀ implications. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16077_t001` (use `read_tool_output` for exact output)

## C5.2.6

### Current Status

- result: `progressed`
- diagnosis: `plan_incomplete` C5.2.6 wrapper lemma is unnecessary - assign_operation_matches_target_shape_Replace_from_typed already has the exact signature needed and is already imported. Adding a duplicate would violate no-duplicate principle.
- latest episode: `E0121`
- blocker: 
- next: Move to C5.2.7 checkpoint then C5.3

### Attempts / Evidence

- `E0117` (progressed, plan_incomplete)
  - irule assign_operation_matches_target_shape_Replace_from_typed for shape derivation in Assign branches; simplified state_well_typed subgoal using no_ctx preservation theorem -> Shape derivation works for Replace via assign_operation_matches_target_shape_Replace_from_typed. Preservation uses no_ctx variants without shape/context. The no-TypeError subgoal for INR case needs assign_target_no_type_error which requires both shape AND assignable_context. Shape is derivable; context is the blocker. ()
- `E0118` (progressed, plan_incomplete)
  - Simplified Assign INR branch preservation using no_ctx theorems (L0491/L0492/L0496). Added shape derivation via irule assign_operation_matches_target_shape_Replace_from_typed for Replace. For no-TypeError subgoal: needs assign_target_assignable_context which is not available for TopLevelVar in INR case. -> Preservation subgoal fixed. Shape derivation confirmed working. No-TypeError subgoal blocked by architectural gap: env_context_consistent does not derive get_module_code from FLOOKUP toplevel_vtypes. ()
- `E0121` (progressed, plan_incomplete)
  - Verified assign_operation_matches_target_shape_Replace_from_typed (vyperTypeStatePreservationScript.sml:2254) has exact signature needed by C6 assignment branches. Works for both BaseTargetV and TupleTargetV. Already imported via vyperTypeStatePreservation ancestor. -> Existing theorem suffices directly. No new lemma needed. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16619_t002` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16637_t001` (use `read_tool_output` for exact output)

## C5.2.7

### Current Status

- result: `progressed`
- diagnosis: `plan_incomplete` C5.2.7 checkpoint: INR no-TypeError branches with TopLevelVar targets need assign_target_assignable_context but env_context_consistent doesn't provide get_module_code. Need architectural fix in env_context_consistent_def or static context premise addition to statement soundness theorem.
- latest episode: `E0122`
- blocker: 
- next: Move to C5.3 (AnnAssign lemmas, Risk 1, no dependency on TopLevelVar gap). Then escalate C5 architectural gap via plan_oracle.

### Attempts / Evidence

- `E0122` (progressed, plan_incomplete)
  - C5.2.7 audit: verified build passes, all C5.2 boundary lemmas compile. C5.2.3 (static+runtime bridge) proved. C5.2.4 (TopLevelVar INL context) proved. C5.2.5 (generic bridge) has TupleTargetV cheat but compiles via metis. C5.2.6 (shape) satisfied by existing assign_operation_matches_target_shape_Replace_from_typed. Inspected Assign INR branch (lines 944-978): no-TypeError cheat at line 978 needs assign_target_no_type_error which requires assign_target_assignable_context. For INR branches (assignment failed), C5.2.5 (INL-success bridge) does NOT apply. C5.2.3 needs assignment_value_static_assignable_context which needs get_module_code facts not derivable from env_context_consistent. -> Checkpoint confirms: INR no-TypeError branches with TopLevelVar targets blocked by env_context_consistent architectural gap. INL-success branches unblocked. Shape derivation unblocked. Must either fix env_context_consistent or add static context premise to statement soundness. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16643_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16642_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16646_t001` (use `read_tool_output` for exact output)

## C5.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0123`
- blocker: 

### Attempts / Evidence

- `E0123` (proved, )
  - Audit existing NoneT/NoneTV lemmas and their usage in AnnAssign branch -> C5.3 is already covered: assignable_type_not_NoneT, evaluate_type_not_NoneT_imp_not_NoneTV, and assignable_type_evaluate_not_NoneTV already exist and are used directly in the AnnAssign branch (lines 873-874). No additional helper lemmas needed. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16657_t002` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16666_t001` (use `read_tool_output` for exact output)

## C5.4

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch`
- latest episode: `E0124`
- blocker: env_context_consistent_def gap: FLOOKUP env.toplevel_vtypes (src,id) = SOME vt only yields well_formed_vtype, not get_module_code/find_var_decl_by_num/lookup_var_slot_from_layout. Need definition fix or alternative invariant to derive assign_target_assignable_context for TopLevelVar in INR branches

### Attempts / Evidence

- `E0124` (stuck, risk_mismatch)
  - Audit C5.4 scope and dependencies: checked what tuple/list assignment packaging needs, whether existing lemmas cover it, and what blocks progress -> C5.4 tuple/list packaging is secondary to the critical blocker: env_context_consistent_def does not derive get_module_code/find_var_decl_by_num/lookup_var_slot_from_layout from FLOOKUP env.toplevel_vtypes entries. This gap blocks ALL INR no-TypeError branches for TopLevelVar targets across C5.4, C5.2.3 (partial), C6, and beyond. Must escalate to plan_oracle for definition fix. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16687_t001` (use `read_tool_output` for exact output)

## C5.4.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0125`
- blocker: 

### Attempts / Evidence

- `E0125` (proved, )
  - Edited type_place_target for TopLevelNameTarget to reject bare-global entries (IS_SOME guard). Proved type_place_target_TopLevelNameTarget_IS_SOME and type_place_target_TopLevelNameTarget_NOT_BARE using simp[well_typed_expr_def], then proved main biconditional by Cases_on + simp. Fixed top_level_HashMap_decl proof (env_context_consistent strengthening made old metis_tac fail; replaced with targeted qpat_x_assum drule). -> Both definition changes compile. vyperTypeEnvTheory, vyperTypeStatePreservationTheory, vyperTypeStmtSoundnessTheory, and vyperSemanticsHolTheory all build successfully. (`tool_output:TO_type_system_rewrite-20260516T153850Z_m16799_t001`, `tool_output:TO_type_system_rewrite-20260516T153850Z_m16803_t001`, `tool_output:TO_type_system_rewrite-20260516T153850Z_m16824_t001`, `tool_output:TO_type_system_rewrite-20260516T153850Z_m16826_t001`)

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16799_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16803_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16824_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16826_t001` (use `read_tool_output` for exact output)

## C5.4.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0126`
- blocker: 

### Attempts / Evidence

- `E0126` (proved, )
  - Add env_consistent_toplevel_storage_static and env_consistent_toplevel_hashmap_static projection lemmas to vyperTypeEnvScript.sml -> Both lemmas proved by gvs[env_consistent_def, env_context_consistent_def] followed by qpat_x_assum drule to target the new Type/HashMapT conjuncts. Full build vyperSemanticsHolTheory passes. ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16853_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T153850Z_m16854_t001` (use `read_tool_output` for exact output)

## C5.4.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0130`
- blocker: 

### Attempts / Evidence

- `E0127` (progressed, tool_limit)
  - Added env_consistent_toplevel_storage_static and env_consistent_toplevel_hashmap_static projection lemmas (C5.4.2 completed). Started C5.4.3 but context burned on excessive grep calls before writing the lemma statements. -> C5.4.2 completed and built. C5.4.3 not started - need to find target_path_type_def and target_runtime_typed_ind then write/prove the mutual bridge lemma. ()
- `E0128` (progressed, tool_limit)
  - Prove standalone TopLevelVar helper target_runtime_typed_TopLevelVar_imp_static_context using sequential fs, then use in mutual theorem via metis_tac -> Standalone lemma approach is correct. After sequential fs[target_runtime_typed_def, target_value_shape_def, well_typed_atarget_def, well_typed_target_def], assumptions are intact: type_place_target env bt = SOME (Type ty), base_target_value_shape env bt (TopLevelVar src id) sbs, location_runtime_typed, target_path_type, env_consistent. BUT irule base_target_value_shape_TopLevelVar_imp_bare_globals_none_spec fails because the spec lemma has universally-quantified vt that appears only in antecedents, so irule cannot determine instantiation. Need metis_tac or explicit instantiation instead. (`TO_type_system_rewrite-20260516T153850Z_m17255_t001`)
- `E0129` (progressed, tool_limit)
  - metis_tac[base_target_value_shape_TopLevelVar_imp_bare_globals_none_spec] for bare_globals, fs[location_runtime_typed_def] to expose FLOOKUP, then metis_tac[env_consistent_toplevel_storage_static, assignment_value_static_assignable_context_TopLevelVar, IS_SOME_EXISTS] for Type branch -> bare_globals proof works with metis_tac. fs[location_runtime_typed_def] successfully exposes FLOOKUP. But metis_tac with 4 lemmas times out on Type branch. Need explicit drule_all + rw/qexists instead of metis_tac. ()
- `E0130` (proved, )
  - Replaced metis_tac timeout in target_runtime_typed_TopLevelVar_imp_static_context with drule_all + rw/qexists_tac for Type branch and drule_all + rw + metis_tac[target_path_type_HashMapT_not_nil] for HashMapT branch -> Standalone lemma proved: drule_all gets existential witnesses, rw rewrites goal to matching form, qexists_tac supplies concrete witnesses ()
  - Fixed mutual theorem target_runtime_typed_imp_static_assignable_context_mutual Goal 4 (TupleTarget/TupleTargetV) using fs + simp + metis_tac -> Mutual theorem proved with all 9 goals discharged ()
  - Added C5.4.4 theorems: target_runtime_typed_imp_assignable_context and target_values_runtime_typed_imp_EVERY_assignable_context -> Both proved by metis_tac composing C5.4.3 static context with C5.2.3 bridge ()

### Evidence refs

- `tool_output:TO_type_system_rewrite-20260516T153850Z_m17311_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T17326_t001` (use `read_tool_output` for exact output)
- `tool_output:TO_type_system_rewrite-20260516T17336_t001` (use `read_tool_output` for exact output)

## C5.4.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0132`
- blocker: 

### Attempts / Evidence

- `E0131` (progressed, other)
  - Fixed Assign materialise TypeError sub-case: reordered gvs[expr_result_typed_def, expr_runtime_typed_def] before drule_at_then Any drule materialise_typed_non_none_no_type_error, matching the AnnAssign pattern. Build verified. -> Assign resume proof now builds successfully. (`TO_type_system_rewrite-20260516T153850Z_m17452_t001`)
  - Wrote complete AugAssign proof replacing cheat+commented-out code. Uses: target_runtime_typed_imp_assignable_context for assignable context, assign_operation_matches_target_shape_def (BaseTargetV+Update is T), assign_target_update_no_type_error for no-TypeError Error sub-case, assign_target_no_return for ReturnException sub-case, well_typed_binop_not_In_second_type + evaluate_type_not_ArrayT_imp_not_ArrayTV + evaluate_type_not_NoneT_imp_not_NoneTV + get_Value_no_type_error for INR get_Value sub-case. -> Written but NOT yet build-verified. Next session must build vyperTypeStmtSoundnessTheory to confirm AugAssign proof compiles. ()
- `E0132` (proved, )
  - Fixed parenthesis mismatch in AugAssign proof and verified build -> AugAssign resume proof now builds successfully with 30s timeout. The proof uses target_runtime_typed_imp_assignable_context for assignable context, assign_operation_matches_target_shape_def (BaseTargetV+Update is T), assign_target_update_no_type_error for INR Error sub-case, assign_target_no_return for INR ReturnException sub-case, and get_Value_no_type_error for INR get_Value sub-case. (`TO_type_system_rewrite-20260516T153850Z_m17494_t001`)
  - Previously fixed Assign materialise TypeError sub-case ordering -> Assign proof verified building in prior session (`TO_type_system_rewrite-20260516T153850Z_m17452_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260516T153850Z_m17494_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260516T153850Z_m17452_t001` (use `read_tool_output` for exact output)
