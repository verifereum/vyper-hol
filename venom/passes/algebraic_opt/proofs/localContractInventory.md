# Local algebraic-opt semantic contract inventory

Audit checkpoint C1.L.INVENTORY, 2026-11-08. This is an interface audit, not a proof of composition or of the frozen function theorem.

## Checked scope and notation

`algebraicOptSequenceLocalProofsTheory` and `algebraicOptRelationProofsTheory` replayed successfully with holbuild at the default tactic timeout (tool output TO_ao-correct-20261108T121945Z_m5225_t004; sequence also TO_ao-correct-20261108T121945Z_m5218_t001). Definitions unchanged.

Below S means `step_inst_base inst s = OK t`. Scalar contracts quantify over a member of the replacement list and conclude `step_inst_base out s = OK t`; they are same-state contracts, not execution of arbitrary lists. Their definitions emit singletons. Successful source evaluation supplies definedness even when the target drops a read. The complete target record equals t (thus index and frame unchanged at base-step level). Actual chunks increment the index per instruction; use `ao_base_step_chunk_single`, whose premises are non-INVOKE and nonterminator, rather than equating base-step indices with chunk indices.

## ao_peephole_inst branch matrix

Dispatch source: algebraicOptDefsScript.sml:654-671. Unless noted, contracts are in algebraicOptLocalProofsScript.sml and require S plus the displayed opcode and replacement membership.

| Dispatch | Branches covered by existing family contract | Contract / extra premises / result |
|---|---|---|
| Empty outputs; ASSIGN, PHI, PARAM | singleton unchanged | Definition only; identity semantic equation. PHI execution must use selected parallel snapshot, not pure-scalar bridge. |
| SHL, SHR, SAR | zero shift becomes ASSIGN; otherwise unchanged, including other operand shapes | `ao_opt_shift_correct`: exact scalar |
| SIGNEXTEND | literal byte count >=31 becomes ASSIGN; smaller literal with bounded non-top range becomes ASSIGN; other cases unchanged | `ao_opt_signextend_correct`: exact scalar; every successfully evaluated operand must lie in its `range_get_range ra lbl idx` at s |
| Exp | exponent 0, exponent 1, base 1, base 0 -> ISZERO; fallback | `ao_opt_exp_correct`: exact scalar; guard priority includes 0^0=1 |
| ADD, SUB, XOR | equal SUB/XOR inputs ->0; right zero identity; (-1)-x ->NOT; x XOR (-1) ->NOT; fallback | `ao_opt_addsub_correct`: exact scalar |
| AND | right max identity; either zero ->0; fallback | `ao_opt_and_correct`: exact scalar |
| MUL, Div, SDIV, Mod, SMOD | either zero ->0; right one identity/zero; unsigned power-of-two MUL/Div/Mod ->SHL/SHR/AND; signed and other fallbacks | `ao_opt_muldiv_correct`: exact scalar; `ao_safe_arithmetic_zero_one` and power-of-two facts are shared algebra, not extra caller assumptions |
| OR | right max ->max; all-truthy + nonzero literal ->1; right zero identity; fallback | `ao_opt_or_correct`: outputs [x], t=update_var x v s; replacement writes w at x over s; v=0 iff w=0; either w=v or all-truthy and w=1 and v nonzero. Only this second alternative permits inexact output. Frame and base index unchanged. |
| EQ | equal operands ->1; right zero ->ISZERO; right max ->NOT then ISZERO; prefer-iszero ->XOR then ISZERO; fallback | `ao_opt_eq_chunk_correct` in SequenceLocalProofs: exact original-variable chunk result, explicit two-temporary freshness below |
| GT, LT, SGT, SLT | equal operands ->0; range replacement; literal never ->0; almost-never ->ISZERO/NOT+ISZERO/EQ; prefer-iszero almost-always ->double ISZERO or NOT/XOR + double ISZERO; unsigned GT-zero; fallback | `ao_opt_comparator_chunk_correct`: same chunk contract as EQ plus range containment at s for every successfully evaluated operand |
| All other opcodes | singleton unchanged | Definition only; not an unconditional nonterminating OK step. Includes control, memory, calls and other side effects; surrounding simulation must transport the relevant frame and preserve terminal result constructors. |

EQ/comparator chunk premises: source S; `SND(fr "not") <> SND(fr "iz")`; both variables absent from instruction operands as Var and from outputs; `fr "xor" = fr "not"`. No assumption that temporary lookups initially are NONE. Conclusion supplies u with successful `ao_cmp_exec_chunk fuel ctx replacement s`, u restored with t's vars/index equals t, u.index=s.index+LENGTH replacement, and lookup equality with t outside the two temporaries. This is stronger than output truthiness but deliberately weaker than identical variable maps. Named `ao_cmp_prefer_iz_{zero,max,general}_chunk`, `ao_iszero_iszero_chunk`, `ao_step_iszero_iszero_chunk`, `ao_not_iszero_chunk` are existing sequence boundaries; do not duplicate them.

## Pipeline wrappers and actual gaps

`ao_transform_inst` (Defs:818-831) first resolves all operands, then bypasses empty-output or ASSIGN/PHI/PARAM, then tries producer rewriting, and only on NONE applies pre-flip, peephole, and MAP post-flip. Peephole contracts alone do not cover this pipeline.

* Resolution: `ao_resolve_iszero_op_eval_exact/truth` (ChainProofs) and `ao_resolve_iszero_cross_exact/truth` (ReadClosureProofs) are conditional read interfaces. They need nonempty endpoint-correct chains, source successful chain valuations and word-chain equations; cross-state versions need exact positive-index target valuations and endpoint agreement, plus a zero-equivalent target root for truthy uses. Source trace/availability results recover valuations, but these are not universal table facts at arbitrary states. `ao_resolve_iszero_inst_fields/support/labels/successors` (ShapeProofs) are structural, not semantic replacement theorems. Literal/Label roots are not silently excluded. General instruction-level resolved-read execution transport remains to be composed; selected PHIs read the predecessor snapshot.
* ISZERO special case is already fully routed: `ao_resolve_iszero_self`, `ao_transform_iszero`, `ao_transform_iszero_step_exact` (IszeroPreservationProofs) and `ao_main_observations_iszero` (RelationProofs). Zero-equivalent successful inputs yield exactly equal Boolean output words over the respective states.
* Bypasses happen AFTER resolution. ASSIGN may need exact resolved values; PHI requires selected operands, not equality of all inactive inputs; PARAM and outputless control/effect instructions require their own execution boundary. Identity dispatch is not identity of the original instruction after resolution.
* Producer: BALANCE(Var v) with ADDRESS def becomes SELFBALANCE; other BALANCE and EXTCODESIZE cases stay unchanged. Nested SIGNEXTEND(Lit w,Var v) with SIGNEXTEND(Lit inner,_) def and inner<=w becomes ASSIGN of Var v (not the producer's underlying input). `ao_opt_producer_shape/labels` prove layout/support only. Search found no general semantic producer theorem. Needed facts are current ADDRESS value and current signextended producer result, recovered from reachable execution plus SSA availability; arbitrary DFG membership alone does not give either. Owned by the unresolved main simulation C1.M, not by the scalar family contracts.
* Pre/post flip: swaps exactly ADD/MUL/AND/OR/XOR/EQ at literal placement guards. `ao_pre_flip_inst_shape`, `ao_post_flip_inst_shape`, `ao_flip_inst_labels` exist (ShapeProofs); no semantic flip equation found by theorem search. C1.L.COMPOSE owns exact flip semantics and lifting MAP post-flip over emitted chunks. Other opcodes and nonbinary shapes are unchanged.
* `ao_main_exact` (RelationProofs:11) forces no-producer inputs, original ISZERO outputs, and outputs with a non-all-truthy producer to be exact. `ao_main_lookup` preserves NONE versus SOME and otherwise exact words or zero equivalence. `ao_main_observations` is only lookups on V. Refl/init, definedness, update, fresh-write and ISZERO lemmas are checked. DFG consumer classification must still justify exact inputs at each value-sensitive consumer and permission for the OR inexact alternative; a pre-flipped record must be connected to the original analyzed producer. Frame, control, block labels and selected-PHI alignment do not follow from observations.

## Proposed minimal conditional composition interface (not a theorem)

Keep peephole composition separate from producer/resolver correctness. For an instruction i after preprocessing/pre-flip, compare successful source execution from s with target execution from r. An exact-input transport boundary should first produce the same pure output over r from equal operand evaluations; family contracts can then be invoked AT r, not at s. For the scalar opcode families require actual successful equal word observations on all operands; use a separate zero-equivalent-input path for justified truthy consumers such as ISZERO/JNZ/assert, not for arbitrary arithmetic or EQ. Never infer arithmetic equality from mere zero equivalence.

| Premise / consequence | Classification |
|---|---|
| Successful source evaluation and actual source/target operand observations | Caller-supplied at local interface; production from reachable relation and consumer classification unresolved |
| Pure opcode output calculation from operand evaluations | Locally proved opcode equations; uniform two-state transport still to prove under C1.L.COMPOSE |
| Range containment for operands in the state where family contract runs | Caller-supplied; source range closure exists, but transferring it to r requires the exact eval equations, including resolved operands at original recorded lbl/idx |
| Fresh variables distinct, absent from inputs/outputs, xor/not alias | Caller-supplied in sequence contract; supply lemmas must instantiate them at the actual rewritten instruction; not guaranteed by arbitrary fr |
| Exact scalar results, OR exact-or-truthy alternative, exact chunk results outside temporaries | Locally proved as matrix above; membership contracts also need singleton length/layout when lifted |
| Original output demand permits the OR exception | Unresolved DFG-to-consumer/demand link at composition site; not an arbitrary exemption set |
| Observation preservation by same-output and fresh writes | Locally proved ao_main_observations_update/fresh; need output relation and fresh NOTIN V at call site |
| Frame equality and correct control position correspondence | Caller-supplied entry relation; local pure writes preserve frame; exact chunk lengths proved for EQ/comparator; global boundary alignment unresolved |
| Terminal/side-effect consumers, parallel selected PHIs, calls | Outside scalar peephole contract; main simulation must consume exact/truthy reads and frame/control facts without totalizing failed evals |

## Admissions and ownership

Source audit of proofs/*.sml finds no cheat in LocalProofs, RangeLocalProofs, SequenceLocalProofs or RelationProofs. The remaining frozen `ao_transform_function_correct_proof` cheat (algebraicOptProofsScript.sml:30) belongs to required C1 and its pending simulation/integration work, including C1.L.COMPOSE and C1.M; this inventory does not discharge it. Separate existing `ao_transform_function_wf_proof` / `ao_transform_function_ssa_proof` admissions in WfProofs/SsaProofs are not imported by these checked local theories and are excluded from the semantic proof dependency path by C1 guidance. Do not use them to close semantic prerequisites. No new uncovered local cheat or broken proof was discovered. Missing semantic wrappers above are identified interfaces under existing COMPOSE/M ownership, not newly asserted facts.
