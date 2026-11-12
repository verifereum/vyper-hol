# Single-argument encoder suffix interface diagnostic (C1.2.2.2)

## Checked artifact and scope

`abiEncodeSinglePtrInterfaceProbeScript.sml` contains the **typechecked term**
`abi_encode_single_ptr_suffix_conditional_statement`, not a theorem and not an
admission. It is the proposed exact statement for
`abi_encode_single_ptr_suffix_conditional`. Every variable is explicitly
universally quantified. Its only semantic assumption beyond the unary suffix
context is `expr_body_pre` of the whole builtin; `code` is constrained to the
actual word/nonword lowering. The first conjunct is exactly the universal
closure of `abi_encode_bytes_pointer_posts` in abiEncodeSinglePtrResult.
The conclusion is precisely the successful gas-summary alternative at lines
36--51 of `type_builtin_unary_vv_sim_ptr_origin`, specialized to `AbiEncode F m`.
There is no decoder-origin exceptional alternative for encoding.

The build checks parsing/type compatibility only, not the truth of this proposed
statement. In particular this component does NOT claim to have proved execution,
caller discharge, or the conditional suffix.

## Shared premise-discharge table

| Phase / suffix premise | Existing route / remaining proof task |
| --- | --- |
| argument succeeds with typed physical value and ABI conversion | `abi_encode_operand_success_type`, `abi_args_success_ready`, `expr_body_pre_physical_type`, `abi_args_fits_conversion` as used in NonwordCase:173--196 and WordCase:99--111 |
| descriptor plan and admissibility | `abi_encoder_translation_admissible` and translated source metadata; physical lowered type is used, not an invented post for staged memory |
| fixed representatives for every taint-respecting memory | `abi_encoder_source_window_robust`: choose ct/rv before mem, preserve equality of encodings only |
| phase trace, fn_has_code splits, live operands, fresh registers | `lower_abi_encode_trace`, `lower_abi_encode_frag_facts`, `abi_encode_translated_operand_liveness`, `abi_encoder_counters`, setup/finish shape |
| local pointers, return buffer/PC stay old | `local_ptrs_reserved_next_var`, compiler growth, monotonicity of not_fresh_at; unary context already supplies origin freshness |
| same-endpoint ordinary state and pure frame | `abi_encode_phases_caller_state` (438--472) and `abi_encode_phases_caller_pure_frame` (643--673); they require no source frontier or source/output separation |
| ordinary bytes vv_post | `abi_encode_bytes_vv_post` / word observation result boundary, using same endpoint; retain origin wb_frame, source scopes domain, and pure-frame composition |
| result pointer posts | conditional bridge premise; output cap is outsz; discharge BOTH val_store_size and lowered type_memory_bytes bounds using builtin result capacity, not just payload length |
| ghost_kept from argument origin to output | compose argument kept with stage kept (word only), then phase kept, with compiler growth; do not replace this by same-state ghost_inv |

## Positive nonword table (cap = val_footprint tv v > 0)

* `abi_encode_nonword_source_resources` supplies clean operand, robust lowered
  val_in_memory, covers for precisely cap, and sb+cap <= pre-allocation frontier.
* `abi_encode_translated_nonword_phase_resources` supplies output row alternative,
  room/invariant, outsz and address bounds, source/output disjointness, method
  exclusion, and scratch separation. Instantiate obs = func; its inclusion
  premise is reflexive. Use the ordinary representative only for its encoding
  equality/length. The robust representative need not equal its type or value.
  All byte-dependent geometry transfers through equality of encodings.
* `abi_encoder_source_window_robust` supplies the robust window on the SAME
  operand word and cap. Equal eval_operand results identify source word, not ABI
  representatives.
* The accepted `abi_encode_staged_phases_caller_ptr` applies after the explicit
  numerical inequalities 32+w <= outsz, p <= d, d+len <= p+outsz and counter
  inequalities have been discharged. Its endpoint alone supplies the pointer
  and ordinary result.

## Zero nonword table (cap = 0)

* Use the zero alternative of
  `abi_encode_translated_nonword_phase_resources`: it explicitly supplies
  `ei = AbiCopy 0 \/ ei = AbiComplex []` and empty encoding. This is the
  translated descriptor lemma, not `abi_encode_zero_footprint_plan` on a
  potentially different syntactic plan.
* Clean operand and robust representation still come from
  `abi_encode_nonword_source_resources`; fixed ct/rv from the robust source
  contract give `abi_encoder_window_input ei ct rv sb 0 mem` for every permitted
  memory. Empty-byte equality transfers from the ordinary representative.
* The remaining output allocation, method/output disjointness and scratch facts
  are unconditional in the translated resources theorem. Project its scratch
  conjunction to discard the source slice component.
* Apply `abi_encode_empty_phases_ptr` directly. There is NO source coverage,
  source frontier, source/output geometry or method/source exclusion premise.
  Do not pass through the positive bridge at cap=0.
* An empty caller bridge is useful but not an external interface repair: take
  exactly the antecedent of `abi_encode_empty_phases_ptr`, append
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
   32+w <= outsz /\ p <= d /\ d+LENGTH(enc at av) <= p+outsz`,
  and append exactly the following to its existential endpoint conjunction:
  `stmt_state_rel ctx func cenv cx es actual /\
   pure_frame cenv func es st initial actual /\
   FLOOKUP actual.vs_allocas st.cs_next_id = SOME(p,outsz) /\
   p+outsz <= actual.vs_alloca_next /\ actual.vs_alloca_next < dimword(:256)`.
  Quantify all free variables. Existing StateTransport premises match the
  empty contract's setup frame, window_strong_result, registered effect,
  preservation and exec frame exactly (wc = ctx, obs = func); neither transport
  theorem asks for positive source geometry. This bridge remains to be proved.

## Word table (cap = 32)

* Compiler word path stages `compile_alloc_buffer 32` then MSTORE.
  `abi_encode_word_source_stage` supplies the pointer path, robust memory
  interpretation, covers 32, clean operand (from covers), kept, state and cursor.
* `abi_encode_word_allocation_geometry` takes the staged source row
  `FLOOKUP initial.vs_allocas source_id = SOME(sb,32)` and
  `source_id <> st.cs_next_id`. Recover that row for the staging ALLOCA and its
  distinct site from stage shape / row preservation; this is a strict local
  proof obligation, not supplied by nonword expr_post.
* `abi_builtin_encode_word_info` makes ei = AbiCopy 32 and maxlen = 32;
  word encoding has length 32. Robust source gives the same fixed window with
  cap 32. Geometry theorem already includes the five framing inequalities.
* `abi_encode_word_body_no_alloca` discharges the scratch implication vacuously.
* Compose staging path and positive phase path (both count 0). No nonword
  `expr_post` is asserted for the staged memory operand.

## Gas-summary introduction

Use `fragGasPathPtr.gas_summary_ptr_at_def` directly with marks = [].
Choose res = INL (Value (BytesV payload)), es_end = ee, r = OK actual, and the
phase ghosts. `gas_explicit [] readings = []`, LENGTH [] = 0. Prove the
source equality for EVERY tail by the pure builtin evaluator equations:
`bind (lift_sum (evaluate_type_builtin ...)) (\w. return (Value w))
 (ee with gas_obs := tail) = (res, ee with gas_obs := tail)`.
The source typing/conversion lemmas supply the successful evaluator result.
Since ee.gas_obs = [], removing observations recovers ee. No source gas charge
is introduced by the ABI builtin. The phase pointer path already has the
required count zero; in words prepend staging with count zero. The remaining
summary branch is the successful post, not expr_exit.

## Review requests / remaining internal obligations

The typed interface exposes no new external mathematical premise after the
empty contract repair. Still unproved: empty caller bridge; nonword resource
assembly with fixed robust representatives; word staging-row/geometry assembly;
same-endpoint observation + origin framing; pure gas-summary packaging and
final conditional proof. The strategist must schedule these, not this note.

Importing `abiDecodePtrUnaryOrigin` to typecheck this term first failed in
unrelated `abiDecodePtrStaticReject` and `abiDecodePtrSupportedTarget`. The
probe does not need that theorem dependency and now imports only its required
constant providers. Final unary composition still depends on that provider;
repairing it is outside C1.2 ownership and should be handled by the lead.
