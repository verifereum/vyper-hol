# Result-layout and Entry dependency audit (E0242 follow-up)

This is a source/signature audit, NOT a proof of supported compiler-image
exclusion and NOT a counterexample to the frozen body judgment.
Checked fixtures: `bodyPtrBytestringBuiltinsResultLayoutAuditTheory`.
The earlier TraceDependencyAudit is an allocation-only inventory; all its
MISSING labels were subsequently closed for allocation_trace, not for Entry.

## Available hypotheses on the actual image route

`bodySim.body_inv_def` (61-88) supplies supported_program, an actual runtime or
deploy unit, and cenv.ce_struct_fields = make_struct_fields_map tops (plus
acyclic metadata and function-table equalities). It does NOT supply source
well-typedness of every function expression. `supportedProgram` explicitly
checks syntax/bindings/return layout, not check_contract or source_typing_ok.
Runtime-unit lowering (`compileVyper` 1402-1429) checks immutable size, external
return-buffer bounds and fn_allocs_ok, not expression typing. Deploy uses the
parallel package route. An expression's local expr_body_pre/expr_sim_inv may
supply well_typed_expr and sfields_tenv_consistent; those local semantic facts
are NOT by themselves a theorem about all functions installed in the unit.

Existing stronger semantic interfaces found by theorem search:
* exprOpenCopies.struct_literal_store_paths: expr_sim_inv ce cx env es and
  well_typed_expr env (StructLit ann nsid kes) imply every actual compiler
  field lookup fty equals expr_type e for members.
* exprSimAggregateLayout.struct_literal_lookup_types: expr_body_pre for the
  literal implies EVERY actual lookup = SOME(expr_type e,type_memory_bytes ...).
* exprOpenCopies.supported_copy_types_store_path: supported_copy_types dst src
  implies is_word_type dst OR is_bytestring_type dst OR dst=src.
* compileVyper.build_compile_env_ce_struct_fields identifies built metadata;
  typedCopyMetadata.build_compile_env_struct_metadata_acyclic requires
  struct_args_unique tops and supported_declaration_headers tops.
None of these allows importing local source typing into a unit-wide syntax
induction without an additional justified bridge.

## Exact LocCode result sources

Open expression body uses ret_ty = expr_type e, independently of requested ty.
Guarded mutual equations at exprLowering 3408-3431 preserve the body result;
invalid out-of-bound callbacks return StackValue via INVALID.

| Source | Returned type and location | Needed justification |
|---|---|---|
| TopLevelName (3000-3009) | annotation ret_ty; ImmutableLoc -> LocCode | Definitional. supported_pure_expr equates annotation to supported_immutable_type for immutable roots; env lookup still needs actual metadata bridge. |
| Subscript (2278-2324) | every place branch returns LocatedValue ret_ty at base callback's location | Definitional returned type. LocCode can only propagate from base. place_type selects map/tuple/struct/array traversal, not returned annotation. No equation of element layout and annotation follows from support alone. |
| Attribute (2331-2351) | LocatedValue ret_ty at base callback's location | Definitional returned type; offset comes from base annotation plus metadata. LocCode only propagates from base. |
| Pop (3012-3029) | LocatedValue ret_ty at target location | Definitional returned annotation, although size is based on target descriptor element type. supported effect Pop is ONLY a storage/transient top-level dynamic array of full-word elements (supportedExprForms 171-178); actual target-table bridge must exclude code. |
| Name (1490-1505) | memory place or invalid stack value | ce_vars lookup has no ImmutableLoc branch; no LocCode. |
| Literal / IfExp / StructLit | bytelike/multiword memory or stack; no code | IfExp result place is explicitly LocMemory; StructLit base_ptr is LocMemory. |
| ordinary builtins | stack or LocMemory; no code | as_ptr_val sites explicitly use LocMemory. Lowered operands may be code, but their result is not propagated as a code place. |
| type builtins | stack or LocMemory; no code | Empty/AbiEncode/AbiDecode allocate memory; other tags are stack-valued. |
| calls | return buffers LocMemory or stack/invalid | Internal/External call branches use base_ptr/mk_ptr LocMemory, not code, despite differing returned type. |

`lowered_value_type_def` 161-175 differs from expr_type ONLY for bytelike
literals, AbiEncode, and internal calls. Those forms do not return LocCode.
Thus the zero-code callback conclusion expr_type e = returned_ty =
lowered_value_type ce e is source-justified as a proposed result-shape theorem,
not yet checked by a global recursion proof. It need not be a typing theorem.
All requested types must stay generalized for child calls (attribute/subscript
and IfExp pass inherited requested ty, not always expr_type child).

## Checked disputed struct case

The fixture declarations are E = empty struct, A = {f:E}, B = {f:uint256},
plus private immutable z:E. Checked computations prove:
1. supported_program for these declarations;
2. supported_pure_expr of StructLit (StructT A) B [(f,TopLevelName E z)];
3. actual compile_expr of that child under ImmutableLoc 0 returns LocatedValue
   E (mk_ptr (Lit 0w) LocCode), unchanged state, for every requested type;
4. built E memory size is zero, but built B.f lookup is (uint256,32).

Hence E0242's sufficient exceptional struct callback qualification is NOT
implied by supported_pure_expr plus matching built metadata. The whitelist
checks supported_struct_elements using the literal's ANNOTATION A, while
compile_expr_body calls compile_struct_lit with its CONSTRUCTOR NAME B.
supported_main_nsid B does not equate A and B. Even knowing the child returned
type equals expr_type/lowered_value_type does not fix that discrepancy.
This witness is a local interface mismatch, not a proof of image_bad or a full
installed body frame. In this particular fixture the destination is a word,
so the store is MSTORE and can be handled without equal-layout copying. Do not
conclude the global image theorem or frozen target is false from the witness.

## Exhaustive remaining Entry producer inventory

Legend: P = proved boundary; F = finite compiler-effect composition still to
prove; R = structural compiler recursion still to prove; S = unresolved semantic
or syntax/result-layout premise. No allocation_trace theorem is relabeled P
for Entry. Every row accounts for the actual three open bodies (2935-3406),
including unsupported tags, which must either be excluded by support inversion
or have their producer certified. Calls are included through compile_call.

### Expression body

| Cases | Entry dependencies / status |
|---|---|
| Literal | F alloc/store for bytelike literals; R compile_store_byte_chunks DROP32; primitive literals unchanged. P allocation Entry and MSTORE reset available, not literal wrapper. |
| Name | F lookup/return/INVALID. |
| IfExp | P word-only stack-result callback probe; F general compile_ifexp_arm/materialize and all control-flow joins; S actual nonword result-layout conversion. |
| AddMod/MulMod/PowMod256 named fast paths | F name-load/unwrap/modular operation; P unwrap primary; no fast-path Entry theorem. |
| Builtin / TypeBuiltin | mutual callback contract, corresponding tables below. |
| Subscript | F mapping hash/tuple offset/array index and bounds; P word-copy/ptr-load boundaries only; S saved base operand and terminal-allocation interaction for arbitrary ADD. |
| Attribute | F single ADD after base callback; S base place/offset can create pending2, so Entry of child alone is not a valid contract. |
| StructLit | P conditional compile_struct_lit_entry and allocation Entry; S qualification fails on checked mismatched-constructor fixture; no complete supported-source closure. |
| FlagMember | unchanged state; rejected by supported_pure_expr. |
| TopLevelName | F lookup/return/INVALID; unchanged code branch. |
| Call | F/R/S call inventory below. |
| Pop | F target-pointer traversal and dynarray_pop; R target recursion; supported Pop restricts location but still needs metadata bridge. |

### Ordinary builtin dispatcher (all tags)

| Tags | Entry dependencies / status |
|---|---|
| Bop | F binop/checked arithmetic and comparisons, bytestring hash, list/array membership; R list membership and multi_exprs; child lower_value needs Entry plus exact unwrap tail handling. Nonalloc arithmetic can use P memory invariant only with its no-tail input, not arbitrary Entry. |
| Not / Neg / Abs | F invert/neg/clamp/abs after child lower_value. |
| Env / Acc | F env-var opcodes/accessor; Acc may recurse into child. |
| Keccak256 / Sha256 | F bytes/bytesM/word hash producers with scratch allocation; excluded by current supported_builtin_form. |
| CalldataLen / Len | F calldatasize/ptr-load wrappers; excluded by whitelist, although ptr-load P with no-tail. |
| BlockHash / BlobHash | F wrappers/conditional ops. |
| AddMod / MulMod / PowMod256 | F modular operations after three/two child lowers. |
| Ceil / Floor | F arithmetic; excluded by whitelist. |
| ECRecover / ECAdd / ECMul | F scratch allocations/copies and precompile sequence; child unwrap P only from no-tail. |
| Concat | Direct four-record bad header; cannot preserve Entry. Excluded by supported_builtin_form; no callback theorem may silently include it. |
| Slice | F builtinBytes slice family; excluded by supported_builtin_form, so reject in supported induction. |
| Uint2Str | F full emitted CFG (not runtime recursive loop); fresh buffer / offset / stores / block joins need Entry proof. |
| AsWeiValue | F decimal/int helper; admitted form restricts unsigned operand. |
| MethodId | F literal/runtime hash; excluded by whitelist. |
| MakeArray NONE | P conditional tuple consumer; allocation prefix P; S actual zero-code callback result shape still to prove. |
| MakeArray SOME | R array elements, F length-word init, S destination/source layout qualification; no Entry consumer theorem yet. |

### Type builtin dispatcher (all tags)

| Tags | Entry dependencies / status |
|---|---|
| Convert | F conversion/clamp/widen-copy, scratch allocation, child lower; metadata pure. |
| Empty | F zero_length_only branch; R compile_zero_words; zero count may leave allocation but Entry allows that. |
| MaxValue / MinValue / Epsilon | unchanged state. |
| Extract32 | F bytestring source/load/clamp; excluded by current whitelist. |
| AbiEncode | R encoder mutual family, F lower_abi wrapper, R tuple staging and store_abi_tuple, S arbitrary loader/clamp/callback contracts must be exact. Only F(SOME mid), singleton tuple form currently admitted; cannot infer all encoder branches disappear without inversion. |
| AbiDecode | R decoder mutual family, F lower_abi_decode/offsets/clamps; admitted F with tuple result of at least two supported scalars. |

### Calls and creation reached through expression body

| Cases | Entry dependencies / status |
|---|---|
| Internal | R multi_vvs, stage_intcall_args and store_multi_results; F materialize/unwrap/copies and INVOKE multi-output. S callee return layout. |
| External | R kwargs/extcall_store_values; F ABI materialization/decode/default handling and return buffers. Supported operands are pure and parameter types words; exact source support inversion needed. |
| Send | F child lowers/CALL/ASSERT (supported 2/3 operand forms). |
| RawCallTarget / RawCallCalldataTarget | F outbuf/finish/msg-data, R kwargs; excluded by supported_effect_expr. |
| RawLog / RawRevert / SelfDestructTarget | INVALID branch; excluded. |
| CreateTarget | F creation snapshot/dispatch, R ctor tuple/blueprint args/salt staging, ABI/copy dependencies; excluded by supported_effect_expr. |

### Shared proved interfaces and limitations

P: MemoryEntry covers copy_memory, copy_memory_dynamic, byte offset,
bytestring length/store, five-way typed-copy and store_memory, under Entry AND
no terminal allocation. UnwrapEntry covers ptr-load/store, immutable-copy,
word-copy, ensure and unwrap with its explicit code-zero exception. Allocation
preserves Entry only; MSTORE can reset Entry from Entry. Delimiters/block switch
interfaces are P. AggregateConsumer/Entry handle tuple and struct recursion
under the EXACT conditional result-layout premises in their source. The
unconditional three-way compiler allocation_trace is P but does not imply Entry.

## Proposed joint recursion contract and unresolved decision

A future source theorem should quantify cenv, ALL requested types, compiler
state, environments and supported pure/effect/place carriers together, and
return (i) Entry, (ii) allocation_trace, (iii) actual result-shape information:
LocCode implies returned type = annotation = lowered_value_type. It must NOT
require universal no-tail. Supported expression/place children and the
builtin/type dispatchers have different support predicates; guarded callbacks
also need their size bound and invalid fallback. Expressions/effects are a
joint carrier, not circular independent assumptions.

This proposed contract is NOT yet fully validated: Attribute and tuple/struct
place-offset ADD need a saved-operand/frontier condition rather than child Entry
alone, and the checked struct-constructor-name mismatch defeats the current
sufficient exceptional consumer qualification. The actual memory boundary can
handle word/bytestring destination branches more generally than same-layout,
but claiming arbitrary mismatched typed copies safe from terminal allocation
would be unjustified. Strategist must choose a broader validated consumer
boundary, strengthen a justified carrier with actual source typing, or replace
the candidate frontier architecture. Do not silently add typing assumptions to
the frozen target, restrict supported_program, or claim unit closure from the
conditional tuples. Statement/wrapper/installed-unit proofs remain separate
required obligations after the three expression-body carrier is genuinely closed.
