# Full Concat offset-cell continuation diagnostic

Scope: C1.image.continuation. This is a source-origin audit, NOT a universal
exclusion theorem. ContinuationProbeTheory supplies checked finite comparisons.
Windows' pre-existing malformed ML quotation-list separators were repaired under
explicit PLAN authorization; Windows and CheckerBoundaryProbe freshly rebuild.

## Comparison object: all sixteen records

From ConcatRunProbe.concat_probe_compilation (ids here are concrete fixture ids):

| id | instruction | fresh off-cell role / required link |
|---|---|---|
| 0 | ALLOCA64 -> %0 | output base b, not off |
| 1 | ADD %0 32 -> %1 | output data pointer data |
| 2 | ALLOCA64 -> %2 | fresh off cell |
| 3 | MSTORE %2 0 | initialize off |
| 4 | MLOAD %2 -> %3 | first immediate reload off |
| 5 | ADD %1 %3 -> %4 | first destination = data + offset |
| 6 | MSTORE %4 padded-byte-1 | first full word store |
| 7 | ADD %3 1 -> %5 | first updated offset |
| 8 | MSTORE %2 %5 | write first update back to SAME cell |
| 9 | MLOAD %2 -> %6 | reload SAME cell |
| 10 | ADD %1 %6 -> %7 | second destination |
| 11 | MSTORE %7 padded-byte-2 | known overhanging word store |
| 12 | ADD %6 1 -> %8 | second updated offset |
| 13 | MSTORE %2 %8 | write second update back |
| 14 | MLOAD %2 -> %9 | final reload SAME cell |
| 15 | MSTORE %0 %9 | returned length in output base |

These links, not numeric ids or variable names in isolation, are the object of
comparison. The exact checked records retain concrete names; an eventual origin
argument must handle arbitrary fresh-name/id shifts. This particular 16-record
object is not the full compilation of arbitrary Concat arguments: bytestring
children, nonliteral children, zero args, and many args have other continuations.
It cannot on its own discharge the general frozen constructor case.

## Known collision's actual first mismatch

ContinuationProbe.continuation_probe_known_collision computes DROP4 of actual
compile_expr terminal_probe_call under terminal_probe_env: the entire suffix is
one INVOKE of sink, carrying %1 and %2, with no MLOAD. The fifth instruction is
therefore INVOKE, versus MLOAD in concat_probe_compiled; _known_mismatch checks
this inequality. Original header also allocates32 rather than64 in record0;
that difference was allowed by header absence, not by full equality to this
literal-Concat fixture. No corrected sink/source alternative was attempted.

The actual installed-source call environment was previously checked separately:
it has the same header, plus later non-call argument-staging instructions and an
INVOKE rejected by pointer-argument membership. Its rejection did not establish
full-code impossibility. We do not infer any universal claim from this mismatch.

## Producer/use-site table

| Candidate | Source equations | Immediate continuation / distinction |
|---|---|---|
| Actual Concat | exprLowering 3199-3217, compile_concat 2151-2175 | Direct match for literal fixed bytes: lower_value literal emits nothing; offset reload, data+offset destination, store, update, store off, recursive repeat. Final dispatcher reloads off and stores output length. Unsupported builtin tag in supported_builtin_form. |
| Empty bytes/string/dynamic array | builtinSimple 68-84; exprLowering 3341-3348 | ALLOCA(size), MSTORE(base,0), return buffer; NO intrinsic MLOAD. A caller can immediately read returned pointer, so return alone is not an exclusion proof. |
| MakeArray dynamic [] | exprLowering 3295-3304, 2218-2225 | ALLOCA(type size), MSTORE(base,LENGTH []), return; NO intrinsic MLOAD. Nonempty children start after length initialization; child may emit no code, but zero initialization then depends on length/n2w. |
| Fixed/struct Empty | compile_zero_words builtinSimple 58-64 | ADD base0 even for first word then MSTORE; no adjacent ALLOCA/base-zero pair. |
| context zero memory | context 428-435 | index0 can store directly; next index uses ADD, then store. No intrinsic reload. Whether caller supplies a just-allocated base is a separate seam question. |
| ABI dynamic static loop | abiEncoder 191-220 | allocates32 index cell, zeroes, JMP/new_block, then reloads; fails64 size and immediate same-block continuation. |
| ABI dynamic loop | abiEncoder 339-380 | allocates32 index cell, zeroes, ALLOCA32 dynamic cell, MUL/init, JMP/new_block, reloads in loop. Not required ALLOCA64/store/reload. |
| ABI parent offset | abiEncoder 281-301 | allocates32 parent cell, zeroes, immediately MLOAD src (caller-owned pointer), then MSTORE dst, encoded child, reload/update/reload parent. Size32; src is NOT definitionally new parent. Cannot silently equate caller pointer with fresh parent. |
| ABI complex dynamic offset | abiEncoder 307-321 | allocates32, writes static size (not uniformly zero), processes children, final reload. No64; child traversal emits ADD element-source. |
| ABI decode index | abiEncoder 510-516, 562ff | allocates32, zeroes, passes cell to loop with control-flow/decoder work. No64 and not Concat data/update links. |
| ECRecover | builtinMisc 32-52 | output alloc32, zero, GAS/STATICCALL/ASSERT, MLOAD output. Not64 nor immediate load. |
| ECAdd/ECMul | builtinMisc 58-99 / point forms | output alloc64 exists but not adjacent zero-store/load; call/check occurs. Inputs staged separately. |
| SHA | builtinHashing 93-136 | buffers32, stores arbitrary input, GAS/STATICCALL/ASSERT before output load. Not64 and not immediate reload after zero. |
| Bytestring conversion | exprLowering load_bytestring_as_word 1615-1631 and type dispatcher | MLOAD v; ADD v32; MLOAD data; shift/clamp. Can immediately read an Empty result (when not optimized zero-capacity conversion), but second instruction is ADD off32, not ADD saved-data loaded-offset. Returned pointer v caller-owned; no intrinsic offset allocation/update/reload sequence. |
| Bytestring source/Len/hash | builtinBytes 43-48; dispatcher Len 3135-3142; builtinHashing bytes | Caller-owned pointer loaded for length then ADD(pointer,32) (Len has only load). Len/hash tags excluded by current support. Caller seams still need source inversion, not blanket no-read assumptions. |
| Internal staging | compile_stage_intcall_args 1299-1330 | vv list retained; stack/fallback unwraps memory complex without load. Memory staging allocates after unwrap, copies/stores. The known no-parameter fixture continues INVOKE immediately. General flags/types require separate inversion. |
| Tuple/struct/array store | exprLowering 2188-2211, struct helpers; context typed-copy | Caller-owned buffer destination, usually destination ADD before copy; memory source may be loaded by typed-copy. No general allocation-read nonalias theorem established by this audit. |

Freshness issue: compile_alloc_buffer returns a fresh variable name, whereas
many MLOAD helpers take saved source/destination operands. The already available
CompilerSeams freshness results may distinguish them ONLY with their exact
counter-monotonicity/not-fresh premises. No such premise is implicitly imported
for arbitrary source syntax or cenv bindings here.

## Remaining unclassified seams / proposed origin obligation

No full matching supported source was found or checked. This is NOT evidence of
its impossibility. We have not classified all expression/call/statement/module
seams, arbitrary inherited environments, zero-code callbacks, immutable reads,
user names that may refer to pointers, or recursive ABI/copy callbacks. Even
though common intrinsic index cells are32, an Empty64 value can be immediately
read by a caller, so a direct producer-only exclusion would be unsound.

A candidate reviewed origin theorem would have to say: under body_inv of an
actual successful runtime/deploy unit, lookup_function of f in that unit,
fn_inst_ids_distinct, actual compile_expr Concat equation and fn_has_code for
its FULL result, plus the existing local expr_body_pre and pointer-frame
antecedents if genuinely used, the full linked off-cell continuation cannot
come from supported source except a real Concat origin (excluded by support).
This is a PROPOSED MISSING IMPLICATION, not an assumed lemma or added theorem.
It must account for actual generated source environments, counter freshness,
block placement, intervening no-code children, supported declaration/field
mismatches and call/ABI staging; the above table is not its exhaustive proof.
It must also handle other Concat arities/operand continuations, not just16 records.

Alternative: construct an actual installed full-code witness before attempting
an admissible frame and applying the known unsafe-store diagnostic. No such
witness was produced. No body_inv construction or universal induction attempted.
Stop here for strategist selection rather than create another generic predicate.
