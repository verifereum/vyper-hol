# Terminal-pair origin diagnostic

Checked theory: bodyPtrBytestringBuiltinsTerminalPairProbeTheory.
This is not an installed-unit counterexample or a refutation of the frozen judgment.

## Decisive computation

The E0244 base literal has annotation A, constructor B, no fields. Its allocation
is 32 bytes. Selecting A.second adds 32. Annotate the selected value Bytes[1]
(the support grammar checks that this is a place type, not that it is the field's
type). Follow it by Empty(Bytes[1]) in compile_multi_vvs. The actual emitted list
is precisely ALLOCA32 %0; ADD %0 32 -> %1; ALLOCA64 %2; MSTORE %2 0.
All declarations and both operands pass support. The Empty result has a base_ptr
with SOME buffer metadata; the Attribute result has mk_ptr with no buffer.

The same prefix is checked in actual compile_expr for an IntCall sink carrying
these two operands. sink is declared Internal with no parameters, NoneT return,
and empty body. supported_program and supported_effect_expr both hold: support
does not enforce call arity. The test environment has the built struct map, zero
returns, no stack flags, and concrete function-label metadata. It is NOT proved
to be build_compile_env for an installed package; no body_inv is asserted.

## Source-site inventory / adjacency constraints

Search scope: production lowering/defs, excluding bytecode evaluation fixtures
and agreement/counterexample theories. MSTORE sites split into the following
classes. This is a source audit, not a formally proved completeness lemma.

* exprLowering 3207-3212: Concat directly emits the entire bad window. Unsupported
  builtin form, but exclusion of this AST alone is insufficient (checked above).
* builtinSimple 68-84: Empty complex allocates size, then directly zeroes the base
  iff zero_length_only. At size 64 this is the required final pair; the branch
  includes dynamic bytes/string and dynamic arrays. No predecessor barrier.
  Fixed/struct zeroing uses compile_zero_words (58-64), which emits ADD even at
  offset zero, so does NOT supply an adjacent allocation/base-store pair.
* exprLowering 3295-3304 / 2218-2225: MakeArray SOME allocates declared capacity,
  then dynamic-array initialization stores literal LENGTH es. Zero iff list is
  empty (modulo n2w); a 64-byte dynamic-array type and [] give the final pair.
  Tuple MakeArray NONE does not initialize a length word.
* context 428-435: compile_zero_memory_loop at index zero directly stores to its
  supplied pointer; other indices first ADD. This is a seam producer when its
  caller just allocated that same 64-byte pointer. It must not be confused with
  builtinSimple's ADD-zero loop. Other context stores take arbitrary supplied
  values, or values freshly loaded/computed before the store.
* abiEncoder 195-197, 342-344, 510-512: literal-zero index cells allocate 32, not
  64. 265 padding zero has preceding address calculation. 287 parent-dynamic
  offset zero takes supplied pointer: inspect callers for a cross-helper seam.
* builtinMisc 43-46: ECRecover output zeroing allocates 32, not 64. Other EC
  stores take operand values. builtinStrings zero-digit stores literal 48/1,
  not 0; nonzero loop stores variable operands.
* stmtLowering 173: tail padding zero has computed tail address, not fresh base.
  AnnAssign 805-837 can skip source instructions and store zero to the declared
  pointer for empty values: emit_local_alloca / expression / initialization is
  a cross-helper seam, not safely ruled out by inspecting expression helpers.
* All remaining stores are operand- or numeric-literal-dependent: context pointer
  store, typed copies, bytestring length store, expression array/tuple/struct and
  internal-call staging, primitive literal staging, literal bytelike lengths,
  mapping hashing scratch, Slice scratch, AbiEncode scratch; builtinHashing,
  builtinBytes, builtinAbi, builtinSystem, builtinCreate; statement assignment,
  return/loop stores; module parameter/default staging. They require either
  ruling out literal zero, ruling out size 64, or proving an intervening emitter.
  Fresh MLOAD/arithmetic/INVOKE values are Var rather than Lit 0 even if their
  runtime value is zero. An arbitrary value parameter can still literally be
  zero, so a generic producer lemma cannot exclude this class by opcode alone.

## Consumer seams tested / remaining

compile_make_tuple and compile_make_array_elems insert destination ADD after
compiling each child and before copying. They do not preserve this pending2
suffix across an ordinary child boundary. In contrast compile_multi_vvs retains
LocatedValue and immediately calls the next child. Internal and external calls
use this actual helper. The checked internal-call prefix realizes the collision.
A standalone nonword lower_value also need not emit an instruction on unwrap.

## Consequence for strategy

The pending2 place can meet the final pair in supported compiler syntax. There
is therefore no validated purely syntactic expression-level exclusion boundary.
Do not embark on a general terminal-pair-origin exclusion induction based on
absence of Concat. Installation under actual build_compile_env and package
checks remains unverified; the checked local environment must not be passed off
as a supported runtime unit or an admissible body frame. Request strategist
review before further global image work. The frozen target remains unchanged.
