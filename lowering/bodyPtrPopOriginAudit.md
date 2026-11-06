# Pop suffix origin audit (2026-11-06)

Diagnostic only. No code-origin theorem or counterexample to pop_expr_ptr_ok
has been proved by this audit. No definitions or admissions were added.

## Consumer and missing sequent

The consumer is expr_vv_sim_ptr_def (bodyPtrDefs, 296--323), instantiated
with e = Pop v10 bt, inside body_expr_ptr_ok. It supplies exactly
compile_expr cenv ty e sa = (vv,sb), fn_has_code sa sb func,
fn_inst_ids_distinct func, local_ptrs_reserved cenv sa,
~ctx_has_dalloca ctx, ~cenv.ce_is_ctor, the two return-pointer freshness
conditions, gas_admissible (eval_expr cx e) expr_vv_res_ok es,
stmt_state_rel ctx func cenv cx es s0, ghost_inv d cenv cx es G0 tn0 s0,
~s0.vs_halted, and the entry block/index equalities.
The enclosing body judgment additionally provides body_inv tops ctx cenv cx
and expr_body_pre cenv cx env e es and the operand judgment. Neither gives
supported_expr for this e.

body_inv_def (bodySim, 61--88) supplies supported_program tops and a
successful runtime/deploy unit lowering with ctx = unit.cu_context.
stmt_state_rel_def (exprLoweringProps, 412--422) includes alloca_room;
alloca_room_def at 245 supplies lookup_function func.fn_name
ctx.ctx_functions = SOME func. expr_body_pre_def (exprSimHypsDefs,
148--160) gives typing/allocation/call restrictions, not source occurrence.

The proposed missing implication is: those actual entry premises plus
the target-fragment decomposition and a supplied slice equality imply
that the header operand/location belongs to an allowed declared dynamic
array root (with full-word element), or that these entry premises are
inconsistent. This is still NOT a finalized HOL statement: the semantic
root relation, its connection to the header's value at the post-index
state, and the exact cenv-to-unit binding relation are unproved missing
interfaces. In particular a syntactic literal header alone would not
identify the arbitrary source bt or establish its type/layout equality.
Do not use this paragraph as an available lemma.

## Exact template

exprSimPopNested 75--101 already defines the storage/transient template
locally and states its shape. Do not duplicate it. For header h, starting
id i, element size z, and distinct outputs a,b,c,d,e,f,g, the nine
mk_inst terms have fields:

| offset | opcode | operands | outputs |
|---|---|---|---|
| 0 | SLOAD/TLOAD | [h] | [a] |
| 1 | ISZERO | [Var a] | [b] |
| 2 | ISZERO | [Var b] | [c] |
| 3 | ASSERT | [Var c] | [] |
| 4 | SUB | [Var a; Lit 1w] | [d] |
| 5 | SSTORE/TSTORE | [h; Var d] | [] |
| 6 | ADD | [h; Lit 1w] | [e] |
| 7 | MUL | [Var d; Lit (n2w z)] | [f] |
| 8 | ADD | [Var e; Var f] | [g] |

Every instruction id is i+offset. compile_dynarray_pop_def
(exprLowering 1152--1169) emits this order without branches. Memory uses
MLOAD/MSTORE and the actual word_scale in instruction 6 (normally 32),
not storage's literal 1. context 134--148 also permits calldata/code
load branches with INVALID stores; these must be excluded from typing
premises, not silently treated as memory.

## Bounded emitter ledger

A search of direct SUB emitters in lowering/defs/*.sml is recorded in
TO_pop-20261106T070927Z_m0690_t001. This is a candidate inventory, not a
proof that computed opcode emitters or all generated instructions have
been covered.

| candidate | comparison | status |
|---|---|---|
| compile_dynarray_pop | exact nine-term template, all three mutable locations | possible, intended producer |
| AugAssign/Sub | stmtLowering 884--907 loads target then compiles RHS then compile_safe_sub then stores | complete internal match excluded textually: exprLowering 321--336 puts checks AFTER SUB, between SUB and store |
| AugAssign/UnsafeSub at 256 bits | rhs code then SUB then store can match offsets 4--5 | unresolved prefix: RHS must produce offsets 1--3 while SUB still reads loaded a, not last fresh result; requires return-operand/freshness interface |
| safe div/mod | exprLowering 391--439 produces double ISZERO and ASSERT | internal extension excluded textually: next opcode is Div/SDIV/Mod/SMOD, not SUB |
| PrevHash | exprLowering 1516--1519 produces SUB [num;1] | internal extension excluded: next opcode BLOCKHASH, not store |
| unary negation / shift / ceil helpers | SUB with literal first operand or different second operand | requires operand constructor distinctions/fresh-output discipline, not opcode-only exclusion |
| builtinStrings | SUB inside loops, including [zd_pos2;1] | unresolved for general emitter proof; no suffix equality checked |
| module/context guard ASSERT | not an array operation | unresolved cross-combinator extension; inventory alone insufficient |
| source Assert | stmtLowering 913--933 emits JNZ and new blocks, not ASSERT | direct bare-Assert template excluded; says nothing about ASSERT in expression lowering |

## Cross-boundary cuts

For a two-fragment concatenation, all eight proper cuts need treatment:

| cut after offset | invariant needed / current status |
|---|---|
| 0 | next fragment must reuse a for zero test; boundary variable visibility/returned operand invariant missing |
| 1 | must consume intermediate b and return to a at offset 4; intermediate variable visibility missing |
| 2 | must consume c as ASSERT, then reuse a; same missing visibility invariant |
| 3 | immediate SUB reads a, not the last generated c; possible only if caller retained a; AugAssign/UnsafeSub is the important unresolved class |
| 4 | caller may store fresh result d at retained h (assignment); prefix must still be classified |
| 5 | subsequent address arithmetic must reuse h and d; result-escape/retained-operands interface missing |
| 6 | MUL must reuse d after e was generated; same missing interface |
| 7 | final ADD must reuse e and f; same missing interface |

Instruction ids do not alone exclude ANY such cut: emit_op/emit_void
(emitHelper 20--42) obtain consecutive ids across ordinary monadic bind.
Likewise distinct fresh outputs can occur across boundaries. A cut
crossing a new_block cannot be a single-block slice, but this only helps
when the emitter really changes blocks. Arbitrary adjacent fragments in
one block remain unresolved. Multi-fragment cuts require a compositional
version of the same invariants, not just checking these eight rows once.

## Stop boundary and candidate invariant

No concrete full-template collision was found or checked. Uniqueness has
not been established. The bounded audit reaches missing compiler
infrastructure: a compositional generated-block invariant must record
which previously fresh operands are exposed at each monadic/source
boundary, which caller-retained operands can be reused, and which
instruction prefixes/suffixes cross each boundary. It must retain exact
mk_inst operands, output names, and ids. It must cover computed opcodes,
block packaging, and internal call continuation blocks as well as direct
SUB sites. A compiler-wide induction without that strengthened interface
is not justified by this audit.

Even if that syntactic invariant succeeded, a second bridge must connect
the classified source root's compile environment/layout to the arbitrary
consumer's cenv, bt and post-index state. No theorem for that bridge has
been identified here. The audit intentionally stops rather than asserting
that supported source Pop restrictions transfer through instruction
containment. Request strategy review before further source proof work.
