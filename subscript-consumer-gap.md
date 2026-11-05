# Sequential subscript consumer audit (C1.Operands.ConsumerGap)

## Scope and status

This is a signature/use-site diagnostic, not a proof or a counterexample.
Frozen target unchanged. E0062 is committed as b77efa085. No new instruction
adapter or global strengthened execution predicate is proposed here.

## 1. Actual compiler and S1 consumer

`lowering/defs/exprLoweringScript.sml:2278-2325` is authoritative:
compile base at A -> B, retain `vv_operand base_vv` and its location, then
`lower_value compile_expr cenv ty idx` at B -> C, then
`compile_array_subscript` at C -> D. In the fixed-memory case the arguments
are dyn=F, cnt=n, ws=32, esz=elem_size_in_location cenv LocMemory elem.
The result is LocatedValue of the child operand in the original location.

There is NO completed S1 endpoint composition proof to replay:
`alan-ref/s1-places-pop/exprSimPlacesScript.sml.txt:104-128` delegates the
array branch to `compile_subscript_array_case`; its actual implementation
in `alan-ref/s1-places-pop/exprSimSubscriptArrayScript.sml.txt:12-38` is
admitted and explicitly describes the retained-local-place gap. Thus a
request to follow its *proof* endpoint split cannot be satisfied. The split
above comes directly from compile_subscript_def, not from an S1 theorem
showing the retained base still represents its source result.

`bodyPtrPredsScript.sml:20-26` gives both operand judgments after body_inv
and expr_body_pre are supplied. The frozen conditional index hypothesis
can be instantiated using any successful base eval, including the marked
source run; it does not itself provide the index's expr_body_pre.
`exprSimHypsDefsScript.sml:148-160` lists that precondition: semantic
invariant, well-typing, byte widths, allocation limits, call safety,
no EVM run, supported internal calls and ABI side conditions. A sequential
preparation wrapper must derive the index instance at the source state
following base evaluation. No ready subscript-specific wrapper was found.
This is not licensed as a new hypothesis of the target.

### Normal-endpoint ledger

At base endpoint t1,G1,tn1 (compiler B), expr_vv_sim_ptr_def
(bodyPtrDefsScript.sml:245-274) provides vv_post, exact PC, ghost_inv,
ptr_vv_ok, memory-base ptr_buf_ok, and root ghost_kept.
At index endpoint t2,G2,tn2 (compiler C), expr_sim_ptr gives expr_post,
exact PC, ghost_inv, ptr_val_ok and ghost_kept relative to B,t1,G1,tn1.
The index's normal value v and operand i are from that SAME execution.
Its ordinary post contains stmt_state_rel, operand value relation and
frame clauses (loweringPostsScript.sml:251-265).

Compiler facts still need a composition preparation wrapper: decompose
compile_subscript/lower_value; slice fn_has_code to A-B,B-C,C-D using
fragExec's fn_has_code_split/start/mid (208,231,246); obtain variable/id
monotonicity from the existing ci_mono family (including
exprLoweringProps:1743,2064,2108) and propagate reservations using
local_ptrs_reserved_next_var (1016) and not_fresh_at_mono
(stmtFragPtrScript.sml:46). These are compiler bookkeeping, not retained
place semantics. `expr_body_pre_lower_value_word_shape`
(exprSimSource:532-548) supplies monotonicity and non-Label word output
once the index precondition is established.

## 2. Critical correction: fixed arrays do NOT require index NONE

`compile_array_subscript_def` (exprLowering:1362-1389) emits LT
[idx_op; Lit(n2w n)] for fixed arrays. Signed negative checking is SLT
[idx_op; Lit 0w]. `access_ok_def` (ptrDiscipline:530-558) imposes its
provenance comparison restriction ONLY on LT/GT/EQ with operand list
[Var u; Var w]. Thus the fixed-array comparison does not need absent
index provenance, irrespective of whether idx_op is Var or Lit.
The taint check still needs clean index taint, supplied by ptr_val_ok.

MUL [idx_op; Lit esz] makes a fresh offset with NONE provenance even if
the index had provenance: out_prov_def (ptrDiscipline:169-186) forwards
only ADD/SUB/ASSIGN, not MUL. The final ADD [base;offset] therefore takes
base provenance. No op_prov index=NONE premise is needed for this fixed
selector arithmetic. ADD/MUL have no memory access check of their own.
This does not yet prove a counted suffix or its coverage bounds.

For dynamic memory/storage arrays len_op is a freshly loaded Var with
NONE provenance. If index is also Var, LT [index;len] triggers the
comparison clause when index has provenance; that clause demands BOTH
variables have the same SOME site, impossible for a NONE length result.
Here NONE for a Var index is genuinely necessary for access_ok at that
instruction, not just a convenient sufficient precondition. Literal
indices bypass the Var/Var clause. A general strengthening must therefore
be scoped to consumers which actually need it, not imposed on fixed
arrays or all expressions by default.

## 3. IntCall route: execution already comes from vv judgment

Let the index be Call ann (IntCall id) args dret. Use its existing
expr_vv_sim_ptr at B, not a new runtime call theorem. Decompose lower_value
(definition at exprLowering:2002) to compile_expr B->M plus unwrap M->C.
`bodyPtrSubscriptCallResult` supplies compile_expr_intcall_result:
located LocMemory OR StackValue declared_return_type (Lit 0w).
This is routing only; the normal vv execution supplies the actual post.

Premise classification for `unwrap_memory_word_prefix_ptr`
(bodyPtrSubscriptMemoryUnwrap:86-112):

- marked prefix: gas_summary_ptr_at_marked (gasSummaryComposePtr:38-46)
  extracts the SAME summary witness; gas_outcome_ptr_def additionally has
  an exempt-certificate alternative, which must remain an outcome branch.
- vv_post, ptr_vv_ok, ghost_inv, root ghost_kept and exact M PC: directly
  supplied by expr_vv_sim_ptr_def on its normal branch.
- LocMemory: compiler result routing, not runtime inference.
- successful read at unchanged ee: vv_holds memory clause
  (loweringPosts:332-349) supplies an existential value and read equality.
  It also equates declared located type with expr_type idx. Therefore
  is_word_type declared type needed by unwrap follows from word index
  plus vv_post; no call metadata typing inversion is needed on this branch.
- evaluate_type and value_has_type: expr_body_pre_runtime_typed
  (exprSimSource:558-577), or expr_body_pre_word_value (518-529), on the
  actual source execution and read. Instantiation must use the marked
  source state with explicit gas observations. expr_body_pre_gas_obs
  (exprSimSource:27) handles this, rather than assuming no source reads.
- ee.gas_obs=[]: summary normal post is already evaluated at
  es_end with gas_obs:=[] (fragGasPathPtr:67-76). For a normalized marked
  endpoint, use record update idempotence; marked execution permits
  replacing es_end by its gas-normalized version. Small packaging wrapper
  needed; no assumption that call prefix marks=[] is justified.
- MLOAD emit equation: lower_value/unwrap_value split plus located type
  equality and compile_ptr_load at LocMemory (unwrap_value:965-978).
- compiler monotonicity, reservations, return-PC/buffer oldness, suffix
  code: compiler preparation wrapper as in section 1, starting with the
  exact antecedents of expr_vv_sim_ptr_def (248-260).
- nonhalting at M: not exported as a separate vv post conjunct. Needs
  derivation from ordinary stmt_state_rel/state_rel or its supporting
  lemma; do not assert it merely from gas_path_ptr ending OK. This is a
  specific ordinary-post interface obligation for the wrapper.
- no dalloca: inherited unchanged from vv judgment antecedent.

For literal branch use unwrap_literal_word_prefix_ptr
(bodyPtrSubscriptLiteralForward:19-39). vv_holds StackValue supplies read
and ordinary value facts; it DOES NOT imply tv=Value v. ptr_vv_ok gives
ptr_val_ok for that same read. No type-metadata alignment or load needed.
The compiler's StackValue unwrap emits no code. This branch retains
s,G,tn exactly. Ghost_inv, ghost_kept and PC are untouched.

Thus the IntCall route is viable conditional on the ordinary/compiler
preparation wrapper, not on a new callee theorem or producer induction.
Its post can add NONE on the same successful witness using completed
suffixes. This does not yet package gas_outcome_ptr for arbitrary source
observations/exempt alternatives. Exceptional target exits are passed
through expr_exit and bind_exception (gasSummaryComposePtr:86-93);
source read failure and exempt alternatives must also be handled by the
outcome combinators, not silently discarded by normal-prefix extraction.

## 4. Retained-base ledger (separate properties)

Use B as index compiler baseline. For a retained base Var p older than B:

* operand VALUE: expr_post old-variable clause (loweringPosts:256-257)
  preserves lookup_var p from t1 to t2, after compiler oldness preparation.
* operand PROVENANCE and operand TAINT: ghost_kept first clause
  (bodyPtrDefs:100-105) preserves FLOOKUP G p and op_taint. Literal base
  has no provenance, and useful nonempty memory coverage instead requires
  a variable via ptr_mem_ok/ptr_buf_ok. This is not a value snapshot claim.
* numeric COVERAGE: retained value, same site and unchanged bounds imply
  the previous address range remains covered. ptr_buf_ok uses full lowered
  buffer size (bodyPtrDefs:172-179); child range inclusion still needs
  layout/bounds facts, not just val_footprint of the source value.
* MEMORY TAINT: ghost_kept's second clause protects old allocations
  disjoint from locals (106-111). Third clause protects local bytes except
  dynarray length words (112-117). Neither protects every byte of an
  arbitrary pointer into a local. A fixed outer array may contain dynamic
  elements, whose header words are excluded by that third clause.
* ORDINARY CONTENT: expr_post old-allocation frame has the same
  disjoint-local restriction; locals_kept has dynamic-length exclusions.
  ghost_inv gives representation of CURRENT local values, not of a captured
  base value or a pointer-to-source-place relation. vv_at merely locates a
  footprint in a local/expression allocation; vv_holds relates its prior
  read, not its future source place. A source Located result can be read
  after the index, so demanding preservation of the OLD whole value would
  itself be the wrong contract for a mutable place.

The S1 reference explicitly identifies x[x.pop()] as a reason this
retained-place correspondence is not derivable by replaying the old
value proof. It is evidence of an interface gap, not a checked
counterexample to the frozen theorem. Storage is more acute: stor_taint_ok
bounds taint by CURRENT dead bytes; a retained place can become dead after
index execution. ptr_vv_ok at the base's original endpoint does not imply
its place-local dead-byte condition at the later endpoint. Dynamic arrays
also reload length AFTER index execution; snapshot length is not adequate.

`exprSimOperandsScript.sml:4-35,57-67` distinguishes expression-owned
allocations from local regions and supplies preservation only with the
appropriate allocation/local separation. It is not a generic solution
for arbitrary vv pointers or mutable source places.

## 5. Minimal next semantic obligation / recommendation

Do NOT commission generic strengthened expression recursion to solve the
fixed-memory branch: it does not need scalar NONE. The real unavailable
strengthening is a temporal place correspondence at the retained address.
A correct next contract must distinguish captured Value from Located:

Given the actual base compiler/run endpoint vv_post at B,t1, the actual
index expr_post and ghost_kept at C,t2, and the actual source base/index
runs, establish the child vv_post and ptr_vv_ok after array selection,
where read_result of the source base is interpreted at the post-index
source state, not necessarily as its pre-index value. It must also
establish full child-buffer coverage and place-local taint. For a base in
its own allocation disjoint from locals, existing frame clauses can supply
the snapshot case. For a base in a mutable local or storage, the current
judgments do not expose the necessary source-path/address relation.

Affected producer/forwarding shapes include Name local, nested Subscript,
Attribute, and Pop (which returns a now-dead place); each can hand out a
Located value that the index then mutates. Call results are normally
expression-owned buffers, so the completed call routing does not solve
this retained-place problem. A new theorem must derive the temporal
contract from actual semantics/compiler shape; merely adding it as a
premise to a consumer does not prove the frozen target.

Recommended strategist checkpoint: prioritize a bounded temporal-place
probe for a fixed array in a local, containing a dynamic member changed
by index evaluation; establish whether retained source read and target
address actually agree. If agreement is true, choose a source-path/address
boundary theorem with explicit mutation semantics, rather than more
suffix adapters. Independently a dynamic Var-index consumer needs NONE;
its IntCall case can use existing vv execution plus the wrapper ledger
above, but arbitrary forwarding constructors remain unresolved there.
No verified falsehood is claimed by this audit.
