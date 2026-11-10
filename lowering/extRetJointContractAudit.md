# C1.13: joint return contract audit (2026-11-10)

Diagnostic only. Nothing in this report is an asserted HOL theorem. In particular,
the two frozen statements and all recursive correctness obligations remain open.
No protected source was changed. The existing branch-by-branch encoder audit in
`extRetRecursiveContractAuditPtrScript.sml:56-158` and typed-copy audit in
`extRetNormalizeLiveChildPtrScript.sml:53-79` remain applicable. This report adds
the caller-domain audit and the proposed common endpoint; it does not promote
those conditional interfaces to recursive correctness.

## 1. Exact caller domains and falsification challenges

The outer theorem has supported_program, deployment/context equality, actual
function lookup, runtime lowering success and a specific package. The widened
statement has NONE of the first, third or runtime-lowering premises, and only
`get_tenv cx = type_env tops`, NOT module code equality or cx = initial context.
Its package accepts arbitrary name/args/defaults/ret/body; it is not asserted to
be the function selected in tops. Its ctx, PG and d are arbitrary. Conversely
it DOES have expr_sim_inv, stmt typing and expression simulations explicitly.

`stmt_exprs_ok` only supplies widths, allocation limits and return_buffer_ok.
It does NOT supply supported_expr, the internal-call supported declarations,
no EVM run, or the other conjuncts of expr_body_pre. The latter cannot simply
be reconstructed in either frame theorem: frame_ret_ok_ptr universally
quantifies returns, not just syntactic members of fbody.

`needs_normalize` tests lowered source type against DECLARED ret, not the
expression annotation. Thus even the outer residual at line 189 with
lowered_value_type = expr_type can require normalization. The widened residual
is not synonymous with 'normalization only': bytes literals and concatenation
can have unequal lowered/annotated capacities but bypass normalization.
The explanatory header of extRetWidenedPtr predates D18 and is not a domain
proof. `lowered_value_type_exceptions` lists five possible exception families,
not only internal calls; word/bytes cases must be dispatched before using the
D18 aggregate bridge.

Disprove-first challenges considered:
* Empty complex and zero copies have no source read. Do not demand a source
  variable, full-capacity clean bytes, or a positive footprint for them.
* Empty dynamic arrays DO read their length word and allocate scratch; empty
  runtime contents do not make their compiled loop/allocation disappear.
* A widened internal call uses the callee's stride, not the annotation's stride.
* Global cyclic metadata, even unrelated to the returned type, selects INVALID
  in compile_store_memory_typed. The existing global acyclicity producer needs
  supported_program, absent from the widened statement. No counterexample with
  all frozen premises satisfied has been verified; do not label the theorem
  false on the strength of this missing interface.
* A package return type need not be the return type of any function in tops in
  the widened theorem. An ABI-plan producer requiring that lookup cannot be
  silently applied there. Typing of the Return may instead provide relevant
  type well-formedness (needs a separate proof).

## 2. Producers: what is actually available

| Needed fact | Outer and widened common producer | Remaining issue |
|---|---|---|
| ce_func_return_type = build_func_return_type tops | external_frame_function_return_map, package/register/same_frame only | Exists WITHOUT supported_program; E0015's broad missing-map concern is resolved. |
| Signature return map on env.fn_sigs | expr_sim_inv_def:38-39 directly | Do not rederive through initial_signature_return_map, which imposes deployment/supported assumptions. |
| sfields_tenv_consistent; distinct field names; numeric field sizes | expr_sim_inv_def:54-59 directly | Exists for arbitrary cx in widened theorem. |
| type_memory_bytes ce ty = type_memory_size tv for evaluated ty | source_external_frame_type_memory_bytes, source_typing_distinct_type_keys and get_tenv equality | Existing producer does NOT require supported_program or a function lookup. |
| Global acyclic_struct_metadata | source_external_frame_struct_metadata_acyclic | REQUIRES supported_program. checked_contract_struct_args_unique gives uniqueness only. Need a checked-contract acyclicity proof or an alternative successful-normalization argument for widened. |
| Source lowered runtime typing | memory_rhs_runtime_layout consumes expr_sim_inv + value_runtime_typed env sty v | The layout conversion itself does not require supported_program. Missing producer is value_runtime_typed at lowered type under the actual frame premises. |
| Internal-call lowered typing | expr_sim_inv ties ce return map to sig; ifexp_frame_signature_return_well_formed needs just inv + signature lookup; annotation-insensitive eval is exported | ifexp_internal_call_read_signature_typed requires expr_body_pre (too strong). Its proof uses eval_expr_read_type_sound; extract/use a producer with inv, well_typed_expr, call_evaluation_safe, signature lookup and successful read, not supported-only body_inv. Validate this before recursion. |
| Ordinary source typing and widening to declared ret | IS_SOME (type_stmt env ret (Return (SOME e))) | Gives well_typed_expr, non-None annotation and type_widens_to annotation ret (type_stmt_return_some_iff). Need compose callee-return-to-annotation with annotation-to-ret for true lowered source. |
| Source robust representation, clean address, positive-read provenance | expression sim at post_value_type, ptr_val_ok_def, ptr_mem_ok_def | D18 gives lowered type for non-word/non-bytes internal calls; bytes need bound/layout transport, not full capacity. Type evaluation still needs producing to use universally guarded ptr_mem_ok. |
| Source allocation exclusion/frontier | expr_post -> expr_val_at; scratch_resource_from_expr and prospective_alloca_expr_interval_disjoint | They protect live footprint, not bytes capacity. Must transport through return-buffer allocation, repeated scratch sites and children. |
| Return-buffer capacity < word bound | stmt_exprs_ok / return_buffer_ok, allocation limits | Does not itself identify an ABI plan or prove encoded length fits. |
| Return-buffer strict end and ptr coverage | compile_alloc_buffer_state_counted_ptr | Requires not_local_ptr for fresh output; code/id distinctness and allocation room come from stmt_frag entry. Persists allocations and expr_val_at. |
| Scratch disjointness | scratch_resource_alloca; return_cursor_allocation_resources; alloca_site_registered_disjoint | Current scratch_resource is for ONE protected interval. Need simultaneous destination/source/live-ancestor protection and preservation on reentry; prospective sites may already be registered. |
| ABI plan and output bound | outer: source_external_return_contract / supported_place_abi_enc_plan / encodable_ret_shape_plan | Existing source_external_frame_ret_abi_plan and size wrapper require supported_program AND actual external lookup; widened has neither. Need plan/size from relevant type evaluation and package metadata, or a direct type-indexed compiler theorem. |
| Source child memory | robust_dynamic_source_child, robust_tuple_source_child, robust_struct_source_child | Exist; they do not supply child ADD provenance, strict bounds, or all remaining-capacity arithmetic. |
| Counted RETURN | gas_path_ptr_then_emit_return_clean | Needs variable dst and len, ptr coverage for actual n, clean len, stor_taint_ok, strict word bounds, exact PC and clean returned prefix. Literal result operands need a separate existing/small bridge, not an assumption that out is Var. |

Important endpoint simplification: stmt_exit_ptr_def:561-565 accepts
ReturnException v under RetQ = (lambda ... . T), independently of r. The ptr
frame theorem does NOT require proving equality of ABI output bytes with enc.
It DOES require a checked counted path and clean returned bytes. An S1 semantic
encoder result can supply execution/length facts, but is not itself that path.
A uniform ABI representative across all memory perturbations is unnecessary:
use one fixed source v throughout. Avoid adding a stronger functional encoding
postcondition solely because an existing S1 theorem has one.

## 3. Fully quantified candidate boundaries (NOT proved)

The following notation expands to predicates on existing HOL terms; it is report
notation, not a proposed axiom. All free parameters in each formula are
universally quantified. W and L below are byte sets.

```
PC a s := ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
          s.vs_inst_idx = LENGTH a.cs_current_insts
Rob tv v q tn s := !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                           val_in_memory tv v q mem
Old a s G tn t H tm := !x. not_fresh_at a x ==>
  lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
  op_taint tm (Var x) = op_taint tn (Var x)
Frame W s tn t tm := mem_agree_outside W t.vs_memory s.vs_memory /\
  (!i. i NOTIN W ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables
AllocFrame s t := alloca_inv t /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!id site. FLOOKUP s.vs_allocas id = SOME site ==>
             FLOOKUP t.vs_allocas id = SOME site)
```

Resource schedule `Resource a z ce cx es tv v src q dst b cap L s G tn`
means all of the following (every site and output is universally quantified):
- stmt_state_rel ctx fn ce cx es s, fn_has_code a z fn, distinct instruction ids,
  no ctx DALLOCA, PC a s, src/dst existing variables when read, clean operands;
- evaluate_type (get_tenv cx) ty = SOME tv, value_has_type tv v, val_wf tv v;
- Rob tv v q tn s; eval_operand src s = SOME (n2w q);
  positive source footprint implies source Var coverage for val_store_size;
  each actual positive read window has strict nonwrapping end;
- eval_operand dst s = SOME (n2w b), ptr_covers G tn dst s cap,
  b+cap < dimword(:256); source live footprint disjoint from [b,b+cap);
- alloca_room ctx fn s and alloca_inv s; source/live L below frontier;
- for every emitted ALLOCA site: membership in fn, actual literal size,
  reserved nonlocal output, id outside source expression interval; if already
  registered, correct size and disjoint from source, destination and L;
  otherwise those protected intervals end below frontier;
- L is disjoint from the destination; each live ancestor cell in L is covered,
  has known clean stored scalar and has an allocation id distinct from every
  child site; child sites and all old source/destination variables reserved.
The simultaneous-resource producer is UNPROVED. This is precisely a missing
contract premise producer, not something supplied by the frozen statements.
Do not encode Resource as a new predicate until its caller production is proved.

Encoder candidate, with all Resource parameters universally quantified:

```
!D ctx fn PG ce cx es tenv ty tv v ei src q dst b cap L sa sb out s G tn.
  tenv = get_tenv cx /\ evaluate_type tenv ty = SOME tv /\
  abi_enc_plan tenv ty ei /\ vyper_abi_size_bound tenv ty <= cap /\
  compile_abi_encode_to_buf (Var dst) src ei sa = (out,sb) /\
  Resource sa sb ce cx es tv v src q dst b cap L s G tn ==>
  ?Gf tnf sf n W.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\ PC sb sf /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    n <= cap /\ n < dimword(:256) /\ ptr_covers Gf tnf dst sf n /\
    (!i. b <= i /\ i < b+n ==> i NOTIN tnf.t_mem) /\
    Rob tv v q tnf sf /\ Old sa s G tn sf Gf tnf /\
    Frame W s tn sf tnf /\ AllocFrame s sf /\ alloca_room ctx fn sf /\
    DISJOINT W L /\
    (!i. i IN W ==> (b <= i /\ i < b+cap) \/
       ?id p size. emitted_alloca_site sa sb id size /\
           FLOOKUP sf.vs_allocas id = SOME (p,size) /\ p <= i /\ i < p+size)
```

Here `emitted_alloca_site` is notation for actual ALLOCA membership in the
fragment, NOT all fresh allocation ids. It must count reused loop sites.
Scratch is included in W, and the endpoint must preserve the values/cleanliness
of L, not merely its allocation metadata (Frame plus DISJOINT does that).
For source-zero branches remove src-evaluation/provenance requirements by a
zero-read specialization; their ABI parent can still emit zero-offset ADDs.
For static/bytes leaves W has no scratch portion. Root inv/stor facts follow
from Frame; allocation/state-rel transport for future scratch still needs proof.

Normalization candidate:

```
!D ctx fn PG ce cx es sty ty stv dtv v src q sa sm sb buf s G tn L.
  compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand ty src sty sm = ((),sb) /\
  type_widens_to (get_tenv cx) sty ty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  [numeric field-size / distinct-name conjunct from expr_sim_inv] /\
  type_memory_bytes ce ty = type_memory_size dtv /\
  [allocation entry and simultaneous-resource premises above for the source,
   newly allocated destination and inherited live L] ==>
  ?Gf tnf sf p dst W.
    buf.buf_operand = Var dst /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\ PC sb sf /\
    lookup_var dst sf = SOME (n2w p) /\
    p+type_memory_size dtv < dimword(:256) /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (p,type_memory_size dtv) /\
    ptr_covers Gf tnf dst sf (type_memory_size dtv) /\
    Rob dtv v p tnf sf /\ Rob stv v q tnf sf /\
    Old sa s G tn sf Gf tnf /\ Frame W s tn sf tnf /\
    AllocFrame s sf /\ alloca_room ctx fn sf /\ DISJOINT W L /\
    [write envelope is destination plus typed-copy scratch; state-rel/local
     and prospective-encoder-site protection as in encoder entry]
```

Bracketed clauses are explicitly unresolved interfaces, not omitted proven
hypotheses. In particular the input candidate cannot yet be instantiated from
the widened theorem; it is NOT a completed theorem specification. The exact
successful endpoint is fixed, but the joint Resource producer is still the
planning blocker. This is preferable to silently asserting caller production.
The normalized destination is a FULL registered allocation, so it feeds the
same encoder as a source; it does not inherit the original expression's
expr_val_at automatically. A new registered-source producer must replace that
assumption for normalized inputs.

## 4. Concrete branch witnesses and required exclusions

These are concrete type/layout witnesses, not counterexamples to a frozen
frame theorem; no assertion that each is supported by supported_program:

- Nested dynamic encoder: `ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2))
  (Dynamic 2)`, value `ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1])])`.
  Inner slot = 96, outer slot = 224 bytes. Both dispatcher levels are
  AbiDynArray; outer dynamic-child iteration must preserve parent/index/tail
  scratch across child allocation. The current static-element loop alone
  cannot execute this tree.
- Widened bytes children: source
  `ArrayT (BaseT (BytesT (Dynamic 32))) (Dynamic 2)` to destination with 64.
  Source slot stride64, destination stride96; total capacities160 and224.
  Actual one-byte child reads length+data (33) for ABI; typed bytes copy can
  use padded64. `normalize_nested_bytes_window_probe` is already checked for
  a related 96-byte child bound, not a recursive-copy theorem.
- Tuple: `TupleT [BaseT (BytesT (Dynamic 32));
  ArrayT (BaseT (UintT 256)) (Dynamic 2)]`. Source offsets0 and64; ABI heads
  each32, tails variable. Requires a dynamic complex parent with two children,
  not a singleton wrapper. In widening, tuple child-list recursion must keep
  separate cumulative source and destination offsets.
- Struct metadata with fields `payload: Bytes[32]` and `xs: DynArray[uint256,2]`
  has the same relevant source offsets as that tuple, but compiler struct copy
  looks up source type/size by field NAME and then increments source_off.
  Equal field-name order must be derived; name lookup alone is insufficient.
  Neither absence nor presence of such fields in supported_program proves
  the widened theorem's full domain. Empty struct has zero capacity and is
  already handled as encodable (not assignable) by encodable_ret_empty_struct_zero_copy.
- Zero-length loop: value `ArrayV (DynArrayV [])` at any valid dynamic array
  type still reads/writes its32-byte header and initializes parent/index/(if
  dynamic elements) tail cells. Typed equal-element dynamic copy emits MCOPY
  with size0; positive-read assumptions must be guarded. AbiComplex [] is an
  actual no-op, covered by abi_complex_empty_dispatch_counted_ptr. AbiCopy0
  emits MCOPY, unlike the empty complex; use the zero-access rule.

## 5. Flat semantic cuts recommended to strategist

Not new component IDs or an executor-owned plan. The following are the finite
interfaces requiring strategist decisions before generic recursion:

1. Actual-frame semantic producer, using inv + Return typing + call safety
   rather than expr_body_pre: lowered runtime typing, source-to-declared
   widening, evaluated layout, acyclic global metadata (or explanation why
   it is unnecessary) and plan/size for arbitrary packaged return type.
   Validate independently for widened and outer residual domains FIRST.
2. Joint registered/prospective allocation protection. Source live windows,
   destination remaining capacity and a SET of live ancestor cells; new
   normalized-source entry without expr_val_at. Include reentered loop sites.
3. Child address/provenance and source-indexed frame: guarded zero reads,
   source strides, separate head/tail budgets, strict ADD/MUL bounds and
   initialized-prefix cleanliness; reusable generic child prefix/suffix.
4. Runtime-loop invariants: typed array layout conversion with different
   strides; ABI dynamic-child loop with head prefix/tail prefix and live
   parent/index/tail scratch. Static-element counted loop needs exterior
   memory/taint/resource frames before reuse as a recursive child.
5. Finite list/struct recursion and compiler dispatch using those interfaces;
   terminal clean RETURN composition. Source typing excludes invalid/fallback
   aggregate cases or supplies their exact read coverage; never use widening
   size monotonicity to justify a destination-sized source read.

No protected-file change is requested by this audit yet. No frozen theorem
falsehood is established. The next decomposition must address (1) before
investing in either recursive implementation; all other candidates remain
conditional until that entry gate and (2) have actual producers.

## 6. Checked semantic-entry progress (C1.14.1 / C1.14.2)

The runtime-typing gap in row 62 is now resolved for actual aggregate Return
reads, without expr_body_pre, supported_program, actual function lookup or
module-code equality. New leaves:

- `extRetInternalCallTypingPtr.ext_ret_internal_call_read_signature_typed`
  proves signature-return runtime typing from expr_sim_inv, well_typed_expr,
  call_evaluation_safe, signature lookup and successful read. Reannotation at
  sig.ret_ty and eval_expr_read_type_sound require no additional premise.
- `extRetSemanticEntryPtr.ext_ret_read_post_runtime_typed` gives
  value_runtime_typed env (post_value_type ce e) v from inv + well_typed_expr
  + call safety + successful read, for ALL expressions.
- `ext_ret_return_post_runtime_layout` replaces expression typing/call safety
  with exactly the Return typing and int_calls_stmt guards in the frozen
  widened theorem; its conclusion is an evaluated post type, value_has_type
  and numeric type_memory_bytes = type_memory_size.
- `ext_ret_aggregate_lowered_post_type` requires only well_typed_expr and
  non-word/non-bytes annotation. It uses the existing
  structlit_uniform_nonword_lowered_type, not the stronger body-pre bridge.
- `ext_ret_aggregate_return_runtime_layout` therefore gives the same evaluated
  layout conclusion at lowered_value_type under actual Return guards and
  non-word/non-bytes annotation. Bytes/word exceptions are deliberately
  separate; this theorem does not claim their narrower lowered buffer has
  the annotated capacity.

These are built HOL theorems, not proposed contracts. No source typing/package
premises are even needed for these particular boundaries. New leaves introduce
no admissions and do not edit any protected theory.

Remaining semantic work is now narrower:

1. For aggregate normalization, lowered-to-declared widening is the composition
   of existing post_value_type_widens (inv + well_typed_expr) and
   type_stmt_return_some_iff (annotation-to-ret). No exported transitivity
   lemma was found by type_widens/arg_type_fits searches; a joint arg_type_fits /
   arg_types_fit transitivity induction would be a separate finite boundary.
   It is not proved by the runtime-layout lemmas above.
2. `check_toplevel_decl` for StructDecl DOES require every field type to be
   assignable in type_env_all_modules, not merely distinct names
   (vyperTypeContractScript.sml:932-934). `check_contract` checks every such
   declaration, so this is a promising actual producer of global acyclicity.
   The existing make_struct_fields_map_acyclic instead goes through
   supported_declaration_headers; its wrapper cannot be applied verbatim.
   Need a new checked-contract/rank boundary connecting evaluated field types
   to the total metadata rank, or prove this stronger route unnecessary.
3. Arbitrary package plan/size: existing external_frame_return_size and
   external_frame_ret_abi_plan do NOT require actual function membership.
   They require assignable_type (type_env tops) ret. Distinct keys and package
   equality are available already. Thus the specific obstruction is deriving
   the relevant encodable plan/size without assignability (empty structs must
   remain allowed), NOT function membership itself. A type-indexed
   evaluated-ret/encodable-shape producer can replace this overly strong
   premise. This has not yet been proved.
4. The failed-metadata compiler branch is precisely contextScript.sml:680-681:
   non-word/non-bytes compile_store_memory_typed emits INVALID when global
   acyclicity fails. stmt_exit_ptr under trivial RetQ accepts a source
   ReturnException independently of r; this does NOT automatically prove
   gas_outcome_ptr_lo's counted terminal cx_dead or per-step check for that
   INVALID. No checked fallback safety path or full-premise counterexample
   is claimed. There is no basis yet to bypass acyclicity by assumption.

### Checked resolution of the metadata-failure endpoint

The concern in item 4 above is now resolved at the typed-copy fragment boundary:
`ext_ret_invalid_normalize_outcome` is proved and built in the same new leaf.
Under the exact non-word/non-bytes dispatch guards, failed global acyclicity,
compile_store_memory_typed equation, fn_has_code, no DALLOCA and entry PC facts,
it proves gas_outcome_ptr for source `raise (ReturnException v)`, arbitrary
normal postcondition Q, and terminal
`(\res ee gt r. stmt_exit_ptr (\v es gt r. T) ee res gt r)`.
It reuses `bodyPtrIfExpStoreContract.store_memory_typed_invalid_counted`,
`emitHelperProps.step_invalid`, and the actual counted summary definition.
The terminal INVALID path retains G/tn and requires no extra storage/deadness
premise: the existing ptr_inst_ok_abort_zero already checks the instruction
against arbitrary D. This is a pointer-safety endpoint, not source/target
functional agreement and not a counterexample.

Consequently a proof of GLOBAL acyclicity is not necessary at a Return with
trivial RetQ: split the dispatch; failed metadata terminates acceptably, and
only the successful-copy branch assumes the positive acyclicity guard. Full
frame composition still needs the normal expression and buffer-allocation
prefixes; the new theorem intentionally proves the exact typed-copy suffix,
not the frozen widened theorem. Repeated unrelated-ancestor timeout in
bodyPtrIfExpBytesFrame was retried once under D0001 and passed unchanged.

C1.14.2 diagnostic conclusion: actual aggregate runtime layout is now a
checked caller-produced interface; global acyclicity can be avoided via a
checked rejection suffix. Remaining finite semantic boundaries are widening
transitivity and evaluated/encodable arbitrary-ret package plan and size
(including empty struct), before the simultaneous allocation-resource work.
No generic recursive implementation or frozen statement has been proved.
