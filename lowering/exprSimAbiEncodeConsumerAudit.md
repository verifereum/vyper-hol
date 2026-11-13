# Singleton nonword consumer audit (C1.F.8.3.6.5)

This is a source/signature audit, not a checked theorem or completion claim.

## Actual branch and substitutions

`exprLoweringScript.sml:3450-3470`: for args=[e], ensure=F and
~is_word_type (expr_type e), the compiler calls

```
compile_expr ce (expr_type e) e origin = (src_vv,sm)
unwrap_value ce src_vv sm = (op,sa)
lower_abi_encode F (OPTION_MAP bytes_method_id_word mid0) op
  (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
  (abi_size_bound ce.ce_struct_fields (expr_type e)) sa = (out,sb)
```

The result is `as_ptr_val vv_ty LocMemory (out,sb)`; `origin` is the
whole builtin's compilation start. Do NOT identify sm with sa, nor the
operand simulation endpoint with the post-unwrap state s.

## Counted suffix premise map

References to lines 23-43 below mean NonwordCountedScript.sml.

* 23 expr_post: `unwrap_value_marked_read` (exprSimUnwrap:958-977)
  gives exactly `expr_post ... e es origin sa s0 ee v op s`, together
  with a marked read_result execution. Its input is the operand vv_post
  at sm. `unwrap_value_path` only handles an already read Value v;
  it is not a substitute for marked_read on arbitrary source results.
* 24 operand expr_body_pre and 25 whole-builtin expr_body_pre: whole
  precondition comes from expr_vv_case; projecting operand precondition
  from singleton typing/safety is an integration obligation (not proved
  here). expr_body_pre_def is exprSimHypsDefs:148-160.
* 26 mid: definitional OPTION_MAP from dispatch.
* 27 nonword: dispatch branch guard.
* 28 plan: use `abi_encode_translated_plan` (PlanTranslation:160-166),
  with sf=ce.ce_struct_fields, E=E0=get_tenv cx. Its assignable_type,
  evaluated-type, consistency and memory-layout premises must be
  projected from expr_body_pre/expr_sim_inv; they are not automatic
  from encoder execution. No new encoder hypothesis is needed.
* 29-30 type and value_has_type: `abi_encode_operand_success_type`
  (PrefixWindow:249-258) from the counted successful operand+read.
* 31 conversion: `abi_encode_singleton_success_conversion`
  (PrefixWindow:261-268) from successful evaluate_type_builtin.
  This does not yet handle an error from that source builtin.
* 32-33 lower result: exact third compiler equation above.
* 34 code/distinctness: distinctness is inherited whole-function input;
  restriction of fn_has_code origin sb to sa sb is needed via compiler
  extension. `ci_mono_unwrap_value` and `unwrap_value_extends` exist;
  this audit does not certify their complete composition at call site.
* 35 local_ptrs_reserved at sa: must transport original reservation
  through compile_expr and unwrap compiler monotonicity. Original
  reservation alone is at origin, not sa.
* 36-37 operand not Label and Var not_fresh_at sa: require static
  compiler output-shape facts through unwrap. `unwrap_value_shape`
  (proofs/loweringShapeProps:1071-1075) has plain_operand output but
  needs cenv_shape_ok and value_shape_ok. It is a candidate, NOT an
  established applicable theorem at this consumer without those inputs.
* 38 fresh_vars_wrt sb s: neither expr_post_def (loweringPosts:251-266)
  nor unwrap_value_marked_read's conclusion mentions this. A separate
  freshness boundary is required from execution/static variable ranges.
  Nonhalted is NOT a conjunct of stmt_state_rel_def (exprLoweringProps:412)
  or state_rel_def (defs/compileEnv:1468). It needs marked execution
  success invariants; do not silently assume it from entry nonhalted.
* 39-40 entry control: exact unwrap_value_marked_read output at sa.
* 41-43 PHI side condition: not an unwrap conclusion. Need a syntactic
  fact for lower_abi_encode on this branch: either no new blocks,
  nonempty final instructions, or zero PHI prefix at final label in func.
  lower_abi_encode_frag_facts currently supplies FRONT-label exclusion,
  which is not by itself the stated PHI condition.

The counted unwrap signatures are overlay admissions owned outside this
TASK; this audit uses them unchanged and does not edit them.

## Endpoint into required postcondition

`expr_vv_sim_def` (exprSimDefs:56-71) requires vv_post for the WHOLE
builtin relative to origin,sb,s0, with the builtin's source result.
`vv_post_def` (loweringPosts:377-391) has seven components:

1. stmt_state_rel: now directly supplied by counted suffix on actual.
2. vv_holds: source singleton result is BytesV(method bytes ++ enc...),
   by `abi_builtin_encode_source_single` (abiBuiltinEncodeSource:22-27).
   Method-word prefix correspondence requires LENGTH method bytes=4
   (`abi_builtin_method_word_prefix`:78-80). Counted bytes plus mload
   provide the concrete length/data representation, but a boundary
   lemma joining the prefix and payload and reconciling result type
   with vv_ty is still needed.
3. vv_at: requires allocation ownership/disjointness for the result
   footprint (loweringPosts:356-373). Counted suffix currently exports
   neither an output ALLOCA witness nor vv_at. State relation + correct
   bytes do not imply this ownership certificate.
4. old variable lookup preservation relative to origin,s0.
5. old alloca-entry preservation relative to s0.
6. protected memory preservation relative to origin,s0 and es scopes.
7. locals_kept relative to es,s0.

Items 4-7 ARE NOT conclusions of NonwordCounted. Memory-length/FMP/
semantic-observation equality is not a substitute. expr_post at the
post-unwrap state has these fields only up to s; they must be extended
through the encoder on the SAME counted actual. Existing registered
ownership/phase-register lemmas are candidate producers, not a counted
consumer boundary yet. In particular strengthening stmt_state_rel alone
has not closed the original expression-frame requirement.

## Exact proposed next boundary statement

Rather than attempt the whole source gas_outcome now, the next theorem
should strengthen the existing `abi_encode_nonword_counted_suffix` IN
PLACE, keeping EVERY existing premise, with these additional conclusions
on its already existential actual (retain all current conclusions):

```
(!x w. not_fresh_at origin x /\ lookup_var x s0 = SOME w ==>
       lookup_var x actual = SOME w) /\
(!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP actual.vs_allocas aid = SOME b) /\
(!aid off sz.
  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id /\
  (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
    off+sz <= b \/ b+sz' <= off) ==>
  mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
locals_kept ce es s0 actual
```

This is a proposed obligation, NOT asserted proved or de-risked. Its
premises must first be audited against the registered-effect witnesses
inside BOTH observer producers; it must not add caller frame assumptions
to the gas bridges. Candidate dependencies: StateTransport's
abi_encode_caller_phase_registers, caller_phase_allocations,
SuffixOwnership's abi_encode_owned_interval_frame, and the original
expr_post fields. A separate same-witness allocation-ownership result is
also necessary for vv_at; its exact shape should follow the existing
vv_at_def rather than a guessed nominal output capacity. After these
boundaries, establish static unwrap/freshness/PHI inputs listed above,
then prove the successful singleton branch with source gas composition.

No unavailable outer-function encoder premise was discovered in this
audit: the outstanding gaps are task-owned consumer/frame and static
applicability boundaries. Failure/conversion-error branches of the source
builtin are outside this successful-suffix audit and remain obligations
of the frozen main theorem.
