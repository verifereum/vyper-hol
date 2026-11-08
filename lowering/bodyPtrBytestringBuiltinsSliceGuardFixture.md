# Concrete Slice global-guard fixture (C1.slice.fixture)

The independent SliceGuardFixture theory checks a closed address producer:
uint256(1) / uint256(0), converted to address, wrapped in Acc Code.
The source is well typed for every typing environment, is_extcode, and evaluates
to Error (RuntimeError "Div0") in every cx and source state, unchanged. Thus the
six-witness global success existential is false even with independent read state.
This is a checked diagnostic, NOT a counterexample to the frozen target.

Important allocation-precondition distinction:
- Standalone Acc Code fails alloc_limits_expr by definition, so its own
  expr_body_pre is impossible (checked slice_guard_source_no_body_pre).
- As source of Slice 1 it is checked through extcode_addr_expr instead. The
  complete Slice with literal start 0 and length 1 passes well_typed_expr and
  alloc_limits_expr (checked). The standalone exclusion does not exclude the
  whole Slice's precondition. The source's body pointer judgment can therefore
  be vacuous; its successful-source guard does not supply a tail judgment.
- Source byte widths, no internal calls and no EVM-run are also checked.

No complete expr_body_pre or body_inv instance is constructed here. Still open:
actual supported unit lowering and installed func/code; complete whole-expression
precondition including expr_sim_inv and context ABI clauses; stmt_state_rel,
allocation/frame space, ghost_inv, arbitrary input provenance/taint and PC;
reservations, no ctor/DALLOCA, gas_admissible, and unavoidable failure of the
required counted outcome/posts despite exception exits. No unsafe tail has been
selected, and no claim is made that guard failure implies target falsehood.

Baseline bodyPtrBytestringBuiltinsTheory builds unchanged (target still cheated).
Independent bodyPtrBytestringBuiltinsSliceGuardFixtureTheory builds with no
admissions in the fixture. Stop here for strategist classification, as planned.
