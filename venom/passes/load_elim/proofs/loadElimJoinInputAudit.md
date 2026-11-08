# Accumulated boundary / current input diagnostic

Scope: C1.P.4.2.3.4.2.17. This is not a proof of the frozen target or
of the initialized solver invariant below. No target statement changed.

## Available checked facts

* `le_solver_process_inflationary`: each boundary changes by accumulating a
  fresh result with `load_join`. `le_lattice_leq` is a prefix-list order;
  it is not a ready-made general join monotonicity theorem.
* `le_process_boundary_block`: processing bb replaces its boundary by
  `load_join old fresh_fold`. It does NOT replace it by fresh_fold.
* `le_pred_lookup_rel k input boundary` already expresses the needed
  conditional set inclusion, including the separate unreached-input case.
* `le_pred_lookup_rel_join_preserving`: own-block update preserves this
  relation when fresh is reached and its key lookup equals input's lookup.
  `le_wf_block_fold_some` supplies reachedness, and `le_fold_preserves_def`
  supplies the lookup equation for preserving blocks.
* NEW `le_pred_lookup_rel_join_context` (loadElimJoinInputDiagnostic):

      le_pred_lookup_rel k (load_join a p) b ==>
      le_pred_lookup_rel k (load_join a (load_join p fresh)) b

  This is a checked unrestricted algebraic fact. It includes p=NONE,
  fresh=NONE, key disappearance, and an unchanged other-predecessor aggregate.
  It uses set inclusion, not list equality or prefix-list monotonicity.

Searches of shared/simulation/memory_copy_elision found no load_join analogue;
existing load-elimination join, solver and provenance interfaces were reused.

## Precise candidate initialized invariant (NOT proved here)

For every bb in fn.fn_blocks and key k whose fold preserves k:

    le_pred_lookup_rel k
      (df_joined_val Forward NONE load_join load_edge_transfer ctx
        (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
        (cfg_analyze fn) st bb.bb_label)
      (df_boundary NONE st bb.bb_label)

This is stronger than the currently checked sole-predecessor provenance
clause. It deliberately does NOT assert unconditional current input presence.

Initialization: all boundaries have no key, including the seeded entry's
SOME FEMPTY, so `le_pred_lookup_rel_empty` discharges the clause.

Own-block update, absent self-edge: use `le_process_boundary_block`,
`le_pred_lookup_rel_join_preserving`, `le_wf_block_fold_some`, and the
preserving-fold lookup equation. Joined input itself is unchanged.

Predecessor update, bb not processed: updated predecessor is old p joined
with fresh. The new context theorem handles a two-component aggregate.
A finite-FOLDL context transport theorem is still required to lift this to
all CFG predecessors (and the optional entry seed). This needs set-level
association/permutation or a direct fold induction, not list equality.

Self-edge / bb also a predecessor: first derive own-boundary relation to the
OLD input as above, then apply finite-FOLDL context transport to the new
input, with the new boundary held fixed. Do not split these into disjoint
cases and accidentally omit the simultaneous effect.

Unreached predecessor becomes reached: the new context theorem covers both
key-present fresh and key-absent fresh. NONE is identity; SOME FEMPTY is not.

Key disappears: unconditional input-presence invariant is false transiently.
`le_join_input_key_disappears` checks that old input has [a;b], while adding
a formerly NONE predecessor now holding SOME FEMPTY empties the joined
input; the old bb boundary can still hold [a;b]. Conditional relation remains
true. Later predecessor accumulation cannot restore a deleted key in that
reached predecessor, but this irreversibility need not be postulated
separately if finite-context transport is proved generally.

Unrelated update: boundary and joined input unchanged.

These cases support the candidate, but a full solver proof still needs the
finite-context lemma, process preservation, initialized wl_iterate lift,
and population lift. None is silently asserted by this diagnostic.

## Actual action supplies the missing presence restriction

`compute_phi_action` requires lattice_single_var at every predecessor of the
chosen join. Thus all these boundaries are reached and have key-present
singletons. For a NONEMPTY predecessor list and a NONENTRY join, their
joined input has a key-present operand union. These hypotheses must be
extracted from actual collected-action/reachability/provenance interfaces;
EVERY alone is vacuous at an empty predecessor list. Entry seeding by
SOME FEMPTY must also be excluded, e.g. using the existing entry-preserving
missing-key theorem and multivalue boundary presence.

Only after these presence facts AND initialized candidate provenance are
proved can one derive boundary alternatives subset current input
alternatives. No new premise should be added to the final suffix certificate.

## Checked insufficiency probe

`le_join_absorbed_stale_alternative` checks an arbitrary old boundary [a;b;c]
absorbing the fresh input join of singleton [a] and singleton [b], while the
conditional inclusion into that current input is false. Consequently neither
fixpoint absorption nor current singleton predecessor facts alone supply the
missing initialized-history bridge. This arbitrary-state algebraic probe is
NOT a counterexample to load_analyze or to the frozen correctness theorem.

## Review request

Stop here as authorized. Request a bounded decomposition for the finite
joined-input context transport, initialized generalized preserving provenance,
and actual-action input-presence extraction. Preserve the checked suffix
boundary and multivalue-prefix helpers unchanged. No occurrence-certificate
integration or target coupling has been attempted in this diagnostic.
