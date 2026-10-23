# Supplied external validation for G0006 / C1.4.2

The owner requested this validation and recovery without starting Alan. Codex
performed the external executions. The previous absence of independent
compiler/EVM artifacts is no longer the resume blocker.

Read the main workspace bundle at
`notes/validation/folded-value-2026-10-23/REPORT.md`, `results.json`,
`corpus/results.json`, `executions.json`, and `identity.json`. Independent
sanitized AST/layout and Python bytecode files are tracked alongside the tests
under `lowering/defs/bytecode/folded-value-oracle/`. Obtain native file/tool
evidence for these real files, then explicitly release L0005's prior external
precondition wait through the normal evidence-backed lead workflow. Do not
manufacture tool output IDs or completion credit.

The Vyper source was exclusively `~/vyper`, clean pinned commit
`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`. Provisioning used a committed clone,
uv 0.10.11, managed Python 3.11.11 and the repository's frozen constraints.
Independent settings and dependency identities are in provenance/identity logs.

All 37 witness rows have actual results: 30 MATCH; four bytecode mismatches
(`ctl03_abi_method_id`, `enc_ensT_uint_mid`, `rc09_abi_encode_data`, `rr03_abi`);
two immutable compile-NONE outcomes; one expected Python rejection. Both HOL
checker modes accept all 36 exported ASTs. Remaining failures retain the task's
#551, #554, #567 and #563 ownership. The current ABI lowering still ignores its
`ensure_tuple` parameter. No compiler/whitelist repair is part of this handoff.

The independent frozen Python corpus reproduced all 101 fixtures and both
additional subcorpora. All four required overflow executions genuinely reverted
on py-evm 0.12.1b1 PragueVM. The permanent `foldedValueParityTheory` proves all
seven new independent fixtures by checked compiler evaluation and data equality;
it never registers expected-byte equalities as evaluator rewrites. Use the final
corpus results for exact target outcomes; an existing internal-tuple lowering
evaluation exceeded 600 seconds without progress and is recorded as a timeout,
not a passing or unexecuted result. Do not repeat that unbounded evaluation as a
substitute for consuming the provided external evidence.

If a saved lane is behind the main workspace, use the normal workspace sync to
make the complete source/artifact set visible before continuing C1.4.2/C1.4.3.
The report records source hashes: repeat any affected comparisons after real
compiler/source changes. Treat the supplied run as evidence to reconcile, not
as an already accepted plan completion. Preserve the Exp restriction and all
other current supported-program restrictions.

The compiler source revision in the receipts is `ac6681fe013c4762158d1bc24e9ae206a19781e8`.
The subsequent bundle adds validation artifacts, documentation and a parity test;
it does not change the compiler/frontend/checker definitions that produced the
observations. Do not declare the run stale solely because committing its
artifacts advances HEAD: compare the recorded source hashes.

Alan was not restarted by this recovery. Do not start it on behalf of the owner.
