# Projected allocation and capture query checkpoint (C1.4.1)

Reference pin: cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c, supplied in
`.agent-files/vyper-reference/vyper/venom/`. This is a source comparison and
checked HOL production-query probe inventory, **not** a Python execution receipt
or a universal equivalence theorem. Reclaim transfer/checker/emission have not
been rewired to these queries yet.

## Allocation projection

`analysis/base_ptr_analysis.py:78-159` accumulates possible Ptrs per variable.
Projection retains allocation-site identity and erases offsets. Normalization
(:161-173) leaves one Ptr per base, even after disagreeing offsets; thus erasing
offsets preserves the cardinality used by `_dalloca_allocation` at
`passes/fmp_lowering.py:555-563`. Missing facts mean the empty set, **not** a
semantic unknown pointer. `_allocation_is_live` (:565-577) tests identity in
every live variable and also the separately pinned identities.

Production `fmp_base_analyze` uses unique instruction IDs (checked) as local
site keys. Ordered sweeps accumulate duplicate-free lists from empty facts;
there is no transfer-monotonicity claim. A bounded iterator stops on extensional
membership equality over instruction outputs. Acceptance rechecks that equality
and every instruction's contributions against the final environment. Failure
returns NONE; consumers must veto reclaim on it. The successful-environment
lemmas expose closure, stability, unique sites, and contribution propagation.
The singleton query requires a DALLOCA site; BUMP and ALLOCA sites do not qualify.

Correspondence of checked `fmpAliasProbeTheory` cases to source rules:

- Equal-size DALLOCAs 10 and 11 remain distinct; ALLOCA 12 and first BUMP
  output 13 seed separate sites (:81-102). BUMP runner and GETFMP have no
  generated facts. Other definitions could still accumulate facts for them.
- ASSIGN copies (:138-139); ADD literal offset and unknown/dynamic offset
  preserve site 10 (:111-125), without offset arithmetic in this projection.
- Semantic-order SUB(pointer,untracked) propagates lhs; SUB(untracked,pointer)
  does not. The rhs propagation branch is explicitly guarded by ADD (:124).
- Two already pointer-bearing operands contribute nothing. A prior accumulated
  output fact survives discovering the second pointer later (:143-159).
- PHI(known,untracked) is known; PHI(two sites) is ambiguous (:130-136).
  Thus neither an untracked input nor an unknown offset is an extra unknown
  identity token. This corrects the initial contradictory PLAN guidance.
- A loop/backedge-shaped ordering closes after re-iteration. Duplicate site IDs
  reject. Live derived aliases and escaped occurrences both keep sites live.

**Ordering limit:** the reference schedules CFG DFS/worklist blocks (:65-76),
whereas this interface takes an explicit instruction-list order and sweeps it.
Negative arithmetic tests make discovery order observable. The checked examples
above follow the same indicated source rules (the loop case assumes its
backedge); they do not certify that arbitrary full-list sweeps equal Python's
CFG worklist. No concrete schedule discrepancy was established by these probes.
Consumers must not infer general Python parity or operational safety merely from
successful closure. Universal iteration completion was not required at this
checkpoint; acceptance is fail-closed.

## Capture and escape queries

`passes/fmp_lowering.py:603-628`: propagation opcodes exempt all occurrences;
otherwise compare variable occurrence counts with safe memory-access counts.
Production `fmp_safe_operands` reuses `mem_read_ops`/`mem_write_ops`, counting
ofst, size, and distinct max_size. HOL compares optional operand values to avoid
counting a default max_size twice; Python uses object identity for the default
alias. Existing shared access descriptions express that default with equal
values. Malformed shared access descriptions fail closed (no safe occurrences).

Production probes check MSTORE(p,p) returns both escaping occurrences, while
MSTORE(p,literal) and MLOAD(p) do not escape. CALL input/output offsets and sizes,
CREATE offset/size, and CREATE2 offset/size are safe; CREATE2 salt escapes. These
are the corresponding shared memory-location table positions in semantic HOL
operand order, reversed from Python operand order. No pointer-value set
subtraction is used.

`fmp_capture_closure` mirrors :647-668 for one root: only single-output
ADD/SUB/ASSIGN/PHI propagate. The bounded result is validated for closure;
failure vetoes. Root membership, closure, propagation and live-derived veto
are proved. Loop-order PHI/ASSIGN/SUB, multi-output exclusion, BUMP exclusion,
live derived capture veto, address-only MLOAD not pinning, and stored derived
pointer pinning are checked production probes. Callers supply **current state**
capture roots to `fmp_capture_query_veto`; this interface does not itself collect
all GETFMP roots or replace current-state scope with a whole-function veto.

## Proof integrity and dependency direction

All three new theories audit their own exported theorem tags (DISK_THM only).
No admissions were added. Shared syntactic helpers (single-output, transparent
opcode, uses-any) moved unchanged from fmpReclaimDefs into fmpAliasDefs, so future
reclaim transfer can import these interfaces without a theory dependency cycle.
The old reclaim transfer/checker semantics are otherwise untouched at this
checkpoint. These static closure/checker facts are not a memory-reuse safety
proof; operational hypotheses and indexed production transfer are later work.
