# Occurrence-sensitive symbolic interface: checked probe, not compiler closure

The new makeSsaCurrentSymbolicInterface theory interprets the existing
current_static_expr syntax. No pass, frozen statement, existing theory, or
static-demand definition is changed.

## Independent environments

A symbol is Initial(variable), Constant(operand), or Occurrence(dynamic paired
step, output index). A total symbolic environment is not a runtime definedness
assertion: Initial(v) denotes an unspecified input origin, not an existing value.
The walk uses option-valued environments so a missing selector can propagate
NONE. The initial environment can be arbitrary. Literals (and non-variable
operands) are retained, never confused with dynamic output atoms.

An ordinary original write interprets CurrentStaticProduced k as
Occurrence(n,k). Only corresponding source/target original instructions may
share n. Inserted PHIs and cleanup copies instead interpret a Read from the
incoming environment. Administrative steps can advance the clock without
producing any atom. A static block/instruction id is NOT a valid dynamic n.

## Checked boundaries

- Empty walk is identity for arbitrary env.
- Ordinary substitution commutes with expression interpretation.
- Selected PHI substitution reads the incoming env, even if the selected
  operand is another output spelling. Missing selectors remain NONE.
- General simultaneous swap reads both old values, never sequential updates.
- Walk concatenation advances the occurrence clock by prefix length.
- Repeating the identical static write uses a different atom on the second
  visit, universally in env, index, variable and substitution.
- Produced equality requires BOTH dynamic occurrence and output index equal.
- Fresh incoming environments exclude Read/Produced equality. The checked
  unbounded_alias theorem refutes that inversion without freshness: an
  arbitrary env may already contain Occurrence(n,k).

These are interface laws, not proofs that the compiler supplies coherent
substitutions. In particular ordinary_transfer and phi_transfer expose exactly
the existing static substitution and do not assume demanded agreement.

## Remaining compiler-wide obligations (UNPROVED)

1. Build admissible aligned walks from actual CFG/phase structure. Tie each
   target original write to its paired source occurrence; target-only copies
   must not be assigned arbitrary Produced atoms. Repeated block visits must
   preserve this pairing. Entry predecessor canonicalization still requires
   empty batches on BOTH sides.
2. Derive seed origin equality and suffix-sensitive backward preservation from
   actual allocation history, dominance, insertion and edge selectors. Unique
   names or owner equality alone do not establish reaching origins.
3. Establish a generation bound on all incoming symbols (strictly older than
   the current clock). Then fresh_read_not_produced can justify local
   Read/Read versus same-occurrence Produced/Produced classification. Static
   output-index equality alone cannot justify that classification.
4. Derive source existence for extra reads independently. Incoming PHI reads
   require predecessor-sensitive availability; cleanup reads may use successful
   source batch completion. Symbol equality and even an Initial atom give no
   runtime lookup witness. Reuse AvailabilityBoundary for the successful batch.
5. Connect symbolic substitution to actual selected PHI output semantics under
   source well-formedness, and connect ordinary Produced values to paired
   successful instruction outputs. No runtime simulation is asserted here.

The next owning-ancestor continuation must address the compiler invariant,
not add fixtures or assume transfer_safe, seed equality, demanded agreement,
or extra-read availability as new hypotheses of the frozen theorem.
