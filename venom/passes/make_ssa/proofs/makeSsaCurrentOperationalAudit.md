# Operational invariant audit (C1.12.probe)

This is a design artifact, NOT a theory, axiom, proved invariant or counterexample.
All mathematical implications labelled OPEN below remain obligations. No accepted
SML interface is changed. Baseline `holbuild(o1ContractMakeSsaTheory)` passes
(TO_makessa-20261105T052724Z_m9584_t001); the frozen contract cheats remain.

## 1. Transformation facts fixing the phases

`makeSsaCurrentDefsScript.sml:442-498` is the implementation authority:
remove self-valued slots, classify the remaining values, retain a PHI verbatim
when the remaining values differ, otherwise emit ASSIGN from their common
nonself name, or NOP when none remain. `keep_current_phi_vars` can reject the
candidate, but does not invent another copy. The prefix partition preserves
relative order within each partition and moves ALL retained PHIs before ALL
copies. Source PHI reads and target retained-PHI reads use incoming snapshots;
copy reads use the progressively updated target store. Reassigned IDs are not
positions.

Source phase cuts: predecessor exit, incoming entry, post-parallel-PHI batch,
ordinary instruction boundaries. Target cuts add the intermediate cleanup
cursor k. A successful source batch advances the source directly to its
post-PHI cut; during target copies the source stays there. No new execution
relation is needed: use current_actual_prefix and current_copies_run.

## 2. One candidate: dynamic write versions, not perpetual owner equality

The following is exact HOL-shaped proposed notation, not declarations. Values
have the existing runtime word type. A source write version is a fresh natural
number allocated to an EFFECTIVE dynamic source write. Parallel writes are
recorded in their actual effective order (reverse PHI pair order); repeated
ordinary output destinations use the actual indexed event order, not an
assumption of distinct source outputs.

S : (num # string # value) list -- chronological effective source writes
T : (string # num # value) list -- chronological target writes with source origin

LastS S v a w <=>
  ?pre post. S = pre ++ [(a,v,w)] ++ post /\
             !b u. ~MEM (b,v,u) post
LastT T n a w <=>
  ?pre post. T = pre ++ [(n,a,w)] ++ post /\
             !b u. ~MEM (n,b,u) post

StoreS S st <=>
  (!v. lookup_var v st = NONE <=> !a w. ~LastS S v a w) /\
  (!v a w. LastS S v a w ==> lookup_var v st = SOME w)
StoreT T st' <=>
  (!n. lookup_var n st' = NONE <=> !a w. ~LastT T n a w) /\
  (!n a w. LastT T n a w ==> lookup_var n st' = SOME w)

An ordinary target write records the source version of its corresponding
indexed effective source event. A retained original PHI target write records
the version of that source PHI's effective write. An inserted retained PHI
records the source version of v at predecessor exit. A cleanup copy propagates
the origin of its source's LAST ALREADY COMPLETED target write. That final rule
cannot be applied unless that write exists: it is not a definition of successful
reachability and does not authorize executing an undefined copy.

The proposed aligned-cut relation R(q,st,st',S,T) has these clauses:

* actual source and target prefixes ending at q's respective cuts;
* control alignment from the certificate's ordinary partition / cleanup cursor;
* execution_frame st = execution_frame st';
* StoreS S st /\ StoreT T st'; versions in S are unique;
* current_singleton_agree (current_instruction_singleton_table fn H) st st';
* demanded selector provenance:
  !v a w n. current_demand fn v l i /\ LastS S v a w /\
    current_token_name H (Selector q v) = SOME n ==>
    LastT T n a w;
* demanded definedness is derived from source actual-prefix availability, not
  included for all allocated names.

Selector q is the existing certificate source-cut environment at body cuts,
predecessor event exit at exit cuts, and the post-leading source-cut environment
at the completed cleanup cut. During cleanup, the ordinary demanded-selector
clause is suspended until its producer copy has executed; the permanent clause
and StoreS/StoreT persist. This staging is essential: a demanded inserted
destination need not be defined just after the retained batch.

Dynamic validity of an inserted allocation x is now `LastT T x a w`, not
`lookup_var x st' = lookup_var v st`. Any later target write to x invalidates the
old claim automatically. In particular another insertion writing a copy-source
y invalidates its old LastT witness. No default token gets an allocation event;
when the spelling v is used by CurrentDefault v its physical binding is still
determined by LastT. Thus a default and an allocated name sharing v are NOT
silently distinguished as two physical stores.

The candidate does not assume a lookup for an upcoming copy, successful future
target execution, or current_refresh_segment. It also does NOT yet prove that
upcoming copies can run. The gap below is a failed inductiveness test, not a
license to add a copy-ready conjunct to R.

## 3. Initialization and ordinary/call boundaries

With S=T=[] and empty variable stores, StoreS/StoreT and permanent agreement
hold (current_singleton_agree_empty). LastS has no witness, so the proposed
version implication is vacuous. This alone does not establish demanded source
SOME; actual-domain initialization and demanded availability must discharge it
where used. Entry has no PHIs by the frozen premise. The control/frame entry
alignment still has to be connected to fn_entry_state; no theorem here asserts
it from arbitrary equal empty stores.

At an ordinary cut, actual source availability plus demanded selector provenance
supplies operand equality. current_certificate_ordinary_step_joint_singleton
then supplies the SAME target successor for chronological and permanent
agreement. The ledger extends from its paired indexed writes; final effective
writes, not all per-slot alignments, justify repeated output destinations.
Existing finalslots/finalevents results cover permanent preservation. Retaining
LastT provenance for each next demanded selector still requires the cut/demand
transport, not simply the local step theorem.

For INVOKE, the base instruction proof is not a substitute for recursive call
transport. The candidate versions are caller-local; returned values create
fresh effective caller write versions after a paired callee result. Frame and
memory correspondence require the existing ctx_bisim/call boundary. Recursive
call success and finite-run fuel transport remain separate unresolved consumers;
no call claim follows from this audit.

## 4. Exhaustive syntactic copy-source classification

Every actual cleanup ASSIGN under the frozen premises is from an inserted
PHI: original PHIs are retained by the accepted nondegeneracy/retention results.
Inserted NOPs are ruled out by current_certificate_inserted_not_nop. For a copy
x <- y, `current_phi_slots_assign_iff` says y<>x and every edge operand is x or
y, with at least one y. By current_certificate_inserted_edge_resolve the actual
predecessor exit spelling is x or y. This is an exhaustive NAME classification,
not yet exhaustive dynamic readiness.

| provenance of y / dynamic writer | availability at the copy | status |
| --- | --- | --- |
| original retained PHI in this header | current retained batch writes y; block output distinctness protects it through preceding copies | established for reinserted original outputs by current_certificate_reinserted_origin / current_certificate_reinserted_next_ready |
| another inserted copy earlier in this header | if actually earlier, propagate LastT from its completed write; block distinctness protects y afterwards | conditional sequencing is elementary; existence of this source class not asserted |
| original ordinary definition earlier in this header visit | no ordinary source-tail instruction has run before the cleanup cursor | cannot justify by this visit; needs an earlier visit or static impossibility proof |
| original ordinary definition later in this header visit | future definition cannot justify present read | impossibility under the certificate is OPEN, not supplied by instruction order |
| another inserted copy later in this header | future copy cannot justify present read | same-owner/same-header token identity suggests exclusion, but no exhaustive origin theorem is imported here |
| original or inserted allocation outside this header | use latest completed dynamic defining visit | OPEN source-version agreement and source-path exclusion of clobber; static dominance is insufficient alone |
| CurrentDefault v spelling | no fictitious writer | OPEN elimination or identification with a physically allocated last write; token inequality does not prove name inequality |

For every nondefault token allocated the name y, allocation injectivity fixes
its unique static output owner. For CurrentInserted v g,
current_certificate_inserted_write_site localizes writes of y to g, including
cleanup writes. This does NOT prevent executing g again or show that its new
value agrees with an old x. For original tokens, source slot provenance fixes
the defining instruction, but repeated dynamic execution remains possible.

The candidate T records all those writes and therefore is alias-closed as a
STORE ledger. It does not automatically preserve the required SOURCE VERSION
identity. This distinction is the precise remaining invariant problem.

## 5. Worked transfer and exact point at which it fails

Take a successful source batch, incoming R, and a cleaned target block with
retained prefix P and ordered copies C. Incoming source v definedness at the
predecessor plus exit-selector provenance yields evaluation of each inserted
survivor through current_certificate_inserted_retained_eval. Original retained
PHIs use current_certificate_retained_projected_eval. The batch assembler
current_certificate_mixed_batch_ready yields target post-batch existence and
permanent agreement once its explicit incoming owner agreements have been
derived from the proposed exit clause. Target writes extend T using the frozen
incoming origins. This is the intended derivation; the exit demand-to-readiness
adapter must still be checked for every inserted survivor.

Induct on the cleanup cursor k, with only the ALREADY EXECUTED prefix of C
recorded in T. For reinserted original outputs, a retained source PHI event
creates the required fresh source version a and target retained PHI y carries
a; current_certificate_reinserted_next_ready protects y and executes x<-y.
This complete class does not need a previous visit.

For another collapsed insertion with actual incoming selector y, incoming R
can supply LastT T_in y a w with LastS S_in v a w, provided predecessor demand
is established. If y is outside the current prefix outputs, block output
distinctness/cleanup nonclobber transports that witness to cursor k. If y is a
current retained output or an earlier copy output, the transfer must identify
its NEW origin with the required source version; merely preserving incoming
y is wrong. These are explicit classification obligations.

For actual incoming selector x, incoming R supplies LastT T_in x a w, NOT
LastT T_in y a w. The copy is x<-y, so neither StoreT nor that demanded clause
allows its step. An old x<-y event only proves equality of origins AT THAT
EVENT. EpochSplit, EpochProgress, InsertedSuffix and InsertedPersistence can
protect x after an executed copy, but do not protect y or preserve the source
version a. The transfer stops before invoking current_cleanup_assign_step.

Exact missing source-level implication, with the actual certificate and
frozen hypotheses in P, and R interpreted as above:

P /\ R(exit(p),a,b,S,T) /\ actual_next_edge p h /\
  collapsed_inserted_copy(v,h,x,y) /\ exit_selector(p,v)=x ==>
  ?version value.
    LastS S v version value /\
    LastT T_after_current_retained_and_prior_copies y version value

`T_after_current_retained_and_prior_copies` refers only to the constructed,
already successful prefix; no future copy is in it. This implication is OPEN.
It is NOT a theorem restated as a premise of reachability. To prove it, either
show that any intervening certified write to y forces a non-x predecessor
selector, or prove equal origin for the alias rewrite. Source no-write alone
is inadequate. First-arrival token exclusion is inadequate because x=v may
be the default spelling (FirstArrival's exact residual). This is the smallest
unresolved semantic case exposed by this candidate.

Without this implication there is no complete ordered-copy success proof and
no outgoing demanded-provenance proof. Adding the implication to R as a
copy-source-SOME clause would hide the original problem; this audit rejects
that repair. No SML invariant is installed.

## 6. Adversarial checks and disposition

* Default collision / first arrival: CurrentDefault v and inserted name x=v
  are physically one name. FirstArrival excludes the inserted TOKEN only and
  leaves exactly this collision. Candidate records physical writes, so it
  neither derives a false inequality nor manufactures a write version. The
  classification remains incomplete for this branch.
* Self return: LastT x can be valid while LastT y has a newer origin. The
  proposed incoming demanded clause alone cannot run x<-y. See section 5.
* Another insertion's alias write: InsertedWriteSite excludes writes from
  blocks other than y's header, but a path visiting that header is possible
  until a certificate/selector argument rules it out. Replacing old T by new
  T correctly invalidates the old witness; no equal-value assumption repairs
  the missing source-version implication.
* Repeated original output slots: LastS uses effective events, so the final
  source value corresponds to the canonical final target slot, not an earlier
  duplicate. This is compatible with InstructionSingleton and FinalSlots.
* Current retained PHI before its reinserted copy: this case IS handled by
  the source frozen nondegeneracy premise and accepted ReinsertedReady.
* Later-this-visit dependency: the table above marks both possible future
  writer classes as exclusion obligations, not ready-by-order cases.

These are symbolic branch/interface checks, not EVAL counterexamples to the
frozen contracts. No concrete source program has been found violating them;
there is no basis here for an unprovability claim or falsehood gate. One
candidate has been tested and found insufficient; no speculative revision is
installed. The next strategist decision must address the source-version
implication and exhaustive source provenance, not request another conditional
store-preservation theorem or pretend this audit establishes inductiveness.
