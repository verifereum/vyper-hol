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

## 7. Rooted token-path test (C1.12.origin_path_test)

This section is a bounded design test, not a proved graph or simulation result.
Baseline targets CollapsedOrigin and o1ContractMakeSsa build unchanged
(TO_makessa-20261105T052724Z_m9687_t001). The two contract cheats remain.

### 7.1 Exact interfaces that are available

The source of each interface, rather than its name alone, was checked:

* SourceCuts:50-145: `current_source_cut A ev n rs E` splits a STATIC
  `current_local_trace` into two traces at equal annotation/source/renamed
  lengths. `current_source_cut_step` exposes the indexed `current_inst_trace`
  and the next source cut. These are not execution-history statements.
* DemandedCut:78-101: `current_actual_demanded_cut_tokens` equates the static
  predecessor block-exit token and successor inherited token. Besides
  wf_function, fn_inst_wf, fn_defs_reach_uses, fn_phi_operands_single_def,
  all_reachable, first_block_no_preds and entry lookup, it requires the CFG
  edge, both DOMINATOR token chains, **no insertion for v at the successor**,
  `current_phi_cut_clear fn v successor`, and selected post-PHI liveness at
  the successor. It does not apply across an inserted reset or a source PHI
  defining v. Its exceptional sibling (32-76) handles global PHI-operand
  occurrence using the single-definition bound; it does not assert arbitrary
  backward liveness through those PHIs.
* LiveTransport:61-107: `current_live_cut_to_pred_exit` requires successor
  post-PHI liveness, no leading-PHI definition of v, and **no occurrence of v
  among any leading-PHI operand variables**, not merely the selected edge's
  operands. `current_live_exit_to_cut` additionally requires no tail definition
  of v in its block. `current_selected_live_edge` combines those requirements.
  A bare CFG route therefore cannot be supplied as a live route.
* LastSite:22-79: no changing site implies no source output and a clear PHI
  cut. `current_non_site_live_route` turns a CFG suffix into a live route only
  with no changing sites on its listed nodes, a clear final cut, and global
  absence of PHI-operand v. LastSite:115-123 splits a finite list at its LAST
  changing site. CutTokens:27-74 proves identity off changing sites and
  constancy at a changing block, but on DOMINATOR scan chains, not an actual
  rooted execution route. LastSite:82-113 can recover strict dominance from
  a last-site-to-live-cut suffix, with frontier closure and the same global
  PHI-operand exclusion. This is a possible bridge, not dynamic preservation.
* FirstArrival:164-185 excludes the TOKEN CurrentInserted v h on an actual
  entry prefix with no earlier `CurrentBatch h phis`. Lines 217-239 give the
  exact NAME residual `name=x <=> x=v /\ exit_token=CurrentDefault v`.
  Its conclusion is not `name<>x`.
* ExitTokens:53-81 excludes defaults given a SINGLE dominating source
  definition and a static ancestor path. Lines 83-106 obtain such a definition
  for original PHI operands from the single-definition premise. They do not
  establish a dominating individual definition for arbitrary multiply-defined
  v merely from definite assignment.
* TokenOwnership:39-95: block/chain scans preserve owner v; an original token's
  owner is its indexed source output, and an inserted token's owner is its
  constructor's variable. PlacementCut:108-118 localizes every insertion of
  a single-definition variable to its defining block when leading PHIs exist.
* CollapsedOrigin:110-205 supplies a nondefault nonself token t naming y,
  allocated-name uniqueness, and incoming-token trichotomy (self, t, default).
  Default incoming tokens retain the physical alternatives v=x or v=y.
  None of those conclusions equates the static scan to a chronological scan.

### 7.2 A precise next graph theorem candidate

Here is the first missing graph implication in a form independent of target
success and of the ledger in section 2. It is proposed notation only; no new
constant or theorem is installed. Let `I = current_actual_inserted fn`, and let
`Pgraph` be exactly:

```
current_structural_certificate s fn fn' s' A H events /\
wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
fn_phi_operands_single_def fn /\ all_reachable fn /\
first_block_no_preds fn /\ entry_block fn = SOME eb
```

For any finite ROOTED CFG route and certified endpoint, test:

```
Pgraph /\ LRC (fn_cfg_edge fn) route eb.bb_label p /\
MEM ep events /\ current_event_label ep = p /\
lookup_block p fn.fn_blocks = SOME pb /\
MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) /\
(!b phi. MEM b fn.fn_blocks /\ MEM phi (collect_phis b.bb_instructions) ==>
         ~MEM v (MAP SND (phi_pairs phi.inst_operands)))
==>
current_event_exit_env ep v =
  current_chain_token fn I v (route ++ [p]) (CurrentDefault v)
```

The LRC list convention must be retained: route lists nodes before the endpoint,
so `[p]` is appended exactly once. Repeated labels are permitted. This is NOT
an equation between the static dominator path and the executed CFG path without
liveness premises. In particular the endpoint is live at EXIT, not necessarily
live after its leading PHIs; an ordinary definition in p is allowed.

Proposed reduction (all unproved steps explicitly exposed): split the rooted
route at its last changing site using current_list_last_site. There are no
insertions or ordinary definitions in the remaining full blocks. Propagate exit
liveness backwards across that suffix using the LiveTransport premises above.
Apply demanded-cut equality at its non-changing successor entries, and local
block scan identity, until reaching the last site's exit. Its block scan is
constant, so its incoming static token is irrelevant. The no-site branch must
instead propagate back to entry and identify its inherited default token.
The existing LastSite dominance/frontier argument is an alternative way to
identify this same last static site. These reductions still need a proof for
an EXIT endpoint (which may define v), and a checked certificate-to-static-scan
adapter on each selected cut. They do not follow from cut equality alone.
This graph implication is the first missing theorem; the bounded test stops
here instead of assuming its conclusion as an operational invariant.

The global PHI-operand exclusion is not silently added to the frozen contract.
If v occurs as an original PHI operand, DemandedCut:10-19 bounds its source
instruction-definition count by one; PlacementCut:108-118 localizes its
insertions to that defining block. A complete consumer must handle that case
separately, including repeated output slots in that one instruction, rather
than invoke the displayed candidate with a false exclusion premise.

### 7.3 What the candidate would say about last h / last t-writer

For an actual predecessor exit, obtain its rooted route from actual_prefix,
not from current_dom_tree. To use 7.2 one must FIRST derive endpoint liveness
from the selected post-PHI liveness that justified insertion at h. In the
non-original-PHI-output case, h has no source leading-PHI definition of v;
if v is not an original PHI operand, current_live_cut_to_pred_exit supplies
this exit liveness on p->h. The original-PHI-output case uses the retained
batch interface below instead. This demand bridge is a separate obligation,
not an assumption that all inserted reads are source uses.

Assume the graph candidate is proved and its premises discharged. If the
certified exit token is CurrentInserted v h, the chronological scan's last
changing block must be h, and that block must have no source definition of v:
a source definition makes its final token CurrentOriginal, not CurrentInserted.
Every changing block after the most recent completed h would contradict that
last-token identity. Since the unique allocated writer of y has owner v,
an intervening visit to its external writer is a changing block too. Thus
this would rule out REFRESHING y after the latest h copy, not just rule out
source writes of v. It is the missing alias-sensitive conclusion in section 5.
Taking the latest h visit automatically handles the case that a t-writer visit
is followed by another h: the newer h, not the old h, seeds the epoch.

There are four distinct local-origin cases, not one dominance slogan:

1. `t=CurrentOriginal h i j`, original PHI: source PHI output uniqueness and
   inst_wf force the appropriate singleton output; nondegeneracy retains it.
   ReinsertedOrigin:53-95 identifies the retained writer before the copy and
   ReinsertedReady supplies its readiness. Here the NEW source PHI version is
   wanted; preservation of the incoming y version would be incorrect.
2. `t=CurrentOriginal h i j`, ordinary tail: y's writer is after the copy on
   this visit, so it cannot justify readiness. In the SELF-token case, 7.2
   would exclude the case entirely: scanning a whole h with any source v
   definition cannot produce inserted(v,h). For a first/nonself entrance a
   separate rooted no-earlier-h argument is still needed to exclude a future
   tail token at its predecessor. Static token occurrence alone is not an
   execution of that writer.
3. `t=CurrentInserted w h`: owner preservation forces w=v; then t=self,
   contradicting CollapsedOrigin's nonself condition. There is no distinct
   earlier/later inserted copy in h for this owner. This is a token-owner
   exclusion, not arbitrary instruction-order reasoning.
4. t outside h: its effective writer is a changing site for v (original
   indexed source output or inserted(v,g)). The last-site conclusion above
   would prohibit its execution after the latest h copy. No interpretation
   of a dominator-tree path as a runtime path is required.

The semantic endpoint would then be: at the most recent completed h copy,
x and y carry the SAME source version; there is no subsequent source v write
and no subsequent allocated y writer before p. Block output distinctness also
protects an external y through the current retained batch and earlier copies.
Consequently LastT y has exactly the LastS v version required in section 5.
This uses a previously completed successful copy from the induction history,
not the success of the copy currently being justified. Establishing that first
successful copy, and the current-retained original-PHI case, cannot be skipped.

### 7.4 First entrances and the two physical default collisions

On first entrance, FirstArrival rules out inserted(v,h) as a TOKEN. Trichotomy
then leaves t or default; spelling x does not itself distinguish them.
For default with v=x, first-arrival-name-residual permits the self SPELLING
but provides no completed h. For default with v=y, the nonself SPELLING can
still be physically uninitialized. Both must be eliminated at a demanded exit
by the same rooted argument plus actual source definedness, not by name
injectivity. Under 7.2, a default endpoint implies no changing site in the
rooted scan: scans never create a default after a nondefault token. An actual
source v definition on the completed route would be a changing site. Source
availability at this demanded actual exit must provide such a completed
source event. This contradicts default in EITHER spelling case. This reduction
requires the actual-domain/demand-to-availability interfaces as well as 7.2;
it is not proved merely by the graph candidate or fn_defs_reach_uses alone.
For original PHI operands the single-definition/dominance route may discharge
this residual instead, with its exact premises from 7.1.

### 7.5 Disposition of the bounded test

No concrete finite source/certificate obstruction was found. No EVAL task
counterexample is claimed. The rooted last-changing-site equality in 7.2 is
an exact next graph candidate, with a reduction to existing list splitting,
backward live transport and static cut equality; the missing exit-endpoint
and certificate adapters are explicit. The singleton-PHI-operand branch,
first entrance nonself readiness, and semantic source-version transfer remain
obligations. This test therefore supports a focused rooted-path proof-design
checkpoint, NOT global simulation integration and NOT another conditional
store wrapper. In particular a proof of 7.2 alone must not be reported as
operational readiness or completion of either frozen theorem.

## 8. Exceptional demanded-origin interface test (C1.12.exceptional_origin_test)

Successor checkpoint, not a claim that section 5's operational transfer is proved.
Section 7.2's displayed graph candidate is now proved as
`current_certificate_rooted_live_exit` in RootedTokens. RootedOrigin and
ChronologicalOrigin supply the chronological last-site/default inversions.
DemandOrigin supplies a definition on a demanded rooted route and, in the
operand-excluded case, excludes default provenance and closes FirstArrival's
physical-name residual. These results resolve the earlier STATIC token gap
only under their displayed restrictions. They do not establish successful
copies or preservation of y's current source value.

### 8.1 Exact exceptional candidate

With `Pgraph` exactly as in section 7.2 and `I = current_actual_inserted fn`,
the candidate for a NEW theorem is:

```
Pgraph /\ LRC (fn_cfg_edge fn) route eb.bb_label p /\
MEM ep events /\ current_event_label ep = p /\
lookup_block p fn.fn_blocks = SOME pb /\
current_demand fn v p (LENGTH pb.bb_instructions) /\
(?ob phi. MEM ob fn.fn_blocks /\ MEM phi (collect_phis ob.bb_instructions) /\
          MEM v (MAP SND (phi_pairs phi.inst_operands)))
==>
current_event_exit_env ep v =
  current_chain_token fn I v (route ++ [p]) (CurrentDefault v)
```

There is deliberately NO exit-liveness premise. The proposed discharge below
uses availability/unique dominance, not backward liveness transport. There is
also no ir-supply premise: this is token equality, not equality of names.
This exact candidate has not been installed or proved by this audit component.

### 8.2 Checked interfaces and discharge map

The following sources were read, including their actual antecedents:
DemandedCut:10-19,32-76,78-101; PlacementCut:108-118;
SingletonSelectors:95-164,194-245,247-290,311-338;
DemandDominance:18-49; DemandOrigin; DominanceBridge:6-14.

1. `current_phi_operand_single_bound` uses the existential leading-PHI
   operand occurrence to bound the number of DEFINING INSTRUCTION occurrences
   by one. `current_phi_operand_has_leading_phi` proves the leading-PHI flag.
   Neither fact asserts a unique output slot.
2. `current_demand_route_definition` supplies l, db, di on route ++ [p].
   It requires fn_inst_wf, present in Pgraph. `lookup_block_MEM` and
   `lookup_block_label` convert the witness to member-block/member-instruction
   form. Thus there really is a defining instruction; the count cannot be zero.
3. Choose its block/instruction indices b,i using MEM_EL. The existing
   `current_defining_sites_member` and `current_single_definition_indexed_site`
   give `current_defining_sites fn v = [(b,i)]`. The canonical token is
   `current_canonical_instruction_token fn v (b,i)`, whose output slot is the
   LAST matching slot, not slot 0 or an arbitrary occurrence.
4. `current_single_definition_chain_token` applies to the chronological route:
   its required defining-block label membership follows from step 2. It allows
   repeated labels, arbitrary initial token t and repeated outputs. Internally
   it uses `current_singleton_block_token` and localization of all changing
   sites. PlacementCut's `current_actual_inserted_single_local` is the insertion
   localization fact and explicitly requires the leading-PHI flag from step 1.
   Thus every completed visit to the defining block resets to the SAME final
   Original token, and every other block preserves it.
5. For the STATIC certificate exit, do NOT invoke
   `current_phi_operand_canonical_exit_token` at this arbitrary demanded p.
   That lemma requires MEM (p,v) in an actual phi's pairs plus the selected CFG
   edge to that phi's block. The global occurrence premise here does not give
   those edge conditions. Its selector corollary is therefore insufficient.
6. A different already-proved interface removes that apparent gap:
   `current_demand_available` gives availability at p's exit, and
   `current_available_unique_dominates` gives fn_dominates of the unique
   defining block over p. Reachability of p comes from all_reachable and its
   lookup. This implication requires only the count and member witness from
   steps 1-2, not the selected PHI edge. Convert to analysis dominance with
   `current_semantic_dominates`.
7. `current_certificate_static_env` supplies the actual static ancestor path
   and its block-exit scan. `current_actual_path_chain` gives the token chain.
   If db.label=p, membership in path ++ [p] is immediate; otherwise strict
   dominance plus `current_actual_chain_membership` gives membership in path.
   Use `current_inherited_token_step`/`current_inherited_token_def` to express
   the static block-exit token as a chain over path ++ [p]. Apply the SAME
   `current_single_definition_chain_token` as in step 4. Both sides are the
   same canonical token; no new general liveness theorem is necessary.

This is a discharge map, not a checked proof of the new candidate. The missing
work is a compact token-level assembly theorem at arbitrary demanded exits;
the selected-edge selector must not be silently generalized. No new semantic
invariant is proposed. The mathematical argument no longer has an unidentified
static implication after including DemandDominance's unique-dominates boundary.

### 8.3 Adversarial branch checks and operational residual

* Empty route: p is entry; DemandOrigin still supplies a definition in that
  block. The exit is after all instructions, so a local definition resets the
  token. No claim about entry's initial store follows.
* Repeated visits to the defining block: each reset is to the same canonical
  final slot; acyclicity or ALL_DISTINCT route is unnecessary.
* Repeated output destinations: the definition bound counts instructions, not
  slots. SingletonSelectors:95-145 explicitly selects the last output slot,
  so an earlier duplicate cannot be substituted into the argument.
* A PHI operand occurrence somewhere else is NOT evidence of a selected p edge.
  Step 6 is essential to avoid that unsound instantiation.
* An insertion at the defining block can occur but its token is overwritten by
  the full original scan on every complete visit; insertion-only resets at
  other blocks are excluded by localization.

Even a proof of the candidate above would establish token provenance only.
Open operational obligations include deriving demand/liveness for the precise
collapsed-copy consumer, classifying each physical y writer by owner-v changing
sites, linking completed source instruction events to the target origin ledger,
and the first successful copy/return-epoch induction. No target success, lookup
SOME, equal-store clause, or copy-readiness assumption was added to this test.
