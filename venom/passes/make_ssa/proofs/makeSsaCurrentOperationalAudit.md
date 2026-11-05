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

## 9. Writer exclusion / return-epoch design (C1.12.writer_epoch_design)

This is a worked interface audit, not a new operational theorem. E0298 now
proves section 8's exceptional token equality in ExceptionalDemandOrigin.
No target success or value equality follows from it alone.

### 9.1 Physical ownership is already classified

RestrictedRuntime:115-151 classifies ALL outputs of a cleaned block, including
ASSIGN cleanup outputs, as history allocations whose owner changes at that
block. Do not add another writer-classification theory.

For a collapsed inserted PHI at h, use exactly CollapsedOrigin:110-139:
its hypotheses include the replayed operand list over the actual predecessor
map, output [x], and simplify_current_phi producing ASSIGN [Var y]. It supplies
x<>y and a STATIC event ev with exit token t, not default(v) and not inserted(v,h),
and token_name H t = SOME y. This ev need not be the executed predecessor.

The ownership discharge is as follows (assembly not yet a named theorem):
* Choose U with history_valid and event_valid/event_names using
  current_certificate_owner_universe (RuntimeOwners:121). Use this SAME U.
* Obtain the insertion annotation (CurrentInserted v h,v) in A h from the
  actual insertion prefix/annotation boundary, as done in
  current_certificate_inserted_exit_token_name (CollapsedOrigin:95-107).
  Event validity and current_event_annotation_owner_covered give MEM v U.
  This does not require v to be an original instruction output.
* Unpack the certificate's tree trace, start with
  current_env_history_owners_default and use current_tree_trace_history_owners
  (ActualRetention:185). This gives EVERY exit-env history ownership for the
  final H. The certificate adapter for this fact is not exported separately;
  it is the same trace extraction already used in ReinsertionNames:395-400.
* At ev, env_history_owners says t=CurrentDefault v OR
  exists n. MEM(t,v,n) H. Eliminate the first using CollapsedOrigin. Thus
  current_history_owner_covered is an alternative check of MEM v U.
  With history_valid, current_env_history_owner_name and token_name H t=SOME y
  give current_owner_name H v y (ActualRetention:163-175).

This composition does not use token spelling to infer owner. In particular
y=v is permitted by current_owner_name_def. Classification plus owner separation
now excludes a write to y in any non-changing block. Required certificate,
wf_function, all_reachable, entry and supply facts are all frozen hypotheses.

### 9.2 Exact chronological suffix boundary

For the actual predecessor p, derive a ROOTED LRC route from the source prefix,
not from the static event ev. To identify its scan with the p event's exit token,
use RootedTokens in the operand-excluded case (exit liveness required), or
ExceptionalDemandOrigin in the PHI-operand case (exit demand required). Demand
or liveness at THIS p for the insertion at h still needs a consumer theorem;
it is not implied by the existence of CollapsedOrigin's static ev.

If the resulting token is inserted(v,h),
current_chronological_inserted_inverse (ChronologicalOrigin:79-103) splits
route++[p] = pre ++ h::post. The h block has no original v output; every block
in post is non-changing for v. Lookup coverage follows from the rooted route.
If post is nonempty, its consecutive CFG edges, lookups and non-changing facts
are precisely current_restricted_path fn v post. If post=[], do NOT invoke
that definition (it explicitly requires nonempty); use the empty phase prefix
identity. post excludes the completed h block and excludes the new h entrance.

For target phases wholly inside post, the remaining interface obligation is an
actual paired-history slice with EVERY phase's label in post (Control allowed).
Then current_restricted_prefix_owner_exclusion excludes owner-v outputs,
including y. This theorem does not require successful next-copy execution.
A completed target slice already obtained by induction can be transported by
current_restricted_actual_prefix_origin_transport, but that corollary protects
a SELECTED ENTRY name. It cannot be instantiated with arbitrary y without
proving selected=latest_current_name(entry_rs ev2) v for some event ev2.
Alternatively use its underlying current_actual_prefix_origin_transport with
the just-derived physical exclusion; no new wrapper is needed.

There are TWO boundary pieces outside post: the tail of the last h visit after
its copy and the retained batch/earlier copies of the current h visit. Whole-
block non-changing exclusion cannot cover either because insertion makes h a
changing site. Need local output distinctness/nonclobber, not inclusion of h
in restricted_path. For external y, allocated-name uniqueness and output
classification localize its writer away from h. For local original-PHI y,
use ReinsertedReady instead and keep its newly produced source version.

### 9.3 Proposed induction judgment and worked steps

Use induction on already completed paired semantic visits, with an inner
induction on the ordered cleanup copy index k. Its state carries actual source
and constructed target prefixes, phase/control alignment, equal execution
frames, current_origin_realizes Val Ms source and Val Mt target, demanded
agreement, and a history of COMPLETED copy seeds. A seed records visit, h, v,
x,y and origin o at its successful completion, with Ms[v]=Mt[x]=Mt[y]=o and
Val(o)=SOME value there. Seeds are past witnesses, not unconditional assertions
that allocated names remain current. A seed's validity at another cut must be
DERIVED by no-write slices; it is not assumed in the judgment for a future
copy. This judgment is proposed only; its initialization/transfer is unproved.

First entrance, non-original-PHI-output v:
1. Derive actual p demand/liveness as above. DemandOrigin excludes defaults in
   the operand-excluded case; in the exceptional case the singleton canonical
   token cannot be default. This eliminates BOTH v=x and v=y default spelling
   collisions without name injectivity. FirstArrival excludes inserted(v,h).
   Collapsed predecessor trichotomy therefore leaves the nonself token t.
2. Rooted equality plus chronological nondefault origin gives a completed last
   changing block d. A local ordinary writer t=Original h i j on this FIRST
   entrance cannot be that completed site: no earlier h occurred. This needs
   an original-token chronological inversion (nondefault_origin alone states
   only equality with block_token at d, not d=the token's block).
3. For external original t, its effective source output event must have an
   already paired target write with the same dynamic origin; for external
   inserted t, use its already completed retained PHI/copy event. Neither
   conclusion follows merely from membership in certificate history H.
4. Last-site suffix exclusion protects y and source v from d to p; local
   nonclobber protects y to index k. Read origin o and Val(o)=SOME value from
   the completed event, execute x<-y using CleanupRuntime, record a new seed.
   This is a design for first success, not a proof that step 3 is exhaustive.

Self return:
1. Rooted equality and inserted_inverse select the latest completed h visit,
   with no original v writes there and no changing sites in post. Induction
   supplies its SUCCESSFUL copy seed, not the current copy's success.
2. Preserve its source origin and Mt[y] through that visit's remaining tail,
   post blocks, and current pre-copy prefix by the exclusions in 9.2. Thus
   Ms[v]=Mt[y]=o and Val(o)=SOME value at the current read. Val extension must
   preserve o; RestrictedRuntime's protected-origins clause supports this for
   completed slices, not for a yet unconstructed slice.
3. CleanupRuntime executes the current copy and updates Mt[x] to o, re-seeding
   this visit. Current retained original-PHI output is a different case:
   ReinsertedReady:66 explicitly retains its writer before the copy and proves
   readiness conditional on the already constructed retained batch and earlier
   copies. It wants the NEW PHI version, not the old self-return epoch.

### 9.4 Smallest unresolved implications / adversarial checks

The first missing consumer implication is: actual dispatch p->h plus the
certified collapsed insertion for v yields the exact demanded/live predecessor
exit premise needed by the rooted equalities, with a split for original PHI
output v. Insertion pruning gives selected post-PHI liveness; LiveTransport
needs absence of leading-PHI v definition and operand exclusion in its ordinary
branch. This discharge has not been assembled here.

After that, the missing DYNAMIC implication is: the chronological final token's
last effective writer has an already completed paired target event (or a
retained PHI in the current batch) with the current source origin. It must be
proved by the proposed execution induction, not added as an assumption hiding
copy readiness. A static H allocation is not such an event.

Adversarial checks: post=[] requires no restricted_path; repeated h visits use
the latest seed; an intervening external alias copy is a changing site and
cannot lie in post; a source no-write suffix alone would not exclude it; default
names remain physically collidable until demand excludes their tokens; current
h is never admitted to non-changing post; duplicate ordinary output slots need
the canonical FINAL slot; original PHIs use snapshot/first-write semantics and
the frozen output-uniqueness premise, not ordinary sequential-write reasoning.
No concrete task counterexample is asserted. No new operational invariant or
conditional runtime theorem is installed by this audit.

## 10. Completed-event judgment signature test (C1.12.completed_history_probe)

This section supersedes the *proposed origin discipline* in sections 2 and 9,
not their accepted historical diagnostics. It is HOL-shaped design notation,
NOT an installed definition or a proved simulation. No SML changed. The baseline
four targets in STATE build (TO_makessa-20261105T052724Z_m9963_t001).

### 10.1 Judgment, admissibility, and event positions

Write `J Ps Pt q st st' V M N L a` for an inductively generated paired
completed-prefix judgment. Fixed parameters are the actual certificate, frozen
hypotheses, contexts and entry state. `Ps,Pt` are chronological semantic phase
lists; `q` carries the two execution locations plus block/source cursor and
cleanup cursor; `L` is a finite chronological list of completed records; `a` is
a fresh-origin generation bound. A record contains:

```
(kind, source_phase_position, target_phase_position,
 source_slot option, target_slot, source_owner, target_name,
 origin, value, source_cut, target_cut)
```

Positions refer to OCCURRENCES in Ps/Pt, not static instruction IDs, labels or
certificate events. A batch record additionally identifies the incoming snapshot
cut and the PHI index. A copy record points to its completed read cut and write
cut. Several indexed writes can belong to one ordinary phase. Their order is the
order in `writes`, and their ordinal is separate from their output slot. A PHI
origin can precede the event that propagates it; event position is NOT the origin.
Every record refers only to phases at or before its two recorded cuts. Historical
records retain their old maps/values as witnesses, not as claims about current
bindings. Default tokens have no fabricated record.

Required fields at a reachable aligned cut:

* `current_actual_prefix fn C (CurrentEntry f) entry Ps next result st` and
  the corresponding target prefix from the same entry store/frame. A continuing
  cut has `next=SOME loc, result=OK st`. Raw stopped cuts may use the existing
  `NONE` constructor but cannot then be continued by the prefix append rule.
* q aligns source ordinary instruction i with the certificate's renamed index
  `LENGTH ip+i`, or source post-PHI cut with target retained-batch/copy cursor k.
  Target cleaned prefix length/index adjustment must use PhaseShape, not identify
  its cleaned index with `LENGTH ip+i` for all phases. Index controls occur in the
  actual prefixes. Equal frames and equal current/previous BBs hold at aligned
  semantic cuts; indices need not agree.
* `current_origin_realizes V M st /\ current_origin_realizes V N st'`;
  `current_singleton_agree (current_instruction_singleton_table fn H) st st'`.
* At ordinary/exit cuts, demanded lookup agreement is the final conjunct of
  `current_joint_rel V M N rs D st st'`, with the certified selector rs and
  precisely the relevant D. During cleanup it is required only for selectors
  already produced. This is NOT permission to assume readiness for the next copy.
* Every effective source write has a completed record paired with an actual
  target write or retained snapshot event with the same origin/value. At an
  ordinary phase, extraction of the current binding uses its final matching
  slot; at PHIs it uses the batch's actual first-binding semantics. This is a
  coverage clause to be established by constructors, not by static MEM in H.
* All origins in M, N, historical record maps and retained seed records have
  first coordinate `< a`. A saved record remains valued by V at its recorded
  value. No clause asserts that its target_name still maps to its origin.

The final two fields are the proposed dynamic ledger invariant. They are not
known to follow from the other fields. In particular demanded agreement is a
transfer conclusion to prove, not evidence by itself that J is inductive.

Constructors must be forward extensions of **already constructed** actual
prefixes: Entry; non-INVOKE ordinary OK (plus its actual control update);
retained batch/dispatch (source stays post-PHI while target copies advance);
completed cleanup ASSIGN or NOP; and terminator/result boundaries. Constructor
premises may contain source execution and a previously proved J, but not a
successful target next step or a read-ready premise for that step. This is a
specification of obligations, not a definition by assuming them. INVOKE is not
among the admissible edges of ExecutionHistory:51-109; extending this skeleton
to calls is explicitly OPEN, not encoded as a fictitious CurrentControl edge.

At an intermediate target copy cursor, actual-prefix admissibility must include
its real `SUC vs_inst_idx` update before a continuing next copy. A raw prefix
ending immediately after a write has `next=NONE`; concatenating another prefix
onto that stopped witness is invalid. The target retained dispatch includes
both CurrentBatch and CurrentControl, as ExecutionHistory:52-61 specifies.
SemanticHistory is used only to extract/fold writes from such actual slices;
its unconstrained CurrentControl cannot manufacture reachability.

### 10.2 Actual entry and freshness test

Entry uses **the actual same state e** with `fn_entry_state fn e`, not arbitrary
states with matching frames. Pass entry-label preservation must establish
`fn_entry_state fn' e`; e has FEMPTY variables, index 0, prev NONE, nonhalted
and the actual entry label (o1PassLift:49-53). Choose `Ps=Pt=L=[]`, `M=N=[]`,
`V=(\o. NONE)`, `a=1` and both actual-prefix empty constructors. Realization,
frame equality, singleton agreement and empty ledger are immediate candidates.
Agreement of empty maps is true even when D is nonempty, but does NOT establish
SOME operand values. Entry has no PHIs; actual source availability is needed
when a later read is attempted. Fuel/location alignment and label preservation
are still proof obligations, not consequences of empty realization alone.

JointOrdinaryStep:143-178 returns `?n writes post'` and valuations
`V1 = current_event_valuation V visit l i n writes`, maps
`M1 = current_event_origins outs M visit l i n writes` and likewise N1.
It imposes NO freshness constraint relative to a historical seed ledger.
`current_origin_absent` checks ALOOKUP of the *current* map only
(JointRuntime:112-114); shadowed historical origins are not protected.
Thus choosing visit equal to a block visit while accepting arbitrary returned n
is not a sufficient ledger allocation discipline.

A precise candidate repair at the J level (unproved here) is to instantiate the
universally quantified `visit` with `a`, and then increase a to `SUC a` after
each ordinary phase, not just each block visit. All new origins then have first
coordinate a, regardless of existential n or repeated slot indices. All old
record/seed/map origins have smaller first coordinate. Consequently V1 agrees
with V on every historical origin. This uses the freedom in the actual theorem
signature; `visit` has no premise equating it to a block-visit number. Keep the
actual block occurrence as a SEPARATE ledger field. Finiteness of L is needed
for initialization/extension of the bound if any entry bindings are ever used;
fn_entry_state here has none. Retained batches and copies only propagate old
origins, so need not allocate a new origin generation. The finite bound and
valuation-preservation induction are explicit obligations for a future theorem,
not facts supplied by current_joint_rel. Without that discipline the interface
test fails exactly on an origin occurring only in an old seed.

### 10.3 Ordinary completed writer: exact supplied and missing facts

Instantiate the certificate ordinary theorem at a source body cut satisfying
its phis/tail split, j bound, non-PHI opcode and i=LENGTH phis+j. Use its SAME U,
rs,E,rt,Et and target out. At this cut J must derive joint agreement on
`operand_vars inst.operands ++ current_before_outputs inst.outputs D`, with
`D SUBSET U`, as well as permanent singleton agreement. Source actual execution
supplies `step_inst_base inst st=OK post` only after excluding INVOKE and applying
the non-INVOKE bridge. The theorem yields the SAME post' for:

1. target base-step OK;
2. shared indexed writes and `MAP FST writes=GENLIST I (LENGTH outs)`;
3. joint relation at rt,D with V1,M1,N1;
4. permanent singleton agreement at post,post'.

This is an ordinary **OK base-step** interface. It supplies neither an INVOKE
callee run nor the actual instruction-index/control edge. Even a terminator's
halt/dispatch choice must be connected to ExecutionHistory's constructors.
No terminal IntRet/Abort transport follows from this OK-only signature.

After making those real non-INVOKE edges, record each shared indexed write with
its two actual phase positions. For the external original writer t, accepted
OriginalOrigin gives the canonical FINAL matching output slot j at its last
changing block d. Select that slot's event from the completed phase's writes;
PairedRuntime:8-19 gives its origin `(a,d,i,n+j)` when the ordered writes are the
GENLIST slots. It occurs in BOTH decorated maps, but only the final hit for v
is its source ALOOKUP. Use LastEvent's final-hit interface, not arbitrary slot
membership. A later ordinary output of v in the SAME block would supersede it;
OriginalOrigin's final instruction/slot is needed before selecting the record.
If t is a PHI, the next subsection applies instead.

The event gives equal value w at its paired post-write cuts and V1(o)=SOME w.
It does not give N_at_p[y]=SOME o. To obtain that, split the already completed
source/target histories at the end of d, transport over d's remaining local
instructions, and then over the non-changing inter-block suffix to p. The latter
uses RestrictedRuntime physical owner exclusion and underlying actual-prefix
origin transport (section 9.2); it must also protect the source owner v. A
batch can read/write before the ordinary body, so the phase slice endpoints
must be explicit. Current-map realization plus historical event membership
alone is insufficient.

### 10.4 Retained original PHI: propagated origin, not a fresh source ID

RetainedJoint:31-50 requires the actual source `eval_one_phi` result, selected
operand v and predecessor p, exit joint relation with MEM v D, singleton output
and frozen nondegeneracy/certificate premises. It yields target retained index r,
name y, `ALOOKUP M_in v=SOME o`, `V o=SOME w`, both snapshot origin-read
relations, and target `eval_one_phi = SOME(y,w)`. It does NOT write M or N, and
it does NOT allocate `(new_visit,h,i,0)` for the source output dst.

Assemble the whole mixed target batch successfully from the incoming agreements
before recording any post-batch lookup. RetainedJoint:98-107 requires this
`eval_phis=OK post'`, PHI-prefix wf, non-PHI suffix boundary, prev p, distinct
outputs and incoming realization. It yields target `N_batch=bindings++N_in`,
realization under unchanged V and `ALOOKUP N_batch y=SOME o`. PhiOrigins supplies
the source batch counterpart. Source PHI output uniqueness is essential when
extracting `ALOOKUP M_batch dst=SOME o`. Both batches read their INCOMING
snapshots; serially reading an earlier updated binding would be wrong.

The completed ledger record links source PHI OUTPUT occurrence dst to target
y with origin o of the INCOMING OPERAND. It may share o with older events.
Demanding a fresh source origin per retained PHI is incompatible with these
published signatures. A source write occurrence and its propagated value-origin
must remain separate. For a current-h original PHI writer this completed batch
record, not an old visit or future ordinary output, is the witness. ReinsertedReady
then protects its read through prior copies. For an external PHI writer d, use
the same historical record plus the suffix transport of 10.3.

### 10.5 First external-writer copy and dependency audit

Fix the FIRST entrance at h and its next copy x<-y for owner v, with external
nonself token t. Use the accepted InsertionDemand bridge and the appropriate
rooted equality (ordinary operand-excluded or ExceptionalDemandOrigin).
DemandOrigin/source availability excludes default; FirstArrival excludes the
self token. OriginalOrigin locates the final original slot if t is original.
Chronological inserted inversion locates the last completed g if
`t=CurrentInserted v g`, with g<>h. These are static-to-route conclusions,
not completed-target-write conclusions.

For an external ORIGINAL ordinary writer, 10.3 identifies the record that the
proposed ordinary constructor must have added at the actual earlier occurrence
of d. For an external original PHI, 10.4 identifies the batch record. The record
plus valuation protection, local d-tail exclusion, non-changing suffix transport
to p, and current-h retained/prior-copy local nonclobber would establish
`ALOOKUP M_post_source v=SOME o /\ ALOOKUP N_cursor y=SOME o /\ V o=SOME w`.
Realization then gives lookup_var y target_cursor=SOME w BEFORE executing the
copy. CleanupRuntime can execute it, and sequential origin copy extends N with
(x,o), after which a new completed seed may be recorded. The remaining local
h nonclobber implication must exclude writes to external y by the actual
retained prefix/prior copies; it is not a source no-write consequence.

For external INSERTED t, the IH must supply a completed producer record for
(v,g) at the **last completed occurrence of g** in the rooted scan, either its
retained inserted PHI batch write or its cleanup copy. Its position is strictly
earlier because g lies in the already completed route ending at predecessor p,
not at the newly entered h; g<>h. Earlier-than-current does not by itself prove
that record exists: insertion coverage and successful batch/copy construction
at that occurrence are required IH clauses. This branch remains OPEN until
those constructors and coverage are proved. It must not be justified by
`MEM (t,v,y) H` or by demanding y ready in J. For CURRENT original-PHI writer
use the already completed current retained batch event from 10.4 instead; this
case does not require an earlier visit and does not preserve an old PHI origin.

Dependency graph (arrows mean requires):

```
actual source dispatch + insertion demand
  -> rooted token / chronological effective writer
  -> earlier completed paired record [J constructors/coverage: OPEN]
  -> protected V(o) + local writer-tail exclusion
  -> completed non-changing source/target slice transport
  -> current retained/prior-copy nonclobber [local assembly: OPEN]
  -> lookup y = SOME w
  -> current copy success
  -> NEW ledger record/seed
```

There is no arrow from current copy success back to its earlier record or read.
Using semantic-history transport of a prefix containing that copy would create
exactly that forbidden cycle. Local current retained success must independently
come from incoming selected-operand agreement and the mixed-batch assembler,
not from the outgoing demanded agreement the copies are meant to establish.

### 10.6 Proposed proof obligations and disposition

These are interfaces for strategist consideration, NOT new theorem declarations:

| obligation | allowed inputs | required conclusion / gap |
| --- | --- | --- |
| J entry | actual fn_entry_state, certificate entry preservation | empty actual prefixes, realizations and aligned cuts; no arbitrary entry state |
| J ordinary OK | J at input-demand cut, actual non-INVOKE source OK | constructed target actual edge, V1/M1/N1, completed indexed records, singleton and next demand; ledger generation bound preserved |
| J retained dispatch | incoming J, actual successful source batch, selected agreements | successful mixed target batch and snapshot records; origin propagation unchanged V; actual control update |
| event extraction | J plus chronological last original/inserted site on completed route | earlier paired record with the effective source origin; inserted branch OPEN |
| first external copy | earlier record and certified no-write slices up to CURRENT cursor | derive SOME, then success and a new record, never success as input |
| J outgoing cut | completed copies, source post-PHI actual cut | demanded successor agreement, not yet supplied by local preservation |
| calls/results | future call/run correspondence infrastructure | outside current actual_prefix and OK-only ordinary theorem; OPEN |

The smallest *interface* obstruction for a historical-valuation ledger without
extra discipline is existential n versus old seed-only origins (10.2). The fresh
first-coordinate discipline would address it without modifying existing lemmas,
but its induction is not proved here. Even with that repair, the first-copy test
stops at completed inserted-producer coverage and local prefix nonclobber, not
at another finite-map fold. This bounded diagnostic has therefore specified a
candidate judgment and isolated its exact remaining transfer obligations; it
has NOT established inductiveness, either frozen contract, or a counterexample.
No speculative operational theory or conditional readiness wrapper is installed.
