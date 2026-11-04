# C3.2.40: Error / consumer / finite-edit audit

Diagnostic only. No new semantic theorem is asserted by this document. Existing
ordinary closure is preserved. Verified target: dftOccurrenceOrdinaryClosureTheory
(2026-11-04, holbuild clean). No new probe theory was needed for the definitional
case tables below. Proposed interfaces and counterexample candidates below are
explicitly **unverified**.

## 1. Result consumer

Source: `venom/compiler/o1PassContractScript.sml:119-133,239-244`;
`venom/simulation/defs/passSimulationDefsScript.sml:96-98`.

| source result | terminates | acceptable target result for dead_result_rel |
|---|---|---|
| Error e | false | ctx_sim makes no demand for this fuel |
| OK s | true | none |
| IntRet v s | true | none |
| Halt s | true | Halt t, with the listed accounts/transient/immutables/returndata/logs/requests agreements |
| Abort Revert_abort s | true | Abort Revert_abort t (no state comparison) |
| Abort any other tag s | true | Abort any tag t (no state comparison) |

Thus no blanket identification of terminates with Halt-or-Abort is valid.
`run_context_def` and `run_function_def` merely forward `run_blocks` after
resolving entries (or return Error). `run_blocks` recurses on its OK continuation,
returns Halt when halted, and forwards IntRet and other stopping results:
`venomExecSemanticsScript.sml:1708-1725,1884-1907`.
`dftOpenAdequacyScript.sml:dft_run_blocks_not_ok` already excludes OK;
`codegenCorrectnessScript.sml:run_context_never_ok` is local, not an exported API.
IntRet is genuinely forwarded, not converted to Halt. The task's
`o1_fn_shape_def` gives `entry_fn_no_return` for the entry function; its definition
excludes RET/RETFMP/DRET. An entry no-IntRet lemma must still connect this syntax
to execution, including the fact that INVOKE consumes an internal callee return.
Do not infer this from terminates. Proposed consumer lemma (not proved here):

```
o1_ctx_shape C ==> !fuel s v t. run_context fuel C s <> IntRet v t
```

This needs verification of all IntRet-producing opcodes before implementation.
Source Error is harmless for ctx_sim only; target Error cannot match source
Halt or Abort. No claim of equal fuel is needed.

## 2. Memory consumer and Error cuts

`codegen/proofs/contextRawReachableScript.sml:26-57` generates observations
BEFORE executing the active instruction. Entry does not require that instruction
to succeed; next/block rules require success only of the preceding instruction.
Callee entry requires decoding, lookup, operands and setup, but no eventual return
and no success of the first callee instruction. Therefore the failing instruction
and all earlier reachable instructions remain observable. Nothing follows an
Error through the next rule; a failing INVOKE can nevertheless expose callee
prefixes through the callee rule.

`unitMemInvScript.sml:96-109` says exactly: entry resolves, and every raw reachable
instruction satisfies M. There is no terminates antecedent. `mem_inv_transport`
currently has the same initial state on both sides; gas-variant transport needs a
separate wrapper. The relevant memory fact constrains ranges even of an
instruction that will fail. Empty ranges make its EVERY clause true.

No-Error use in `dftOccurrenceOrdinaryClosureScript.sml`:
- `dft_ordinary_no_error` excludes DftDone(Error e) at EVERY iterate, even inside
  a suspended call. It is substantially stronger than ignoring root Error.
- `sync_pair_segment:879-892` uses it twice: to reject Error of x, then Error
  of y after successful x. This selects OK/Abort cases.
- `sync_segment:924-936` needs it only on the crossed-pair branch. Outside-pair
  synchronization/coverage is independent of it. `endpoint_segment` simply
  dispatches sync vs cleared Abort. Live-shift propagates the all-orbit premise;
  it does not establish it from task hypotheses.

| source cut | target-observation issue | available facts / gap |
|---|---|---|
| x Error before y | target visits y first; source never visits y | readiness eliminates undefined-operand Error, not all runtime Error; need empty ranges of y or another justified coverage argument |
| x OK then y Error | source visits x and failing y | target y is covered at source y using operand/range/memory frame; if target y also Errors, it never visits target x; Error equivalence is needed |
| callee Error | prefixes inside the callee still matter | outside-pair synchronized calls cover common prefixes; open-call simulation cannot simply discard Error stack or future target observations |
| x Abort before y | target visits y before it stops | existing ordinary Stop facts make speculative y ranges empty under the precise pair premises, and yield cleared Abort; NOT a general arbitrary-error fact |
| source Abort, target subsequently Error | result matching fails if source Abort terminates | existing directional stopping facts must show target Abort, not merely non-OK; abort compatibility and original orientation matter |

### Adversarial Error case: unresolved, not a task counterexample

`dftGuardsScript.sml:78-86,121-127` isolates runtime Error opcodes
DELEGATECALL/CREATE/CREATE2; all read all effects. Under inst_wf and readiness,
NoFail instructions outside that family are total. `dftStoppingSwapScript.sml:
140-161,164-183` explains why ASSERT/ASSERT_UNREACHABLE/INVALID cannot move right
(the original no-output empty-effect guard in dft_must_order), and why
RETURNDATACOPY bounds failures Abort rather than Error.

Independence with an all-read instruction forces its partner's WRITES empty,
not its READS empty (`dft_all_read_independent_empty_write`). Consequently it
is unsound to deduce that partner's memory ranges are empty from that fact.
`dft_ordinary_no_memory_ranges` requires BOTH no memory reads and no memory writes.

A concrete opcode-level candidate is x=CREATE (or CREATE2), y=MLOAD with
disjoint outputs and literal operands. `venomEffectsScript.sml:60,65-66,117-118`
gives CREATE all reads but no memory writes, so MLOAD's memory read need not
conflict. `exec_create_def:528-545` can return Error when extract_venom_result
returns NONE, even with correct output arity. Source then never visits MLOAD;
target could visit it first with a range in the lowered forbidden gap.
This is NOT checked existence of such a CREATE state, NOT checked DFT schedule
order, and NOT a counterexample to dft_ctx_sim_gas. The EVM run/extract behavior,
o1_run_state_ok, source lowered invariant, all static premises and actual dft_fn
schedule must all be verified. No claim that initial-state constraints permit
this Error has been made. Because this could obstruct the frozen invariant
implication, request a bounded checked falsification gate before implementing an
unconditional Error-inclusive observation theorem.

## 3. Complete adjacent edit inventory

Work on the non-pseudo body, keeping the fixed pseudo prefix outside the edit.
`dftScheduleEditsScript.sml:inv_edit_factor` supplies an original-direction finite
chain from distinct orig to PERM dest. `inv_edit_provenance` needs DISTINCT DEST
and final preservation of a relation R, and concludes original a-before-b,
final b-before-a, and ~R a b. For task schedules use protected relations covering
`dft_must_order` AND the abort-incompatibility edges from
`dft_fallible_order_kept_def`; dft_block_rel alone supplies only the first.
Transfer between instruction IDs and instructions must retain distinct IDs and
from_block. Pseudos, ALLOCA and terminators are not extra semantic swap cases:
pseudos stay in the prefix, ALLOCA is excluded by dft_fn_rel, and terminators
are protected (original wf terminator is last). Impossible-class claims still
need the standard syntax/distinctness premises.

Let O mean non-pseudo, nonterminator, non-ALLOCA, non-GAS, non-INVOKE.
All ordered opcode classes are:

| original x,y | status / needed extension |
|---|---|
| O,O | actual ordinary orbit closure proved, but only source wf_ssa and all-orbit no-Error; not yet composable |
| GAS,GAS | accepted fixed-occurrence GAS edit infrastructure |
| GAS,INVOKE | accepted mixed open-call infrastructure; no future return required |
| INVOKE,GAS | accepted mixed infrastructure must be instantiated in reverse orientation with same occurrence identity; not a new same-state commutation assumption |
| GAS,O | missing whole-orbit interface; GAS assignment/occurrence consumed, ordinary may stop, speculative GAS has no memory range |
| O,GAS | missing whole-orbit interface; ordinary Error/Abort before GAS cannot require reading a future source occurrence; result-only matching vs empty GAS observation |
| INVOKE,O | missing whole-orbit interface; full effects force O no effects; original must-order additionally rules out no-output empty-effect x only when x is O, not when x is INVOKE; call Error/divergence and O speculation need explicit treatment |
| O,INVOKE | missing whole-orbit interface; effect-free O must not alter call operands; no-output O barrier forbids its moving right; open callee observations must be covered without assuming return |
| INVOKE,INVOKE | impossible by effect conflict, since both read/write all effects |

The mixed accepted machinery is not a proof that all rows compose. In particular
no generic ordinary theorem covers GAS/O or INVOKE/O merely because they are
nonterminators. Preserve the accepted local APIs rather than weakening them.

## 4. Original SSA / protected-current environment (proposal, unimplemented)

Static data must name original C0 and original blocks, current C and schedules:
- original wf_ssa/wf_function/inst_wf/pseudo-prefix/no-ALLOCA from dft_fn_rel;
- current functions preserve names, block labels, entry blocks and instruction
  identity, with unchanged pseudo prefix and a PERM of each original body;
- schedule_edges original R current, where R includes must_order and required
  incompatible-abort edges; distinctness and CFG syntax are transported, NOT
  wf_ssa of current instruction order;
- label-map domain bounds from ctx_labels_bound and preserved operands.

Dynamic cut data must refer to the ORIGINAL fn and block: strict_dom_vars_defined,
current bb label, and defined outputs for pseudo prefix ++ done. Together with
PERM/schedule_edges this is exactly the input to
`dftProtectedPrefixScript.sml:dft_protected_cut_operand_defined:79-88`:

```
wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
EVERY inst_wf bb.bb_instructions /\
pp = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
PERM (done ++ y::todo)
  (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) /\
schedule_edges bb.bb_instructions dft_must_order (pp ++ done ++ y::todo) /\
bb.bb_label = t.vs_current_bb /\ strict_dom_vars_defined fn t /\
(!d v. MEM d (pp ++ done) /\ MEM v d.inst_outputs ==> v IN FDOM t.vs_vars)
==> !v. MEM (Var v) y.inst_operands ==> v IN FDOM t.vs_vars
```

Missing preservation obligations are: establish this dynamic cut at original
entry; preserve it at successful current-schedule steps; establish successor
block entry using unchanged original CFG dominance and evaluated phis; establish
callee entry and restore suspended caller cut on return; carry occurrence
addresses across all edits. Operand-defined is only one conclusion and supplies
neither ext-EVM termination nor a universal no-Error theorem.

Exact existing static preservation interface is
`inv_edit_rtc_schedule_edges`:
```
ALL_DISTINCT dest /\ schedule_edges orig R dest /\
schedule_edges orig R u /\ RTC (inv_edit orig dest) u v
==> schedule_edges orig R v
```
It carries no dynamic safety or SSA theorem.

If the Error obstruction is eliminated, the intended missing observation consumer
has the SAME conclusion as `dft_ordinary_orbit_observe:1036-1046`, replacing its
source-wf_ssa/all-orbit-no-Error assumptions with the original/current environment
and established cut invariant (not with observations as hypotheses). A separate
terminal consumer should assume a source ROOT Halt/Abort endpoint, and return a
target root endpoint with dead_result_rel-compatible result; it must not require
all intermediate schedules to be universally Error-free. These are design
requirements, not authorized/proved definitions.

## Recommended next boundary

Do NOT begin unrestricted closure. First authorize a small checked probe of the
CREATE/MLOAD Error-cut candidate: exhibit (or rule out under run_state_ok) the
NONE branch of extract_venom_result for a well-formed CREATE with literal inputs.
Then test actual dft_fn ordering and lowered-memory antecedent in a complete
one-function context before claiming task falsehood. If it is impossible, expose
the exact safety theorem ruling it out. If only the optional universal coverage
helper is false, retain task obligations and ask for a different invariant-transport
boundary; helper failure alone is not task falsehood.

## C3.2.41.1 bounded runtime investigation (partial, not a verdict)

New `dftCreateErrorProbeScript.sml` is kernel-checked and build-clean:
- `create_probe_state_ok`: default Venom state, labels code_end=0, call gas=1000
  satisfies o1_run_state_ok. No account/call-context validity assumptions are
  added by that predicate; its clauses constrain vars/halt/memory/allocas/fmp
  and code layout, not EVM wf_state.
- `create_probe_empty_extract`: running make_venom_create_state at address 1,
  gas 100, value 0, empty init code produces a non-NONE extraction. Checked by
  finite OWHILE unfolding and EVAL_TAC. It is a negative test, not safety.
- `create_probe_extract_none_iff`: extraction NONE iff run-result NONE or
  SOME(result,fs) with LENGTH fs.contexts <> 1. Result exception tag alone
  is not an extraction failure, including vfm_abort at a singleton frame.
- `create_probe_nonabort_extract`: wraps the actual run_contexts_length_1:
  run es=SOME(r,fs), wf_state es and non-vfm_abort result imply non-NONE
  extraction. These three premises remain obligations for arbitrary CREATE.

Checked signature obtained after importing vfmContextLength:
```
run s = SOME (r,es') /\ wf_state s /\
(!e. r = INR e ==> ~vfm_abort e) ==> LENGTH es'.contexts = 1
```
Loaded vfmExecution definitions distinguish fatal vfm_abort tags OutsideDomain,
Unimplemented, Impossible from normal OutOfGas/InvalidOpcode/etc. handle_step
reraises fatal tags; other tags go through handle_create/handle_exception.
Thus an INVALID bytecode is not by itself evidence of extraction NONE.
An attempted direct EVAL of one-byte INVALID (0xfe) hit the per-tactic timeout
at the first EVM step; the experiment was removed, not admitted or retained
as an unfinished theorem. Empty code's finite run was actually checked.
Inspection of precompile_bls_pairing_def found malformed-input failure maps to
OutOfGas, not Unimplemented; this does not classify every precompile/opcode.
No nested fatal-abort witness has been checked.

Residual runtime investigation, requiring strategy review before extension:
1. Establish wf_state (make_venom_create_state ...) from precisely the allowed
   initial constraints, or isolate a concrete permitted failure of wf_state.
2. Establish existence of a SOME run (termination is NOT implied merely by
   the spelling of finite gas); no usable universal termination theorem was
   found in the loaded-name search for 'terminat'.
3. Exclude fatal abort in nested contexts, or exhibit a concrete nested fatal
   abort with final context count >1. A fatal abort with one context is not
   enough, and an ordinary exceptional halt is not fatal vfm_abort.
The preferred positive witness or universal safety claim is NOT established.
The CREATE/MLOAD candidate remains unverified; no task counterexample follows.
The environment provides dependency theories to holbuild but not their source
paths in this worktree; DB queries through a temporary Theorem/FAIL_TAC probe
were used for exact signatures, and all inspection dummy theorems were removed.

## C3.2.41.2 constructor and fatal-handler boundary

Two further checked interfaces (no execution enumeration):
```
wf_state (make_venom_create_state s a gas value code) <=>
  wf_accounts (transfer_value s.vs_call_ctx.cc_address a value s.vs_accounts)
vfm_abort e ==> handle_step e es = (INR e,es)
```
The first is `create_probe_constructor_wf_iff`; the second is
`create_probe_fatal_keeps_state`. All parameters remain symbolic.

Actual imported `vfmExecutionProp.wf_state_def` is the conjunction of:
- contexts nonempty;
- LENGTH contexts <= SUC context_limit;
- EVERY (wf_context o FST) contexts;
- EVERY wf_accounts (all_accounts es);
- stack_room_ok es;
- gas_stack_ok es;
- outputTo_consistent_stack es.

Constructor residual-obligation table:
| Clause | Constructor status |
| --- | --- |
| nonempty / context limit | singleton contexts, automatic |
| wf_context | initial_context, automatic by existing simp interface |
| account validity | exactly wf_accounts of the transferred accounts; not automatic |
| stack_room_ok / gas_stack_ok | singleton initial context, automatic after their definitions |
| outputTo_consistent_stack | automatic: initial message outputTo=Code a and callee=a |

The direct constituent `wf_accounts a <=> !x. wf_account_state (a x)`
requires every account to satisfy
`nonce < 2 ** 64 /\ LENGTH code <= 2 ** 14 + 2 ** 13`.
Neither `o1_run_state_ok` nor its initial-state constituent supplies these:
`o1_initial_state_ok` constrains only empty vars, not halted, empty memory,
empty allocas, and alloca_next=0; run_state_ok additionally equates fmp and
initial_fmp and requires code_layout_valid. In particular no account nonce
or code-length premise is present. This is a missing safety route premise,
NOT a demonstrated failure of extraction.

Exact fatal handling clauses from `vfmExecution`:
```
handle_step e = if vfm_abort e then reraise e
                else handle (handle_create e) handle_exception
reraise e s = (INR e,s)
```
Fatal tags are SOME(OutsideDomain d), SOME Unimplemented, SOME Impossible;
all other exception constructors and NONE are nonfatal. Thus a fatal
handler preserves the *entire* current context stack; it does not unwind
nested frames. A concrete reachable fatal event with more than one frame
would survive that handler with multiple frames. No such reachability, nor
OWHILE NONE, has been proved. The earlier conditional extraction theorem
still additionally needs a SOME run and nonfatal result.

Recommendation for the next semantic boundary: classify the reachability
of OutsideDomain under the constructor's `Collect empty_domain` (and the
permitted arbitrary account code), specifically whether nested frame entry
can precede a fatal domain check. This is one concrete fatal source, not a
proposal to enumerate arbitrary bytecode or prove universal termination.
The missing wf_accounts premise alone does not license abandoning the
frozen theorem. Parent suspicion gate remains unresolved.

Evidence: constructor residual goals in m4439/m4443/m4447; direct constituent
signatures m4451/m4455; exact reraise and initial-state clauses m4458.
Temporary inspection theorems were removed; only the two checked lemmas
above are retained.

## C3.2.41.3 OutsideDomain under Collect

Imported `vfmDomainCollection` builds successfully. Its exact interfaces:
```
computes_minimal_domain step
computes_minimal_domain (step_call x)       (* x : opname *)
computes_minimal_domain (step_create x)     (* x : bool *)
(?d. s.msdomain = Collect d) /\ step s = (r,s') ==>
  ?d. s'.msdomain = Collect d
run s = OWHILE (ISL o FST) (step o SND) (INL (),s)
```
The first four are respectively step_computes_minimal_domain,
step_call_computes_minimal_domain, step_create_computes_minimal_domain,
and step_preserves_collect. None has a wf_state or wf_accounts premise.
These call/create interfaces include their frame-entry effects; one need
not assume that entering a nested frame resets the state's domain mode.
The step preservation theorem applies regardless of context-stack length.

Checked new boundary lemmas:
- `create_probe_collect_domain_check`: domain_check on Collect d runs cont
  after updating msdomain to Collect (upd_dom d), ignoring Enforce checks.
  The parameter was renamed from `add` (a parsed library constant).
- `create_probe_minimal_no_outside`: computes_minimal_domain m, m s=(r,t),
  and s.msdomain=Collect d exclude every INR(SOME(OutsideDomain x)).
- `create_probe_collect_step_no_outside`: specializes that interface to step.

Actual computes_minimal_domain definition quantifies s,r,t,d and, when
m s=(r,t) and s.msdomain=Collect d, conjoins: no OutsideDomain result;
replay on any collecting input domain with an extended output domain;
replay on sufficiently large enforcing domains; and an OutsideDomain
result on insufficient enforcing domains. Only the first conjunct is
needed for the retained no-OutsideDomain boundary.

Consequently every finite iteration from make_venom_create_state stays
Collect and excludes OutsideDomain at each step, including nested calls
and creates. The run loop's body is exactly step on the preceding state.
A global theorem lifting this induction through OWHILE was deliberately
not developed in this bounded probe; the available one-step interfaces
have no account-well-formedness gap for that lift. This rules out using a
*finite collecting step* as the previously suggested OutsideDomain witness.
It does not prove OWHILE termination or extraction success. Unimplemented,
Impossible, and OWHILE NONE remain separate unresolved possibilities.
No task falsehood follows; no unrelated simulation is authorized.

Recommended next boundary for strategist decision: inspect existing
interfaces excluding Unimplemented and Impossible in collecting executions,
rather than revisiting OutsideDomain or arbitrary bytecode enumeration.
Evidence: imported exact step/run signatures m4481; definition m4483;
checked boundary build recorded with this episode. All temporary inspection
theorems removed.

## C3.2.41.4 Remaining fatal routes and totality audit

**Correction to the earlier termination residual:** loaded
`vfmDecreasesGas.run_eq_tr` is unconditional:
```
run s = case run_tr (step s) of (x,y) => SOME (INR x,y)
run_tr (r,s) = case r of INL _ => run_tr (step s) | INR x => (x,s)
```
The second function is defined by well-founded recursion, not OWHILE.
`decreases_gas_cred_step` states `decreases_gas_cred T 0 0 step` without
premises. Thus no CREATE-constructor invariant is needed for run totality.
The new checked `create_probe_run_not_none` excludes NONE for **every** es;
`create_probe_extract_run_none_iff` reduces extraction failure exactly to a
SOME result with final context length different from one. This is a theorem
application, not an inference merely from finite gas. Earlier loaded-name
search for "terminat" missed the relevant interface.

Production-site inspection of loaded vfm definitions (excluding generated
CV conversions and datatype eliminators) found:
- No Unimplemented-producing runtime clause in this inspection. The tag
  occurs in vfm_abort and the exception datatype. This is **not** yet a
  compositional theorem excluding Unimplemented from step/run.
- `get_current_context`, `get_original`, `set_current_context`,
  `set_original`, and `pop_context` fail Impossible if contexts=[].
- `unuse_gas n` asserts n <= current_context.gasUsed with Impossible.
- `dispatch_precompiles a` falls back to fail Impossible outside its listed
  addresses (1..17 and 256).
- `vfmDecreasesGas.pop_helper` asserts 1 < number of contexts with
  Impossible. It is an auxiliary proof interface, not evidence it is an
  independently reachable runtime branch.
- `step_inst_def` covers all opcode constructors, including Invalid as
  fail InvalidOpcode; it has no direct Unimplemented fallback.

Exact applicable or conditional imported interfaces:
```
vfmExecutionProp.step_preserves_nonempty_contexts:
  s.contexts <> [] ==> (SND (step s)).contexts <> []
vfmExecutionProp.run_preserves_nonempty_contexts:
  run s = SOME rs /\ s.contexts <> [] ==> (SND rs).contexts <> []
vfmRunWithinFrame.dispatch_precompiles_inr_not_reverted_not_abort:
  s.contexts <> [] /\ fIN a precompile_addresses /\
  dispatch_precompiles a s = (INR e,s') ==>
  ~vfm_abort e /\ e <> SOME Reverted
vfmHandleStep.gas_stack_ok_parent_has_child_unused:
  gas_stack_ok s /\ LENGTH s.contexts >= 2 ==>
  (FST (EL 1 s.contexts)).gasUsed >=
  (FST (HD s.contexts)).msgParams.gasLimit -
  (FST (HD s.contexts)).gasUsed
vfmRunCall.step_preserves_gas_stack_ok:
  wf_state s ==> gas_stack_ok (SND (step s))
vfmRunCall.run_preserves_wf_state:
  wf_state s /\ run s = SOME (r,s') ==> wf_state s'
vfmContextLength.run_contexts_length_1:
  run s = SOME (r,t) /\ wf_state s /\
  (!e. r = INR e ==> ~vfm_abort e) ==> LENGTH t.contexts = 1
```
Here gas_stack_ok bounds each parent's gasUsed below by unused gas in
its child prefix; wf_context bounds stack length/gasUsed and equates parsed
code to parse_code. The constructor discharges initial context, gas-stack,
output and stack-room constraints, but full wf_state still requires exactly
wf_accounts of the transferred accounts (create_probe_constructor_wf_iff).
The task's o1_run_state_ok does not supply that premise. Consequently the
wf_state-based preservation route cannot simply be instantiated. The
precompile theorem itself has no account-validity premise; a global proof
would still need to show dispatch only occurs at those addresses and that
all intermediate helper contexts are nonempty. Nonempty preservation at the
step boundary alone does not establish every internal pop/unuse assertion.

Residual table:
| route | classification | exact remaining obligation |
|---|---|---|
| OWHILE/run NONE | proved excluded unconditionally | none; run_eq_tr and new checked theorem |
| finite Collect OutsideDomain | already proved excluded | global final-result lift remains separate |
| precompile Impossible fallback | excluded conditionally by existing theorem | nonempty dispatch input and address membership at call site |
| empty-context Impossible | boundary nonemptiness preserved without wf_accounts | internal helper sequencing/pop guards, not just step endpoints |
| unuse_gas Impossible | conditional gas-stack interface exists | establish adequate gas-stack safety under permitted accounts without assuming full wf_state |
| Unimplemented | no producer found in loaded-definition inspection | compositional step/run exclusion not yet proved |
| nonsingleton final contexts | unresolved, only possible extraction-failure route | singleton result under actual task premises (or concrete nested fatal execution) |

No realizable fatal counterexample or frozen-task falsehood was obtained.
Recommended strategist decision: replace the obsolete run-NONE suspicion
with the single concrete residual of final context-stack safety, and decide
whether weaker account-independent gas-stack/handler safety suffices before
requesting a universal no-Error theorem. Do not release C3.3 on this audit.
Evidence: exact totality signatures m4525; production clauses m4521;
nonempty/precompile/gas-stack interfaces m4529. Temporary DB-print diagnostics
were removed; only two small theorem applications are retained.
