# LowerDload backward execution: bounded operational closure experiment

Scope: C1.preservation.execution.operational_test. This is a residual-obligation
report, NOT a proof of an operational invariant. No new aggregate definition,
axiom, or unproved theorem was added. The frozen contract is unchanged.

## Candidate synchronized witness (not yet a named predicate)

Source witness: `ld_annotated_reachable vs C astk k L AP AG tn fn inst s`.
Target has the corresponding original instruction boundary, target annotated
stack bstk, ordinary maps H,BP,AH, owner table E, variable domain V, target
state t and taint un. Required clauses are:

* `ld_frame_embedding E L H s t` and `ld_owned_vars V E AG AH tn un s t`;
* paired parameter/provenance selections and `LIST_REL
  (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) astk bstk`;
* current byte relation `ld_byte_rel R tn.t_mem un.t_mem
  (\j. read_memory j 1 s) (\j. read_memory j 1 t)`, with R including
  fixed-region identity and all live owner byte pairs (scratch excluded);
* actual allocation account `ld_alloc_account keys d A s t`, target
  allocation validity, live-local-or-below-frame-floor end bounds;
* source/target nonmemory observations agree outside source taint, target
  taint included in source taint there; execution environment/outcome stream
  agreement; original instruction/block correspondence;
* producer reserve equation described below, not merely target no-wrap.

Strict-prefix witness retains this entire pre-macro witness at s,t0,tn,un0,
plus `ld_target_prefix C' code t0 un0 n t un`, `0 < n /\ n < LENGTH code`.
The macro start's account is not asserted of arbitrary intermediate t.

The environment/control conjunction and R's fixed-region component are NOT
fully specified by the current PLAN or by the existing saved-frame package.
Consequently none of the four cases below can honestly be certified as full
successor closure of one predicate yet. The matrix distinguishes actual
available boundaries from missing producers, rather than making the missing
successor clauses assumptions of a new theorem.

## Reserve ledger: exact proposed arithmetic

Let suspended frame scratch sets be `As : num set list`, head nearest caller.
Define the expression (no new HOL definition):

    d = 32 * SUM (MAP CARD As)
    t.vs_alloca_next = s.vs_alloca_next + d + 32 * CARD A

The latter equality is ld_alloc_account_frontier. At call, the ledger becomes
`A::As`, child active set `{}`, and child displacement `d+32*CARD A`.
At return, pop As, restore the saved caller's A,d, and keep callee memory.
At fresh scratch, replace A by `q INSERT A`; at cached scratch keep A.

Critical producer goal at synchronized boundaries:

    SUM (MAP CARD (A::As)) <= ctx_dload_count C

A *fresh* scratch needs the stronger successor budget:

    q NOTIN A ==>
    SUM (MAP CARD ((q INSERT A)::As)) <= ctx_dload_count C

Given that budget and source headroom, the concrete fresh allocation goal is:

    t.vs_alloca_next + 32 < dimword (:256)

This is strictly stronger than the current-state conclusion of
ld_alloc_account_nowrap. Cached scratch needs `p+32 < dimword (:256)` for
its stored base p; alloca_next_valid only gives `p+32 <= t.vs_alloca_next`,
so the old budget suffices there. The successor budget can follow by charging
q to a configured DLOAD key in the active function, but that charging and the
stack ledger have not been proved invariant.

ld_alloc_stack_budget already bounds CARD sums for a function-indexed A and
caps, assuming `ld_stack_origin vs C stk fn s0`. Its caps premise is:

    EVERY (\g. FINITE (caps g) /\ A g SUBSET caps g /\
      CARD (caps g) <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
      (fn :: MAP (\f. f.cf_fn) stk)

The ledger must therefore produce (i) source stack origins and frame reach
prefixes, (ii) an identification of each saved actual scratch set with the
function-indexed set, and (iii) fresh configured-key membership. The present
LIST_REL saved certificate existentially stores keys,d,A but has NO equation
linking a frame's d to the tail's counts and NO key-to-function bound. These
are missing predecessor invariant clauses, not implications of the package.
No new conditional reserve consumer was proved in this experiment.

## Closure matrix

### 1. Entry (ld_annotated_reachable_entry, ownership source lines 424-434)

Actual source premises: entry name lookup, fn_entry_label, enters_block from
`vs with <|vs_prev_bb:=NONE; vs_current_bb:=lbl; vs_inst_idx:=0|>`,
`s1.vs_allocas=FEMPTY`, and active_inst. Witness substitutions:

    astk=[]; k=0; L=H=FEMPTY; AP=BP=[]; AG=AH=FEMPTY;
    E=FEMPTY; A={}; As=[]; d=0; tn=un=entry_taint.

If target entry state is the same s1 except for transformed PHI/PC structure,
empty selection, account, and initial byte/taint equalities are straightforward.
But the required target-to-source entry step is still unproved:

    enters_block fn' target_entry t1 /\ active_inst fn' j t1 ==>
    ?s1 inst. enters_block fn source_entry s1 /\ active_inst fn inst s1 /\
              [original-position relation between inst,s1 and j,t1]

This cannot be derived from empty maps. It needs exact block expansion/PHI
correspondence, including empty blocks and entry PHIs. The bracketed position
relation is a missing specification, not a valid HOL theorem statement yet.
Consumer: initial case of lowerDloadBackwardExecutionTheory's future witness
induction. Entry closure status: PARTIAL, no complete paired entry theorem.

### 2. Configured DLOAD, fresh and cached

Use actual target ALLOCA step and configured [a;b;c;d] expansion. At n=0,
freeze source s, retain predecessor certificate. Witness for n=1..3 is the
prefix itself; n=4 must create a source successor z and advance annotated
source reachability via its next rule (lines 435-446). Active source ordinary
map L and owner serial k stay unchanged: DLOAD is not source ALLOCA.
Target A becomes `a.inst_id INSERT A`; H is unchanged.

Existing checked producers: ld_alloc_account_scratch handles actual
`exec_alloca a t 32w = OK t1`, both fresh/cached. ld_load_completed_byte_rel
supplies source `step_inst fuel C inst s = OK z` and current memory relation
at completion. This theorem still requires no-wrap and outside-scratch
premises. Exact missing operational goals for its invocation are:

    p + 32 < dimword (:256)
    !j k. R j k ==> k < p \/ p + 32 <= k

No-wrap consumes the ledger successor budget above. Scratch separation needs
local allocation validity plus an inductively retained scratch-vs-live-owner
fact for cached allocations; current ordinary embedding alone does not imply
it. Source access/raw facts and target valid geometry are inputs but have not
been connected to all reachable frame/prefix states.

Completion additionally requires original-variable equality for the DLOAD
result (not supplied by a byte-only theorem), taint-var inclusion, original
PC/active_inst correspondence, and updated nonmemory observation clauses.
Generated av,bv must be excluded from V using actual pass supply freshness.
The completed source step alone does not supply these clauses. DLOADBYTES
also requires destination pointer relocation and payload copying, not the
same scratch-only word argument. Macro closure status: PARTIAL.

### 3. INVOKE entry (annotated call rule, lines 455-468)

Actual semantic premises include decode_invoke, callee lookup, eval_operands,
setup_callee, enters_block and active_inst on each side. Proposed source
witness is exactly the constructor's record cons; target uses corresponding
record with H,AH,BP,un.t_var. Child choices:

    L=H=FEMPTY; AG=AH=FEMPTY; A={}; As'=A_parent::As;
    d'=d_parent+32*CARD A_parent;
    AP'=MAP (ld_op_prov AG_parent) source_ops;
    BP'=MAP (ld_op_prov AH_parent) target_ops;
    tn'=tn with t_var:=FEMPTY; un'=un with t_var:=FEMPTY.

ld_alloc_account_enter proves the child account at actual setup_callee
results (not yet after entry PHIs). ld_setup_callee_floor gives frame floor
bookkeeping. Parent certificate can be saved without storing stale memory.
But source argument definedness, paired callee resolution, entry PHI
correspondence and inherited live-memory coverage must be constructed from
target call premises and the predecessor relation. A raw setup equality is
not a paired call execution theorem. Source callee lookup is structural;
parameter values need operand relation plus taint_ok clean INVOKE operands.
Reserve ledger cons arithmetic is elementary, but its origin/caps invariant
and actual saved-frame displacement chain are still missing. Status: PARTIAL.

### 4. IntRet (annotated ret rule, lines 469-481)

Actual source premises are `step_inst ... = IntRet ret s_end`,
`bind_outputs ... (adopt_return_fmp ret (merge_callee_state ...)) = SOME s'`,
and active_inst at the advanced caller PC. Target has corresponding premises.
Proposed source witness restores f.lf_local, f.lf_params, and restricts
f.lf_prov by COMPL(set f.lf_inst.inst_outputs); caller taint restores only the
saved variable mask excluding outputs; current callee memory persists.
Restore the saved caller A,d; pop the ledger; restrict E to surviving owners.

ld_saved_embedded_return_layout/account/vars cover the MERGE states only,
NOT adopt_return_fmp, bind_outputs or the final advanced state. The result
values must be shown clean/equal under return taint policy before erasing
output provenance; no relation on ret.iret_values is present in a generic
saved certificate. Required actual-return goals include:

    ?ret s_end. step_inst fuel C rinst s = IntRet ret s_end
    ret.iret_values = target_ret.iret_values

(or a sufficient output-wise masked relation, if source return discipline
allows it). These need current callee state/control clauses and actual RET
semantics, not merely saved caller projections. Owner restriction needs the
survivor premise on every selected current/saved annotation. This is
conditional in ld_saved_stack_restrict; the ret rule removes current callee
locals but also restores params/provenance, so surviving support must be
identified explicitly. Use ld_owned_return_memory, not old saved memory.
Reserve restoration is local once the ledger stores its chain; the chain is
not yet in ld_saved_embedded. Status: PARTIAL.

## Result and requested checkpoint decision

No entire case is certified, and no new partial theorem is advertised as
full closure. The experiment exposed two specification holes before a global
opcode sweep: an exact configured control/entry-position relation and a
per-stack reserve ledger tying existential saved accounts to function caps.
The existing account, scratch-memory and owner-support libraries remain true
and useful but do not produce these holes. The next decomposition must name
these invariant clauses and their actual rule-based producers before
certifying a backward-execution induction. This report is the diagnostic
output authorized by the PLAN, not evidence that the required task theorem
is false.
