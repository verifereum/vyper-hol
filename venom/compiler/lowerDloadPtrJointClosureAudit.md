# Joint closure constructor experiment (C1.12.64)

This is a source-backed **candidate**, not a checked invariant or a proof of the
contract. No SML definition or theorem statement is changed by this note.
Baseline check: `holbuild` on lowerDloadPtrHashTheory and
o1ContractLowerDloadPtrTheory passed (TO_ld_ptr_v2-20261104T185312Z_m5138_t001).
That does not certify the frozen theorem: its remaining obligation is unchanged.

## 1. Explicit candidate Q

The following are metanotation for inline HOL formulas, not proposed constants.
Fix the TASK antecedent A and its source static witness P. All free parameters
below are fixed by A. Set:

```
U f = set (fn_ir_vars f)
V f = U f DIFF {v | retpc_var f v}
O f = {id | ?ci. MEM ci (fn_insts f) /\ ci.inst_id = id}
Defs U s t = !v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)
```

`Q ds PH H un g j t` is the following disjunction, with all the displayed
metanotation recursively expanded. Every witness in a disjunct is existential.

Normal disjunct:

```
?cs PG G tn f i s q emitted n fuel t0 H0 un0 fs.
 frame_reachable vs C cs PG G tn f i s /\
 dload_boundary_core lo fs (V f) (MAP (\c. V c.cf_fn) cs)
   PG PH G H0 tn un0 s t0 cs ds /\
 dload_control_match q f g s t0 i emitted 0 /\
 dload_prefix_match fuel C' PH emitted n t0 H0 un0 t H un /\
 dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
 Defs (U f) s t0 /\ Support cs PG G f /\
 Stack fs cs ds /\ Cover q f g /\
 (!k. k < LENGTH cs ==> Saved fs cs ds k)
```

Here the exact ancillary formulas are:

```
Cover q f g = ir_supply_covers_fn q f /\
              (?q'. lower_dload_function_supply q f = (g,q'))
Support cs PG G f =
 FDOM G SUBSET fn_pv P f /\
 (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
 (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
 (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
    EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name)
Stack fs cs ds =
 LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
 (!k. k < LENGTH fs ==>
   (EL k fs).dr_scratch =
     FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
     O (EL k (f::MAP (\c. c.cf_fn) cs)))
Saved fs cs ds k =
 let c = EL k cs; d = EL k ds in
 dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
   (DROP (SUC k) fs) /\
 dload_equal_environment c.cf_state d.cf_state /\
 c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
 c.cf_inst = d.cf_inst /\
 Defs (U c.cf_fn) c.cf_state d.cf_state /\
 (?qc. Cover qc c.cf_fn d.cf_fn /\
   dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
     c.cf_inst [c.cf_inst] 0)
```

`Stack` and `Saved` are lexically inside the normal existential, so their
references to f,s,t0 have the bindings above. Static target label distinctness
is intended to be *derived* from Cover plus source shape, not assumed externally.
Support and scratch identity are candidate invariant fields; they have not been
certified jointly. In particular Stack uses the anchor t0, not a partial scratch
allocation state. Ws contains precisely the corresponding original-variable sets.

Terminal disjunct (no memory match, shared-store or equal-environment claim):

```
?cs PG G tn f i s q emitted fs bb a z tb aa zz.
 frame_reachable vs C cs PG G tn f i s /\
 Cover q f g /\ dload_control_match q f g s t i emitted 0 /\
 emitted = [i] /\ j = i /\
 lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
 lookup_block t.vs_current_bb g.fn_blocks = SOME tb /\
 revert_forward_pair bb a z /\ revert_forward_pair tb aa zz /\
 a < s.vs_inst_idx /\ s.vs_inst_idx <= z /\
 aa < t.vs_inst_idx /\ t.vs_inst_idx <= zz /\
 Defs (U f) s t /\
 (!v. v IN U f ==> op_taint tn (Var v) = op_taint un (Var v)) /\
 Support cs PG G f /\
 dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
 dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
                         (t::MAP (\d. d.cf_state) ds)
```

The copy at aa is handled in normal mode; terminal mode begins *after* it.
The terminal alternative intentionally does not include access_ok or taint_ok as
fields: those are conclusions to derive. It also intentionally omits saved
control information: terminal mode must have no call, block, or return successor.
This candidate is NOT asserted to close. Source-success reflection of the exempt
copy is an explicit unresolved entry obligation (see below). In particular it is
not enough simply to replay target ASSIGNs and assert source reachability.

## 2. Literal constructor substitutions

Rules are ptrDisciplineScript.sml:456-508. Substitute the following exact
arguments into Q; no completed-call induction is being used.

* Entry conclusion: `Q [] [] FEMPTY entry_taint fn inst s1`.
  dload_actual_joint_entry produces source reachability, covering supply,
  control at phase zero, empty tables and equality of all variable lookups.
  Narrow its V by restriction to V f; Saved is vacuous, Stack is empty-table
  arithmetic, Support follows from empty provenance. Need a checked restriction
  interface for boundary_core if existing restriction lemmas do not apply.
* Next conclusion: `Q stk PG (step_prov PG G inst s')
  (step_taint inst s s' tn) fn inst'
  (s' with vs_inst_idx := SUC s.vs_inst_idx)` (these are rule-bound target G,s).
  In normal mode instantiate the anchor witnesses above. If n+1 < LENGTH emitted,
  dload_prefix_extend gives replay, but control and target safety at that phase
  still need their actual emission interfaces. If n+1 = LENGTH emitted, source
  must advance once and all ancillary fields must be rebuilt, not copied.
  The four-step DLOAD and two-step DLOADBYTES finish consumers exist in
  BackwardNext:60-150; singleton control/reachability consumers exist in
  JointNext. They do not prove all strengthened fields. If the current singleton
  is the forwarding copy, switch to terminal mode only after proving source
  success and definedness/taint preservation plus table/frontier preservation.
  Terminal next at index k<zz must be ASSIGN. Advance its source counterpart,
  preserve definedness and operand taint, increase both indices, retain the
  interval witnesses. At k=zz the opcode is REVERT and the next-rule
  nonterminator premise is false.
* Block conclusion: `Q stk PG (entry_prov fn s' G)
  (entry_taint_vars fn s' tn) fn inst' s1`.
  Normal mode must first force phase zero and an unchanged singleton terminator;
  reflect target branch result, advance source via frame_reachable_block,
  match new blocks and parallel PHIs, then establish Defs on ALL original vars,
  Support and all saved fields. Existing PHI/local branch transports are inputs,
  not the proof of this whole implication. Terminal interior ASSIGN contradicts
  is_terminator; terminal endpoint REVERT must contradict `step_inst ... = OK s'`
  (not merely ~s'.vs_halted). This separately discharges block, unlike the
  exec_block no-normal lemma.
* Call conclusion:
  `Q (<|cf_fn:=caller;cf_inst:=inv;cf_state:=s;cf_params:=PG;
        cf_prov:=G;cf_tvar:=tn.t_var|>::stk)
     (MAP (op_prov G) ops) FEMPTY (tn with t_var:=FEMPTY) callee inst s1`.
  Normal mode needs phase zero, inv unchanged, matched decoded name, stage lookup
  and callee entry shape. dload_actual_invoke_call (Invoke:204-252) supplies
  source call reachability, new boundary and definedness. Its hardwired callee
  set must be restricted; caller set is saved as V::Ws. NEW Saved head needs
  exact caller singleton control, current lookup definedness, supply coverage,
  saved environment/address and suffix layout. Old Saved fields shift by one.
  Stack must be pushed with empty current scratch. Support for params comes
  from source ptr_use/parameter discipline, not just FEMPTY current provenance.
  Terminal interval opcodes ASSIGN/REVERT contradict inv.opcode=INVOKE.
* Ret conclusion:
  `Q stk f.cf_params
     (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
     (tn with t_var:=DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
     f.cf_fn inst' (s' with vs_inst_idx:=SUC f.cf_state.vs_inst_idx)`.
  Normal mode must force unchanged RET and phase zero, use saved caller at k=0,
  then dload_actual_return (Return:295-358). Its extra environment, address,
  layouts, control and saved Defs premises are the explicit Saved fields above;
  none follows merely from boundary_core. It returns source reachability,
  pop boundary, resumed control, Defs and suffix layouts. Still reconstruct
  Cover, Support and Stack after pop. Terminal ASSIGN cannot yield IntRet;
  terminal REVERT yields Abort Revert_abort rather than IntRet (or an Error on malformed/undefined operands). Need step_inst result
  inversion for both, not the successful-exec_block exclusion.

## 3. Concrete consumer-interface failure

BackwardNext:61,84 hardwires `{v | ~retpc_var f v}` yet :68 requires generated
av and cv outside it; :78 also requires both outside `set (fn_ir_vars f)`.
DLOADBYTES :111-114,:124 has the analogous cv requirement. Freshness produces
exclusion from ORIGINAL variables, not membership of the opaque retpc closure.
Therefore the existing consumers cannot be applied to the proposed V f by
mere instantiation. Their statements may be valid conditional theorems but
covering supply is not a producer of their hardwired freshness premises.
This is a repair request, NOT a counterexample to the TASK. Do not change these
statements without strategist authorization (and task permission).

Invoke's output likewise hardwires all non-retpc callee variables. Restriction
is enough for that output if a boundary restriction interface is available;
restriction cannot fix the expansion consumers' input/NOTIN mismatch.

## 4. Premise-origin ledger and exact residual contracts

In the following `N` and `T` mean exactly the expanded normal/terminal formulas
above, and R means the actual corresponding rule antecedent, without its
recursive reachability conjunct. These are residual proof contracts, not new
exported theorems or a proposed blanket conditional closure axiom.

1. Expansion finish: `A /\ N ds PH H un g j t /\ R_next /\
   (source opcode = DLOAD \/ source opcode = DLOADBYTES) /\
   n+1 = LENGTH emitted ==> N ds PH Hnext unnext g jnext tnext`.
   Existing generic boundary finish transports are inputs. Missing: restricted-V
   actual wrapper, source success premises from actual source contract, and
   preservation of Support/Stack/Saved/Cover/Defs together. Fresh vars/IDs and
   operand exclusions must be derived from the *covering* supply at the anchor.
2. Forwarding entry: `A /\ N ds PH H un g j t /\ R_next /\
   j.inst_opcode = RETURNDATACOPY /\
   (?tb aa zz. lookup_block t.vs_current_bb g.fn_blocks = SOME tb /\
      revert_forward_pair tb aa zz /\ t.vs_inst_idx = aa)
   ==> T ds PH Hnext unnext g jnext tnext`.
   Pair transformation is checked in Forward:384-486. Its converse at an actual
   target pair and boundary anchor still needs an origin argument. Source copy
   successful execution is NOT supplied by forwarding_step_var_taint, which is
   only conditional ghost transport. Also handle a copy exempt by
   about_to_revert alone: produce a terminal pair (if derivable), or a separate
   immediate REVERT alternative. Do not identify that exception with endpoint
   in_revert_forward by assertion.
3. Terminal successor: `A /\ T ds PH H un g j t /\ R_next
   ==> T ds PH Hnext unnext g jnext tnext`.
   forwarding_step_var_taint proves equality only given operand definedness.
   It does not prove reflected ASSIGN success, Defs preservation, provenance
   table relation, endpoint correspondence or source reachability. These remain
   semantic obligations. Terminal access_ok is vacuous for ASSIGN and exempt
   at REVERT; taint_ok needs operand taint agreement and source taint_ok. REVERT
   exempts memory reads but NOT operand taint. This is why variable ghosts remain.
4. Safety extraction: `A /\ Q ds PH H un g j t ==>
   access_ok lo H g j t /\ taint_ok g un j t /\ allocas_from lo t /\
   (ctx_has_dalloca C' ==> allocas_below_fmp t)`.
   Normal source safety comes from source reachability and ptr_discipline,
   fn_ptr_ok from source static witness. Tracking comes from Support and static
   use checks; Defs must include opaque variables as above. Generic operand and
   memory transports plus accepted opcode facts are inputs, not a complete
   dispatcher. Terminal safety is described in item 3. allocas_from uses layout
   and tables. CORRECTION (C1.12.65): although o1_fn_shape:340-351 does not
   exclude DALLOCA, the full o1_src_inv_def:540 DOES. Existing
   lower_dload_stage_no_dalloca transports this absence to C'. The checked
   consumer lower_dload_src_inv_below_fmp (lowerDloadPtrStaticScript.sml)
   discharges the target conditional vacuously for every t. No below-initial-FMP
   bound on relocated sites is needed. The earlier resource concern overlooked
   the full invariant, and is resolved; it is not a counterexample path.
5. Resource origins: target and source reachability plus source callee_first
   yield live indices/support through dload_joint_runtime_scratch_budget.
   That theorem STILL requires exact scratch identity, length alignment and
   per-frame supply correspondence. Stack+Saved+Cover supply those at a boundary.
   Source headroom comes via frame-to-raw mem_inv bridge; target frontier
   inequality additionally needs the scratch-budget layout bound. No external
   target headroom hypothesis is licensed. All these origins must be applied
   anew after push/pop and at proper-prefix anchors. These dimword scratch
   headroom obligations are independent of the now-resolved DALLOCA conditional;
   absence of DALLOCA does not itself supply scratch frontier headroom.

Remaining singleton semantic families (including storage/calls/creation and
memory/environment observations) must be dispatched against their current
signatures or reported missing; checked scalar, memory, call, return and SHA3
local results do not constitute this dispatch. This diagnostic deliberately
adds no further opcode proof. The proposed formula exposes, rather than solves,
these closure obligations.

## 5. Outcome

Current candidate fails the consumer-composition test before global induction:
restricted original V is not accepted by the actual expansion wrappers.
Forwarding entry/success reflection and interval successor closure also remain
unproved. The safety extraction DALLOCA conditional is now checked from the full
source invariant by lower_dload_src_inv_below_fmp; lowerDloadPtrStaticTheory
built successfully (TO_ld_ptr_v2-20261104T185312Z_m5175_t001). This resolves only
that conditional. Request strategist review of coherent interface repair and
terminal closure, not another isolated opcode leaf. No new checked probe was needed: the mismatch
is directly visible in current theorem premises. No claim of falsehood of the
frozen statement is made.

## 6. Tracked-set interface repair (C1.12.66)

`dload_tracked_backward_next` and `dloadbytes_tracked_next`, in
lowerDloadPtrBackwardNextScript.sml, now give the general implementations with
independent V (relational values) and U (definedness). Historical actual-next
statements are unchanged and their proofs are short specializations. The
hardwired-set failure described in section 3 is historical evidence motivating
this repair, not a remaining obstacle to these two new interfaces.

Both original-variable use sites were checked by temporary local probe theorems:
V = set(fn_ir_vars f) DIFF {v | retpc_var f v}, U = set(fn_ir_vars f).
Each used original-name freshness only, derived fresh NOTIN V by set difference,
then applied the corresponding general next theorem with drule_all. DLOAD and
DLOADBYTES probe builds passed (TO_ld_ptr_v2-20261104T185312Z_m5199_t001,
TO_ld_ptr_v2-20261104T185312Z_m5201_t001). The probes were removed to avoid
retaining near-duplicate specializations.

The probes kept operand membership/non-retpc premises explicit: DLOAD requires
`!v. off = Var v ==> v IN U /\ ~retpc_var f v`; DLOADBYTES requires the same for
every variable operand. They did not claim supply freshness proves non-retpc use,
source safety, or scratch headroom. No Support/Stack/Saved/Cover propagation or
terminal closure was established by these interface checks. The old forward
DLOAD consumer in ExpansionNext retains its independent clean-offset boundary
interface; this repair does not require an import cycle from it to BackwardNext.

## 7. Terminal semantic boundary experiment (C1.12.67)

Checked interfaces are in lowerDloadPtrJointClosureProbeScript.sml. These
are semantic probes, not a proof that section 1's Q is closed.

* `forwarding_copy_success_reflect` allows distinct destination values. Target
  success forces three defined operands and the returndata source-range check.
  Source success additionally needs defined source destination, equal evaluated
  offset and size, and equal returndata lengths. There is no destination bound
  or equality check in step_inst RETURNDATACOPY. The source poststate preserves
  vars, labels, allocation table and frontier. No memory agreement is concluded.
* `terminal_assign_success_reflect` proves source success, paired original-var
  definedness and variable-taint equality, and unchanged tables/frontiers/labels.
  It requires all-operand definedness equivalence, NOT equal operand values.
  This is stronger evidence than conditional forwarding_step_var_taint alone.
* `revert_no_reachable_successor_result` excludes both OK and IntRet, for every
  operand shape. `assign_no_terminal_constructor` excludes is_terminator,
  INVOKE, and IntRet for ASSIGN. Thus interior ASSIGN excludes block, call and
  return rules separately. Endpoint REVERT excludes next by the nonterminator
  condition, block by OK inversion, call by opcode, and return by IntRet inversion.
  No successful-exec_block lemma is used for these exclusions.

### Literal instantiations and residual origins

For entry section 4.2, instantiate the copy lemma with source i,s, target j=t's
active instruction (after singleton control establishes j=i), and Ct=C'. Target
R_next gives its OK premise. N's boundary equal-environment supplies returndata
length and labels at phase zero. Definedness for the destination comes from
Defs(U f) plus equal labels (case analysis on the operand); variable membership
comes from active source instruction membership in fn_insts. To apply
`scalar_operand_equal` for off and sz one still must explicitly derive:

```
 !v. off = Var v ==> v IN V f
 !v. sz  = Var v ==> v IN V f
 op_prov G off = NONE /\ op_prov G sz = NONE
 op_taint tn off = {} /\ op_taint tn sz = {}
```

These are not new external assumptions: intended producers are source
fn_ptr_ok/ptr_use_ok for non-pointer scalar positions and source taint_ok for
RETURNDATACOPY (it is neither ASSIGN, shift nor store). Support connects G to
the static witness. Their combined extraction from A/N, especially the opaque
retpc exclusion, has NOT been proved by this experiment. Generic copy success
therefore does not yet instantiate the complete forwarding-entry contract.

For section 4.3 instantiate the ASSIGN lemma with current source/target i and
states s,t, U=U f, tn,un. T already has its variable-definedness and taint
premises. Operand membership follows from active_inst and fn_ir_vars. The
remaining exact premise is

```
 !op. MEM op i.inst_operands ==>
   (eval_operand op s = NONE <=> eval_operand op t = NONE).
```

T's Defs handles Var, and Lit is total. For Label l this requires equivalence
of FLOOKUP s.vs_labels l and FLOOKUP t.vs_labels l being NONE. The checked
`terminal_variable_definedness_does_not_cover_labels` isolates why Defs alone
does not imply it. It is NOT a counterexample to T with its reachability and
control fields, nor to the TASK. Equal labels holds at N's boundary and both
copy/ASSIGN preserve labels; retaining this fact in a revised terminal formula
would avoid reconstructing it from two independent frame_reachable derivations.
Current T does not retain it. No such revision has been made here.

To advance interval witnesses in T after this semantic step one must also prove
`k<z <=> kt<zz` and corresponding endpoint alignment from actual transformed
prefix lengths. Control match at the current instruction alone has not been
shown to produce this endpoint correspondence. Forward:384-486 transports a
SOURCE pair to a target pair at LENGTH transformed prefixes; entry instead
starts with an arbitrary TARGET pair. Required origin formula is:

```
 Cover q f g /\ current singleton control /\ target pair(tb,aa,zz)
 /\ target index=aa ==>
 ?bb a z preA preZ. source pair(bb,a,z) /\ source index=a /\
   aa=LENGTH preA /\ zz=LENGTH preZ /\
   preA/preZ are the actual transformed source prefixes.
```

The forward pair theorem does not prove this converse. In particular resolver
preservation and unchanged ASSIGN intervals must be used in the reverse
origin argument, rather than renaming its existential prefixes.

Finally about_to_revert at a copy supplies only an active REVERT at the next
index. It supplies neither the pair's resolved src=Lit 0w condition nor the
resolved destination/size equalities. Thus section 4.2's pair premise cannot
be inferred merely by unfolding about_to_revert. For this case a separate
immediate-endpoint alternative is needed unless a different transport retains
the normal relation. Its next target instruction is REVERT; checked inversion
then excludes all successor constructors, but operand-taint safety at that
endpoint still requires a ghost relation and source reachability. Existing T
specifically requires two forwarding pairs, so it cannot be asserted as the
output of this entry without the missing origin proof.

Outcome: semantic success reflection is possible without equal pointer values;
the current Q experiment still has explicit scalar-origin, label-definedness,
pair-converse/endpoint alignment, and about_to_revert-only entry residuals.
No frozen-contract falsehood, complete terminal closure, or global induction
has been established. This is a terminal diagnostic deliverable for strategist
review, not authorization to add further isolated opcode inventory.

## 8. Suffix origin repair (C1.12.68)

The reverse-pair obligation in section 7 is superseded by the revised PLAN:
retain the TARGET forwarding pair and synchronize an identical source suffix;
there is no need to prove source resolver equalities or a source forwarding pair.

lowerDloadPtrTerminalTheory now checks four interfaces, in abstraction order:

* lower_dload_terminal_prefix_origin: any transformed ASSIGN/REVERT prefix is
  literally the same source prefix, with the same supply at its end. Uses
  nonempty/control-origin/special-emission facts, including malformed DLOAD and
  DLOADBYTES fallback branches. No source shape or freshness premise is needed.
* lower_dload_terminal_boundary_origin: reflects such a prefix after an actual
  supplied left boundary; gives every intermediate transformed-prefix boundary.
* lower_dload_terminal_index_origin: the TAKE/DROP index interface, including
  the source length bound and identical source slice.
* dload_control_terminal_slice_origin: lifts to actual dload_control_match at
  phase zero, lookup of the target block, and target label distinctness. It
  returns a member source block, its actual supply/prefix boundary, a source
  slice identical to the target slice, every corresponding instruction equal,
  and every corresponding transformed prefix. It does not assume the source
  slice or source endpoint; they are derived. Control already supplies the
  function transform field needed here; no additional ir_supply_covers_fn
  premise is required by this structural argument.

Literal use after a copy at source index a and target index aa:

1. Given singleton copy control, apply existing
   dload_control_singleton_next_fields with s1=s,t1=t. The target next active
   instruction exists because the forwarding pair has aa<zz and its interval
   supplies an instruction there. This produces phase-zero control at source
   a+1 and target aa+1; it need not assume a successful source copy (semantics
   is separately C1.12.69).
2. Apply dload_control_terminal_slice_origin at that boundary with
   d=zz-aa and mid=TAKE d (DROP (aa+1) tb.bb_instructions).
   Target pair middle-ASSIGN and endpoint-REVERT give EVERY ASSIGN-or-REVERT
   on this slice. The pair endpoint bound supplies its length premise.
3. The returned length bound puts the source endpoint
   z=(a+1)+(d-1)=a+(zz-aa) in bounds. Instruction equality at k=d-1 makes
   that source endpoint REVERT. For all smaller k the same equality makes
   the source instruction ASSIGN. Affine offsets obey z-a=zz-aa. Prefix
   equality is returned for every k<=d, not inferred from current control.
   The case zz=aa+1 is d=1: the same result gives an immediate REVERT with
   no interior ASSIGNs and no separate structural induction case.

These interfaces validate structural origin at the real block/control boundary.
They do NOT establish successful source copy execution, source reachability
advancement, retained terminal ghost relations, or immediate REVERT access
transport. Those remain the separate C1.12.69/C1.12.70 integration obligations.
Section 7's semantic scalar/label origins are not solved by this structural work.

## 9. Actual copy scalar/success origins (C1.12.69)

The Terminal theory now checks the scalar and execution part of the section 7
ledger. No retpc freshness assumption, scalar-equality premise, or source-copy
success premise is introduced into the actual consumer.

* `dload_copy_operand_origin` uses `opaque_use_ok_retpc_use`: RETURNDATACOPY
  is neither ASSIGN/PHI nor RET/RETFMP/DRET, so none of its Var operands is a
  retpc variable. `fn_ir_vars_operand` supplies membership in U f.
* `dload_copy_boundary_scalar_origin` consumes normal boundary, Defs(U f),
  Support's current FDOM clause, fn_ptr_ok, opaque_use_ok and source taint_ok.
  It derives off/size equality, destination definedness equivalence, and equal
  returndata length. Pointer values at the destination are not compared.
* `dload_copy_boundary_terminal_fields` reflects the successful target copy,
  returns source success, both allocation/frontier equalities, equal labels,
  Defs(U f), unchanged Var taints on each side, and post-step
  dload_vars_match on V f. It intentionally does not preserve memory_match,
  shared_store or equal_environment. It reuses the existing copy ghost helper.
* `dload_actual_copy_terminal_fields` obtains function membership through
  frame_reachable_raw_certificate; instruction membership from phase-zero
  control; fn_ptr_ok from the source static witness; opaque_use_ok and the
  copy's empty outputs from o1_ctx_shape; source taint_ok from ptr_discipline.
  Its remaining premises are the actual normal boundary, Defs, current Support,
  source reachability, source static witness and singleton control plus the
  actual target OK step. Cover is unnecessary for this semantic consumer.

The two previously local `external_copy_scalar_clean` and
`external_copy_ghosts` facts in this task's Copy theory are now public; their
statements/proofs are unchanged. This avoids duplicating their implementations.

Exact residual for terminal integration: the copy preserves each side's Var
 taints independently and preserves matching on V f. It does NOT establish
matching on excluded opaque retpc variables in U f. The earlier proposed pair
formula demanded all-U taint equality, while normal boundary only supplies V
matching. Thus C1.12.70 must either justify that extra origin from the actual
normal invariant or use source shape to restrict suffix taint transport to V
(non-retpc outputs cannot copy retpc inputs). No all-U matching is claimed by
this checkpoint. Structural suffix alignment, source reachability advancement,
terminal safety and complete joint closure remain unproved.
