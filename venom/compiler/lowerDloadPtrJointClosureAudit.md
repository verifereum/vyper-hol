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

## 10. Separate ASSIGN interfaces (C1.12.70.1)

The original Ordinary theory already proved `retpc_assign_input_tracked`,
`assign_step_success` and `assign_ghost_updates`. They are now public, with
unchanged statements/proofs; no duplicate copy-closure lemma is introduced.

The Terminal theory adds:

* `dload_terminal_assign_definedness`: source success reflection, allocation
  table/frontier preservation, equal labels and post Defs(U), with no ghost
  premise at all. Equal labels plus Defs(U) supplies operand NONE-equivalence;
  actual target success supplies the singleton operand/output shape.
* `dload_terminal_assign_vars_match`: post vars_match(V) from pre vars_match(V),
  source instruction membership and matched labels. It uses retpc copy closure
  only when the queried updated output belongs to V. Then any Var input is
  non-retpc and original, so its matched taint/value relation is available.
  Opaque-only ASSIGNs require no ghost matching outside V.
* `dload_terminal_assign_fields`: the consumer combining those two independent
  interfaces. Source instruction membership derives all operand membership in
  U=set(fn_ir_vars f). It concludes source OK, labels, allocation fields,
  Defs(U) and step-provenance/step-taint vars_match(V). No memory agreement,
  all-U taint matching, or source forwarding pair is assumed or restored.

These are local terminal transition interfaces, not a global reachability
closure proof. C1.12.70.2 still must validate immediate-REVERT access and identify
all required retained layout/provenance clauses before integration is safe.

## 11. C70.2 terminal safety validation (memory-free)

Checked exports in `lowerDloadPtrTerminalScript.sml`:

- `dload_terminal_operand_origin` treats RETURNDATACOPY and REVERT together;
  `dload_copy_operand_origin` retains its old statement as a specialization.
  Source opaque-use shape excludes retpc operands; fn_ir_vars membership comes
  from actual instruction membership, not from lookup success.
- `dload_revert_scalar_clean` derives length provenance NONE and both operand
  taints empty from fn_ptr_ok, source provenance support and source taint_ok.
  Even when dst=sz, ptr_use_ok's single-occurrence restriction excludes pointer
  length. `dload_terminal_revert_length` derives equal evaluated lengths using
  vars_match(V) and equal labels, without a memory relation or all-U matching.
- `dload_terminal_revert_taint` transports REVERT taint_ok using V-only variable
  ghost equality. about_to_revert exempts only its memory-taint clause.
- `dload_terminal_assign_access` and `dload_terminal_assign_taint` discharge
  interior ASSIGN safety independently of forwarding exemption. In fact,
  in_revert_forward marks only the two pair endpoints, NOT interior ASSIGNs.
- `dload_terminal_forward_access` discharges REVERT access at an exempt target
  endpoint. Pair endpoint membership still needs its lookup/index witnesses.
- `dload_terminal_revert_access_values` checks access transport with live layout
  and clean destination value matching, under explicit source non-forwarding.
  Zero-length reads need no bounds. A scalar address remains identical, with
  source access ruling out a nonempty above-lo scalar access. A pointer address
  translates its within-site interval via dload_pointer_word_interval. No
  memory agreement, shared store, or environment equality is used.
- `dload_terminal_revert_access` combines these facts. Its explicit guard
  implication `in_revert_forward f s ==> in_revert_forward g t` is essential:
  source access_ok alone does not supply bounds when source forwarding holds.
- `lower_dload_terminal_forward_guard` PROVES that implication from actual
  source/target block lookups, a covering block supply, original operands in
  its used-variable set, and target index equal to the emitted source-prefix
  length. It invokes the existing lower_dload_block_supply_forward_pair for
  either endpoint; it does not postulate source non-forwarding.
- `dload_actual_terminal_revert_safety` is the checked combined safety consumer.
  Source function membership is derived from frame_reachable, instruction
  membership from active_inst, fn_ptr_ok from the static witness, opaque_use_ok
  from o1_ctx_shape, and access_ok/taint_ok from source ptr_discipline. Its
  remaining relational premises are precisely live layout, vars_match(V),
  equal labels, source provenance support, and the block/prefix witnesses just
  listed. No source success, scalar-length equality, or non-forwarding premise
  is left externally assumed.

### Integration ledger (not a claim of terminal closure)

C70.3 must retain the concrete target block lookup and original-prefix supply
index through terminal entry. For immediate mode they are the actual phase-zero
control fields at the REVERT endpoint (the preceding copy leaves allocation
and variable fields unchanged). For pair mode the actual target pair supplies
endpoint exemption; interior ASSIGNs use unconditional safety and advance the
identical suffix. The accepted slice/index origin lemmas and actual supply
freshness witnesses are still needed to reconstruct the endpoint block/prefix
fields if that route is used. Independent source/target reachability or an
unindexed suffix is NOT enough to invoke the guard theorem. No theorem here
claims reachable-constructor closure, nor does it discharge the frozen contract.

## Checked actual terminal entry (C1.12.70.3.1)

`dload_actual_copy_terminal_entry` in lowerDloadPtrTerminalScript.sml now
builds, including its table-stack Resume and Finalise (build evidence
TO_ld_ptr_v2-20261104T185312Z_m5704_t001 and
TO_ld_ptr_v2-20261104T185312Z_m5706_t001). This is an entry result,
not recursive terminal closure or proof of the frozen contract.

The inline witness is exactly the theorem's existential `s',ss,tt,bb,tb,bs,bt,mid`.
The suffix starts at the bumped indices, is nonempty ASSIGN*;REVERT, and
retains the actual block transformation and every emitted-prefix length.
The alternative is a target forwarding pair at `tt.vs_inst_idx-1` ending
at `tt.vs_inst_idx+LENGTH mid-1`, or `LENGTH mid=1`. No source forwarding
pair, all-U taint equality, or post-copy memory agreement is assumed.

Premise-origin ledger:
- Source success, real successor reachability, Defs(U), equal labels,
  vars_match(V), and unchanged allocation fields: actual copy next consumer.
- Target suffix: actual target exemption and active instruction; distinct
  target labels identify the forwarding block. Immediate mode supplies the
  one-element next-REVERT suffix.
- Cover and normal control: covering block-supply slice origin supplies
  source lookup, original operand membership, used-set coverage, identical
  source slice, and all prefix equations.
- Source active instruction: post-copy control correspondence.
- Post-copy provenance domain support: frame_reachable_prov_supported
  at the actual source successor, using EVERY(fn_ptr_ok P).
- Live layout: normal boundary layout and unchanged frontiers.
- Table stack: normal boundary tables and unchanged allocation maps and
  frontiers; saved frames are unchanged. The table proof specializes the
  original index equation before splitting zero/successor indices.

Recursive ASSIGN closure and endpoint constructor exclusions remain open.

## Indexed terminal safety and constructor boundary (C1.12.70.3.2.3)

Checked exports in `lowerDloadPtrTerminalScript.sml`:
- `dload_indexed_terminal_safety` proves both target safety predicates at every
  valid suffix offset. It uses the unchanged source reachability, block supply,
  prefix alignment, support and non-retpc variable relation. No memory agreement
  or source forwarding pair is added. Malformed REVERT arity has empty access
  ranges; operand taint is transported from the actual reachable source.
- `dload_indexed_terminal_constructor_exclusions` needs only the static suffix
  shape. Every position excludes INVOKE and IntRet. Interior positions exclude
  terminators (hence block transitions); the last position excludes OK (hence
  both next and block transitions). Together these rule out call/ret everywhere
  and every continuing constructor at REVERT. Interior next transitions use
  `dload_terminal_assign_next`, not a second copy of the entry existential.

Verification: two-target holbuild passed, evidence
`TO_ld_ptr_v2-20261104T185312Z_m5792_t001`. This checks the terminal interfaces,
not the global joint reachability induction or the frozen contract proof.

## Canonical terminal closure checkpoint (C1.12.71–72)

The terminal candidate in section 1 is superseded by
`dload_terminal_mode lo P vs C ds H un g j t` in
`lowerDloadPtrTerminalClosureScript.sml`. This is the canonical indexed,
memory-free suffix disjunct; no normal boundary memory relation is retained.
Its entry consumer `dload_actual_copy_terminal_mode` obtains source success,
reachability and the slice from `dload_actual_copy_terminal_entry`, rather than
assuming source success separately. Safety is `dload_terminal_mode_safety`.

`dload_terminal_mode_next` propagates the disjunct at the literal next-rule
boundary using the interior ASSIGN transport. Its explicit
`ALL_DISTINCT (fn_labels g)` premise is required: `active_inst` by itself can
select an instruction in another same-label block. Global consumers must supply
this premise from target shape, not infer it from the terminal predicate.
The call, return and block constructor exclusions are respectively
`dload_terminal_mode_no_call`, `dload_terminal_mode_no_return`, and
`dload_terminal_mode_no_block`.

This certifies terminal-mode propagation only. Normal Support/Stack/Saved
propagation and the full target `frame_reachable` induction remain open, as
does the frozen stage contract. The next strategy review must address those
normal-mode joint consumers, not another terminal inventory.

## 15. Tracked block successor interface (C1.12.77–78)

`dload_boundary_core_phis_tracked` and
`lower_dload_function_supply_enters_boundary_tracked` in BlockEntry now separate
relational V from definedness U. Their PHI-only backward closure premise is
proved for V = set(fn_ir_vars f) DIFF {v | retpc_var f v} by
`dload_original_phi_input_tracked`. Old statements remain specialization wrappers.
The original-V/U block-entry consumer was checked and removed to avoid a duplicate
export (TO_ld_ptr_v2-20261104T185312Z_m6086_t001).

Branch now exports `dload_boundary_core_branch_tracked` and
`dload_actual_branch_block_tracked`. They reflect target JMP/JNZ/DJMP success
without assuming source success and produce actual source block reachability,
successor control, original-variable definedness and entry ghost boundary.
The latter uses arbitrary V with explicit PHI closure. Its original-V consumer
was checked (TO_ld_ptr_v2-20261104T185312Z_m6112_t001) and removed; original operand
membership followed from singleton control and fn_ir_vars_operand, while
non-retpc branch operand use remained explicit. Historical branch theorem
statements are unchanged, with short specialization proofs.

These interfaces do NOT certify normal-Q block closure. Stack/Saved/Support
propagation and phase/terminator inversion remain downstream obligations.
The outer constructor must still produce singleton phase-zero control, source
reachability, static fn_ptr_ok, FDOM support, source taint safety, non-retpc
operand use, Cover and distinct target block labels. Target step/nonhalting,
enters_block and activity are the target frame_reachable_block premises.
The frozen contract remains unfinished.

## 16. Normal phase-zero branch ancillary closure (C1.12.79)

`dload_normal_branch_block` in NormalBlock consumes the tracked branch interface
once and retains its actual source successor, reachability, control, definedness
and entry core witnesses. It additionally preserves the inline Stack and Saved
fields, retains Cover, and derives current/saved provenance and parameter support
from `frame_reachable_prov_supported` at that actual successor. Stack uses target
allocation-map stability under jump and PHI entry; Saved uses source call-context
stability under the same operations. No successor support or source-success
premise is added. Relational V remains independent of original definedness U.

The checked theorem closes only the singleton phase-zero branch constructor
interface. The outer induction must still produce that phase/control inversion,
branch membership, tracked operand use, source safety, Cover and target label
distinctness. It does not establish the global joint reachability induction or
the frozen stage contract.

## Checked full return constructor (C1.12.83)

`lowerDloadPtrJointReturnTheory.dload_joint_return_closed` uses exactly the
normal/terminal disjunction of JointCall, expanded inline. Its input is
`Q (d::ds) PH H un g ri t`; its output is
`Q ds d.cf_params (DRESTRICT d.cf_prov (COMPL (set d.cf_inst.inst_outputs)))
 (un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs)))
 d.cf_fn j (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx)`.
The premises are the actual ret constructor's active instruction, arbitrary
`IntRet rt tend`, binding into the saved caller, and resumed active instruction.
No premise assumes RET, phase zero, tend=t, or source success.

Premise origins: the existing `step_inst_intret_opcodes` theorem handles INVOKE
as well as base execution. Emission inversion then forces the original
singleton and phase zero. Source instruction membership and `fn_ptr_ok` exclude
RETFMP/DRET, leaving RET; its equation yields tend=t. Zero-prefix inversion
identifies all anchor fields. Source discipline supplies taint safety, and
source static witness supplies pointer-use safety. Original-variable
membership supplies operand definedness. Opaque return-use restrictions forbid
a retpc variable in FRONT (using the actual nonempty RET operand list).
Stack length equalities expose source caller and two allocation frames.
The saved-head supply witness plus source caller shape gives distinct target
caller labels; source caller membership comes from `frame_stack_prefix`.

`dload_normal_return` is consumed whole, including popped boundary, source
return/reachability, resumed control, all-original definedness, scratch stack,
saved-frame witnesses and provenance support. Output normal witnesses use
`cs0`, `c.cf_params`, restricted saved source provenance/taint, `c.cf_fn`, its
resumed source state/control/supply, n=0, pfuel=0, the resumed target state,
restricted saved target provenance/taint, and `ef::fs1`. Saved instruction
equality reconciles restrictions. Terminal input is impossible by
`dload_terminal_mode_no_return`. This certifies only the return constructor,
not next closure, global induction, or the frozen stage theorem.

## 18. Exact-Q next constructor audit (C1.12.84)

This is an interface audit, NOT a checked next-closure theorem. Baseline
`holbuild [lowerDloadPtrJointReturnTheory,o1ContractLowerDloadPtrTheory]` passed
(TO_ld_ptr_v2-20261104T185312Z_m6386_t001). The task obligation remains open.
Use section 1's **normal** existential exactly as expanded in JointReturn:28–64
and JointCall, and replace section 1's obsolete terminal candidate by
`dload_terminal_mode`. In this section Q, U, V, O, Support, Stack and Saved are
only metanotation for those literal formulas; no new HOL constant is proposed.

### 18.1 Exact proposed consumer

The desired theorem, after expanding A and both occurrences of Q inline, is:

```sml
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  Q ds PH H un g j t /\
  frame_reachable vs C' ds PH H un g j t /\ active_inst g j t /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel C' j t = OK t1 /\
  active_inst g j' (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  Q ds PH (step_prov PH H j t1) (step_taint j t t1 un)
    g j' (t1 with vs_inst_idx := SUC t.vs_inst_idx)
```

The six constructor premises (from the first `frame_reachable` through final
`active_inst`) are literally ptrDisciplineScript.sml:469–472 with simultaneous
renaming `(vs0,ctx,stk,PG,G,tn,fn,inst,inst',s,s')` to
`(vs,C',ds,PH,H,un,g,j,j',t,t1)`. In particular arbitrary `fuel` is retained;
there is NO `~t1.vs_halted` premise in next. Target reachability can be unused
by the eventual consumer, but is not silently replaced by source reachability.
There is no external source-success, phase-zero, successor-support, scratch-map,
operand-safety or call-address premise.

### 18.2 Fuel and phase partition

Control gives `n < LENGTH emitted`. Thus exactly one of
`SUC n < LENGTH emitted` and `SUC n = LENGTH emitted` holds. Supply inversion
(Rel:322; PhaseNext:66) says a non-singleton emission is DLOAD of length 4 or
DLOADBYTES of length 2. Every other emission is `[i]`, hence n=0 and j=i.
At interior phases the source anchor s and target anchor t0 stay unchanged;
at completion the new anchor is the actual bumped successor, with phase zero
and a new emitted list supplied by `dload_control_emission_next_fields`.

The existing `dload_actual_phase_next` (PhaseNext:95–118) is NOT directly
applicable: its phase core and successful step share one fuel, whereas Q's
prefix fuel `pfuel` is existential and the rule's fuel is arbitrary.
There is a legitimate bridge, but it needs a checked interface:

- Every instruction in a proper nonempty expanded prefix is one of ALLOCA,
  ADD, CODECOPY, MLOAD, by supply inversion (including the last instruction
  when extending to the complete prefix). None is INVOKE.
- `step_inst_non_invoke` (venomExecSemantics:1829–1832) rewrites each such
  step to `step_inst_base`, independent of fuel AND context. In particular
  the final constructor step may be rewritten at **pfuel**, keeping the
  preceding prefix unchanged. Then `dload_prefix_extend` at pfuel is legal.
- Equivalently a bounded-prefix induction on dload_prefix_match_def:10–20
  transports the entire prefix between fuels under
  `!k. k < n ==> (EL k emitted).inst_opcode <> INVOKE`.
  No such general fuel-transport export was found in Phase/PhaseNext.
- For singleton completion `dload_prefix_zero` already identifies t=t0,
  H=H0, un=un0 for every pfuel. Its one rule step can be replayed at the
  arbitrary constructor fuel. No prefix-fuel equality is needed.

Thus there is no semantic fuel obstruction, but substituting the rule's fuel
for the existential witness without this argument would be an invalid proof.
For the interior output preserve every ancillary witness verbatim (including
Stack, which refers to t0, NOT t1); only prefix/control/current phase change.
Control fields follow `dload_expanded_step_blocks` and
`dload_control_interior_next_fields`; target label distinctness comes from
Cover plus source shape. Extending to a *complete* prefix is required before
using the backwards completion consumers below.

### 18.3 Exhaustive opcode consumer matrix

Rows classify the ORIGINAL i at completion, not the generated j. Every row
also requires the ancillary ledger in 18.4. The ASSIGN/PARAM/RETPC_PARAM row
now has a whole normal-Q proof (C1.12.89); other normal completion rows remain
boundary interfaces rather than whole-Q proofs.
Names without a file prefix are in lowerDloadPtr<File>Script.sml as indicated.

| Original opcode / input mode | Existing consumer and actual interface | Missing interface or origin |
|---|---|---|
| terminal input, any next | TerminalClosure:121 `dload_terminal_mode_next` | Full terminal Q output already; distinct target labels still derive from stage/source shape, not terminal mode alone. |
| interior DLOAD or DLOADBYTES | PhaseNext:95 `dload_actual_phase_next` | Fuel bridge above; preserve anchor ancillary fields. No source step here. |
| complete DLOAD | BackwardNext:62 `dload_tracked_backward_next` | Accepts arbitrary V,U; returns source step/reachability, boundary on `(r1::rs)`, Defs(U), next control, and `r1.dr_scratch = generated_id INSERT r.dr_scratch`. Needs actual freshness, headroom, offset, and full-prefix replay origins. Does NOT return whole Stack/Saved or allocation-map footprint. |
| complete DLOADBYTES, ordinary write | BackwardNext:108 `dloadbytes_tracked_next` | Arbitrary V,U; returns source step/reachability, next control, boundary and Defs(U); explicitly requires `~in_revert_forward f s`. No allocation-map/call-address footprint is exported. |
| ALLOCA singleton | JointAlloc:136 `dload_actual_alloca_boundary_next` | Arbitrary V, returns source step/reachability/control/boundary and exact updated head scratch-map identity. Does NOT return Defs(U), source call-address stability or full ancillary Saved/Support. |
| ASSIGN singleton | JointVariable `dload_joint_tracked_variable_next`, via Ordinary `dload_boundary_core_assign_tracked_index` | Whole normal-Q successor proved at arbitrary rule fuel, exact original V and U. Input tracking derives from original membership and `dload_assign_original_input_closed`; no source-success or successor-footprint premise. |
| PARAM, RETPC_PARAM | Same JointVariable consumer, via Parameters `dload_boundary_core_parameter_tracked_index` | Whole normal-Q successor proved; RETPC_PARAM output exclusion derives from `dload_parameter_retpc_output`. No enlargement to complement-only V. |
| LT, GT, EQ | Ordinary:289 `dload_boundary_core_compare_index` | Already arbitrary V,U and exports variable-only footprints. Use it, not a larger-set wrapper; operand origins and next packaging still needed. |
| MUL, Div, SDIV, Mod, SMOD, Exp, ADDMOD, MULMOD, SLT, SGT, ISZERO, AND, OR, XOR, NOT, SIGNEXTEND, BYTE | Scalar:139 `dload_boundary_core_scalar_index` | Arbitrary V,U, returns boundary/Defs and variable-only footprints; JointNext:285 wrapper is complement-only and must NOT be used as-is. |
| ADD, SUB | Affine:112 `dload_boundary_core_affine` | Arbitrary V,U boundary/Defs with variable-only footprints; :181 actual wrapper fixes complement V. Source affine/static/taint hypotheses must come from Q/A. |
| MLOAD | MemoryRead:114 `dload_boundary_core_mload` | Arbitrary V,U boundary/Defs, variable-only footprints; requires source non-forwarding. :178 wrapper fixes complement V. |
| MSTORE | MemoryStore:62 `dload_boundary_core_mstore` | Arbitrary V,U boundary/Defs; output arity from source shape. :156 wrapper fixes complement V. Need memory-only allocation/address footprint for ancillary packaging. |
| MSTORE8 | ByteStore:71 `dload_boundary_core_mstore8` | Arbitrary V,U boundary/Defs; :164 actual wrapper fixes complement V; same footprint obligation. |
| MCOPY | MCopy:176 `dload_boundary_core_mcopy` | Arbitrary V,U boundary/Defs, but actual wrapper fixes complement V; source non-forwarding required. |
| SLOAD, TLOAD | Storage:121 `dload_boundary_core_storage_read` | Arbitrary V,U; returns variable-only footprints and Defs(U). Actual storage wrapper is complement-only. |
| SSTORE, TSTORE | Storage:248 `dload_boundary_core_storage_write` | Arbitrary V,U; shared-store change is already handled inside boundary; allocation/address fields still needed outside it. |
| CODECOPY, CALLDATACOPY, RETURNDATACOPY, non-exempt | Copy: boundary `dload_boundary_core_external_copy` (Finalise:215), actual :228 | Boundary accepts arbitrary V,U; actual wrapper fixes complement V and requires source non-forwarding. Must establish source non-forwarding from target guard/control or choose terminal row. |
| RETURNDATACOPY, target exempt | TerminalClosure:55 `dload_actual_copy_terminal_mode` | Exact original V; returns whole terminal disjunct. Need actual arity `[dst;off;sz]`, source/target distinct labels and target `in_revert_forward \/ about_to_revert`; no new memory invariant is promised. |
| SHA3 | Hash:109 `dload_boundary_core_sha3` | Arbitrary V,U; :182 actual wrapper fixes complement V. Same next/ancillary packaging requirement. |
| MEMTOP, DRET, GETFMP, SETFMP, RETFMP, FMP_PARAM | ptrDiscipline:120–140 fn_ptr_ok | Impossible original members, not generic equal-environment steps. |
| DALLOCA | Static:48 `lower_dload_function_no_dalloca`, source fmp-free invariant | Must obtain source exclusion from A. Supply retains DALLOCA, so it is not excluded by emission inversion alone. |
| JMP, JNZ, DJMP, RET, RETURN, REVERT, STOP, SINK, SELFDESTRUCT, INVALID | venomInst:346 is_terminator; singleton supply | Impossible from literal next nonterminator premise. DRET/RETFMP also terminate and were excluded above. |
| INVOKE | singleton supply and literal next premise | Impossible j=i; no invocation fuel theorem is needed. |
| DELEGATECALL, CREATE, CREATE2, OFFSET | unitShapeDefs:312 inst_shape_ok | Impossible source members under o1_fn_shape. SELFDESTRUCT and DJMP are independently shape-excluded but already in terminator row. |
| all other constructors (listed below) | No whole-boundary next consumer identified in existing next families | Remaining semantic work, not justified by equal_environment alone. |

The final residual row is exactly:
`SHL; SHR; SAR; ILOAD; ISTORE; PHI; NOP; INITIAL_FMP; BUMP; CALLER; CALLVALUE;
CALLDATALOAD; CALLDATASIZE; ADDRESS; ORIGIN; GASPRICE; GAS; GASLIMIT;
COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID; SELFBALANCE; BALANCE;
BLOCKHASH; BASEFEE; CODESIZE; EXTCODESIZE; EXTCODEHASH; EXTCODECOPY;
RETURNDATASIZE; BLOBHASH; BLOBBASEFEE; CALL; STATICCALL; LOG; ASSERT;
ASSERT_UNREACHABLE`.
Together with the table these cover the opcode datatype verbatim
(venomInst:23–69). Some residual constructors may be excluded by further source
shape/fmp-free clauses or impossible OK results, but those inversions must be
proved rather than treating this residual row as a single scalar step. In
particular CALL/STATICCALL execute memory-observing external calls
(venomExecSemantics:1072–1094), unlike read0. SHL/SHR/SAR are in neither Affine's ADD/SUB interface nor
Scalar's enumerated list, and need masked shift/taint transport. ILOAD/ISTORE are not MLOAD/MSTORE instances.

A normal source satisfying in_revert_forward needs endpoint classification too:
contextCodegenRel:331–341 defines this predicate ONLY at either endpoint of a
revert_forward_pair, not at every interior ASSIGN. By
`revert_forward_pair_interval_opcode` (Forward:10), an active endpoint is
RETURNDATACOPY or REVERT. Thus DLOAD/DLOADBYTES/MLOAD/MCOPY cannot satisfy
source in_revert_forward. For an external copy, a source forwarding endpoint
is the RETURNDATACOPY start, not a contradiction: transport the actual pair
through the covering supply (Forward:384/470) to establish the target guard
and use the terminal row. This is a required origin proof, not an extra
assumption. The only copy exemption supported by the existing terminal entry
is the actual RETURNDATACOPY case, not arbitrary CODECOPY/DLOADBYTES.

### 18.4 Whole-boundary origin and preservation ledger

For every completed normal emission, choose new source state s1 from the
backward semantic consumer, source state `s2 = s1 with vs_inst_idx :=
SUC s.vs_inst_idx`, and target anchor `t2 = t1 with vs_inst_idx :=
SUC t.vs_inst_idx`. For expanded emissions t1 is the LAST constructor result;
full-prefix replay includes its bumped index and actual final ghost updates.
The new phase-zero prefix can use fuel 0. Keep cs,ds,PG,PH,f,g,q; change
G,tn,H,un by the precise consumer ghost equations and choose fs' returned by
allocation transport (never assume fs'=fs in allocation cases).

| Field needed in new Q | Origin / missing preservation |
|---|---|
| Source function membership/shape, fn_ptr_ok, safety | Source frame_reachable plus frame-to-raw certificate; EVERY static witness gives fn_ptr_ok; ptr_discipline gives access_ok/taint_ok. No source successful step follows from safety alone. |
| Source successful step and reachability | The backwards consumers in 18.3 reflect target success; singleton next uses `dload_singleton_reachable_next_fields`, expanded next uses `dload_control_emission_next_fields` plus frame_reachable_next. Residual opcodes still need reflection. |
| Original operand membership and non-retpc use | fn_ir_vars_operand from source instruction membership; opaque-use restrictions from source o1_fn_shape. PHI/ASSIGN/PARAM/RETPC_PARAM need their specialized tracked reasoning; cannot demand all operands in V unconditionally. |
| Boundary on V and saved Ws | General-V cores are available for most existing families, including the accepted tracked ASSIGN and parameter cores. JointVariable consumes those at exact original V. Expanded and original alloca cores return changed head frame. |
| Defs(U) at new anchor | General cores explicitly export it except original ALLOCA consumer; ALLOCA must use its actual matching output updates and initial Defs, not pointer safety. Expanded DLOAD/bytes consumers explicitly export original-U definedness after freshness. |
| Support for current and saved frames | Re-derive from `frame_reachable_prov_supported` at the actual new source reachability and EVERY(fn_ptr_ok P). Do not assume it for s2 or prove it from target boundary. PG and saved frames unchanged in next. |
| Stack lengths | Same cs,ds; original ALLOCA and DLOAD replace only head frame, so prove LENGTH fs' = LENGTH fs. |
| Stack at k=0 | Non-allocation steps need actual target allocation-map stability. Original ALLOCA exports exact head identity (JointAlloc:159–160). DLOAD exports scratch insertion but still needs final-prefix FDOM update, generated id freshness outside O f and no later prefix map change. Cannot copy old Stack through scratch allocation. |
| Stack at k=SUC k' | Saved states unchanged and tail fs unchanged for allocation families; prove tail equality of chosen fs'. Boundary table relation alone is NOT the syntactic scratch-map identity. |
| Cover | Same f,g,q, so retain predecessor witnesses exactly; successor instruction/control existence comes from control-next, not a new supply. |
| Saved layouts | At successor require DROP(SUC k) fs' layouts; head replacement drops out for all saved k, but explicitly prove this for chosen fs'. Saved states/frontiers unchanged. |
| Saved environment, instruction, definedness, supply/control | Unchanged saved cs,ds; retain fields. |
| Saved call-address equation | Must prove s2.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address. Index bump alone only proves equality with s1, not with s. Variable-only footprints in Ordinary/Scalar/Affine/read families suffice; memory/store/alloca/expanded/residual families need actual semantic footprints. Boundary equal_environment compares source to target and does not relate new source to old source. |
| Scratch budget/freshness/headroom | JointBudget `dload_joint_runtime_scratch_budget` from full Stack/source reachability and frozen assumptions; Static member-covered/scratch-fresh facts from actual Cover; SourceInv offset/headroom from source reachable state. These are inputs derived at the old anchor, not new-Q fields. |

### 18.5 Smallest missing interfaces for strategy review

1. A bounded non-INVOKE replay fuel bridge (or local explicit non-INVOKE
   rewrite at the extension step), then exact-Q **interior** packaging. It
   must keep all ancillary anchor witnesses and work with arbitrary rule fuel.
2. Tracked ASSIGN and PARAM/RETPC_PARAM boundary interfaces on original V,
   retaining independent U; use existing implementations once, do not add
   more complement-only actual-next wrappers. Other families should consume
   their existing general-V cores directly.
3. A reusable next ancillary assembler for unchanged allocation maps and
   source call-address, plus allocation variants using actual fresh/repeated
   head-frame equations. It must produce Defs(U) for original ALLOCA and
   exact Stack for completed DLOAD; no externally assumed successor fields.
4. Exhaustive residual-opcode reflection/boundary consumers or checked static
   exclusions for the explicit residual list. Partition read0/read1, masked
   shifts, immutables, external effects and no-op/assert/PHI/fmp
   cases by semantics, not a giant case proof assuming equal observations.
5. Full completion packaging with origin inversions, target-exempt copy switch
   via the canonical terminal consumer, and zero-prefix reconstruction. Only
   AFTER these checked producers should a full literal-next leaf and global
   induction be authorized.

This diagnostic identifies genuine interface gaps; it does not establish that
all next cases close on paper. In particular tracked block/return success
cannot repair complement-only ASSIGN/parameter statements, missing residual
opcode semantics, or the syntactic scratch-map and Saved-address obligations.
No theorem/definition was edited and no continuity/global certification is
claimed.

### 18.6 Checked variable-only singleton checkpoint (C1.12.89)

Supersedes the ASSIGN/parameter gaps in the historical 18.5 list, not the
remaining completion or global-closure obligations. The tracked kernels in
Ordinary/Parameters preserve independent U and V and are implemented once;
the complement-only interfaces remain compatibility consumers.

`NormalNext.dload_normal_unchanged_successor` assembles full normal Q from
actual successor reachability, original-V boundary and Defs(U), current
control, target allocation-map stability and source call-address stability.
It recomputes Support from source reachability and preserves Stack/Saved by
index. `JointVariable.dload_joint_tracked_variable_next` now supplies all of
these premises for ASSIGN, PARAM and RETPC_PARAM without externally assuming
source success, operand trackedness, successor Support, or footprints.
Singleton replay forces phase zero and equates the current target with its
original anchor. The accepted indexed kernels reflect the literal arbitrary-
fuel target step, give the bumped boundary and variable-only footprints;
singleton control-next gives source reachability. The shared assembler then
returns the exact whole normal-Q existential, including exact step_prov and
step_taint at the literal target successor.

Still unresolved: allocation/expansion footprints and head-frame completion;
actual premise origins and whole-Q packaging for the other existing semantic
families; residual opcode reflection/boundary or static exclusions; full
literal-next integration; and global induction. This local theorem is not a
proof of the frozen stage contract. Verification: holbuild targets
lowerDloadPtrJointVariableTheory and o1ContractLowerDloadPtrTheory passed.

### 18.7 Checked comparison/scalar normal-Q next consumer

`lowerDloadPtrJointScalarTheory.dload_joint_tracked_scalar_next` builds with
arbitrary literal fuel and exact step_prov/step_taint successors. It covers
LT/GT/EQ and MUL, Div, SDIV, Mod, SMOD, Exp, ADDMOD, MULMOD, SLT, SGT,
ISZERO, AND, OR, XOR, NOT, SIGNEXTEND, BYTE. Source access/taint safety comes
from ptr_discipline at the incoming frame_reachable witness; fn_ptr_ok uses
the separate Q policy P. Operand trackedness follows from source shape and
opaque-use restrictions. Indexed semantic kernels retain exact non-retpc V
and independent all-original U, without added source-success or footprint
premises. Singleton control and NormalNext reconstruct every ancillary Q
field. No definitions or existing theorem statements changed.

This is only this opcode-family closure row. Allocation, expansion completion,
other semantic families/residual opcodes, and global reachability closure
remain unresolved; this does not certify the frozen stage contract.

### 18.8 Checked affine normal-Q next consumer

`lowerDloadPtrJointAffineTheory.dload_joint_tracked_affine_next` proves the
whole normal-Q next row for original ADD/SUB at arbitrary literal fuel.
It consumes the general-V affine semantic core with independent all-original
U, derives source safety and operand origins from the incoming witness, and
uses index-update, singleton reachability, and NormalNext interfaces to
reconstruct the exact successor ghosts and ancillary fields. No source
success, successor support, or allocation footprint premise is added.

This covers ADD/SUB only, not shifts. Allocation, expansion completion,
residual opcode families and global induction remain unresolved; neither
this row nor its successful build proves the frozen stage contract.

## C1.12.92: checked ordinary MLOAD whole-normal-Q row

`lowerDloadPtrJointMemoryReadTheory.dload_joint_tracked_mload_next` closes the
literal arbitrary-fuel next constructor for an original MLOAD with exactly the
incoming normal existential above and the global source hypotheses. Its output
is the full normal existential, including exact step_prov/step_taint ghosts,
finite V, independent U definedness, Support, Stack, Cover and Saved fields.
Source non-forwardness is derived, not assumed: the source active block is the
lookup block by distinct labels from source shape; revert_forward_at_opcode
excludes MLOAD. The semantic step uses the existing arbitrary-V/U MLOAD boundary
core and does not demand equality of loaded tainted words. Index-update,
singleton reachability, and normal unchanged-successor interfaces reconstruct
the boundary and ancillary fields. No memory-read semantics were duplicated.

Checked build: lowerDloadPtrJointMemoryReadTheory and
 o1ContractLowerDloadPtrTheory (TO_ld_ptr_v2-20261104T185312Z_m6744_t001).
This is local closure evidence only: allocation, expansion and remaining
families/global induction still need proof, and the frozen contract is not
certified by this build.

## C1.12.93: checked ordinary MSTORE8 whole-normal-Q row

`lowerDloadPtrJointMemoryStoreTheory.dload_joint_tracked_mstore8_next` has the
same whole-normal-Q incoming and outgoing existentials as the MLOAD row, with
only the incoming opcode restriction changed to MSTORE8. Arbitrary literal
target fuel is retained. Source shape provides empty outputs and operand
origins; source reachability and discipline provide access/taint safety;
distinct-label active lookup excludes revert forwarding. The existing general
V/U byte-store core provides source success, exact ghosts, definedness and the
post boundary. The new `dload_mstore8_step_fields` proves allocation/frontier,
call-context and control field preservation directly from successful semantics.
The fields-version singleton reachability interface, index update and NormalNext
then return every ancillary Q field. No byte-store memory proof is duplicated.

Checked build: lowerDloadPtrJointMemoryStoreTheory and
o1ContractLowerDloadPtrTheory (TO_ld_ptr_v2-20261104T185312Z_m6778_t001).
This is only the original MSTORE8 next row, not MSTORE, MCOPY, an expansion
completion, or global closure; the frozen theorem remains unfinished.

## C1.12.94: checked ordinary MSTORE whole-normal-Q row

`dload_joint_tracked_mstore_next` in lowerDloadPtrJointMemoryStoreTheory closes
the exact same normal-Q literal-next interface with opcode MSTORE. The extra
core premise, bounded source operand masks, follows from the incoming source
frame_reachable witness using dload_reachable_op_taint_bound; it is not a new
caller hypothesis or an inference from taint_within. Shape supplies empty
outputs and operand eligibility; source discipline supplies safety. The checked
MSTORE core preserves the actual finite V and independent U and exact ghosts.
A successful-step field lemma supplies unchanged control, allocation and call
context fields, allowing the existing fields-singleton, index-update and
NormalNext interfaces to return every Q field without unfolding the boundary.
Checked build: lowerDloadPtrJointMemoryStoreTheory and
o1ContractLowerDloadPtrTheory (TO_ld_ptr_v2-20261104T185312Z_m6792_t001).
This is local MSTORE next closure only, not allocation/expansion/global closure.
