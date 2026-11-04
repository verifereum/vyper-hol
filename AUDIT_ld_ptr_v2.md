# Ordinary-next transport interface audit (C1.3.14.1)

This is a design proposal, NOT an asserted/proved HOL theorem. Existing SML statements and definitions are unchanged. Startup lowerDloadPtrAllocTheory build passed (TO_ld_ptr_v2-20261104T033958Z_m1154_t001).

## Exact proposed integration contract

The allocation case is separate because it changes fs. The following nonallocating ordinary-next contract includes explicit additional invariants not yet proved available. No predicates are introduced.

```sml
!fuel C C' vs0 supply P fn gn inst lo fs V Ws PG PH G H tn un
  s t cs ds t1.
  o1_ctx_shape C /\
  frame_reachable vs0 C cs PG G tn fn inst s /\
  fn_ptr_ok P fn /\
  dload_control_match supply fn gn s t inst [inst] 0 /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  V = {v | ~retpc_var fn v /\
       ?i. MEM i (fn_insts fn) /\
           (MEM v i.inst_outputs \/ MEM (Var v) i.inst_operands)} /\
  (!v. (?i. MEM i (fn_insts fn) /\
            (MEM v i.inst_outputs \/ MEM (Var v) i.inst_operands)) ==>
       (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  FDOM G SUBSET fn_pv P fn /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  ~in_revert_forward fn s /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ~MEM inst.inst_opcode [ALLOCA; DLOAD; DLOADBYTES; DALLOCA; PHI] /\
  step_inst fuel C' inst t = OK t1 ==>
  ?s1.
    step_inst fuel C inst s = OK s1 /\
    (!v. (?i. MEM i (fn_insts fn) /\
              (MEM v i.inst_outputs \/ MEM (Var v) i.inst_operands)) ==>
         (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G inst s1) (step_prov PH H inst t1)
      (step_taint inst s s1 tn) (step_taint inst t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds
```

All identifiers/types are the existing HOL constants. Types inferred: fuel/lo num, C/C' context, vs0/s/t/s1/t1 venom_state, supply ir_supply, P string -> num set, fn/gn ir_function, inst instruction, fs dload_reloc_frame list, V string set, Ws string set list, PG/PH (num#num) option list, G/H (string,num#num) fmap, tn/un taint, cs/ds call_frame list. `taint` and `ir_supply` here are explanatory type names, not new annotations. This proposal requires type-check validation before implementation; no speculative SML was installed.

The strengthened definedness conjunct is intentional: dload_vars_match omits opaque retpc variables, but an ASSIGN from such a variable still must succeed in both runs. Its output is opaque too and not in V, so value equality is unnecessary. Definedness for opaque variables is NOT currently in boundary_core.

Post-step: fs,V,Ws,PG,PH,cs,ds unchanged; G/H and tn/un updated exactly as frame_reachable.next. Both indices advance from their own pre-step values (never equated). Post-step dload_control_match for inst' is a SEPARATE control lemma using the transformed prefix and the target next active instruction. The above does not pretend current [inst] remains active after increment.

Saved-suffix layouts are unchanged in this nonallocating case: fs/cs/ds unchanged, so their inline formula can be framed without assuming it follows from boundary_core. ALLOCA must preserve it via head replacement.

## Premise origins and unresolved dependencies

| Premise | Future origin / status |
|---|---|
| source frame_reachable, control match, boundary core | induction witness, still to be built in C1.3.18 |
| o1_ctx_shape C | frozen assumption |
| fn_ptr_ok P fn | ptr_discipline witness plus source function membership |
| access_ok / taint_ok | ptr_discipline applied to source reachability |
| V = original operand/output variables minus retpc_var | proposed fixed selection; static opaque closure from unitShapeDefs; never quantify over generated target temporaries |
| all-variable definedness | UNAVAILABLE in current core; entry true, needs preservation at ordinary/PHI/call/return rules |
| FDOM G SUBSET fn_pv P fn | UNAVAILABLE as an existing dynamic theorem; must prove reachable provenance support jointly with parameter-position support on call stacks |
| ~in_revert_forward | NOT universal; needs a separate forwarding coverage branch, including CALL/STATICCALL failures and intervening forwarding instructions |
| exclusions ALLOCA/DLOAD/DLOADBYTES | separate allocation / expansion transport |
| DALLOCA exclusion | ~ctx_has_dalloca C from o1_src_inv + reachable function membership |
| PHI exclusion | sequential PHI returns Error; block-entry PHIs handled separately |
| C' relationship | no extra context relation needed here: step_inst_non_invoke makes the semantics context-independent; control match already witnesses fn transform |

No claim that this candidate is sufficient or derivable yet. In particular fn_ptr_ok's static affine and pointer-use restrictions need dynamic provenance support before they restrict actual pointer operands. Arbitrary G unrelated to fn_pv would make e.g. MUL transport unjustified.

## Exhaustive opcode partition (venomInstScript.sml:24-68)

Each datatype constructor appears once below. Families concern source original instructions; generated ALLOCA/ADD/CODECOPY/MLOAD are expansion phases, not occurrences of these unchanged instructions.

1. Affine pointer or exact scalar: ADD, SUB. fn_ptr_ok.affine_pointer_ops controls position/count of pointer operands. Output provenance is first_prov.
2. Exact scalar (no pointer operands allowed by ptr_use_ok, no taint by taint_ok): MUL, Div, SDIV, Mod, SMOD, Exp, ADDMOD, MULMOD, SLT, SGT, ISZERO, AND, OR, XOR, NOT, SIGNEXTEND, BYTE.
3. Comparable pointers or exact scalar: EQ, LT, GT. access_ok supplies same positive site and inclusive bounds; live-site uniqueness and interval translation give equal comparison result.
4. Masked scalar transport: SHL, SHR, SAR; ASSIGN. Shift amounts must be exact and unprovenanced. ASSIGN can carry pointers or opaque tokens; opaque result is excluded from V but definedness must be tracked.
5. Memory: MLOAD, MSTORE, MSTORE8, MCOPY, SHA3. Need range transport from access_ok outside forwarding; masked read/write byte lemmas, including zero length. MSTORE8 tainted value is forbidden (unlike MSTORE). SHA3 reads must be entirely untainted.
6. Shared store: SLOAD, SSTORE, TLOAD, TSTORE. Keys exact; read results related under storage masks; writes preserve shared-store relation. BALANCE/SELFBALANCE are grouped with environment below because accounts agree outside storage.
7. Immutables: ILOAD, ISTORE. Static fn_ptr_ok forbids pointer operands. Executable access uses vs_memory; ISTORE ALSO updates vs_immutables. Need both memory and t_imm bookkeeping, not merely fmap equality.
8. Exact environment/read0/read1: INITIAL_FMP, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE, ADDRESS, ORIGIN, GASPRICE, GAS, GASLIMIT, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, CHAINID, SELFBALANCE, BALANCE, BLOCKHASH, BASEFEE, CODESIZE, EXTCODESIZE, EXTCODEHASH, RETURNDATASIZE, BLOBHASH, BLOBBASEFEE. Equal environment supplies code/labels/context/FMP; shared store supplies account nonstorage fields. GAS is equal in this IR semantics (no step gas debit), so it need not be omitted from V.
9. Exact-data-to-relocated-memory copies: CALLDATACOPY, CODECOPY, EXTCODECOPY, RETURNDATACOPY. Destination range transports; source offset/size/account address exact. RETURNDATACOPY success bound uses equal returndata; forwarding exception requires separate proof.
10. Observable parameters: PARAM. dload_param_values_lookup supplies pointer relation or equality. RETPC_PARAM produces opaque output, not value equality; operand/output shape and definedness still needed.
11. No value change / guarded success / side effects: NOP, ASSERT, ASSERT_UNREACHABLE, LOG, CALL, STATICCALL. Assertions require exact condition. LOG data/topics exact. External calls require equal request payload plus account nonstorage/environment equality; write back returned bytes at corresponding output ranges, preserve caller storage mask. A failed call may start a revert-forward exemption (not covered by main candidate).
12. Allocation: ALLOCA. Fresh site inserts paired source and target bases, repeated site keeps frame. Separate core-preservation theorem needed. Static freshness/disjointness from scratch, memory initialization masks, target frontier headroom, variable relation extension under new fs all remain semantic integration obligations; the allocator layout theorems alone are not this theorem.
13. Pass expansions: DLOAD, DLOADBYTES (C1.3.15).
14. Block/call/return: JMP, JNZ, DJMP, RET, RETURN, REVERT, STOP, SINK, SELFDESTRUCT, INVALID, DRET, RETFMP, INVOKE, PHI. The first 12 are terminators (DJMP/SELFDESTRUCT also shape-excluded); only successful OK terminators JMP/JNZ/DJMP feed frame_reachable.block. RET/RETFMP/DRET feed ret via IntRet, others Halt/Abort do not feed next. INVOKE uses call/ret, not completed big-step simulation. PHI prefix uses enters_block; sequential PHI has no OK result.
15. Excluded by fn_ptr_ok or o1_src_inv: MEMTOP, GETFMP, SETFMP, FMP_PARAM, DALLOCA.
16. Excluded by fn_shape_ok.inst_shape_ok: BUMP is NOT excluded and needs its own exact-scalar TWO-output update proof (fn_ptr_ok prevents pointer inputs). DELEGATECALL, CREATE, CREATE2, OFFSET ARE excluded. Do not accidentally classify BUMP with prohibited raw FMP ops. (DRET/RETFMP already listed among terminators.)

## Reusable exact interfaces

- Rel:196 dload_matched_operand:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> v IN V) /\ eval_operand op s = SOME x /\ eval_operand op t = SOME y ==>
  dload_value_word fs (op_taint tn op) (op_prov G op) (op_prov H op) x y.
- Rel:213 dload_matched_operand_defined: same first three premises ==> (eval_operand op s = NONE <=> eval_operand op t = NONE).
- Rel:121 dload_pointer_word_interval:
  dload_live_layout lo sf tf fs /\ dload_pointer_word fs (b,n) (c,n) x y /\ b <= w2n x /\ w2n x <= b+n ==> w2n y = c+(w2n x-b).
- Rel:91 dload_live_site_positive_identity:
  dload_live_layout lo sf tf fs /\ dload_live_site fs owner id b c n /\ dload_live_site fs owner' id' b c' n /\ 0<n ==> owner=owner' /\ id=id'.
- Call:95 dload_param_values_lookup:
  dload_param_values fs PG PH xs ys /\ k<LENGTH xs ==> k<LENGTH ys /\
  dload_value_word fs {} (if k<LENGTH PG then EL k PG else NONE) (if k<LENGTH PH then EL k PH else NONE) (EL k xs) (EL k ys).
- Boundary:5,17 exec_alloca_fresh_site / exec_alloca_repeated_site give exact OK state equations from singleton output and absent/present lookup, respectively. Boundary:32 positive_site_translation_order is natural arithmetic, NOT modular pointer transport by itself.
- Alloc:226 dload_layout_original_insert:
  dload_live_layout lo sf tf (f::fs) /\ FLOOKUP f.dr_source id=NONE /\ FLOOKUP f.dr_target id=NONE /\ tf+n<dimword(:256) ==>
  dload_live_layout lo (sf+n) (tf+n) ((f with <|dr_source:=f.dr_source |+ (id,(sf,n)); dr_target:=f.dr_target |+ (id,(tf,n))|>)::fs).
- Aggregate:47-101 boundary projection lemmas; Rel:331 dload_control_match_boundary.
- venomExecSemantics run_defs:1645-1670 / step_inst_non_invoke: non-INVOKE step reduces to step_inst_base regardless of fuel/context. frame_reachable.next is ptrDiscipline:458-466.

## Proposed missing reusable statements (not proofs)

First tier, independent small interfaces:

```
!fs x y. dload_value_word fs {} NONE NONE x y ==> x=y

!fs mask p q x y d.
 dload_value_word fs mask p q x y ==>
 dload_value_word fs mask p q (x+d) (y+d)
```

The second proposal is deliberately REJECTED: addition does not preserve arbitrary byte masks through carries. Only pointer-word addition is valid without extra mask premises:

```
!fs a b x y d. dload_pointer_word fs a b x y ==>
 dload_pointer_word fs a b (x+d) (y+d)
```

Further family boundaries should be supplied by strategist after review: shifts need shift_taint's exact endianness/mask equations; memory reads need relocated slice agreement and byte-mask-to-word agreement; writes need pairwise fixed/live interval disjointness and taint set update laws. These must precede the proposed integration theorem. All-variable definedness and dynamic provenance support affect PHI/call/return siblings, not only this ordinary-step component.

## Adversarial conclusions

- Masked addition is false in general; never use it for scalar tainted arithmetic (taint_ok excludes that case).
- Core cannot imply opaque definedness, dynamic provenance support, or saved-suffix bounds; these are missing execution invariants, not tactical gaps.
- Calls inherit frontier displacement. Param relation covers all vs_params; it cannot be used to assert equality of vs_return_pc_token, which setup_callee sets from LAST args. Ordinary RETPC_PARAM must ignore its value on V.
- No counterexample to the frozen task has been verified by this audit. This report is not a proof of ordinary_step_match or the frozen theorem.

# Forwarding and frame-constructor interface checkpoint (C1.12.2.1)

This section is a proposal, not a semantic transport result. No definition or
existing theorem statement is changed. Repository search found no interval
classification helper: the existing `revert_forward_at_opcode` classifies only
endpoints. `lowerDloadPtrForwardTheory.revert_forward_pair_interval_opcode`
now proves the three-way interval classification directly from
`revert_forward_pair_def` (ordinary holbuild passed, TO_m1252).

## Exact proposed forwarding alternative

The following is an inline alternative in the target reachability invariant,
not a new predicate. Free outer variables are the current target frame
`gn, t, PH, H, un, ds` and source context/initial state `C, vs0`. Existential
variables are witnesses. It intentionally relates memory only at the anchor,
not after RETURNDATACOPY. `fuel` must be chosen consistently with the prefix;
all instructions in this segment are context/fuel independent non-INVOKEs.

```sml
?fn bb tb i j a b k ri ti supply fs V Ws PG G tn s t0 H0 un0 cs fuel.
  frame_reachable vs0 C cs PG G tn fn ri s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx = i /\ revert_forward_pair bb i j /\
  get_instruction bb i = SOME ri /\
  lookup_block t0.vs_current_bb gn.fn_blocks = SOME tb /\
  t0.vs_inst_idx = a /\ revert_forward_pair tb a b /\
  get_instruction tb a = SOME ti /\
  dload_control_match supply fn gn s t0 ri [ti] 0 /\
  dload_boundary_core lo fs V Ws PG PH G H0 tn un0 s t0 cs ds /\
  a <= k /\ k <= b /\
  t.vs_current_bb = t0.vs_current_bb /\ t.vs_inst_idx = k /\
  dload_prefix_match fuel C' PH
    (TAKE (SUC b - a) (DROP a tb.bb_instructions)) (k-a)
    t0 H0 un0 t H un
```

This formula is only the forwarding-specific part. At its anchor retain the
same explicit strengthened conjuncts as at ordinary boundaries: actual
`lower_dload_function_supply` witness and original/transformed context
membership; original-variable set selection and all-original definedness;
source G/PG support and saved caller support; exact saved suffix layouts;
distinct function-index/scratch-injection witnesses; saved supply/control and
saved all-original-variable definedness. None follows from boundary_core.
The alternative requires both source and target recognized pairs: neither
recognition is inferred from mere interval membership. In particular proving
that the supply transform preserves `resolve_block_assigns` and the pair
endpoints is an UNRESOLVED syntax obligation (the opcode classifier does not
prove it). There are no DLOAD expansions strictly inside a recognized pair,
since every interior opcode is ASSIGN; target index translation still needs
the actual transformed prefix before the first endpoint.

Unlike an ordinary boundary alternative this need not reconstruct a source
state at the current k. Its obligations are target `access_ok` and `taint_ok`
at each active k, extension by successful ASSIGN, and impossibility of a next,
block, call, or ret constructor leaving the terminal REVERT. Access bounds
are exempt at recognized endpoints; strict interior ASSIGN has no ranges or
pointer comparison. Taint safety is NOT implied by the opcode classifier:
REVERT's variable operands must still have empty variable taint, and
RETURNDATACOPY's operand and memory-taint updates must be checked. Syntax
alone does not imply operand evaluation succeeds. For already reachable
prefixes replay supplies successful intermediate steps, but endpoint safety
still needs anchor invariants and evaluation/taint preservation. No claim of
post-copy `dload_memory_match` is made or needed on a terminal-only path.

## Finite premise-origin audit

References are to the five constructors of `frame_reachable` in
`ptrDisciplineScript.sml:447-500`, not completed big-step invocations.

| Constructor | Given by constructor | Additional origin / unresolved obligation |
|---|---|---|
| entry | context entry name, function lookup, entry label, enters_block, active_inst; PG=[], G=FEMPTY, entry_taint, empty stack | initial core from dload_boundary_initial after initial frontier/headroom; same initial variables give definedness BEFORE PHIs only; parallel PHI entry matching and transformed entry control still needed. Empty support/suffix/index-stack facts are base cases, not supplied by enters_block. |
| next (ordinary) | prior target reachability, active instruction, nonterminator/non-INVOKE, successful step, active successor; exact step_prov and step_taint updates | prior induction alternative determines ordinary, expansion, or forwarding case. Ordinary and expansion finish transport remain external obligations. For forwarding RETURNDATACOPY/ASSIGN extend prefix; retain anchor ghosts rather than infer a new boundary. Need segment instruction lookup and index bounds for successor, not endpoint-only in_revert_forward. |
| block | successful terminator step, not halted, enters_block, active successor; entry_prov fn s' G and entry_taint_vars fn s' tn | recover matching source branch using translated untainted observations; prove simultaneous PHI transport with pre-entry G0/tn0 fixed (not sequential output substitutions); preserve all-original definedness including opaque variables, original support, exact saved suffix facts, and supply/control. Cannot carry a forwarding REVERT through this rule: its result is Abort, not OK. |
| call | INVOKE decode, lookup callee, operand evaluation, setup_callee, enters_block; pushes caller snapshot; PG becomes MAP(op_prov G) ops, G=FEMPTY, variable taint=FEMPTY | translate args and parameter provenance; paired setup/entry/PHIs; push exact saved suffix layout with original caller frontier; save original definedness/support/control; derive callee function index and distinctness from callee_first and actual lookup. Constructors do not supply source/target scratch budget or supply freshness. External C1.6/C1.7/C1.8 and source support work remain needed. |
| ret | nonempty saved stack, IntRet step, bind_outputs after adopt_return_fmp/merge_callee_state; caller PG restored, caller G and variable taint DRESTRICTed by output names | pair returned untainted values and bind_outputs definedness; restore SAVED caller suffix frontier/layout, never infer it from callee frontier; discard callee tables/scratch; restore saved original control/definedness and restrict provenance/taint by exact output names. Global memory taint comes from current tn while t_var comes from saved frame. Need return memory/shared-state transport; aggregate core alone does not imply these premises. |

## Failed external CALL/STATICCALL entry

`exec_ext_call_def` returns OK for a well-formed single output even when the
outcome success word is zero. This is an ordinary `next` step, NOT the
`frame_reachable.call` constructor (which is exclusively INVOKE).
`step_inst_base_def` evaluates CALL/STATICCALL operands before exec_ext_call;
`consume_call_outcome` provides the new returndata, memory and shared state.
The following branch/block steps may lead to a recognized forwarding pair.
Required origins are: paired call request/oracle outcome and shared-state
transport from ordinary transport; paired branch tests from untainted
observations; transformed block and pair recognition from control/supply
syntax. The same reasoning must not assume failed calls never occur or
infer a paired outcome from equal opcode alone. The forwarding anchor must
be established at the copy endpoint reached by those steps, not at an
arbitrary caller state and not by assuming ordinary memory agreement after
the exempt copy.

`ASSIGN` has OK only for one input, one output and a defined operand
(venomExecSemanticsScript.sml:813-820); it leaves memory unchanged, but updates
variable provenance/taint. `REVERT` yields Abort with padded memory slice
returndata, or Error for malformed/undefined operands (lines 771-780), never
OK or IntRet. It therefore cannot have a sequential successor through any
frame_reachable rule. None of these observations proves relational closure:
that remains blocked pending the explicit support, memory, PHI, call/return,
and forwarding-taint obligations above.

## Source provenance support checkpoint (C1.12.3.1)

The syntax obligation described as unresolved at lines 183-187 is now proved:
`lower_dload_insts_supply_forward_pair` and the source-context-facing
`lower_dload_block_supply_forward_pair` in lowerDloadPtrForwardScript.sml.
This does not close the replay/safety obligations at lines 189-200.

### Candidate and adversarial branch check

The source-only candidate is domain support for G in fn_pv P fn, support of
non-NONE PG positions in P fn.fn_name, and both properties for every saved
caller. This is NOT yet a theorem. No counterexample was found by inspecting
all five frame_reachable constructors and all branches of out_prov/set_prov.
The examination did not reveal a necessary o1_ctx_shape premise for this
*domain-only* candidate: malformed instructions either kill provenance or
still propagate along an existing static def-use edge. This does not assert
that domain support proves provenance/value soundness.

For induction, also carry MEM fn C.ctx_functions and
`!f. MEM f stk ==> MEM f.cf_fn C.ctx_functions`, or first prove that membership
as a separate reachability fact. The candidate as originally phrased does
not include these auxiliary induction facts; static fn_ptr_ok for a restored
caller cannot be recovered merely from its parameter/provenance support.
Lookup membership is available from venomInst.lookup_function_mem/MEM.
An active instruction belongs to fn_insts via active_inst's block lookup,
get_instruction's bounded EL, and fn_insts_blocks_MEM.

| Constructor | Source-only support origin and remaining closure |
|---|---|
| entry | G=FEMPTY, PG=[], stk=[]: support is immediate. This constructor does NOT apply entry_prov, even though enters_block evaluates PHI values. For support this empty map is harmless. Function membership follows from lookup. |
| next | PG/stk unchanged. set_prov either updates a SINGLE output with SOME site or DRESTRICTs all outputs. ALLOCA/DALLOCA singleton outputs are ptr_roots, regardless of the actual site value. PARAM can yield SOME only with literal index in PG bounds and non-NONE slot; PG support puts it in P, hence its singleton output is a root. ADD/SUB/ASSIGN SOME first_prov must come from a Var operand whose name is in FDOM G, hence fn_pv; pointer_derived_vars_edge puts every output in fn_pv. Every other opcode has out_prov=NONE. Malformed ALLOCA/DALLOCA multiple outputs are killed by set_prov; malformed PARAM operands yield NONE. |
| block | entry_prov selects a block of this function or is identity. phis_prov reads phi_prov from the SAME G0 for every PHI. An unsupported, malformed or missing predecessor selection yields NONE and kills outputs. A SOME selected Var is an operand member (existing resolve_phi_MEM), its provenance comes from G0, and the PHI static edge contains its outputs. Recursion changes only the accumulation map, not G0. Stop at first non-PHI. |
| call | Snapshot preserves caller G/PG and static membership. New callee G=FEMPTY. At k<LENGTH(MAP (op_prov G) ops), a non-NONE entry implies EL k ops=Var v with v in FDOM G. Caller fn_ptr_ok supplies ptr_use_ok. Its INVOKE clause uses exactly the decoded args (not inst_operands including the label), so k is already the argument index and no +/-1 adjustment is permitted. decode_invoke is functional; lookup identifies callee.fn_name=nm. Then k IN P callee.fn_name. No callee_first or context shape premise supplies or is needed for this argument. |
| ret | Caller PG is restored from f.cf_params. Saved domain support and FDOM_DRESTRICT imply support for the restored, output-killed provenance. Remaining stack is a sublist of the old stack; saved membership recovers fn_ptr_ok for the restored caller. Current callee PG/G support does not imply caller support and cannot replace the saved conjunct. |

### Existing interfaces to reuse (do not duplicate)

- lowerDloadPtrClosure.pointer_derived_vars_edge: finite roots plus an
  instruction member, pointer-preserving opcode and supported Var input
  imply supported output. pointer_use_vars_contains gives root inclusion.
- lowerDloadPtrStatic.FINITE_ptr_roots: finiteness is already proved.
- execEquivParamBase.resolve_phi_MEM:
  `resolve_phi prev ops = SOME op ==> MEM op ops` (quantified over all three).
  Other upstream copies exist; use an allowed existing version, not the
  owner-prohibited lowerDloadClassify theory and not another duplicate.
- finite_map.FDOM_DRESTRICT is the general domain equality. Restriction
  support alone is a direct set-theoretic corollary, so no new duplicate
  DRESTRICT-domain theorem was added.

### Checked small support boundaries

New lowerDloadPtrSupportScript.sml exports:

```
op_prov_outside_support:
  FDOM G SUBSET V /\ (!v. op = Var v ==> v NOTIN V) ==>
  op_prov G op = NONE

set_prov_support:
  FDOM G SUBSET V /\
  (!v site. outs = [v] /\ p = SOME site ==> v IN V) ==>
  FDOM (set_prov G outs p) SUBSET V

out_prov_param_supported:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  (!k. k < LENGTH PG /\ EL k PG <> NONE ==> k IN positions) /\
  out_prov PG G inst s' <> NONE ==> w2n idx IN positions
```

set_prov_support exercises the existing DRESTRICT law in its kill branch and
requires support only for the actual singleton/SOME update branch. The PARAM
probe formally excludes out-of-range and unmarked positions. All three pass
holbuild lowerDloadPtrSupportTheory (TO_ld_ptr_v2-20261104T033958Z_m1510_t001).

### Missing closure statements for strategist review (not assumed facts)

1. Non-PHI output support:
   `MEM inst (fn_insts fn) /\ FDOM G SUBSET fn_pv P fn /\
    (!k. k < LENGTH PG /\ EL k PG <> NONE ==> k IN P fn.fn_name) /\
    inst.inst_outputs = [v] /\ out_prov PG G inst s' <> NONE ==>
    v IN fn_pv P fn`.
   Derive step_prov domain support with set_prov_support. This does not need
   successful execution as a premise; the updated state is used only for the
   site value, not its domain.
2. Parallel PHI support:
   `FDOM G0 SUBSET fn_pv P fn /\
    (!inst. MEM inst xs ==> MEM inst (fn_insts fn)) ==>
    FDOM (phis_prov prev G0 xs) SUBSET fn_pv P fn`.
   Then entry_prov support by block membership. Keep G0 fixed under induction
   on xs; no sequential substitution of PHI input provenance.
3. Decoded argument support:
   `fn_ptr_ok P caller /\ MEM inv (fn_insts caller) /\
    inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm,ops) /\
    FDOM G SUBSET fn_pv P caller ==>
    !k. k < LENGTH (MAP (op_prov G) ops) /\
        EL k (MAP (op_prov G) ops) <> NONE ==> k IN P nm`.
   Use ptr_use_ok, EL_MAP and a Var operand inversion; no label-index shift.
4. Joint source frame support: the candidate plus active/saved function
   membership for induction. Entry/call use context lookup, next/block use
   (1)/(2), ret uses saved facts and FDOM_DRESTRICT. This full induction is
   deliberately not attempted before review.

None of these source-only closures supplies paired opaque definedness,
post-expansion memory transport, scratch budget or saved suffix layout.

## Parallel PHI definedness boundary (C1.12.3.5)

Checked in `lowerDloadPtrPhiTheory`: `eval_operand_definedness`,
`update_var_definedness`, `eval_one_phi_definedness`, and
`eval_phis_definedness`. No new definitions. Exact main signature:

```sml
!xs V s t t'.
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!i v. MEM i xs /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  eval_phis t xs = OK t' ==>
  ?s'. eval_phis s xs = OK s' /\
       (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
```

The single-PHI boundary requires the same predecessor and label map,
input-variable NONE equivalence for variables in that instruction's operands,
and `eval_one_phi t i = SOME (out,b)`; it returns an `a` with
`eval_one_phi s i = SOME (out,a)`. Successful target evaluation excludes
malformed output lists, missing predecessors, unresolved PHIs and undefined
selected operands. The scalar values need not agree. Paired update_var writes
the same output name but arbitrary differing values, preserving NONE equivalence
on any V. The list proof keeps the original input states fixed while evaluating
the tail, then applies the paired write boundary.

### Premise origins for future consumers (not full consumer proofs)

| Premise | Initial entry | Later block entry |
|---|---|---|
| Matching predecessor | Both entry setup states explicitly set vs_prev_bb to NONE. Exact paired entry construction still to be integrated. | Needs matched branch destinations and originating block labels from the paired control invariant. Not supplied by source support. |
| Equal label maps | Common starting state gives equality; matched function labels are available from lower_dload_function_supply_labels when constructing callee setup. Setup/control reconstruction remains unproved here. | Must be retained across paired transitions and setup/returns. No derivation from provenance domain support. |
| Identical PHI list/prefix | Actual supply expansion leaves PHI instructions unchanged and expands DLOAD/DLOADBYTES to non-PHIs; this still needs a common-prefix equality boundary for corresponding selected blocks. | Same missing common-prefix equality boundary, using actual block transform witnesses and lookup correspondence. |
| Input coverage in V | Choose V to contain all original operand and output variable names, INCLUDING retpc variables. For an original PHI prefix coverage follows from instruction membership. | Same syntactic membership argument, once the common prefix is identified. |
| Input NONE equivalence on V | Identical initial variables establish this before entry PHIs. Paired setup at INVOKE is a separate unfinished obligation. | Must be maintained inductively on ALL original V, including opaque variables. Existing boundary_core does not imply it. |
| Successful target eval_phis | Invert the target enters_block witness. | Invert target enters_block after the matched terminator. |

Inspected `lower_dload_function_supply_phi` in StaticTheory, lines 486-490:
it preserves `phi_pv_all_var` given covering supply and static pointer-use
hypotheses. It is NOT a PHI-prefix equality or successful eval_phis theorem.
Likewise `lower_dload_insts_supply_phi_prefix` in o1ContractLowerDloadTheory
preserves the PHI-prefix ordering property, NOT equality of prefixes. Neither
may be substituted for the still-missing common-prefix correspondence origin.
This checkpoint proves definedness/success transport only, not dload_vars_match,
provenance/taint coupling, saved suffix layouts or whole enters_block transport.

## Exact supply PHI computation (C1.12.3.6)

Checked in lowerDloadPtrPhiTheory:
- `lower_dload_insts_supply_phi_exact`: from
  `lower_dload_insts_supply q xs = (ys,q')`, gives the conjunction
  `phi_prefix_length ys = phi_prefix_length xs`,
  `TAKE (phi_prefix_length ys) ys = TAKE (phi_prefix_length xs) xs`, and
  `!s. eval_phis s ys = eval_phis s xs`.
- `lower_dload_block_supply_phi_exact`: the same three equalities for
  `bb'.bb_instructions` and `bb.bb_instructions`, given the actual
  `lower_dload_block_supply q bb = (bb',q')` witness.
- `lower_dload_block_supply_phi_definedness`: given that block witness,
  equal predecessors and labels in s,t, coverage of all Var operands of
  bb's instructions by V, equal lookup definedness on V, and successful
  target `eval_phis t bb'.bb_instructions = OK t'`, obtains successful
  source `eval_phis s bb.bb_instructions = OK s'` with equal definedness
  on V in s',t'. Values need not agree.

The list proof reuses existing inst-supply nonempty, special and control
lemmas rather than duplicating expansion shape facts. PHIs remain singleton
expansions; the first non-PHI expansion head remains non-PHI, so both
computations stop there, including on malformed DLOAD fallbacks.

Premise origins for subsequent consumers:
- Entry AND later block: common-prefix equality and same-state eval_phis
  equality now follow from the actual block-supply witness, not ordering.
- Both: obtaining that witness from the selected transformed function/block
  remains an integration obligation. These theorems do not supply lookup
  correspondence or equality of block labels.
- Entry: original variable definedness starts from identical initial vars;
  predecessor/label equality still requires paired setup reasoning.
- Later block: original-variable definedness and equal predecessor/labels
  must be maintained by the relational invariant; no new origin proved here.
- V operand coverage is a syntactic choice (all original variables); opaque
  original variables must not be removed from definedness coverage.
- No provenance/value/memory relation, saved suffix layout, call/return,
  or full enters_block transport is established by these equalities.

## Actual function block-entry consumer (C1.12.3.7)

Checked `lower_dload_blocks_supply_lookup`: an actual supply transformation
of a block list and successful target lookup yield a successful source
lookup and an actual block-supply witness for those selected blocks.
The induction preserves first-match lookup even with duplicate labels.

Checked `lower_dload_function_supply_enters_block` in PhiTheory:
given the actual function-supply witness, equal current block, predecessor
and label map, coverage of source function Var operands by V, definedness
agreement on V, and `enters_block g t t'`, obtains `enters_block f s s'`,
equal post-entry instruction indices, and definedness agreement on V.
The selected-block witness is derived internally, not an added premise.
It consumes the checked block PHI definedness/exactness interfaces.

Still-required premise producers:
- Initial entry must show paired setup selects the same entry label, sets
  equal predecessor/label maps and starts with identical original vars.
- Later block entry must preserve the selected current label, predecessor,
  label map and all-original-variable definedness in transition transport.
- Function-supply correspondence must come from stage/function lookup.
- V operand coverage is syntactic; include opaque retpc original operands.
This is successful entry/index/definedness transport ONLY. Pointer values,
parallel provenance/taint, memory, allocation layouts and saved-frame
relations remain separate central integration obligations. No full
enters_block boundary-core transport has been proved.

## Parallel PHI relational kernel (C1.12.4)

Checked `dload_vars_match_phis` in PhiTheory with the exact planned kernel:
equal predecessor and labels, initial dload_vars_match on tracked V,
selected-input closure for tracked singleton outputs, and successful source
and target eval_phis imply dload_vars_match after parallel phis_prov and
phis_taint updates. Source and target selections read fixed pre-PHI inputs.
The theorem does not require distinct outputs, SSA, or equal opaque values.
`dload_matched_phi` supplies related selected values and equal taint masks;
`dload_vars_match_write` handles paired singleton writes, including untracked
outputs. Its explicit old taint-map arguments make record-update matching
work directly at the tail-first PHI consumer.

Selected-input closure remains an explicit premise: source provenance-domain
support does NOT establish trackedness of scalar/opaque selected operands.
For the eventual V excluding retpc variables, the static producer must rule
out an opaque input flowing to a tracked PHI output (or show that output is
opaque too). No such producer is certified by this checkpoint.

By inspection, eval_phis changes only vs_vars (via update_var): memory,
allocation maps/frontier, storage, transient storage, labels and control
fields are unchanged. phis_prov changes the provenance map and phis_taint
changes t_var only; other taint fields are retained by record update. These
observations have NOT been promoted to a full boundary_core preservation
proof. Actual transformed entry can use exact same-state PHI equality and
E0060 success/definedness, but still needs tracked-input closure, paired
control setup and assembly of untouched memory/frame fields. Calls/returns,
allocation, external effects, forwarding and saved suffix transport remain
unproved central obligations.

## C1.12.11: producer audit after scalar transport (2026-11-04)

Verification: standard holbuild of lowerDloadPtrScalarTheory and
lowerDloadPtrOrdinaryTheory passed (TO_ld_ptr_v2-20261104T033958Z_m2119_t001).
Reviewed scalar consumers committed as d06e556a1. No semantic source changed
in this audit. This is a candidate invariant, NOT a checked simulation theorem.

### Existing consumer interfaces and premise origins

ScalarScript:98-182 exports dload_boundary_core_scalar and _index.
OrdinaryScript exports dload_boundary_core_compare and _index. Both take
opcode membership, MEM i (fn_insts f), fn_ptr_ok P f,
FDOM G SUBSET fn_pv P f, access_ok lo G f i s, taint_ok f tn i s,
equal labels, Var operand membership in V and U, U-definedness agreement,
boundary_core and target OK. They produce source OK, updated definedness,
step_prov/step_taint boundary_core and variable-only state equalities.
Index wrappers do not assert equal source/target indices.

| Premise | Producer / precise missing obligation | Constructor |
|---|---|---|
| fn_ptr_ok, source safety | Unfold source ptr_discipline (PtrDiscipline:612-621), specialize its P and source frame_reachable witness | all boundaries |
| Source instruction membership | active_inst at the source witness; existing EVERY_active_inst boundary | all boundaries |
| Source G and PG support, saved support | frame_reachable_prov_supported in SupportTheory; requires EVERY fn_ptr_ok and source reachability, not target core | all boundaries |
| Var membership in U | Choose U(f)={v | ?i. MEM i (fn_insts f) /\ (MEM v i.inst_outputs \/ MEM (Var v) i.inst_operands)} | static |
| Var membership in V | Choose V(f)=U(f) DIFF {v | retpc_var f v}. opaque_use_ok_retpc_use plus retpc_use_ok_def (UnitShapeDefs:73-99) excludes opaque operands for scalar/compare/ADD/SUB/memory/INVOKE. PHI and ASSIGN require output-sensitive copy closure instead; RET's last token is deliberately excluded | static family-specific discharge still unproved |
| U-definedness | Entry starts with same original vars; checked PHI, entry, ASSIGN, scalar and compare consumers preserve it. Missing for remaining opcodes and saved return/bind_outputs | entry, next, block, call, ret |
| Equal labels/environment | dload_boundary_environment; dload_equal_environment_code. Actual block-entry theorem still takes matching control/labels explicitly | next/control/call/ret preservation missing |
| Input supply covers original fn | fn_pass_step_input_covers_fn, lower_dload_stage_every_covered (Static:24-45). Must retain an actual per-function supply witness from stage, not an arbitrary supply | entry/call lookup |
| Generated output freshness | Static lower_dload_function_supply_fresh_output_unique, reserved_output, scratch_fresh. Must specialize actual covered supply witness. These do not assert runtime ghost-map support | expansion |
| Generated ID disjointness and scratch capacity | Missing explicit runtime subset/injection below. Covering supply alone is not a runtime table-domain invariant | fresh/reused scratch, call/ret |
| Live tables/layout | boundary_core (Aggregate:8-20) supplies current tables and current frontier layout. AllocTheory supplies table fresh/repeated/push/pop and layout insert/push lemmas | allocation/call/ret |
| Saved suffix layout | NOT in core. Carry exact formula below; saved_layout_push/head_replace/restore/pop (Alloc:303-355) already checked | call, allocation, ret |
| Saved metadata | core supplies dload_saved_metadata at DROP (SUC k) fs; only vars and params, NOT current memory/environment nor saved control/definedness | call/ret strengthened clauses missing |
| Source raw bounds and headroom | o1_src_frame_raw_mem_ok and o1_src_frame_dload_headroom_ok (SourceInv:13-35) from actual source reachability | source boundary; completion post-state requires renewed reachability |
| Backward success | Existing consumers assume target OK, derive source OK. Do not assume successful source evaluation to start full induction | next/control/call/ret |
| Phase anchoring | dload_phase_core stores boundary at t0, prefix replay to t. It says nothing about allocation/memory relation at t itself (Aggregate:24-32) | proper expansion prefix |

### Exact candidate joint boundary proposition (notation only)

Use the actual target frame_reachable judgment as induction antecedent. For a
boundary target judgment frame_reachable vs C' ds PH H un gn j t, existentially
choose cs,PG,G,tn,fn,i,s,fs,Ws,supply,emitted,ks and saved supplies so that:

1. frame_reachable vs C cs PG G tn fn i s /\ active_inst fn i s;
   lower_dload_function_supply supply fn=(gn,supply_end) /\
   ir_supply_covers_fn supply fn /\
   dload_control_match supply fn gn s t i emitted 0.
2. dload_boundary_core lo fs (V fn) Ws PG PH G H tn un s t cs ds.
3. !v. v IN U fn ==> (lookup_var v s=NONE <=> lookup_var v t=NONE).
4. FDOM G SUBSET fn_pv P fn /\
   (!k. k<LENGTH PG /\ EL k PG<>NONE ==> k IN P fn.fn_name).
   Saved versions are obtained from frame_reachable_prov_supported, not postulated
   as conclusions of core.
5. !k. k<LENGTH cs ==> dload_live_layout lo
   (EL k cs).cf_state.vs_alloca_next (EL k ds).cf_state.vs_alloca_next
   (DROP (SUC k) fs).
6. LENGTH ks=LENGTH fs /\ ALL_DISTINCT ks /\
   EVERY (\k. k<LENGTH C.ctx_functions) ks /\
   !a. a<LENGTH fs ==> FINITE (EL a fs).dr_scratch /\
     CARD (EL a fs).dr_scratch <=
       LENGTH (FILTER (\i. i.inst_opcode=DLOAD)
         (fn_insts (EL (EL a ks) C.ctx_functions))).
   Each ks position names the corresponding active/saved source fn; actual
   saved frame equality and supply witness is retained at each position.
7. For each frame f with its actual function supply q: every original runtime
   table id is an original ALLOCA id of f, and every scratch id is the ALLOCA
   emitted for a DLOAD occurrence of f under q. Concretely the latter set is
   {id | ?bb n u i tail q1 ys q2. MEM bb f.fn_blocks /\
     bb.bb_instructions=TAKE n bb.bb_instructions ++ i::tail /\
     lower_dload_insts_supply u (TAKE n bb.bb_instructions)=(ys,q1) /\
     i.inst_opcode=DLOAD /\
     ?as q3. lower_dload_inst_supply q1 i=(as,q3) /\
       as<>[] /\ (HD as).inst_opcode=ALLOCA /\ (HD as).inst_id=id}.
   IMPORTANT: u must be the actual block-input supply obtained by threading q
   through preceding blocks, not arbitrary u. This is a witness constraint;
   its extraction and occurrence injection are MISSING, not checked facts.
   Original-ID/scratch-ID disjointness must hold for the whole frame, including
   original instructions not yet executed. This is stronger than frame_sites.
8. !k. k<LENGTH cs ==> Ws[k]=V ((EL k cs).cf_fn) and, writing c=EL k cs,
   d=EL k ds, retain their actual supply/function correspondence,
   dload_control_match q c.cf_fn d.cf_fn c.cf_state d.cf_state
     c.cf_inst [c.cf_inst] 0 for unchanged INVOKE sites (or its actual singleton
   emission), and !v. v IN U c.cf_fn ==>
     (lookup_var v c.cf_state=NONE <=> lookup_var v d.cf_state=NONE).
   Control matching also carries the actual instruction index mapping; raw
   equality of indices is NOT a substitute.

At proper prefixes retain ALL these anchor witnesses at t0, together with
0<phase /\ phase<LENGTH emitted and dload_phase_core ... . A terminal forwarding
alternative remains separate; neither a successful complete expansion nor its
memory relation is implicit in this candidate.

### Allocation obligations (next substantive family recommendation)

Prefer original ALLOCA integration BEFORE ADD/SUB: the existing layout/table
kernels make the semantic gap explicit and allocation produces the very site
relations consumed by pointer arithmetic. No new opcode-only conditional lemma
should hide the following obligations.

* Original fresh id: core tables identify HD fs with s/t.vs_allocas. Domain
  equality and whole-function ID disjointness must give target NONE from source
  NONE. Both evaluate the same size (source ptr_use_ok excludes pointer size;
  taint_ok excludes masked size; original definedness gives source evaluation).
  New fs replaces head source/target maps by (sf,n)/(tf,n), no scratch insertion.
  Prove layout with extended frontiers, old vars/params/saved metadata monotone
  under this extension, and new output pointer relation. Memory is not cleared:
  new bytes must be tainted in BOTH ghosts, including reused old callee garbage.
  Need post-frontier <dimword, not just pre-frontier <dimword.
* Original repeated id: frame_sites gives corresponding SOME (c,n) from source
  SOME (b,n); amount may differ from stored n but exec_alloca ignores it on both
  sides (semantics:535-552). Preserve fs/frontiers/memory and write related bases;
  out_prov/step_taint must use stored size/site, not current operand size.
* Zero n: same fresh/repeated split; no positive-site uniqueness can be used.
  Layout separation is vacuous for empty intervals, pointer translation still
  needs the actual owner/id witness. Zero-size reused bases are not evidence of
  site identity. No counterexample claimed; positive comparisons exclude it.
* Fresh scratch: source state stutters; head target map gains (tf,32), scratch
  set gains id. Actual emitted-ID injection bounds CARD scratch; distinct live
  source function indices plus headroom bound total scratch over ALL frames.
  Scratch write/taint is phase-local until full DLOAD completion. Repeated scratch
  keeps frontier/set unchanged and reuses the stored 32-byte buffer.
* Table kernels already checked: Alloc:47-98 dload_table_original_fresh,
  _original_repeated, _scratch_fresh, _scratch_repeated. They are not whole-core
  allocation transport. saved_layout_head_replace protects suffix formulas;
  current-frame growth must not rewrite saved frontiers.

### Constructor tests of candidate (paper checks; no proof claims)

Entry: boundary_initial supplies empty table relation only before PHIs; source
entry success and actual function lookup/control still need assembly. Support
empty, U-definedness reflexive, saved clauses vacuous, ks singleton. Initial
source table emptiness follows run-state hypothesis; do not assume arbitrary vs.

Next: checked variable families preserve fields. Site-extending next needs the
allocation obligations above and ghost-relation monotonicity for saved suffixes.
Each source successful next plus matched active successor reconstructs source
frame_reachable; conditional source step success alone does not do that.

Block: checked enters_boundary handles PHIs after matching successful source
terminator. Branch equality, predecessor/current-block matching and jump success
remain producers. Membership V uses opaque-use for branch conditions.

INVOKE: opaque_use rules exclude retpc-derived arguments; taint_ok gives empty
operand masks (Call:221), so params get dload_param_values through evaluated
args. Recover actual callee supply via stage lookup. setup_callee gives empty
vars/allocas, same inherited frontiers. Push empty relocation frame via
layout_call_push/table_call_push; save caller definedness/control and current
layout via saved_layout_push. Must prove no live duplicate function index using
callee_first and actual call edges. Callee entry PHIs read fresh variable maps;
param ghosts are MAP op_prov, not PG=[]; keep token opaque. These paired setup
and call-reachability conclusions are still MISSING.

Return: IntRet value list must have backward successful source execution and
appropriate value/definedness relation; RETPC token need not be equal. Pop
callee relocation frame; merge restores saved caller allocation frontier/table
but adopts callee memory/shared effects (semantics:1409-1421). Use saved_layout_restore,
NOT current layout with the smaller restored frontier. Restrict memory relation
to remaining live sites; preserve fixed region. Use saved_metadata for caller
vars/params, saved U-definedness and actual control/supply witnesses for resumed
instruction. bind_outputs overwrites return values, and G/t_var are DRESTRICTed
by output names (ptrDiscipline:486-499); prove resulting output relation rather
than treating saved metadata alone as return transport. Actual source ret rule
then reconstructs source reachability. All these semantic return producers
remain MISSING.

Review question: authorize a real original-ALLOCA core transport leaf only after
separately checking site-extension monotonicity and post-allocation bounds.
The scratch runtime occurrence injection and callee-first live index certificate
are independent unresolved integration producers, not consequences of core.
