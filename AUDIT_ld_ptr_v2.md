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
