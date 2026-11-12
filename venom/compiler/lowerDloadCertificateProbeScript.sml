Theory lowerDloadCertificateProbe
Ancestors
  lowerDloadStoreProducer lowerDloadFrameCertificate lowerDloadTargetGeometry
  lowerDloadPairedBoundary lowerDloadOperand lowerDloadOwnership
  lowerDloadAllocation lowerDloadOpaqueExecution
  ptrDiscipline venomExecSemantics venomState finite_map pred_set

Theorem ld_owned_empty_initial:
  !V E tn s. ld_owned_vars V E FEMPTY FEMPTY tn tn s s
Proof
  simp[ld_owned_vars_def, ld_owned_value_def] >>
  rpt strip_tac >> gvs[ld_mask_word_identity]
QED

Theorem ld_certificate_initial_boundary:
  s.vs_allocas = FEMPTY /\ FINITE keys /\ lo <= s.vs_alloca_next ==>
  ld_frame_embedding FEMPTY FEMPTY FEMPTY s s /\
  ld_owned_vars V FEMPTY FEMPTY FEMPTY entry_taint entry_taint s s /\
  (!v:string. v IN V ==> (lookup_var v s = NONE <=> lookup_var v s = NONE)) /\
  ld_alloc_account keys 0 {} s s /\
  ld_frame_bound s.vs_alloca_next FEMPTY [] FEMPTY /\
  ld_stack_bound s.vs_alloca_next [] /\ lo <= s.vs_alloca_next
Proof
  strip_tac >> drule_all ld_geometry_initial_charge >>
  simp[ld_owned_empty_initial, ld_frame_embedding_def,
       ld_owned_selection_def, ld_erase_def]
QED

Theorem ld_owned_vars_mstore:
  ld_owned_vars V E AG BH tn un (mstore p x s) (mstore q y t) <=>
  ld_owned_vars V E AG BH tn un s t
Proof
  simp[ld_owned_vars_def, mstore_def, lookup_var_def]
QED

Theorem ld_frame_embedding_mstore:
  ld_frame_embedding E L H (mstore p x s) (mstore q y t) <=>
  ld_frame_embedding E L H s t
Proof
  simp[ld_frame_embedding_def, mstore_def]
QED

Theorem ld_alloc_account_mstore:
  ld_alloc_account keys d A (mstore p x s) (mstore q y t) <=>
  ld_alloc_account keys d A s t
Proof
  simp[ld_alloc_account_def, mstore_def]
QED

Theorem ld_mstore_lookup:
  lookup_var v (mstore p x s) = lookup_var v s
Proof
  simp[mstore_def, lookup_var_def]
QED

Theorem ld_empty_outputs_prov_tvar:
  i.inst_outputs = [] ==>
  ld_step_prov AP AG L i = AG /\
  (step_taint i s s' tn).t_var = tn.t_var
Proof
  simp[ld_step_prov_def, ld_set_prov_def, step_taint_def, set_var_taint_def,
       DRESTRICT_DEF, fmap_EXT, FLOOKUP_DEF]
QED

Theorem ld_owned_vars_mstore_step:
  i.inst_outputs = [] /\ ld_owned_vars V E AG BH tn un s t ==>
  ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s (mstore p x s) tn) (step_taint i t (mstore q y t) un)
    (mstore p x s) (mstore q y t)
Proof
  strip_tac >> drule ld_empty_outputs_prov_tvar >> strip_tac >>
  simp[ld_empty_outputs_prov_tvar] >>
  irule (iffRL ld_owned_vars_tvar_cong) >>
  simp[ld_empty_outputs_prov_tvar, ld_owned_vars_mstore] >>
  qexistsl_tac [`tn`,`un`] >> simp[]
QED

(* Restoring only memory characterizes every unchanged nonmemory projection. *)
Theorem ld_mstore_nonmemory:
  (mstore p x s) with vs_memory := s.vs_memory = s
Proof
  simp[mstore_def]
QED

Theorem ld_reachable_mstore_state_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst;value] /\
  i.inst_outputs = [] /\ ~in_revert_forward fn s /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) [dst;value] ==> v IN V) /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz < dimword(:256) /\
    bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\
    (bt+sz <= ct \/ ct+cz <= bt)) /\
  op_taint tn value SUBSET count 32 /\ op_taint un value SUBSET count 32 /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t /\
  (!v:string. v IN full_names ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel CT i t = OK t' ==>
  ?s' x v y w.
    step_inst fuel CS i s = OK s' /\
    s' = mstore (w2n x) v s /\ t' = mstore (w2n y) w t /\
    eval_operand dst s = SOME x /\ eval_operand dst t = SOME y /\
    eval_operand value s = SOME v /\ eval_operand value t = SOME w /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    ld_frame_embedding E L H s' t' /\ ld_alloc_account keys d A s' t' /\
    (!v:string. v IN full_names ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    (s' with vs_memory := s.vs_memory) = s /\
    (t' with vs_memory := t.vs_memory) = t
Proof
  strip_tac >> drule_all ld_reachable_mstore_backward >>
  disch_then (qx_choose_then `s'` (qx_choose_then `x`
    (qx_choose_then `v` (qx_choose_then `y` (qx_choose_then `w` strip_assume_tac))))) >>
  qexistsl_tac [`s'`,`x`,`v`,`y`,`w`] >>
  asm_rewrite_tac[] >>
  simp[ld_frame_embedding_mstore, ld_alloc_account_mstore, ld_mstore_lookup,
       ld_mstore_nonmemory] >>
  irule ld_owned_vars_mstore_step >> simp[]
QED

(*
TYPED INTERFACE AUDIT (2026-11-04; interface_audit checkpoint)
==========================================================================
This is a source inventory, NOT a new HOL predicate or a preservation proof.
The conjunction below is a candidate interface. Missing producers are explicit.
In particular neither ld_certificate_initial_boundary nor
ld_reachable_mstore_state_backward proves this entire conjunction.

BINDERS / ALIGNMENT
------------------
vs0,s,t,s',t' : venom_state; tn,un : taint;
CS,CT : venom_context; fn,ft : ir_function; i,j : instruction;
astk,gstk : ld_saved_frame list; k,lo,d : num;
E : ((num # num), num # num # num) fmap (triple is right-associated);
L,H : (num, (num # num) # (num # num)) fmap;
AG,BH : (string, (num # num) # (num # num)) fmap;
AP,BP : ((num # num) # (num # num)) option list;
V,U : string set; keys,A : num set; live : (num # num) set;
suspended : num set list; supports : string set list;
keysets : num set list; names : string list.
Use V for all original names of fn, U={v | v IN V /\ ~retpc_var fn v}.
V must include operands AND outputs, even undefined or opaque names.
The source alignment is ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s.
Function alignment is lower_dload_function_supply supply fn = (ft,supply').
Instruction alignment is a boundary in the configured expansion, NOT equal
vs_inst_idx: ld_target_prefix CT code t0 un0 n t un handles internal phases.
A block-entry relation must identify corresponding original positions; a
complete such execution alignment is still missing. fn/ft block labels agree.

EXPLICIT COMMON CLAUSES (schematic conjunction; all constituent terms exist)
--------------------------------------------------------------------------
C1  ld_frame_embedding E L H s t
C2  LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))
C3  ld_owned_vars U E AG BH tn un s t
C4  !v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)
C5  ld_alloc_account keys d A s t /\
    d = 32 * SUM (MAP CARD suspended)
C6  ld_frame_bound t.vs_alloca_next H BP BH /\
    ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next
C7  !owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs
C8  !owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\
      bt+sz <= t.vs_alloca_next
C9  !owner other bs bt sz cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
      (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)
C10 ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t)
C11 (!v. op_taint tn (Var v) SUBSET count 32) /\
    (!v. op_taint un (Var v) SUBSET count 32)
C12 un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
    un.t_imm SUBSET tn.t_imm

C7-C9 must be reconciled with exact live selection and table restriction on
return, not replaced by geometry over all historical FDOM E. C8 is natural
(non-strict). Strict endpoints < dimword(:256) are derived only at observed
instructions using raw_mem_ok, ld_paired_live_endpoints and
ld_charged_frontier_budget. The latter consumes ld_stack_origin, a LIST_REL
of finite per-frame scratch sets with CARD bounded by source DLOAD counts,
callee_first, account, exact d and dload_headroom_ok. Those stack/count
premises need production alongside C5; an arbitrary reserve is invalid.

Saved clauses, in addition to LENGTH astk = LENGTH gstk and equal lengths of
supports/keysets/suspended, for each j < LENGTH astk, f=EL j astk, g=EL j gstk:
  ld_saved_embedded {v | v IN EL j supports /\ ~retpc_var f.lf_fn v}
    E (EL j keysets) (32 * SUM (MAP CARD (DROP (SUC j) suspended)))
    (EL j suspended) f g
  !v. v IN EL j supports ==>
    (lookup_var v f.lf_state = NONE <=> lookup_var v g.lf_state = NONE)
  !v. (case FLOOKUP f.lf_tvar v of NONE => {} | SOME m => m) SUBSET count 32
  !v. (case FLOOKUP g.lf_tvar v of NONE => {} | SOME m => m) SUBSET count 32
Also saved function/instruction alignment and saved observable projections
below are needed at resume. ld_saved_embedded alone has NONE of full-support
opaque definedness, mask bounds, interval separation or function alignment.
No saved-memory equality: merge_callee_state keeps current callee memory.

PARAMETERS / OBSERVABLES / CONTROL
---------------------------------
Selection pairing AP/BP does NOT relate s.vs_params and t.vs_params values.
For PARAM a candidate extra clause is equal parameter lengths and, for each
q below that length, ld_owned_value E (EL q AP) (EL q BP) {} {}
(EL q s.vs_params) (EL q t.vs_params), with matching selection-list lengths.
This is NOT established by C2. Parameters passed at INVOKE must first be
shown untainted by taint_ok; there is no parameter-mask field in taint_state.
If nonempty parameter masks are introduced as logical lists, each must be
SUBSET count 32 and a PARAM producer must explain how its out_taint={} is
compatible. Do not assume such lists are an existing invariant.

Observation consumers actually needed by the frozen taint row:
request_taint_transport requires current address equality, storage agreement
outside D.d_stor at that address, transient agreement outside D.d_trans there,
and C12's storage/transient subsets BEFORE a request-growing successful step.
final_taint_transport requires the same at halt, imms_agree_except D,
LENGTH s.vs_returndata = LENGTH t.vs_returndata and
(!q. q < LENGTH s.vs_returndata /\ q NOTIN D.d_ret s.vs_returndata ==>
 EL q s.vs_returndata = EL q t.vs_returndata), plus all C12 and Rt SUBSET R.
Both additionally consume actual SOURCE reachability/success/finality. Their
existential witnesses are not state-only clauses; no producer currently
closes taint_within_observation_transport's two quantified coverage premises.

For intermediate operations, agreement must be stronger than final dead-set
agreement: key_taint masks for storage/transient loads and per-key immutables
must follow source taint, not an arbitrary larger D. Candidate explicit terms:
  !a. storage_agree_except tn.t_stor
    (s.vs_accounts a).storage (t.vs_accounts a).storage
  !a. storage_agree_except tn.t_trans (s.vs_transient a) (t.vs_transient a)
  FDOM s.vs_immutables = FDOM t.vs_immutables
  !q. q IN FDOM s.vs_immutables ==>
    word_agree_except {b | (q,b) IN tn.t_imm}
      (s.vs_immutables ' q) (t.vs_immutables ' q)
The all-address storage version is sufficient but possibly stronger than
needed: ordinary writes affect only current address. A minimal split tracks
current storage with masks and equality elsewhere; CALL adoption must prove
that split. No checked general producer for either version yet.
Non-storage account fields require
  !a. (s.vs_accounts a with storage := (t.vs_accounts a).storage)=t.vs_accounts a
for BALANCE/SELFBALANCE/EXTCODE* and external requests. Code/data/environment
and call context equality feed unchanged environment reads and CODECOPY:
  s.vs_call_ctx=t.vs_call_ctx /\ s.vs_code=t.vs_code /\
  s.vs_data_section=t.vs_data_section /\ s.vs_outcomes=t.vs_outcomes.
Other environment projections must be checked in step_inst_base before a
single common equality package is chosen. Labels equality is ALREADY in C3.
vs_params values relocate; vs_return_pc_token deliberately need not agree.
GAS reads cc_gas, not an allocation frontier: no gas decrement is introduced
by step_inst in the expansion. RETPC_PARAM values are excluded from U, while
C4 retains their definedness. Do not extrapolate this to arbitrary GAS values.
vs_returndata needs exact equality before RETURNDATACOPY if its bytes may be
consumed (out_taint does not track a separate returndata mask); at terminal
RETURN use the weaker masked slice relation above. Length equality suffices
for RETURNDATASIZE and bounds but not copy contents. Outcome equality and
request-change equivalence feed ld_adoption_guard_agreement; full request
list equality is not needed for adoption. Request payloads/snapshots need
request_agree_except D only if proving dead_result_rel, not this taint row.
Similarly logs, pending_deletions and vs_halted equality are requirements of
dead_result_rel, NOT of final_taint_transport. Control still needs matching
halt/nonhalt classifications, prev/current block labels and an instruction
position correspondence for reconstruction. No numeric equality of indices
across expanded blocks. Frame FMP projections are unaffected in raw phase;
DALLOCA/FMP opcodes are excluded, not simulated using arbitrary FMP equality.

SOURCE FACTS AND EXACT CHECKED PRODUCER LIMITS
--------------------------------------------
o1_src_inv_def provides reserved_intervals_wf, mem_inv raw_mem_ok, all fn_eom
NONE, no DALLOCA, existential lo with fixed_region_reserved and ptr_discipline,
source taint_within, fmp_free_ctx, mem_inv dload_offset_ok/headroom_ok.
ptr_discipline_def supplies lo<=vs0.next, existential P with EVERY(fn_ptr_ok P),
and access_ok, taint_ok, allocas_from for SOURCE frame_reachable states.
Recover P once; source annotated reachability erases to frame_reachable.
These facts give NO target discipline, successor certificate or source run.
o1_run_state_ok supplies o1_initial_state_ok, fmp=initial_fmp, code_layout_valid;
use the actual entered entry state (PHIs already evaluated), not vs0 blindly.
Shape supplies membership/opaque-use/well-formed control through its component
facts; it is not definite assignment (o1_pre_walk_inv is strictly stronger).

Seed signature: s.allocas=FEMPTY /\ FINITE keys /\ lo<=s.next ==>
C1(empty) /\ C3(shared entry_taint) /\ C4(reflexive) /\ C5(keys,0,{}) /\
C6(empty frame/stack). This is E0159, theorem ld_certificate_initial_boundary;
it does not initialize all observables/control/parameter clauses at entry.
C10/C11/C12 and shared projections are reflexive/empty at a genuinely shared
seed; their entry PHI transfer and reconstructed reachability still need proof.

Store signature: ld_reachable_mstore_state_backward assumes source annotated
reachability, ptr_discipline, EVERY fn_ptr_ok expressed pointwise, MSTORE
shape, NOT in_revert_forward, C3, operand support, provenance-owner inclusion,
strict live endpoints, C9, both value masks bounded, C10,C1,C5,C4 and target
OK. It produces source OK, evaluated operands, post C10,C3,C1,C5,C4 and
restore-memory equations. It DOES NOT produce its geometry/mask/support
premises or advance annotated alignment. step_taint_nonmemory (task theory)
adds unchanged t_stor/t_trans/t_imm for opcodes outside
[SSTORE;TSTORE;ISTORE;CALL;STATICCALL], so gives post C12 for MSTORE from C12.
Restore-memory equations preserve observable projections for this opcode
only; they do not prove a general observable invariant (E0160/E0161).

Existing conditional interfaces inspected by signature:
- ld_nonopaque_assign_backward: membership, shape, C3/C4, support, target OK
  ==> source OK and post C3/C4; no post geometry, account or memory clause.
- ld_nonopaque_phis_backward: C3/C4, equal prev_bb, membership/support,
  target eval_phis OK ==> source eval_phis OK and post C3/C4.
- ld_retpc_param_backward: RETPC_PARAM shape,C3/C4,target OK ==> source OK,
  post C3/C4; no token equality required.
- ld_owned_mload_access_backward: C3,support,clean address,access_ok,
  non-revert, strict source provenance endpoints and ALL table target
  endpoints, R covers fixed/live,C10,target OK ==> source OK,post C3 only.
  Its all-history endpoint premise is stronger than C8; do not silently infer
  it from live geometry. Adapt/reuse interface only after PLAN authorization.
- ld_paired_live_endpoints: C1,C2,saved embedding,target frame/stack bounds
  ==> target live endpoint <= target frontier. Not separation or strictness.
- ld_saved_charge_push_pop: head saved embedding and indexed tail embeddings
  ==> pushed indexed embedding and saved account/frontier equation. No callee
  completion. ld_nonopaque_ret_backward gives a SOURCE IntRet STEP, not run.
- ld_alloca_fresh_byte_rel: paired exec_alloca, pre byte relation and target
  fresh-range disjointness ==> extended byte relation. No whole certificate.

EXHAUSTIVE OPCODE PARTITION / MISSING SUCCESSOR OUTPUTS
-----------------------------------------------------
Each opcode below occurs once (venomInst.opcode); rows are semantic work,
not claims that existing similarly named helpers discharge the whole row.
Every admitted row still needs complete relevant C1-C12, observable/control,
saved clauses and produced source annotated successor, unless terminal.

1 ADD SUB OFFSET: owned offset helpers exist; integrate C4/masks/geometry and
  nonopaque operand support, plus scalar-left ADD and clean scalar fallback.
2 MUL Div SDIV Mod SMOD Exp ADDMOD MULMOD SLT SGT ISZERO AND OR XOR NOT
  SIGNEXTEND BYTE: pure scalar interfaces conditional on scalar/clean operands;
  derive those premises from fn_ptr_ok, taint_ok and opaque-use first.
3 EQ LT GT: same-owner ordered comparison needs positive-size/no-wrap access
  classification; no cross-owner numeric comparison shortcut.
4 SHL SHR SAR: shift_taint masked word lemmas exist; produce mask bounds and
  full simultaneous successor, not value agreement alone.
5 ASSIGN PHI RETPC_PARAM: nonopaque interfaces above; integrate other clauses
  and alignment, including block PHIs' parallel pre-state semantics.
6 PARAM: missing parameter VALUE relation/definedness producer; selection-only
  AP/BP insufficient. FMP_PARAM excluded with FMP raw convention constraints.
7 MLOAD ILOAD: masked reads conditional on related byte ranges; ILOAD uses
  actual memory-read semantics, inspect separately from ISTORE immutables.
8 MSTORE: checked partial simultaneous boundary above. MSTORE8 MCOPY: no
  complete producer; MCOPY must transport overlap-safe source slice/taints.
9 SLOAD TLOAD SSTORE TSTORE ISTORE: need masked keys/values and nonmemory
  state/taint production, domain preservation for immutable updates.
10 ALLOCA: original fresh/repeated sites separately; owner extension, account,
   new_site taint, live table retention/separation. Repeat ignores new size.
11 DLOAD DLOADBYTES: target macro phases ALLOCA/ADD/CODECOPY/MLOAD or
   ADD/CODECOPY. Need scratch disjointness, clear scratch load, fresh names,
   offset no-wrap and alignment; existing local macro consumers insufficient.
12 JMP JNZ DJMP: clean/equal control operands, block label transfer, parallel
   PHIs, source annotated block successor; no unconditional index equality.
13 INVOKE RET: setup and local return interfaces conditional; full recursive
   source completion and terminal annotated provenance missing. Saved support,
   parameters, masks, exact tail charges and current-memory return merge.
14 RETURN STOP: produce source Halt/final_taint, returndata masks/subsets and
   final observable clauses. SELFDESTRUCT: additionally account changes and
   pending deletion semantics, not just a STOP rewrite.
15 REVERT INVALID ASSERT_UNREACHABLE SINK: inspect Abort versus Halt outcomes;
   abort alone imposes no final_taint but may lie on revert-forward prefixes.
16 ASSERT NOP: successful unchanged control/state except ordinary index step;
   assert guard must be produced equal when normal, not assumed.
17 CALLER CALLVALUE CALLDATALOAD CALLDATASIZE ADDRESS ORIGIN GASPRICE GAS
   GASLIMIT COINBASE TIMESTAMP NUMBER PREVRANDAO CHAINID SELFBALANCE BALANCE
   BLOCKHASH BASEFEE CODESIZE EXTCODESIZE EXTCODEHASH RETURNDATASIZE BLOBHASH
   BLOBBASEFEE MEMTOP INITIAL_FMP: environment/field reads; MEMTOP specifically
   reads rounded LENGTH vs_memory (not vs_alloca_next); scratch writes can
   change it. It must be excluded or separately justified, not grouped as a
   shared constant. Check INITIAL_FMP raw admission separately.
18 CALLDATACOPY CODECOPY EXTCODECOPY RETURNDATACOPY: source bytes/code/data
   agreement and destination range transport, returndata bounds, post C10.
19 SHA3 LOG: clean memory observations from taint_ok outside about_to_revert;
   clean operand/range transport. LOG equality not itself a taint-row goal.
20 CALL STATICCALL: request-growing paths, outcome consumption/adoption guard,
   pre-request taint coverage; precompile paths may have NO new request.
21 DELEGATECALL CREATE CREATE2: concrete nested external execution sees source
   storage/transient untainted by taint_ok; not handled by shared-outcome CALL
   proof. Produce byte inputs and resulting accounts/taints/requests.
22 DALLOCA DRET GETFMP SETFMP RETFMP BUMP: excluded by raw/FMP-free hypotheses;
   prove exclusion at reachable source/target points rather than assuming it.

NORMAL / REVERT-FORWARD MODES AND NEXT DECOMPOSITION
--------------------------------------------------
Normal range consumers require ~in_revert_forward fn s. access_ok weakens in
revert-forward execution; taint_ok's clean-memory observation premise is
conditional on ~about_to_revert fn i s. Thus neither MSTORE nor MLOAD normal
interfaces can cover that mode. A separate mode must show either matched
remaining observations or that the forward suffix reaches Revert_abort
without request/halt observations. That property is NOT yet proved and must
include internal calls and target macro phases; cannot just discard the path.

Concrete next low-risk candidates for strategist selection:
(a) derive/expose original-name operand support and nonopaque use from actual
shape/member premises (no new total-definedness assumption);
(b) global variable-mask <=32 preservation for step_taint/PHI/entry/return,
including saved t_var restrictions; parameter values remain separately open;
(c) initialize C10-C12 and explicit shared projections at the entered seed;
(d) audit/exclude MEMTOP and raw FMP reads before environment producer work.
Then decompose PARAM, scalar/copy, memory, nonmemory, allocation/macros, calls,
revert mode and observations in production. Do NOT start global execution
induction until those successor-producing interfaces exist. In particular,
no conditional RET or final transport lemma proves backward coverage.
*)

(*
CLOSURE AUDIT (2026-11-05; closure_audit checkpoint)
=================================================
This inventory does not assert a preservation theorem. R below is notation
in this comment only, with the binders/types of the preceding audit:
 R(E,live,keys,lo,t) =
 !owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
   bt+sz <= lo \/ (?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)).

TRANSITION / PRODUCER / GAP
Shared seed: live={} makes R vacuous. ld_certificate_initial_boundary gives
C1,C3,C4,C5,C6 with empty local maps, but does not state R or live={}.
Original ALLOCA: ld_frame_embedding_target gives a witness ONLY for entries
of current H. Neither ld_live nor C7 says every live owner belongs to H.
Need new-site extension AND old-live retention; account/byte ALLOCA lemmas
alone do not produce R. Repeated ALLOCA must retain the cached size.
Scratch macro: ld_load_prefix_live_representation preserves assumed R for
live' SUBSET live and n<=4. ld_load_semantic_backward composes this with
source OK,C3,C10,C5. It does not initialize R or admit newly live owners.
INVOKE: R with global lo is NOT inductively closed. setup_callee_def clears
vs_allocas while retaining vs_alloca_next. ld_call_selected retains argument
owners; ld_live_def also retains all selected saved caller sites. Thus take
one caller allocation (bt,32) with bt>=lo and pass it as an argument: at child
entry its owner remains live, bt+32>lo, and the child allocation map is empty.
This is a concrete interface obstruction, NOT a counterexample to the task.
No claim that this schematic trace is a checked program counterexample.
ld_alloc_account_enter/ld_call_geometry correctly account for empty child
maps; neither supplies R. ld_saved_embedded only pairs selections, layout,
values and account: it contains no suspended-site floor certificate.
Return: merge_callee_state_def restores caller allocation map/frontier but
KEEPS callee memory. ld_return_geometry restores bounds/account; saved
embedding return lemmas restore layout and variables conditionally. R for
surviving caller owners can use saved witnesses, not child-map witnesses.
Callee-only owners must be removed from live/table before caller restoration;
ld_saved_embedded_table_cong is a conditional congruence, not that producer.

REPAIR SHAPES (proposed obligations, NOT existing theorems)
Keep global lo in C10. Introduce a separate logical frame floor f, with
 lo<=f /\ allocas_from f t /\ f<=t.vs_alloca_next, and require
 !owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
   bt+sz<=f \/ (?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j=SOME(bt,sz)).
A generalized scratch separation consumer should then conclude
 ?p. f<=p /\ p+32<dimword(:256) /\
   ((FLOOKUP t.vs_allocas id=NONE /\ p=t.vs_alloca_next) \/
     FLOOKUP t.vs_allocas id=SOME(p,32)) /\
   (!aa bb. ((aa=bb /\ aa<lo) \/ ld_site_bytes E live aa bb) ==>
     bb<p \/ p+32<=bb).
Its remaining premises are ld_live_scratch_separation's account, id/key,
nonoverlap, validity and headroom premises, with allocation floor f rather
than lo. Do NOT use f for the identity part of the byte relation: relocated
caller bytes below f are not generally equal at equal numeric addresses.
Existing ld_live_scratch_separation is the special case f=lo; changing its
statement is not authorized. Generalize at the strategy level without
creating a near duplicate or rewriting accepted statements here.

Intended entry producer, binders E live keys lo f t child fn args:
 setup_callee fn args t=SOME child /\ lo<=t.vs_alloca_next /\
 (!o bs bt sz. o IN live /\ ld_site_entry E o bs bt sz ==>
   bt+sz<=t.vs_alloca_next) ==>
 allocas_from t.vs_alloca_next child /\
 (!o bs bt sz. o IN live /\ ld_site_entry E o bs bt sz ==>
   bt+sz<=t.vs_alloca_next \/
   (?j. j NOTIN keys /\ FLOOKUP child.vs_allocas j=SOME(bt,sz))).
ld_setup_callee_floor already supplies the first clause. C8/paired endpoints
supply the second's premise. The callee floor is the saved target frontier,
not an arbitrary reserve. Preserve it across all child steps. Return must
recover the SAVED caller floor, map witnesses and live restriction, while
transporting C10 over current callee memory (ld_owned_return_memory and
ld_site_bytes_return_memory are conditional tools, not completed execution).

MACRO STRUCTURAL MATRIX (C rows refer to preceding audit)
DLOAD: C3,C10,C5 and fixed-live R checked by ld_load_semantic_backward.
C1: old local-map lookup preservation checked by ld_load_prefix_old_lookup;
needs consolidated embedding transport (target scratch is absent from H).
C2: source/target original output provenance becomes NONE; target ADD temp
is also NONE. Need quantified paired-selection update plus unchanged AP/BP.
C4: ld_reachable_load_owned gives ownership, not full opaque definedness;
need original-name lookup statement including out and excluding av,bv.
C6: endpoint bounds must advance with nondecreasing target frontier; frame
and stack bound monotonicity must be assembled with preserved params/maps.
C7: post selected/live shrink after out overwrite; no new original owner.
C8,C9: E unchanged, live may shrink; need endpoint/frontier and subset proof.
C11: output MLOAD clean (ld_load_completed_output), scratch/temp masks need
boundedness integration. C12 and all observable shared fields: no account,
storage, transient, immutable operation occurs, but no whole macro transport
has yet assembled these equalities with step_taint. Saved frames unchanged;
scratch charge A inserts a.inst_id, so indexed saved charges (tail sums) stay
unchanged; exact global charge/count support still needs integration.

DLOADBYTES: ld_reachable_bytes_memory gives source OK and C10 only.
C1,C5: ld_bytes_completed_projections preserves allocation fields and
ld_alloc_account_transport can lift them; source is memory-only.
C2,C3,C4: ld_bytes_completed_lookup gives original lookups outside av;
original outputs must be [] and av fresh in full V. Need t_var/provenance
transport at the complete two-step boundary, not compiler ADD discipline.
C6: ld_bytes_completed_params plus unchanged allocation fields; same bounds.
C7-C9: same original locals/params/provenance/live and E, no owner extension.
C11-C12: require completed taint transport; memory mask equation alone does
not cover variable masks or storage/transient/immutable projections.
Saved clauses: unchanged frames/charges, but table/live compatibility must
be preserved by a consolidated boundary. Observables/control and source
annotated successor remain separate missing integration rows for BOTH macros.

RECOMMENDATION
First generalize scratch separation to distinguish fixed lo and frame floor,
with a call-entry and saved-return floor/witness probe; do not build a larger
macro assembler over global R. Then consolidate all structural macro rows
using existing effect transports. No global execution induction is justified
by this inventory; revert-forward and observation production remain open.
*)

(* Frame-floor probe follow-up (2026-11-05).
   Checked lowerDloadLiveScratch.ld_live_scratch_separation_floor now has
   independent lo/f; the original separation theorem is a specialization.
   lowerDloadFrameRepresentation exports ld_representation_empty, _enter,
   _return. Entry representation uses the endpoint bound only; combine with
   ld_setup_callee_floor for floor facts. Return representation uses SAVED R
   and explicit surviving-entry inclusion, not an assumed post-return R;
   combine with ld_return_floor. ld_step_floor (non-INVOKE) and
   ld_enters_block_floor preserve allocas_from f and f<=frontier within a
   frame; calls reset f to the saved target frontier, returns restore saved f.
   Still missing: actual call transition must produce entry endpoints from
   C8/ld_paired_live_endpoints and retained-live inclusion (including saved
   frames and argument selections). Actual return must produce the surviving
   entry implication from live/table restriction, not just table congruence.
   Ordinary ALLOCA must preserve old R and insert a witnessed new owner;
   repeated ALLOCA must preserve cached geometry. Neither these probes nor
   saved embedding proves those producers, macro C1-C12 closure, completion
   of calls, revert-forward execution, or observation coverage.
*)

(* Concrete live transition checkpoint: lowerDloadFrameRepresentation now
   proves ld_live_call_shape and ld_live_call_endpoints for the pushed saved
   frame plus mapped argument selectors, consuming the six paired-geometry
   hypotheses rather than assuming endpoints. ld_live_restrict_shape uses
   arbitrary restriction keys; ld_live_return_entries produces survivor
   inclusion from table agreement on SAVED live owners. This last agreement
   is still an explicit invariant input: C1-C12 do not assert preservation
   of an earlier saved table's entries across intervening owner allocation.
   Fresh-owner extension needs a domain/fresh-serial bound; return table
   restriction needs retention on all saved live owners. Existing conditional
   table congruence lemmas do not produce that temporal agreement. No whole
   call completion or memory restoration follows from these selector facts.
*)

(* Saved-table support checkpoint: lowerDloadTableSupport proves projection
   of every saved-live support into the current live set, then reuses
   ld_alloca_owner_extension to transport OLD snapshot agreement through the
   concrete fresh/cached ALLOCA table update. ld_return_pruned_snapshot and
   ld_return_pruned_entries retain the actual restored-live support under
   DRESTRICT, including older suspended frames. No global table-domain bound
   is required: annotated serial freshness is needed only on live owners.
   The remaining temporal execution induction must carry agreement with each
   saved snapshot, use identity on unchanged tables, allocation transport on
   ALLOCA and retention on return. These local transitions do not establish
   whole-call completion, successor representation for a newly allocated
   owner, or full macro/observation closure. No saved memory is restored.
*)

(* Ordinary ALLOCA representation checkpoint: ld_alloca_live_representation
   now produces concrete post-selection/provenance live-site representation
   at the unchanged frame floor f. Old live owners keep their table entries
   and existing target allocation witnesses; the fresh site is witnessed by
   the ordinary instruction ID outside scratch keys. Cached ALLOCA adds no
   live site. This geometry result permits zero sizes and does not change lo.
   Whole ALLOCA certificate assembly, macro C1-C12 closure, call completion,
   revert-forward production, observations and temporal execution induction
   remain separate unresolved obligations.
*)
