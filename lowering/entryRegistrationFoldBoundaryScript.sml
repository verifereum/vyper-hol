(* Chosen-endpoint preservation for source-valued positional registration. *)
Theory entryRegistrationFoldBoundary
Ancestors
  calldataRegistrationExec calldataMemberResourceFrame abiDecoderReentry
  abiDecoderFrame abiDecoderCoherence moduleLowering compileEnv venomState venomExecSemantics words list arithmetic finite_map

Theorem entry_registration_preserves_owned_local:
  old_id < st.cs_next_id /\ st.cs_next_id < first.cs_next_id /\
  st.cs_next_id < final.cs_next_id /\ st.cs_next_var <= first.cs_next_var /\
  FLOOKUP initial.vs_allocas old_id = SOME (p,type_memory_size tv) /\
  eval_operand dst initial = SOME (n2w p) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  val_wf tv x /\ val_in_memory tv x p initial.vs_memory /\
  ready.vs_memory = initial.vs_memory /\
  (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
    FLOOKUP ready.vs_allocas id = SOME entry) /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op ready = eval_operand op initial) /\
  FLOOKUP ready.vs_allocas st.cs_next_id = SOME (q,n) /\
  calldata_member_resource_frame ctx fn site limit_st first.cs_next_id final.cs_next_id
    first.cs_next_var q n ready out scratch ==>
  FLOOKUP out.vs_allocas old_id = SOME (p,type_memory_size tv) /\
  eval_operand dst out = SOME (n2w p) /\
  val_wf tv x /\ val_in_memory tv x p out.vs_memory
Proof
  strip_tac >> drule calldata_member_resource_observations >> strip_tac >>
  drule calldata_member_resource_endpoint >> strip_tac >>
  `FLOOKUP ready.vs_allocas old_id = SOME (p,type_memory_size tv)` by metis_tac[] >>
  `FLOOKUP out.vs_allocas old_id = SOME (p,type_memory_size tv) /\
   FLOOKUP out.vs_allocas st.cs_next_id = SOME (q,n)` by metis_tac[] >>
  `eval_operand dst out = SOME (n2w p)` by
    metis_tac[abi_decoder_operand_live_mono] >>
  asm_rewrite_tac[] >>
  irule registration_owned_footprint_value >>
  asm_rewrite_tac[] >>
  qexistsl [`ready`,`type_memory_size tv`,`(q,n)::scratch`,
    `final.cs_next_id`,`st.cs_next_id`,`p`,`old_id`] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> gvs[]
  >- (qexists_tac `st.cs_next_id` >> simp[]) >>
  fs[calldata_member_wit_def] >> first_x_assum drule >>
  strip_tac >> qexists_tac `id` >> asm_rewrite_tac[] >> decide_tac
QED

(* Probe only: the fixed full-tuple source is regrouped, never re-encoded
   as the remaining suffix. The head-size bridge is generic despite its
   historical ctor_ name. *)
Theorem entry_registration_source_cursor_step[local]:
  has_types (pre ++ at::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\
  abi_decoder_coherent ce env sf ty tv /\
  at = vyper_to_abi_type env ty /\
  off = 4 + SUM (MAP abi_member_head_size pre) ==>
  has_types ((pre ++ [at]) ++ post) ((pvs ++ [av]) ++ rest) /\
  LENGTH (pre ++ [at]) = LENGTH (pvs ++ [av]) /\
  off + abi_embedded_static_size ce.ce_struct_fields ty =
    4 + SUM (MAP abi_member_head_size (pre ++ [at]))
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[abi_decoder_header_def, SUM_APPEND]
QED

(* Empty-prefix validation uses the actual empty-registration equation,
   not a new definition of the proposed invariant. *)
Theorem entry_registration_source_cursor_empty[local]:
  has_types ats avs ==>
  has_types ([] ++ ats) ([] ++ avs) /\
  compile_register_positional_args ce []
    (4 + SUM (MAP abi_member_head_size [])) st = (ce,st)
Proof
  simp[compile_register_positional_args_def, comp_return_def]
QED

(* INVARIANT / CONSUMER LEDGER (interface audit, not an asserted theorem).

   Proposed index k, total specs S and ORIGINAL source values X:
   D = TAKE k S, R = DROP k S, XD = TAKE k X, XR = DROP k X.
   LENGTH S = LENGTH X. Keep positional outputs O of length k, with
   LIST_REL between ZIP(D,XD) and O. An output is (dst,p,id); the associated
   spec/source metadata also supplies name, ty, tv, value and capacity n.
   Each relation entry requires ce.vars[name] = PtrVar dst n,
   n = type_memory_size tv = type_memory_bytes ce ty, value_has_type tv v,
   val_wf tv v, val_in_memory tv v p s.memory,
   FLOOKUP s.allocas id = SOME(p,n), eval_operand dst s = SOME(n2w p),
   id < st.next_id, operand_live st.next_var dst. Literal allocation/output
   provenance must be retained as well (see below). Do not match source
   positions by equality of decoder descriptors.

   Fixed tuple: ATS = PRE ++ ATS_remaining; AVS = PVS ++ AVS_remaining;
   has_types ATS AVS; LENGTH PRE = LENGTH PVS = k; a positional source
   conversion for each ty/v to at/av, with a common env/sf; and fixed
   bs = enc (Tuple ATS) (ListV AVS). Calldata at 4 is bs and 4+LENGTH bs
   fits a word. The cursor is 4+SUM(MAP abi_member_head_size PRE).
   A descriptor's sz must equal abi_embedded_static_size ce.struct_fields
   ty; coherence then gives sz = abi_member_head_size at via
   ctorRegisterArgsScript.sml:109. positional_descriptor_metadata alone
   does NOT provide the sz equality. Empty and successor regrouping/cursor
   obligations are checked by the two local probes above.

   Compiler continuation: compile_register_positional_args ce R off st =
   (cer,registered), and compile_guarded_body cer F nk ut iv body rt
   registered = ((),completed), with ~block_is_terminated registered.
   Keep fn_has_code st completed fn and the singleton interval code fact;
   keep fn_inst_ids_distinct fn, budget bound and the same fn/site/limit_st.
   Carry alloca_inv, alloca_frontier_inv ctx fn site s, alloca_history fn s,
   fresh_vars_wrt limit_st s, st.next_var <= limit_st.next_var, future-id
   absence for id >= st.next_id, ~s.halted, s.current_bb = st.current_bb,
   s.inst_idx = LENGTH st.current_insts. Compilation counter monotonicity
   and environment congruence come from calldataRegistrationExecScript.sml
   registration_compile_counters:676, registration_env_fields:622 and
   registration_dec_info_env_cong:602; use coherent_env_cong separately.

   Accumulate entry_decoder_obs initial s, history at THIS s, successful
   run/result+memory transfer and all-fuel safety transfer back to initial.
   These are continuation transfers, not evidence of finite reachability.
   For k=0: D,XD,O,PRE,PVS are empty; these LIST_REL/length conditions are
   vacuous, off=4, state is initial, transfers are identities and remaining
   compilation is the original equation. Initial resources/alignment are
   premises, not consequences of empty registration.

   Successor: entrySingletonProducerScript.sml:38 supplies ready/out and
   calldata_member_success at that SAME out, for the ORIGINAL v. Its
   prefix preserves old allocations, old live operands and memory; child
   resource_frame plus entry_registration_preserves_owned_local above
   preserves every previous relation entry. Newly decoded v is appended
   to O at the parameter site's id = st.next_id. Use
   registration_unmentioned_binding (calldataRegistrationExec:584) for old
   names; it needs distinct names/name-not-in-suffix, independently of
   resource preservation. New live-operand/id bounds and future absence
   must be propagated. Resource observations at out give freshness and
   allocation/frontier properties; compose both transfers and observations
   through ready/out. Keep cumulative provenance separate from the current
   child footprint ((p,n)::scratch), which alone preserves previous values.

   TERMINAL CONSUMER AUDIT:
   - local_ptrs_reserved (compileEnv:921) is compile-only: no MemLocs,
     reserved/distinct pointer variables and immutable pointer separation.
     Reuse register_positional_args_local_ptrs; it is not a runtime result.
   - local_ptrs_rel (compileEnv:971): connect original X to lookup_scopes of
     es0 via bind_arguments; obtain lookup_var from Var dst and eval_operand,
     with n2w/w2n justified by alloca_inv/bounds. Need pairwise distinct
     parameter ids; then allocation disjointness, original values and types.
   - local_backed (compileEnv:944): reuse register_singleton_alloca_output
     (calldataRegistration:258), retaining MEM ins, ALLOCA, output [vname]
     and id=st.next_id, or registration_singleton_owned_backing
     (calldataRegistrationExec:1076). The former does NOT export literal
     operands, although its proof constructs [Lit(n2w n)]. This provenance
     is available compile-only and must be carried through the fold; it
     cannot be inferred from an allocation map entry alone.
   - state_rel (compileEnv:1465) additionally needs storage/transient,
     environment storage/transient metadata, accounts, immutables, logs,
     call-context/static flags, outcomes, requests and pending deletions.
     entry_decoder_obs frames source-state fields, not these initial
     source/machine agreements; initial-entry/package bridges remain needed.
   - stmt_state_rel (exprLoweringProps:412) also requires alloca_inv and
     alloca_room. entryInitialResources:19 alloca_frontier_inv_room supplies
     the latter with its fn/site and unit budget hypotheses. Monotonicity
     of vs_alloca_next alone is insufficient.
   - fmp_room (exprLoweringProps:258) is separate: need the entry no-DALLOCA
     or reservation/pending-call bound argument, not supplied by old-value
     preservation. Runtime immutable_alloca_sep is vacuous under ~ce_is_ctor;
     immutable_base_zero (compileEnv:1170) needs NONE or a framed zero base.
   - literal ALLOCA-size consistency (exprLoweringProps:417) does NOT follow
     from alloca_history (venom/proofs/allocaHistory:18, order/cursor only).
     abiAllocationHistory:100 abi_alloca_history_function_size suffices
     with fn_inst_ids_distinct, but needs the DIFFERENT predicate
     abi_alloca_history (abiAllocationHistory:15), containing literal sizes.
     Current singleton exports only alloca_history; neither it nor the
     resource frame supplies abi_alloca_history. Thus a separate same-state
     literal-size preservation bridge remains a real missing consumer
     boundary. Do not silently claim it from the existing endpoint.

   This file validates local-value preservation and cursor shape only.
   Full source-valued fold, bind_arguments-to-scopes, initial resources,
   fmp_room and literal-size propagation remain unproved here. All reused
   boundaries are named above with source locations; corresponding public
   signatures are in .holbuild/obj/lowering/<Theory>.sig. No invocation of
   registration_list_owned_provenance is a source-correctness argument.
*)
