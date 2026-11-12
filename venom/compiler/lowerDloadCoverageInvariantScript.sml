Theory lowerDloadCoverageInvariant
Ancestors
  lowerDloadSupplySegment lowerDloadSharedState lowerDloadFrameCertificate lowerDloadCertificateProbe
  lowerDloadOwnership lowerDloadPairedBoundary lowerDloadAllocation
  venomExecSemantics ptrDiscipline finite_map

(* Data at original-instruction boundaries, NOT the complete coverage
   invariant. Memory, live geometry, control and macro anchors are separate. *)
Definition ld_frame_data_def:
  ld_frame_data V U E L H AP BP AG BH tn un s t <=>
    ld_frame_embedding E L H s t /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
    ld_owned_vars U E AG BH tn un s t /\
    (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    ld_shared_state tn un s t
End

Theorem ld_frame_data_embedding:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_frame_embedding E L H s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_params:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  LIST_REL (ld_owned_selection E) AP BP
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_provenance:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  !v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_vars:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_owned_vars U E AG BH tn un s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_definedness:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  !v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_shared:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_shared_state tn un s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_initial:
  s.vs_allocas = FEMPTY ==>
  ld_frame_data V U FEMPTY FEMPTY FEMPTY [] [] FEMPTY FEMPTY
    entry_taint entry_taint s s
Proof
  simp[ld_frame_data_def, ld_frame_embedding_def, ld_erase_def,
       ld_owned_selection_def, ld_owned_empty_initial, ld_shared_state_identity]
QED

(* This is genuinely anchored at source entry. The reflexive second conjunct
   does not identify s1 with the transformed program's entered state. *)
Theorem ld_frame_data_source_entry:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>) s1 /\
  s1.vs_allocas = FEMPTY /\ active_inst fn inst s1 ==>
  ld_annotated_reachable vs0 ctx [] 0 FEMPTY [] FEMPTY
    entry_taint fn inst s1 /\
  ld_frame_data V U FEMPTY FEMPTY FEMPTY [] [] FEMPTY FEMPTY
    entry_taint entry_taint s1 s1
Proof
  strip_tac >> conj_tac
  >- (irule ld_annotated_reachable_entry >> simp[] >>
      goal_assum (drule_at Any)) >>
  irule ld_frame_data_initial >> simp[]
QED

(* Indexed saved-stack probe: budgets count strictly older suspended scratch.
   This explicit schema is not yet a global coverage invariant. *)
Theorem ld_saved_indexed_empty:
  LENGTH ([]:ld_saved_frame list) = LENGTH ([]:ld_saved_frame list) /\
  LENGTH ([]:string set list) = LENGTH ([]:ld_saved_frame list) /\
  LENGTH ([]:num set list) = LENGTH ([]:ld_saved_frame list) /\
  LENGTH ([]:num set list) = LENGTH ([]:ld_saved_frame list) /\
  (!j. j < LENGTH ([]:ld_saved_frame list) ==>
    ld_saved_embedded
      {v | v IN EL j ([]:string set list) /\
           ~retpc_var (EL j ([]:ld_saved_frame list)).lf_fn v}
      E (EL j ([]:num set list))
      (32 * SUM (MAP CARD (DROP (SUC j) ([]:num set list))))
      (EL j ([]:num set list)) (EL j ([]:ld_saved_frame list)) (EL j ([]:ld_saved_frame list)) /\
    (!v. v IN EL j ([]:string set list) ==>
      (lookup_var v (EL j ([]:ld_saved_frame list)).lf_state = NONE <=>
       lookup_var v (EL j ([]:ld_saved_frame list)).lf_state = NONE)) /\
    (!v. (case FLOOKUP (EL j ([]:ld_saved_frame list)).lf_tvar v of
      NONE => {} | SOME m => m) SUBSET count 32) /\
    (!v. (case FLOOKUP (EL j ([]:ld_saved_frame list)).lf_tvar v of
      NONE => {} | SOME m => m) SUBSET count 32))
Proof
  simp[]
QED

Theorem ld_saved_indexed_cons:
  (LENGTH (g::gs) = LENGTH (f::fs) /\
   LENGTH (V::supports) = LENGTH (f::fs) /\
   LENGTH (keys0::keys) = LENGTH (f::fs) /\
   LENGTH (A::suspended) = LENGTH (f::fs) /\
   (!j. j < LENGTH (f::fs) ==>
     ld_saved_embedded
       {v | v IN EL j (V::supports) /\ ~retpc_var (EL j (f::fs)).lf_fn v}
       E (EL j (keys0::keys))
       (32 * SUM (MAP CARD (DROP (SUC j) (A::suspended))))
       (EL j (A::suspended)) (EL j (f::fs)) (EL j (g::gs)) /\
     (!v. v IN EL j (V::supports) ==>
       (lookup_var v (EL j (f::fs)).lf_state = NONE <=>
        lookup_var v (EL j (g::gs)).lf_state = NONE)) /\
     (!v. (case FLOOKUP (EL j (f::fs)).lf_tvar v of
       NONE => {} | SOME m => m) SUBSET count 32) /\
     (!v. (case FLOOKUP (EL j (g::gs)).lf_tvar v of
       NONE => {} | SOME m => m) SUBSET count 32))) <=>
  (ld_saved_embedded {v | v IN V /\ ~retpc_var f.lf_fn v}
     E keys0 (32 * SUM (MAP CARD suspended)) A f g /\
   (!v. v IN V ==>
     (lookup_var v f.lf_state = NONE <=> lookup_var v g.lf_state = NONE)) /\
   (!v. (case FLOOKUP f.lf_tvar v of NONE => {} | SOME m => m) SUBSET count 32) /\
   (!v. (case FLOOKUP g.lf_tvar v of NONE => {} | SOME m => m) SUBSET count 32) /\
   LENGTH gs = LENGTH fs /\ LENGTH supports = LENGTH fs /\
   LENGTH keys = LENGTH fs /\ LENGTH suspended = LENGTH fs /\
   (!j. j < LENGTH fs ==>
     ld_saved_embedded
       {v | v IN EL j supports /\ ~retpc_var (EL j fs).lf_fn v}
       E (EL j keys) (32 * SUM (MAP CARD (DROP (SUC j) suspended)))
       (EL j suspended) (EL j fs) (EL j gs) /\
     (!v. v IN EL j supports ==>
       (lookup_var v (EL j fs).lf_state = NONE <=>
        lookup_var v (EL j gs).lf_state = NONE)) /\
     (!v. (case FLOOKUP (EL j fs).lf_tvar v of
       NONE => {} | SOME m => m) SUBSET count 32) /\
     (!v. (case FLOOKUP (EL j gs).lf_tvar v of
       NONE => {} | SOME m => m) SUBSET count 32)))
Proof
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV
    (HO_REWR_CONV arithmeticTheory.FORALL_NUM))) >>
  simp[] >> metis_tac[]
QED

Theorem ld_saved_indexed_frame:
  LENGTH gs = LENGTH fs /\ LENGTH supports = LENGTH fs /\
  LENGTH keys = LENGTH fs /\ LENGTH suspended = LENGTH fs /\
  (!j. j < LENGTH fs ==>
    ld_saved_embedded
      {v | v IN EL j supports /\ ~retpc_var (EL j fs).lf_fn v}
      E (EL j keys) (32 * SUM (MAP CARD (DROP (SUC j) suspended)))
      (EL j suspended) (EL j fs) (EL j gs) /\
    (!v. v IN EL j supports ==>
      (lookup_var v (EL j fs).lf_state = NONE <=>
       lookup_var v (EL j gs).lf_state = NONE)) /\
    (!v. (case FLOOKUP (EL j fs).lf_tvar v of
      NONE => {} | SOME m => m) SUBSET count 32) /\
    (!v. (case FLOOKUP (EL j gs).lf_tvar v of
      NONE => {} | SOME m => m) SUBSET count 32)) /\
  j < LENGTH fs ==>
  ld_saved_embedded
    {v | v IN EL j supports /\ ~retpc_var (EL j fs).lf_fn v}
    E (EL j keys) (32 * SUM (MAP CARD (DROP (SUC j) suspended)))
    (EL j suspended) (EL j fs) (EL j gs)
Proof
  simp[]
QED

Theorem ld_owned_selection_owner_domain:
  ld_owned_selection E (SOME (owner,(bs,sz))) pt ==> owner IN FDOM E
Proof
  simp[ld_owned_selection_def, lowerDloadLifetimeTheory.ld_site_entry_def,
       FLOOKUP_DEF] >> metis_tac[]
QED

(* LIVE-SUPPORT AUDIT (C2.package.stack).
   ld_live_def is the disjunction of current ld_selected L AP AG and a
   selected local/parameter/provenance site of any saved frame MEM f astk.
   ld_selected_def covers all three sources, not only allocation locals.
   This matches the support needed by saved_embedded; its source selections
   identify owners in E by ld_owned_selection_owner_domain. The target
   selection has the same owner, and frame_embedding allows target-only
   scratch entries instead of demanding erase H = target.vs_allocas.
   No mismatch was found in the live-set definition. On table extension,
   existing supported entries must be retained. On return, restrict E only
   after identifying the selections of the surviving current/saved frames:
   historical FDOM E is NOT a live geometry bound, and callee memory must
   NOT be replaced by a saved caller memory snapshot. Indexed cons above
   computes the head's inherited scratch charge from suspended_tail only;
   it proves neither actual call push nor return preservation. *)

(* CONFIGURED ALIGNMENT / ENTRY AUDIT (C2.package.alignment_audit).
   These are candidate HOL clauses and producer interfaces, NOT definitions
   or proved simulation assertions. In particular the data probes above do
   not establish any of the memory/geometry obligations below.

   1. Configured supply, not legacy arithmetic instruction IDs.
   lower_dload_configured_with_supply_def starts init_ir_supply unit and
   folds unit/context/functions/blocks/instructions left to right. For a
   selected function retain lower_dload_function_supply a fn = (gn,b).
   Exact incoming block and instruction supplies can be witnessed by:
     fn.fn_blocks = bpre ++ bb::bpost /\
     lower_dload_blocks_supply a bpre = (qpre,a0) /\
     lower_dload_block_supply a0 bb = (gb,a3) /\
     lower_dload_blocks_supply a3 bpost = (qpost,b) /\
     gn.fn_blocks = qpre ++ gb::qpost /\
     bb.bb_instructions = pre ++ i::post /\
     lower_dload_insts_supply a0 pre = (p,a1) /\
     lower_dload_inst_supply a1 i = (code,a2) /\
     lower_dload_insts_supply a2 post = (tail,a3) /\
     gb.bb_instructions = p ++ code ++ tail.
   Existing lower_dload_function_supply_active_origin gives existential
   block origin and instruction segment inversion. It does not expose the
   preceding block fold qpre: use configured fold equations if that stronger
   witness is needed. Existing lower_dload_insts_supply_segment_reconstruct
   and lower_dload_insts_supply_segment_index already give reconstruction
   and EL; do not duplicate them.

   2. Boundary/phase positions (supplies and segments as in 1):
     lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     lookup_block t_anchor.vs_current_bb gn.fn_blocks = SOME gb /\
     s.vs_current_bb = t_anchor.vs_current_bb /\
     s.vs_prev_bb = t_anchor.vs_prev_bb /\
     s.vs_inst_idx = LENGTH pre /\
     t_anchor.vs_inst_idx = LENGTH p.
   Phase envelope additionally has
     ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
     ld_frame_data V U E L H AP BP AG BH tn un_anchor s t_anchor /\
     ld_target_prefix CT code t_anchor un_anchor n t un /\
     n < LENGTH code.
   Memory/live geometry and stack conjuncts remain separate, required at
   the anchor, not at an intermediate ALLOCA/ADD/CODECOPY state.
   n=LENGTH code must trigger source-step completion, never EL n code.
   ld_target_prefix alone proves neither block selection nor prev_bb.
   Missing producer: configured successor alignment from the segment
   equations and a successful expansion, yielding source index SUC(LENGTH
   pre) and target index LENGTH p + LENGTH code (plus corresponding next
   segment). No new independent completed-run simulation is needed.

   3. Name support / scratch.
     V = set (fn_ir_vars fn) /\ U = {v | v IN V /\ ~retpc_var fn v}
   is the candidate support. ld_original_operand_support and
   ld_original_output_support cover uses AND outputs;
   ld_original_nonopaque_operand_support handles observable uses.
   Definedness must still quantify all V, including RETPC/opaque names;
   clean-value agreement over U alone does not cover ASSIGN/PHI of tokens.
   Scratch keys must be generated by the actual configured fold for this
   fn (the ALLOCA head of each well-shaped DLOAD code in 1), not by legacy
   lower_dload_inst or by arbitrary numeric ranges. Candidate membership:
     id IN keys <=> ?bb a0 a1 a2 pre i post p code.
       MEM bb fn.fn_blocks /\ bb.bb_instructions = pre ++ i::post /\
       lower_dload_insts_supply a0 pre = (p,a1) /\
       lower_dload_inst_supply a1 i = (code,a2) /\
       i.inst_opcode = DLOAD /\
       (?op out. i.inst_operands=[op] /\ i.inst_outputs=[out]) /\
       id = (HD code).inst_id
   with a0 additionally tied to the block prefix in 1 (existential a0 by
   itself is UNSOUND as a configured key description). Existing
   lower_dload_function_supply_contract / ld_ids_supply_ok and supply
   coverage give fresh IDs; a packaged configured key/name producer is
   missing, not a license to equate target allocas with erase H.

   4. Entry witnesses.
   Given source entry lookup, fn_entry_label fn=SOME lbl, and
     z = vs0 with <|vs_prev_bb:=NONE; vs_current_bb:=lbl; vs_inst_idx:=0|>,
   lower_dload_function_supply_enters_block proves
     enters_block gn z s1 <=> enters_block fn z s1.
   Hence an actual target entered witness can serve as the source entered
   witness at TOP entry: both start from this SAME z, not arbitrary related
   states. lower_dload_block_supply_phis and
   lower_dload_insts_supply_eval_phis/phi_length are already proved.
   ld_annotated_reachable_entry plus active source instruction and empty
   allocas yields the source annotation. o1_initial_state_ok_def supplies
   initial empty vars/allocas; first_block_no_phi from o1_fn_shape_def
   supplies unchanged entry data (no PHI result updates).
   Missing packaged initialization signature: from ctx_pass_stage,
   o1_ctx_shape, o1_run_state_ok and an actual target frame_reachable_entry
   witness, produce the configured fn/gn supplies, source entered active
   instruction, source annotation and boundary phase witnesses in 1-2,
   with ld_frame_data and the required geometry/memory initialization.
   The existing ld_frame_data_source_entry proves only source/reflexive
   data and cannot replace this producer. At CALL entry states are not
   equal: PHI evaluation equality on a single state is insufficient for
   related argument values. Paired PHI preservation remains required.

   5. PARAM: the apparent top-entry length conflict has a shape resolution,
   NOT an initial-state restriction. o1_run_state_ok_def and
   o1_initial_state_ok_def do NOT require vs_params=[]. Annotated entry AP
   is [] nevertheless. But o1_fn_shape_def requires entry_fn_no_params,
   whose definition excludes every is_param_opcode in the entire entry
   function. Thus no successful PARAM step there needs the length premise.
   Candidate parameter envelope, without imposing any extra task hypothesis:
     (CS.ctx_entry = SOME fn.fn_name /\ AP=[] /\ BP=[] /\
      entry_fn_no_params fn) \/
     (LENGTH AP = LENGTH s.vs_params /\
      LENGTH BP = LENGTH t.vs_params /\
      LENGTH s.vs_params = LENGTH t.vs_params /\
      (!q. q < LENGTH s.vs_params ==>
        ld_owned_value E (EL q AP) (EL q BP) {} {}
          (EL q s.vs_params) (EL q t.vs_params))).
   This is a candidate, not yet an invariant: a call to the designated entry
   fn uses the second branch if possible (shape may exclude such calls).
   At call, setup_callee_def installs evaluated args and annotation call
   installs MAP (ld_op_prov AG) ops. Need a producer deriving the second
   branch from paired eval_operands and owned clean arguments, including
   opaque return-PC handling; do not assume arbitrary args are clean.
   ld_param_backward / ld_param_certificate_backward already consume that
   second branch. ld_param_selection handles inherited ownership.
   PARAM semantics checks w2n idx < LENGTH s.vs_params; ld_out_prov_def
   checks w2n idx < LENGTH AP separately and returns NONE for AP=[].
   Missing producer: PARAM successor from this disjunctive entry/call
   envelope, eliminating the first branch using entry_fn_no_params, then
   consuming existing ld_param_certificate_backward. Existing definitions
   and existing PARAM theorem statements must remain unchanged.

   6. Saved resume / parameters.
   Annotated call saves lf_fn=caller, lf_inst=inv, lf_state=s, lf_params=AP,
   lf_prov=AG, lf_tvar=tn.t_var, lf_local=L; target saves its own state and
   configured caller. Candidate saved alignment is the clause in 2 applied
   to f.lf_state,g.lf_state and INVOKE's singleton configured code.
   merge_callee_state_def retains caller params, control, vars, allocas,
   frontier, but uses CURRENT callee memory and shared effects. Return's
   bind_outputs/adopt_return_fmp do not replace caller params. Annotated ret
   restores f.lf_params and resumes at SUC f.lf_state.vs_inst_idx; target
   resumes at SUC g.lf_state.vs_inst_idx. These indices are NOT equal:
   the INVOKE segment is singleton, so target successor is LENGTH p+1.
   Candidate saved parameter clause is the envelope in 5 at
   (f.lf_fn,f.lf_params,g.lf_params,f.lf_state,g.lf_state).
   ld_saved_embedded restores local data, not shared memory. Existing
   ld_annotated_call_pop reconstructs actual source completion from a
   terminal annotated witness; ghost reachability alone is not completion.
   Missing producer: paired return with saved configured alignment,
   common IntRet record, bind_outputs and current-memory transport yields
   restored parameter envelope and successor phase/alignment. Never
   restore a saved memory snapshot or identify return-PC token values.

   This audit closes only the diagnostic. It authorizes neither a global
   coverage definition nor a claim that the missing producers are proved.
*)
