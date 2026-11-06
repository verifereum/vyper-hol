Theory lowerDloadRecursiveInterface
Ancestors
  lowerDloadProjectedReachability lowerDloadNormalData lowerDloadReachability
  lowerDloadRevertSuffix lowerDloadSavedExtension lowerDloadPhaseBoundary
  lowerDloadControlPosition lowerDloadOwnership lowerDloadDefs
  lowerDloadConfiguredSuccessor
  lowerDloadIndexedStageEntry lowerDloadTopEntryControl ctxLookupAgreeHelpers
  contextCodegenRel venomExecSemantics venomInst venomExecProofs venomWf
  ptrDiscipline list finite_map pred_set words

(* Diagnostic quotation only: not a definition, theorem, or closure claim.
   CS, lo, rpolicy and view are fixed environmental parameters. Context
   membership uses the actual per-function ctx_pass_stage certificates,
   NOT a hypothetical single supply fold across the context. Saved control
   certificates are indexed by the SAME index as saved data. *)
val ld_recursive_candidate =
  ``\vs0 CT projected_stk un gn j t.
    (?astk gstk k L AP AG tn fn i s ta ua V U E H BP BH live keys A
       suspended f fa fb bb gb a0 a1 a2 a3 pre post p code tail
       bpre bpost qpre qpost supports savedkeys s0 n.
      ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
      ld_stack_origin vs0 CS (MAP ld_erase_frame astk) fn s0 /\
      ld_normal_data CS fn V U lo E L H AP BP AG BH tn ua s ta
        astk live keys (32 * SUM (MAP CARD suspended)) A suspended gstk f /\
      V = set(fn_ir_vars fn) /\ U = {v | v IN V /\ ~retpc_var fn v} /\
      (?cpre cpost gpre gpost observed out.
        CS.ctx_functions = cpre ++ fn::cpost /\
        CT.ctx_functions = gpre ++ gn::gpost /\
        LENGTH cpre = LENGTH gpre /\
        fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed fa fn out /\
        out.fpo_function = gn /\
        observed.cu_context.ctx_entry = CS.ctx_entry /\
        observed.cu_context.ctx_global_reserved = CS.ctx_global_reserved /\
        ctx_fn_names observed.cu_context = ctx_fn_names CS /\
        view CT fn observed) /\
      lower_dload_function_supply fa fn = (gn,fb) /\
      fn.fn_blocks = bpre ++ bb::bpost /\
      lower_dload_blocks_supply fa bpre = (qpre,a0) /\
      lower_dload_block_supply a0 bb = (gb,a3) /\
      lower_dload_blocks_supply a3 bpost = (qpost,fb) /\
      gn.fn_blocks = qpre ++ gb::qpost /\
      bb.bb_instructions = pre ++ i::post /\
      lower_dload_insts_supply a0 pre = (p,a1) /\
      lower_dload_inst_supply a1 i = (code,a2) /\
      lower_dload_insts_supply a2 post = (tail,a3) /\
      gb.bb_instructions = p ++ code ++ tail /\ code <> [] /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      lookup_block ta.vs_current_bb gn.fn_blocks = SOME gb /\
      s.vs_current_bb = ta.vs_current_bb /\ s.vs_prev_bb = ta.vs_prev_bb /\
      s.vs_inst_idx = LENGTH pre /\ ta.vs_inst_idx = LENGTH p /\
      active_inst fn i s /\ active_inst gn j t /\
      ~in_revert_forward fn s /\
      ((n = 0 /\ t = ta /\ un = ua /\ j = HD code) \/
       (0 < n /\ n < LENGTH code /\
        ld_target_prefix CT code ta ua n t un /\ j = EL n code)) /\
      projected_stk = MAP (\g.
        (g.lf_fn,g.lf_inst,g.lf_state,g.lf_tvar)) gstk /\
      keys = set(MAP (\a. a.inst_id)
        (FILTER (\a. a.inst_opcode = ALLOCA) (fn_insts gn))) DIFF
        set(MAP (\a. a.inst_id) (fn_insts fn)) /\
      LIST_REL (\a g. FINITE a /\ CARD a <= LENGTH
        (FILTER (\ii. ii.inst_opcode = DLOAD) (fn_insts g)))
        (A::suspended) (fn::MAP (\sf. sf.lf_fn) astk) /\
      LENGTH astk = LENGTH gstk /\ LENGTH supports = LENGTH astk /\
      LENGTH savedkeys = LENGTH astk /\ LENGTH suspended = LENGTH astk /\
      (!q. q < LENGTH astk ==>
        ld_saved_embedded
          {v | v IN EL q supports /\ ~retpc_var (EL q astk).lf_fn v}
          E (EL q savedkeys)
          (32 * SUM (MAP CARD (DROP (SUC q) suspended)))
          (EL q suspended) (EL q astk) (EL q gstk) /\
        (!v. v IN EL q supports ==>
          (lookup_var v (EL q astk).lf_state = NONE <=>
           lookup_var v (EL q gstk).lf_state = NONE)) /\
        (!v. (case FLOOKUP (EL q astk).lf_tvar v of NONE => {} | SOME m => m)
          SUBSET count 32) /\
        (!v. (case FLOOKUP (EL q gstk).lf_tvar v of NONE => {} | SOME m => m)
          SUBSET count 32) /\
        EL q supports = set(fn_ir_vars (EL q astk).lf_fn) /\
        (?sf tf sk stn origin sa sb cpre cpost gpre gpost observed out
            bs bt bpre bpost gp gt a b pre post p tail c d.
          sf = EL q astk /\ tf = EL q gstk /\
          ld_annotated_reachable vs0 CS (DROP (SUC q) astk) sk
            sf.lf_local sf.lf_params sf.lf_prov stn
            sf.lf_fn sf.lf_inst sf.lf_state /\ stn.t_var = sf.lf_tvar /\
          ld_stack_origin vs0 CS (MAP ld_erase_frame (DROP (SUC q) astk))
            sf.lf_fn origin /\
          sf.lf_inst.inst_opcode = INVOKE /\ tf.lf_inst = sf.lf_inst /\
          lower_dload_function_supply sa sf.lf_fn = (tf.lf_fn,sb) /\
          CS.ctx_functions = cpre ++ sf.lf_fn::cpost /\
          CT.ctx_functions = gpre ++ tf.lf_fn::gpost /\
          LENGTH cpre = LENGTH gpre /\
          fn_pass_step rpolicy (CFP_Simple VP_LowerDload)
            observed sa sf.lf_fn out /\
          out.fpo_function = tf.lf_fn /\ out.fpo_supply = sb /\
          observed.cu_context.ctx_entry = CS.ctx_entry /\
          observed.cu_context.ctx_global_reserved = CS.ctx_global_reserved /\
          ctx_fn_names observed.cu_context = ctx_fn_names CS /\
          view CT sf.lf_fn observed /\
          sf.lf_fn.fn_blocks = bpre ++ bs::bpost /\
          lower_dload_blocks_supply sa bpre = (gp,a) /\
          lower_dload_block_supply a bs = (bt,b) /\
          lower_dload_blocks_supply b bpost = (gt,sb) /\
          tf.lf_fn.fn_blocks = gp ++ bt::gt /\
          bs.bb_instructions = pre ++ sf.lf_inst::post /\
          lower_dload_insts_supply a pre = (p,c) /\
          lower_dload_inst_supply c sf.lf_inst = ([tf.lf_inst],d) /\
          lower_dload_insts_supply d post = (tail,b) /\
          bt.bb_instructions = p ++ tf.lf_inst::tail /\
          lookup_block sf.lf_state.vs_current_bb sf.lf_fn.fn_blocks = SOME bs /\
          lookup_block tf.lf_state.vs_current_bb tf.lf_fn.fn_blocks = SOME bt /\
          sf.lf_state.vs_inst_idx = LENGTH pre /\
          tf.lf_state.vs_inst_idx = LENGTH p /\
          sf.lf_state.vs_current_bb = tf.lf_state.vs_current_bb /\
          sf.lf_state.vs_prev_bb = tf.lf_state.vs_prev_bb /\
          sf.lf_state.vs_call_ctx = tf.lf_state.vs_call_ctx /\
          sf.lf_state.vs_tx_ctx = tf.lf_state.vs_tx_ctx /\
          sf.lf_state.vs_block_ctx = tf.lf_state.vs_block_ctx /\
          sf.lf_state.vs_prev_hashes = tf.lf_state.vs_prev_hashes /\
          sf.lf_state.vs_code = tf.lf_state.vs_code /\
          sf.lf_state.vs_data_section = tf.lf_state.vs_data_section /\
          sf.lf_state.vs_fmp = tf.lf_state.vs_fmp /\
          sf.lf_state.vs_call_entry_fmp = tf.lf_state.vs_call_entry_fmp /\
          sf.lf_state.vs_initial_fmp = tf.lf_state.vs_initial_fmp /\
          EL q savedkeys = set(MAP (\ii. ii.inst_id)
            (FILTER (\ii. ii.inst_opcode = ALLOCA) (fn_insts tf.lf_fn))) DIFF
            set(MAP (\ii. ii.inst_id) (fn_insts sf.lf_fn)) /\
          ((CS.ctx_entry = SOME sf.lf_fn.fn_name /\
            sf.lf_params = [] /\ tf.lf_params = [] /\
            entry_fn_no_params sf.lf_fn) \/
           (LENGTH sf.lf_params = LENGTH sf.lf_state.vs_params /\
            LENGTH tf.lf_params = LENGTH tf.lf_state.vs_params /\
            LENGTH sf.lf_state.vs_params = LENGTH tf.lf_state.vs_params /\
            (!z. z < LENGTH sf.lf_state.vs_params ==>
              ld_owned_value E (EL z sf.lf_params) (EL z tf.lf_params) {} {}
                (EL z sf.lf_state.vs_params) (EL z tf.lf_state.vs_params))))))) \/
    (?gb copypos endpos.
      lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
      revert_forward_pair gb copypos endpos /\
      copypos <= t.vs_inst_idx /\ t.vs_inst_idx <= endpos /\
      get_instruction gb t.vs_inst_idx = SOME j)``;

(* VALIDATION LEDGER -- PARTIAL, no constructor closure is asserted.

   Projection:
   ld_frame_reachable_projected_ind is checked. Its P ignores raw PG/G;
   synthetic gstk projection has exactly its operational tuple type. No
   scratch-inclusive target provenance equality is needed. This supersedes
   the purported raw-provenance bridge requirement in the older audit.

   Exceptional mode (proposed inclusive copy position):
   ld_revert_pair_suffix_step requires copypos < index <= endpos. It proves
   no Halt/IntRet, no request growth, stable block and next index in range.
   ld_revert_pair_suffix_enter handles copypos=index and successful OK,
   including no request growth and bounded next position. It does NOT itself
   state no Halt/IntRet at the copy. That dispatch fact must be verified.
   The transformed pair is obtained from ld_lower_revert_pair_suffix and
   revert_forward_pair_def, not assumed from arbitrary source indices.
   The quote currently uses the concrete target pair; configured membership
   may be redundant in this disjunct, since observations and preservation
   depend only on target syntax. This must be explicitly ruled in validation.

   Request consumer target (ptrDiscipline.taint_within_def):
   step_inst fuel CT j t = OK t' /\
   LENGTH t.vs_requests < LENGTH t'.vs_requests ==>
     un.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
       (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
     un.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
       (t.vs_transient t.vs_call_ctx.cc_address).
   Exceptional mode should contradict strict growth, not transport memory.

   Halt consumer target (final_taint_def and taint_within_def):
   j.inst_opcode <> INVOKE /\ step_inst fuel CT j t = Halt th ==>
     (step_taint j t th un).t_stor SUBSET
       D.d_stor th.vs_call_ctx.cc_address
         (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
     (step_taint j t th un).t_trans SUBSET
       D.d_trans th.vs_call_ctx.cc_address
         (th.vs_transient th.vs_call_ctx.cc_address) /\
     (step_taint j t th un).t_imm SUBSET D.d_imm th.vs_immutables /\
     ret_taint un j t SUBSET D.d_ret th.vs_returndata.
   Exceptional mode should contradict Halt. Normal/strict phases require
   actual external/terminal producer facts; no statement here proves them.

   CONSTRUCTOR LEDGER (P means the single quotation above, N its first
   disjunct, R its second). The five exact substituted clause TERMS are
   ld_recursive_clause_goals below. None is asserted as a theorem.

   ENTRY -- C2.coverage / C2.control:
   Target clause: entry hypotheses ==> P vs0 CT [] entry_taint gn j t1.
   ld_frame_data_source_entry supplies annotated entry and reflexive data,
   but only for a SOURCE entered state s1. Needed residual:
     enters_block gn target0 t1 ==> ?fn s1 i fa fb.
       lower_dload_function_supply fa fn = (gn,fb) /\
       enters_block fn source0 s1 /\ active_inst fn i s1 /\
       [N with astk=gstk=[], k=0, L=H=AG=BH=FEMPTY,
        AP=BP=[], E=FEMPTY, A={}, suspended=[], n=0, ta=t1]
       OR R gn j t1.
   lower_dload_function_supply_enters_block is forward, not this backward
   residual. Actual ctx_pass_stage_def supplies indexed fn_pass_step
   certificates, NOT lower_dload_functions_supply over the whole context.
   The quote now retains that actual certificate with the chosen fa/fb.

   NEXT -- C2.control / C2.allocation.closure / C2.external.closure:
   Exact target successor is P vs0 CT stk (step_taint j t t' un) gn j'
     (t' with vs_inst_idx := SUC t.vs_inst_idx).
   For N, n+1<LENGTH code: ld_target_prefix_step_iff grows the same prefix;
   source annotation, saved witnesses and normal_data stay at the OLD anchor.
   For completion: ld_normal_ordinary_backward supplies source OK plus
   normal_data with ld_step_prov and step_taint for its enumerated opcodes.
   ld_annotated_reachable_next additionally needs ld_select_alloca and
   ld_erase L'=s'.vs_allocas. Configured successor supplies new pre/p split,
   not the data conjuncts. ALLOCA and macro boundaries own those data clauses.
   Exact saved-envelope residual when E becomes E': for each saved sf/tf
   and each z<LENGTH sf.lf_state.vs_params, preserve
     ld_owned_value E' (EL z sf.lf_params) (EL z tf.lf_params) {} {}
       (EL z sf.lf_state.vs_params) (EL z tf.lf_state.vs_params).
   E0345 updates saved DATA, not this extra indexed envelope. No new wrapper
   is inferred. R successor uses suffix_step or suffix_enter and the SAME
   target block/pair. Copy-to-R entry still needs the actual configured pair.

   BLOCK -- C2.control:
   Exact target is P vs0 CT stk (entry_taint_vars gn t' un) gn j' t1.
   Strict prefixes cannot contain a terminator (supply definition). At phase
   zero a changed code has no terminator either. For unchanged terminators
   the residual is source step_inst fuelS CS i s=OK s' /\ ~s'.vs_halted /\
     enters_block fn s' s1 /\ active_inst fn i' s1,
   together with N at s1/t1, AG'=ld_entry_prov fn s' AG and
   BH'=ld_entry_prov gn t' BH. This includes backward PHI data and configured
   positions, not just equal labels. R has opcode copy/ASSIGN/REVERT; only
   REVERT is a terminator, and it cannot produce OK. Hence no R block exit.

   CALL -- C2.calls:
   Supply makes INVOKE singleton and identical, so n=0, j=i and the new
   projected tuple is (gn,i,ta,ua.t_var). Choose synthetic saved tf from
   H/BP/BH and source saved sf from L/AP/AG, exactly ld_annotated_reachable_call.
   ld_call_entry_geometry_backward produces source args/setup/enters and
   child account at {} with charge A::suspended. ld_call_entry_memory covers
   memory only. Remaining formula is N at child entry with pushed witnesses,
   plus the new head's saved-envelope (ld_normal_data_envelope) and configured
   INVOKE certificate (the old current-position fields). Old q becomes SUC q;
   DROP(SUC(SUC q))(sf::astk)=DROP(SUC q)astk. No raw PG/G equation is needed.
   R cannot call: none of copy/ASSIGN/REVERT is INVOKE.

   RET -- C2.calls:
   The only IH is P with the saved tuple consed onto stk. Use projection to
   identify sf/tf and POP the indexed witnesses. Current source annotation
   plus ld_annotated_prefix_at_origin and ld_frame_return_complete can recover
   a completed source call; the IH itself is not a completed run.
   ld_nonopaque_ret_backward's precise result is source IntRet with the SAME
   rr record and unchanged source/target states. ld_annotated_call_pop then
   supplies the restored annotation, not an assumed completed-run premise.
   ld_return_pop_backward supplies account/frame/stack bounds but not all
   normal_data. The repair above now has direct producers for the missing
   retained caller slice: current ld_normal_data_frame, ld_frame_data_shared
   and ld_shared_state_def produce all nine equalities at push, including
   vs_call_entry_fmp. Old entries do not change. At pop, merge_callee_state
   retains call_ctx/tx_ctx/block_ctx/prev_hashes/code/data_section/fmp/
   call_entry_fmp/initial_fmp from the saved caller, and bind_outputs only
   updates variables, so precisely the saved slice supplies these fields.
   accounts/transient/immutables/outcomes/returndata instead come from CURRENT
   callee ld_shared_state. Current memory comes from ld_call_return_memory;
   old caller memory is never restored. Mask inclusions survive t_var reset.
   Saved parameter envelope supplies restored AP/BP and caller params. The
   caller's vs_labels are covered by saved ld_owned_vars, not the slice.

   Adoption audit (both constructors of the option): NONE leaves merge
   untouched. If source and target both have SOME p with the same p, fmp is
   overwritten equally; the other eight slice fields are untouched. Equal
   records with unequal adopted pointers are impossible; unequal return
   records would leave a genuine fmp residual and cannot be justified from
   the saved slice. For the frozen environment the actual return is RET:
   source fmp_free_ctx excludes RETFMP/DRET and lowering introduces neither;
   step_inst_intret_opcodes excludes every other non-INVOKE opcode. RET's
   result has iret_adopt_fmp=NONE by step_inst_base_def. This is a required
   dispatch proof in C2.calls, NOT an extra assumption on the return rule.
   The sibling o1LowerDloadRunnerExec[ret] contains this same opcode argument
   for its forward direction; it is not a backward reachability theorem.

   Reindexing audit for the repaired slice: ENTRY has no saved entries.
   NEXT/BLOCK leave saved states unchanged (even if E changes). CALL head
   is exactly current s/ta at phase zero; all nine equalities are current
   shared_state projections. Tail index SUC q uses old q. RET drops the head;
   new index q uses old SUC q; surviving saved states themselves are unchanged.
   No transport hypothesis on E or on mutable storage is required for this
   slice. R cannot return because copy/ASSIGN/REVERT cannot produce IntRet.
   Remaining C2.calls formula is the complete N at resumed caller with
     L=sf.lf_local, AP=sf.lf_params, H=tf.lf_local, BP=tf.lf_params,
     AG=DRESTRICT sf.lf_prov (COMPL(set sf.lf_inst.inst_outputs)),
     BH=DRESTRICT tf.lf_prov (COMPL(set tf.lf_inst.inst_outputs)),
   and tn/un t_var reset to the respective restricted saved tables, after
   binding the common rr.iret_values into the two merged states. Restrict
   owners only after restoring these surviving selections and envelopes.

   OBSERVATIONS -- C2.external.closure / C2.terminal:
   Exact targets are the two rows above. For N phase zero with unchanged
   instruction, source storage/transient masks come from taint_ok and target
   masks from ld_normal_data_masks; D transport still requires equality of
   the dead-set-observed state modulo source masks (dead_wf), not literal
   equality of relocated memory. For Halt also require the source Halt and
   return-byte correspondence; these are terminal residuals, not provided
   by ordinary OK backward execution. Strict phases use only the expansion
   opcodes ALLOCA/ADD/CODECOPY/MLOAD and cannot grow requests/Halt/IntRet.
   R uses suffix_step beyond copy. At copy, step_inst_base's RETURNDATACOPY
   branch has only operand-error, bounds-error, or OK write-memory results;
   it has no Halt/IntRet branch and suffix_enter proves request stability.
   These syntactic eliminations do not require a normal_data witness in R.

   Diagnostic status: the saved caller slice repairs E0348's specific missing
   producer and has push/preserve/pop producers at all five clauses. The
   remaining full-constructor and observation formulas above are residual
   PROOF obligations, not facts established by this diagnostic. Their owners
   are C2.coverage (entry/indexed witnesses), C2.control (configured/block/
   prefix/exceptional dispatch), C2.allocation.closure (ALLOCA and macro data),
   C2.calls (push/pop/envelope restoration/owner restriction/common return),
   C2.external.closure (request steps and dead-set transport) and C2.terminal
   (Halt/return-byte observations). No global invariant, closure lemma or
   observation theorem is asserted; global recursion needs those proofs.
*)

(* Term-only constructor substitution. These are obligations, NOT theorems.
   Keeping the actual five clause terms prevents a prose ledger from silently
   omitting a quantifier, a saved field, or the sole recursive premise of ret.
   In particular this creates no assumed-closure theorem. *)
val ld_recursive_clause_goals =
  let
    val (p, body) = dest_forall (concl ld_frame_reachable_projected_ind)
    val (clauses, _) = dest_imp body
    val _ = if type_of p = type_of ld_recursive_candidate then ()
            else raise Fail "recursive candidate has wrong predicate type"
  in
    map (subst [p |-> ld_recursive_candidate]) (strip_conj clauses)
  end;
val _ = if length ld_recursive_clause_goals = 5 then ()
        else raise Fail "projected constructor inventory changed";

(* Specialize only the constructor's environment parameters. *)
val ld_recursive_entry_goal =
  let val (v0::ct::rest, body) = strip_forall (hd ld_recursive_clause_goals)
  in subst [v0 |-> mk_var("vs0", type_of v0),
            ct |-> mk_var("CT", type_of ct)]
       (list_mk_forall (rest, body))
  end;

Theorem ld_recursive_entry_clause:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions /\
  lo = vs0.vs_alloca_next ==>
  ^ld_recursive_entry_goal
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all lower_dload_stage_lookup_indexed >> strip_tac >>
  `?raw. lower_dload_function_supply a f = (fn,raw)` by
    (qpat_x_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
     simp[o1PassContractTheory.fn_pass_step_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `CS.ctx_entry = SOME name` by
    gvs[o1PassContractTheory.ctx_pass_stage_def] >>
  `fn_entry_label f = SOME lbl` by
    metis_tac[o1ContractLowerDloadTheory.lower_dload_function_supply_labels] >>
  `first_block_no_phi f` by
    (gvs[o1PassContractTheory.o1_ctx_shape_def, EVERY_MEM,
         o1PassContractTheory.o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  `wf_function f` by
    (gvs[o1PassContractTheory.o1_ctx_shape_def, EVERY_MEM,
         o1PassContractTheory.o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     gvs[wf_function_def, fn_labels_def]) >>
  qpat_assum `active_inst fn inst s1`
    (strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[MEM_lookup_block] >>
  `s1.vs_current_bb = lbl` by
    (qpat_x_assum `enters_block fn _ s1` mp_tac >>
     simp[enters_block_def, NoAsms] >> strip_tac >> gvs[] >>
     drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `enters_block fn z s1` >>
  `z = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                  vs_inst_idx := 0|>` by simp[Abbr `z`] >>
  `lookup_block lbl fn.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all lower_dload_top_entry_control >> strip_tac >>
  BETA_TAC >> Cases_on `in_revert_forward f s1`
  >- suspend "revert"
  >> suspend "normal"
QED

Resume ld_recursive_entry_clause[normal]:
  disj1_tac >>
  qexistsl_tac [`[]`, `[]`, `0`, `FEMPTY`, `[]`, `FEMPTY`,
    `entry_taint`, `f`, `i`, `s1`, `s1`, `entry_taint`,
    `set(fn_ir_vars f)`, `{v | v IN set(fn_ir_vars f) /\ ~retpc_var f v}`,
    `FEMPTY`, `FEMPTY`, `[]`, `FEMPTY`, `{}`,
    `set(MAP (\a. a.inst_id) (FILTER (\a. a.inst_opcode = ALLOCA) (fn_insts fn)))
       DIFF set(MAP (\a. a.inst_id) (fn_insts f))`,
    `{}`, `[]`, `vs0.vs_alloca_next`, `a`, `raw`, `bb'`, `bb`,
    `a`, `a`, `amid`, `aend`, `[]`, `post'`, `[]`, `code`, `tail`,
    `[]`, `TL f.fn_blocks`, `[]`, `TL fn.fn_blocks`, `[]`, `[]`, `z`, `0`] >>
  simp[NoAsms, lower_dload_blocks_supply_def, lower_dload_insts_supply_def] >>
  conj_tac
  >- (irule ld_annotated_reachable_entry >>
      conj_tac
      >- (qpat_x_assum `s1 = z` SUBST_ALL_TAC >>
          qpat_x_assum `z = _` SUBST_ALL_TAC >>
          qpat_x_assum `o1_run_state_ok vs0` mp_tac >>
          simp[NoAsms, o1PassContractTheory.o1_run_state_ok_def,
               unitTransformDefsTheory.o1_initial_state_ok_def]) >>
      conj_tac
      >- (qexists_tac `name` >> metis_tac[]) >>
      conj_tac >- (first_assum ACCEPT_TAC) >>
      qexists_tac `lbl` >> metis_tac[]) >>
  conj_tac
  >- (simp[NoAsms, Abbr `z`] >> irule ld_stack_origin_base >> metis_tac[]) >>
  conj_tac >- suspend "data" >>
  conj_tac
  >- (qexistsl_tac [`pre`, `post`, `before`, `after`, `observed`, `out`] >>
      simp[]) >>
  `f.fn_blocks = bb'::TL f.fn_blocks` by
    (qpat_x_assum `fn_entry_label f = _` mp_tac >>
     qpat_x_assum `lookup_block lbl f.fn_blocks = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `f.fn_blocks` >>
     simp[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm] >>
     rpt strip_tac >> gvs[]) >>
  `fn.fn_blocks = bb::TL fn.fn_blocks /\
   lower_dload_blocks_supply aend (TL f.fn_blocks) = (TL fn.fn_blocks,raw)` by
    (qpat_x_assum `lower_dload_function_supply a f = _` mp_tac >>
     pure_rewrite_tac[lower_dload_function_supply_def] >>
     qpat_x_assum `f.fn_blocks = _` (fn th => once_rewrite_tac[th]) >>
     qpat_x_assum `lower_dload_block_supply a bb' = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     Cases_on `lower_dload_blocks_supply aend (TL f.fn_blocks)` >>
     simp[lower_dload_function_supply_def, lower_dload_blocks_supply_def] >>
     strip_tac >> gvs[]) >>
  `s1.vs_inst_idx = 0` by
    (qpat_x_assum `s1 = z` SUBST_ALL_TAC >> simp[Abbr `z`]) >>
  metis_tac[]
QED

Resume ld_recursive_entry_clause[revert]:
  `s1.vs_inst_idx = 0` by
    (qpat_x_assum `s1 = z` SUBST_ALL_TAC >> simp[Abbr `z`]) >>
  `?endpos. revert_forward_pair bb' 0 endpos` by
    (qpat_x_assum `in_revert_forward f s1` mp_tac >>
     qpat_x_assum `lookup_block lbl f.fn_blocks = _` mp_tac >>
     qpat_x_assum `s1.vs_current_bb = lbl` mp_tac >>
     qpat_x_assum `s1.vs_inst_idx = 0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[in_revert_forward_def, revert_forward_at_def] >>
     rpt strip_tac >> gvs[] >>
     metis_tac[revert_forward_pair_def, prim_recTheory.NOT_LESS_0]) >>
  disj2_tac >> qexistsl_tac [`bb`, `0`, `endpos`] >>
  `revert_forward_pair bb 0 endpos` by
    (drule_all ld_lower_revert_pair_zero >> simp[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  simp[NoAsms] >> conj_tac >- decide_tac >>
  simp[get_instruction_def, NoAsms] >> metis_tac[]
QED

Resume ld_recursive_entry_clause[data]:
  `CS.ctx_entry = SOME f.fn_name /\ entry_fn_no_params f` by
    (qpat_x_assum `o1_ctx_shape CS` mp_tac >>
     qpat_x_assum `lookup_function name CS.ctx_functions = SOME f` mp_tac >>
     qpat_x_assum `CS.ctx_entry = SOME name` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `MEM f CS.ctx_functions /\ f.fn_name = name` by
       metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
     gvs[o1PassContractTheory.o1_ctx_shape_def, EVERY_MEM,
         o1PassContractTheory.o1_fn_shape_def]) >>
  qpat_x_assum `s1 = z` SUBST_ALL_TAC >>
  qpat_x_assum `z = _` SUBST_ALL_TAC >>
  qpat_x_assum `o1_run_state_ok vs0` mp_tac >>
  simp[NoAsms, o1PassContractTheory.o1_run_state_ok_def,
       unitTransformDefsTheory.o1_initial_state_ok_def] >> strip_tac >>
  qpat_x_assum `CS.ctx_entry = SOME f.fn_name` mp_tac >>
  qpat_x_assum `entry_fn_no_params f` mp_tac >>
  qpat_x_assum `lo = vs0.vs_alloca_next` mp_tac >>
  qpat_x_assum `vs0.vs_allocas = FEMPTY` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  simp[ld_normal_data_def, lowerDloadCoverageInvariantTheory.ld_frame_data_initial,
       lowerDloadAllocationTheory.ld_alloc_account_init,
       ld_frame_bound_def, ld_stack_bound_def, ld_live_def, ld_selected_def,
       lowerDloadRelocationTheory.ld_byte_rel_def, allocas_from_def] >>
  simp[lowerDloadLifetimeTheory.ld_site_bytes_def, entry_taint_def, op_taint_def]
QED

Finalise ld_recursive_entry_clause

(* Entry history only: the checked theorem above keeps its expanded statement.
   All subsequent operational clauses use the corrected single binding below.
   The saved raw endpoint is independent of dispatcher postprocessing. *)
val ld_entry_history_candidate = ld_recursive_candidate;
val ld_entry_history_conclusion = concl ld_recursive_entry_clause;
val ld_recursive_candidate =
  let
    val count = ref 0
    fun saved_supply_eq tm =
      is_eq tm andalso
      (let val (l,r) = dest_eq tm in
         is_var r andalso fst(dest_var r) = "sb" andalso
         is_comb l andalso is_const (rator l) andalso
         same_const (rator l) (rator ``out.fpo_supply``)
       end handle HOL_ERR _ => false)
    fun repair tm =
      if is_conj tm andalso saved_supply_eq (rand(rator tm)) then
        (count := !count + 1; repair (rand tm))
      else if is_abs tm then
        let val (v,b) = dest_abs tm in mk_abs(v,repair b) end
      else if is_comb tm then mk_comb(repair(rator tm),repair(rand tm))
      else tm
    val corrected = repair ld_entry_history_candidate
  in if !count = 1 then corrected
     else raise Fail "expected exactly one saved raw/configured equality"
  end;
val _ = if aconv ld_entry_history_conclusion (concl ld_recursive_entry_clause)
        then () else raise Fail "historical entry statement changed";
val ld_recursive_clause_goals =
  let
    val (p, body) = dest_forall (concl ld_frame_reachable_projected_ind)
    val (clauses, _) = dest_imp body
  in map (subst [p |-> ld_recursive_candidate]) (strip_conj clauses) end;

Theorem ld_recursive_candidate_weaken[local]:
  (^ld_entry_history_candidate) vs0 CT stk un gn j t ==>
  (^ld_recursive_candidate) vs0 CT stk un gn j t
Proof
  BETA_TAC >>
  rpt (FIRST [disch_then ACCEPT_TAC,
              disch_then (ACCEPT_TAC o CONJUNCT2),
              ho_match_mp_tac MONO_OR, ho_match_mp_tac MONO_AND,
              ho_match_mp_tac MONO_EXISTS, ho_match_mp_tac MONO_ALL,
              ho_match_mp_tac MONO_IMP, conj_tac, gen_tac]) >>
  simp[]
QED

(* Only the operational binding is used below.  The historical entry clause
   is consumed through ld_recursive_candidate_weaken, never rebound. *)
val ld_recursive_inside =
  let
    val (args,body) = strip_abs ld_recursive_candidate
    val (normal,_) = dest_disj body
    val (ws,b) = strip_exists normal
    val n = List.last ws
    val code = hd (filter (fn v => fst(dest_var v) = "code") ws)
    val bounded = list_mk_exists(ws,mk_conj(b,``SUC ^n < LENGTH ^code``))
  in list_mk_abs(args,bounded) end;

Theorem ld_active_lookup_el[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) gn.fn_blocks) /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  active_inst gn j t ==>
  j = EL t.vs_inst_idx gb.bb_instructions
Proof
  rw[active_inst_def] >>
  `lookup_block t.vs_current_bb gn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >> gvs[]
QED

Theorem ld_recursive_prefix_next:
  o1_ctx_shape CS /\
  (^ld_recursive_inside) vs0 CT stk un gn j t /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> strip_tac >>
  `ld_target_prefix CT code ta ua n t un` by
    asm_simp_tac (srw_ss()) [ld_target_prefix_empty] >>
  `j = EL n code` by (asm_simp_tac (srw_ss()) [EL]) >>
  `ld_target_prefix CT code ta ua (SUC n)
     (z with vs_inst_idx := SUC t.vs_inst_idx)
     (step_taint j t z un)` by
    (rewrite_tac [ld_target_prefix_step_iff] >>
     qexistsl_tac [`t`,`un`,`z`,`fuel`] >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     qpat_x_assum `ld_target_prefix _ _ _ _ n _ _` mp_tac >>
     simp[EL,ld_target_prefix_empty]) >>
  `i.inst_opcode IN {DLOAD;DLOADBYTES}` by
    (spose_not_then assume_tac >>
     `i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` by
       fs[IN_INSERT,IN_SING] >>
     qpat_x_assum `lower_dload_inst_supply a1 i = _` mp_tac >>
     qpat_x_assum `SUC n < LENGTH code` mp_tac >>
     simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) gn.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >>
     disch_then (mp_tac o SRULE [EVERY_MEM]) >>
     disch_then (qspec_then `fn` mp_tac) >>
     impl_tac >- simp[] >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     disch_then (mp_tac o CONJUNCT1) >>
     pure_rewrite_tac [fn_labels_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  drule_all lower_dload_configured_prefix_labels >> strip_tac >>
  qpat_x_assum `(z with vs_inst_idx := _).vs_current_bb = _` (assume_tac o SRULE []) >>
  `lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
     gn.fn_blocks = SOME gb` by
    (qpat_x_assum `lookup_block ta.vs_current_bb _ = SOME gb` mp_tac >> simp[]) >>
  drule_all ld_active_lookup_el >> strip_tac >>
  drule_all lowerDloadPositionBoundaryTheory.ld_target_prefix_position >>
  strip_tac >>
  `j' = EL (SUC n) code` by
    (qpat_x_assum `j' = EL _ _` mp_tac >> asm_rewrite_tac []) >>
  disj1_tac >>
  qexistsl_tac [`astk`,`gstk`,`k`,`L`,`AP`,`AG`,`tn`,`fn`,`i`,`s`,
    `ta`,`ua`,`V`,`U`,`E`,`H`,`BP`,`BH`,`live`,`keys`,`A`,`suspended`,
    `f`,`fa`,`fb`,`bb`,`gb`,`a0`,`a1`,`a2`,`a3`,`pre`,`post`,`p`,
    `code`,`tail`,`bpre`,`bpost`,`qpre`,`qpost`,`supports`,`savedkeys`,
    `s0`,`SUC n`] >>
  asm_rewrite_tac [] >> simp[] >>
  qexistsl_tac [`cpre`,`cpost`,`gpre`,`gpost`,`observed`,`out`] >>
  asm_rewrite_tac []
QED
