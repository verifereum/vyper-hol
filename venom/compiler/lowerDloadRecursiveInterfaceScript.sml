Theory lowerDloadRecursiveInterface
Ancestors
  lowerDloadProjectedReachability lowerDloadNormalData lowerDloadReachability
  lowerDloadTargetValidity lowerDloadConfiguredScratch lowerDloadCoverageReserve
  lowerDloadCoverageLoad
  lowerDloadRevertSuffix lowerDloadSavedExtension lowerDloadPhaseBoundary
  lowerDloadNormalJump lowerDloadNormalEntry lowerDloadReachableJump
  o1LowerDloadEntryFetch o1LowerDloadJointEntry lowerDloadNonhalted
  lowerDloadConfiguredSelection lowerDloadCoverageBytes lowerDloadResidualNonmemory
  lowerDloadControlPosition lowerDloadOwnership lowerDloadDefs
  lowerDloadCoverageAlloca lowerDloadNormalLive lowerDloadReachableFloor
  lowerDloadConfiguredSuccessor lowerDloadOrdinaryNext lowerDloadSourceInterface venomInstProps
  lowerDloadIndexedStageEntry lowerDloadTopEntryControl ctxLookupAgreeHelpers
  contextCodegenRel venomExecSemantics venomInst venomExecProofs venomWf
  ptrDiscipline list rich_list finite_map pred_set words

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
   ld_recursive_block_anchor proves that a successful target terminator
   retains the full normal certificate with n=0, code=[i], a2=a1, j=i,
   t=ta and un=ua. It excludes strict prefixes and the revert interval;
   it does NOT prove backward successful branch execution. The residual is
   source step_inst fuelS CS i s=OK s' /\ ~s'.vs_halted /\
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

(* Geometry refinement is shared by historical entry and operational consumers. *)
fun ld_refine_geometry candidate =
  let
    val (args,body) = strip_abs candidate
    val (normal,exceptional) = dest_disj body
    val (ws,b) = strip_exists normal
    fun named s = hd (filter (fn v => fst(dest_var v) = s) ws)
    val ta = named "ta"
    val stk = List.nth(args,2)
    val t = List.last args
    val refined = list_mk_exists(ws,mk_conj(b,``alloca_inv ^ta``))
  in list_mk_abs(args,
       list_mk_conj [``alloca_inv ^t``,
         ``!f i st tv. MEM (f,i,st,tv) ^stk ==> alloca_inv st``,
         mk_disj(refined,exceptional)]) end;
val ld_entry_geometry_history = ld_refine_geometry ld_recursive_candidate;
val ld_entry_geometry_history_goal =
  let
    val (p, body) = dest_forall (concl ld_frame_reachable_projected_ind)
    val (clauses, _) = dest_imp body
    val clause = subst [p |-> ld_entry_geometry_history] (hd(strip_conj clauses))
    val (v0::ct::rest, b) = strip_forall clause
  in subst [v0 |-> mk_var("vs0", type_of v0),
            ct |-> mk_var("CT", type_of ct)] (list_mk_forall(rest,b)) end;

(* Specialize only the constructor's environment parameters. *)
val ld_recursive_entry_goal =
  let val (v0::ct::rest, body) = strip_forall (hd ld_recursive_clause_goals)
  in subst [v0 |-> mk_var("vs0", type_of v0),
            ct |-> mk_var("CT", type_of ct)]
       (list_mk_forall (rest, body))
  end;

Theorem ld_entry_geometry_history_clause[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions /\
  lo = vs0.vs_alloca_next ==>
  ^ld_entry_geometry_history_goal
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
  `alloca_inv s1` by
    (qpat_x_assum `s1 = z` SUBST_ALL_TAC >>
     qpat_x_assum `z = _` SUBST_ALL_TAC >>
     qpat_x_assum `o1_run_state_ok vs0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[o1PassContractTheory.o1_run_state_ok_def,
          unitTransformDefsTheory.o1_initial_state_ok_def,
          venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def,
          venomMemDefsTheory.alloca_next_valid_def]) >>
  BETA_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >> Cases_on `in_revert_forward f s1`
  >- suspend "revert"
  >> suspend "normal"
QED

Resume ld_entry_geometry_history_clause[normal]:
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
  reverse conj_tac >- first_assum ACCEPT_TAC >>
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

Resume ld_entry_geometry_history_clause[revert]:
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

Resume ld_entry_geometry_history_clause[data]:
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

Finalise ld_entry_geometry_history_clause

Theorem ld_recursive_entry_clause:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions /\
  lo = vs0.vs_alloca_next ==>
  ^ld_recursive_entry_goal
Proof
  strip_tac >>
  mp_tac ld_entry_geometry_history_clause >>
  (impl_tac >- simp[]) >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name fn lbl inst s1. _`
    (qspecl_then [`name`, `fn`, `lbl`, `inst`, `s1`] mp_tac) >>
  (impl_tac >- simp[]) >> BETA_TAC >>
  disch_then (mp_tac o CONJUNCT2 o CONJUNCT2) >>
  ho_match_mp_tac MONO_OR >> reverse conj_tac >- simp[] >>
  rpt (ho_match_mp_tac MONO_EXISTS >> gen_tac) >>
  disch_then (ACCEPT_TAC o CONJUNCT1)
QED

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
(* Literal saved-clause interface, extracted only from the operational quote. *)
val ld_recursive_saved =
  let
    val (_,body) = strip_abs ld_recursive_candidate
    val (_,normal) = strip_exists (fst (dest_disj body))
    val indexed = List.filter
      (fn tm => is_forall tm andalso
        fst(dest_var(fst(dest_forall tm))) = "q") (strip_conj normal)
    val (q,guarded) = dest_forall (hd indexed)
    val (_,saved) = dest_imp guarded
    val e = hd (List.filter (fn v => fst(dest_var v) = "E") (free_vars saved))
    val result = list_mk_abs([e,q],saved)
  in
    if length indexed = 1 andalso aconv (rhs(concl((DEPTH_CONV BETA_CONV)(mk_comb(mk_comb(result,e),q))))) saved
    then result else raise Fail "saved clause extraction mismatch"
  end;

Theorem ld_recursive_saved_support[local]:
  q < LENGTH astk /\
  (!owner bs sz. ld_selected (EL q astk).lf_local (EL q astk).lf_params
    (EL q astk).lf_prov (owner,(bs,sz)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  ((^ld_recursive_saved) E q ==> (^ld_recursive_saved) E' q)
Proof
  BETA_TAC >> strip_tac >>
  ho_match_mp_tac MONO_AND >> conj_tac
  >- (strip_tac >> irule lowerDloadOwnerTransportTheory.ld_saved_embedded_support >>
      qexists_tac `E` >> asm_rewrite_tac []) >>
  rpt (FIRST [disch_then ACCEPT_TAC, ho_match_mp_tac MONO_AND, conj_tac]) >>
  rpt (ho_match_mp_tac MONO_EXISTS >> gen_tac) >>
  strip_tac >> asm_rewrite_tac [] >>
  disj2_tac >> gen_tac >> strip_tac >>
  irule lowerDloadOwnerTransportTheory.ld_owned_value_support >>
  qexists_tac `E` >> conj_tac
  >- (gvs[] >> rpt gen_tac >> strip_tac >>
      first_x_assum irule >>
      simp[ld_selected_def] >> qexistsl_tac [`bs'`, `sz`] >>
      disj2_tac >> disj1_tac >>
      rewrite_tac [MEM_EL] >> qexists_tac `z` >> gvs[]) >>
  gvs[]
QED

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

(* One fixed-anchor intermediate transition, generalized over its invariant. *)
val ld_recursive_anchor_normal =
  let
    val (args,body) = strip_abs ld_recursive_candidate
    val (ws,b) = strip_exists (fst(dest_disj body))
    val ta = hd (filter (fn v => fst(dest_var v) = "ta") ws)
    val p = ``P:venom_state->bool``
  in list_mk_abs(p::args,list_mk_exists(ws,mk_conj(b,mk_comb(p,ta)))) end;
val ld_recursive_anchor_inside =
  let
    val (args,body) = strip_abs ld_recursive_anchor_normal
    val (ws,b) = strip_exists body
    fun named s = hd (filter (fn v => fst(dest_var v) = s) ws)
    val n = named "n"
    val code = named "code"
  in list_mk_abs(args,list_mk_exists(ws,mk_conj(b,``SUC ^n < LENGTH ^code``))) end;

Theorem ld_recursive_anchor_prefix_next[local]:
  !P.
  o1_ctx_shape CS /\
  (^ld_recursive_anchor_inside) P vs0 CT stk un gn j t /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_anchor_normal) P vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  gen_tac >> BETA_TAC >> strip_tac >>
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
  qexistsl_tac [`astk`,`gstk`,`k`,`L`,`AP`,`AG`,`tn`,`fn`,`i`,`s`,
    `ta`,`ua`,`V`,`U`,`E`,`H`,`BP`,`BH`,`live`,`keys`,`A`,`suspended`,
    `f`,`fa`,`fb`,`bb`,`gb`,`a0`,`a1`,`a2`,`a3`,`pre`,`post`,`p`,
    `code`,`tail`,`bpre`,`bpost`,`qpre`,`qpost`,`supports`,`savedkeys`,
    `s0`,`SUC n`] >>
  asm_rewrite_tac [] >> simp[] >>
  qexistsl_tac [`cpre`,`cpost`,`gpre`,`gpost`,`observed`,`out`] >>
  asm_rewrite_tac []
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
  strip_tac >>
  qspec_then `\_. T` mp_tac ld_recursive_anchor_prefix_next >>
  BETA_TAC >>
  RULE_ASSUM_TAC BETA_RULE >>
  (impl_tac >- (pure_rewrite_tac [AND_CLAUSES] >> asm_rewrite_tac [])) >>
  disch_tac >> BETA_TAC >> disj1_tac >>
  pop_assum (mp_tac o BETA_RULE) >>
  pure_rewrite_tac [AND_CLAUSES] >> disch_then ACCEPT_TAC
QED

(* A post-anchor predicate is retained only by the normal alternative. *)
fun ld_retain_anchor candidate q =
  let
    val (args,body) = strip_abs candidate
    val (normal,exceptional) = dest_disj body
    val (ws,b) = strip_exists normal
    val ta = hd (filter (fn v => fst(dest_var v) = "ta") ws)
  in list_mk_abs(args,mk_disj(list_mk_exists(ws,mk_conj(b,mk_comb(q,ta))),
                            exceptional)) end;
val ld_recursive_post_anchor =
  ld_retain_anchor ld_recursive_candidate ``Q:venom_state -> bool``;

Theorem ld_recursive_exceptional_next_anchor[local]:
  !Q.
  revert_forward_pair bb copypos endpos /\
  copypos <= t.vs_inst_idx /\ t.vs_inst_idx <= endpos /\
  get_instruction bb t.vs_inst_idx = SOME j /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks) /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_post_anchor) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  gen_tac >> strip_tac >>
  drule_all ld_revert_pair_interval_step >> strip_tac >>
  `~is_terminator j.inst_opcode /\ z.vs_requests = t.vs_requests /\
   (next_inst z).vs_current_bb = t.vs_current_bb /\
   copypos < (next_inst z).vs_inst_idx /\
   (next_inst z).vs_inst_idx <= endpos` by metis_tac[] >>
  `z.vs_inst_idx = t.vs_inst_idx` by
    (irule step_inst_preserves_inst_idx >> metis_tac[]) >>
  `next_inst z = (z with vs_inst_idx := SUC t.vs_inst_idx)` by
    simp[venomStateTheory.next_inst_def, arithmeticTheory.ADD1] >>
  `lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
      gn.fn_blocks = SOME bb` by
    (qpat_x_assum `(next_inst z).vs_current_bb = _` mp_tac >>
     qpat_x_assum `lookup_block t.vs_current_bb _ = _` mp_tac >> simp[]) >>
  drule_all ld_active_lookup_el >> strip_tac >>
  BETA_TAC >> disj2_tac >> qexistsl_tac [`bb`,`copypos`,`endpos`] >>
  asm_rewrite_tac [] >>
  `endpos < LENGTH bb.bb_instructions` by
    gvs[contextCodegenRelTheory.revert_forward_pair_def,
        venomInstTheory.get_instruction_def] >>
  qpat_x_assum `copypos < (next_inst z).vs_inst_idx` mp_tac >>
  qpat_x_assum `(next_inst z).vs_inst_idx <= endpos` mp_tac >>
  simp[venomStateTheory.next_inst_def, venomInstTheory.get_instruction_def] >>
  rpt strip_tac >> simp[]
QED

Theorem ld_recursive_exceptional_next:
  revert_forward_pair bb copypos endpos /\
  copypos <= t.vs_inst_idx /\ t.vs_inst_idx <= endpos /\
  get_instruction bb t.vs_inst_idx = SOME j /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks) /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qspec_then `\s. T` mp_tac ld_recursive_exceptional_next_anchor >>
  BETA_TAC >> pure_rewrite_tac [AND_CLAUSES] >> simp[]
QED

(* Entry diagnostic: the raw supply boundary needs separation from the source
   variables. Both DLOAD and DLOADBYTES occur before the forwarding copy. *)
Theorem ld_revert_entry_supply_collision_probe[local]:
  let bb = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ASSIGN [Lit 0w] ["formal_var_0"];
     mk_inst 1 DLOAD [Lit 0w] ["loaded"];
     mk_inst 2 DLOADBYTES [Lit 0w; Lit 0w; Lit 0w] [];
     mk_inst 3 RETURNDATACOPY [Lit 0w; Var "formal_var_0"; Lit 0w] [];
     mk_inst 4 REVERT [Lit 0w; Lit 0w] []] |> in
  let a = <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
    irs_used_inst_ids := []; irs_used_vars := []; irs_used_labels := [] |> in
  revert_forward_pair bb 3 4 /\
  ~revert_forward_pair (FST (lower_dload_block_supply a bb)) 7 8 /\
  revert_forward_pair
    (FST (lower_dload_block_supply
      (a with irs_used_vars := ["formal_var_0"; "loaded"]) bb)) 7 8
Proof
  CONV_TAC EVAL >> simp[] >> CONV_TAC EVAL >> simp[]
QED

(* EXCEPTIONAL ENTRY AUDIT (not a theorem or an assumed closure).

   The collision probe above refutes transport for arbitrary raw supplies:
   ASSIGN formal_var_0 = 0; DLOAD 0 -> loaded; DLOADBYTES 0 0 0;
   RETURNDATACOPY 0 formal_var_0 0; REVERT 0 0.
   Empty used-vars lets the inserted ALLOCA overwrite formal_var_0. Source
   (3,4) is a pair; target (7,8) is not. Reserving the two source variables
   restores the pair. This is NOT a counterexample to the configured pass.

   Required semantic interface for a general proof:
   For source operands x,y whose variables belong to block_ir_vars bb,
     same_after_assigns (REVERSE (TAKE c bb.bb_instructions)) x y
       ==> same_after_assigns (REVERSE before) x y.
   Generated ALLOCA/ADD outputs must be separated from these variables.
   Non-ASSIGN writes are NOT ignored: step_back_assign returns NONE on a
   matching output. DLOAD's final MLOAD has exactly its original outputs;
   generated writes can be skipped only with freshness. DLOADBYTES removes
   any malformed original outputs, so a universal resolution EQUALITY is
   not justified without shape; forward same_after_assigns transport is the
   appropriate prospective interface. Malformed lowering branches are kept.

   Literal suffix from ld_lower_revert_pair_suffix:
     before ++ copy :: (mid ++ rev :: after), EVERY ASSIGN mid.
   The three pair clauses reduce separately to:
     same_after_assigns (REVERSE before) src (Lit 0w);
     same_after_assigns (REVERSE before) p
       (resolve_block_assigns (REVERSE mid) p');
     same_after_assigns (REVERSE before) rds
       (resolve_block_assigns (REVERSE mid) rds').
   The middle resolution is literally unchanged. Its resulting operands
   are either original operands or ASSIGN sources in mid, hence supported
   by block_ir_vars bb. Each clause needs the forward prefix interface;
   none follows just from interval opcode preservation.

   CFGNorm supply_*_cong lemmas require equal-length LIST_REL with equal
   opcodes/outputs and identical ASSIGNs. They do not apply to a 1:N DLOAD
   expansion. supply_block_image_revert_forward_pair is CFGNorm-specific.

   Premise producers for the quotation below:
   - fn_pass_step: lookup_unique_function in observed, and covers_unit fa
     observed. Together these supply coverage of fn_ir_vars fn.
   - fn.fn_blocks=bpre++bb::bpost: block variables are function variables.
   - lower_dload_blocks_supply fa bpre=(qpre,a0): used-vars monotonicity
     (lower_dload_blocks_supply_vars) transports coverage to block supply.
   - segment decomposition: existing candidate and supply append lemmas
     provide the block and TAKE-prefix equations; fresh_ir_var_contract
     separates each generated name from initial used-vars, monotonically.
   No new source shape assumption is needed merely for the intended forward
   same_after_assigns transport. It remains UNPROVED, not a premise available
   to later proofs. Configuration must produce the coverage premise.

   Consumer cases still distinct:
   - ordinary completion arriving at copy: this boundary gives pair syntax
     only; source/target successor positions and lookup still need producers.
   - block entry at copy index zero: ld_lower_revert_pair_zero already gives
     pair syntax. Actual PHI execution and entry positions remain separate.
   - entry at REVERT endpoint: in_revert_forward includes this endpoint too.
     Same pair transport would locate the shifted endpoint, not copypos.
     A prefix lowering length equation and actual endpoint position are
     still needed. A copy-only entry argument cannot cover this branch.
   Thus neither full NEXT/BLOCK closure nor normal-to-exceptional execution
   is asserted by this ledger or its typechecked prospective quotation.
*)
val ld_revert_entry_prospective = ``
  EVERY (\v. MEM v a.irs_used_vars) (block_ir_vars bb) /\
  revert_forward_pair bb c e /\
  lower_dload_block_supply a bb = (gb,b) /\
  lower_dload_insts_supply a (TAKE c bb.bb_instructions) = (before,q) ==>
  revert_forward_pair gb (LENGTH before) (LENGTH before + (e-c))``;

Theorem ld_recursive_configured_revert_anchor[local]:
  !Q.
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed fa fn out /\
  fn.fn_blocks = bpre ++ bb::bpost /\
  lower_dload_blocks_supply fa bpre = (qpre,a0) /\
  lower_dload_block_supply a0 bb = (gb,a3) /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lower_dload_insts_supply a0 (TAKE s.vs_inst_idx bb.bb_instructions) = (p,a1) /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  t.vs_inst_idx = LENGTH p /\
  get_instruction gb t.vs_inst_idx = SOME j ==>
  (^ld_recursive_post_anchor) vs0 CT stk un gn j t
Proof
  gen_tac >> strip_tac >>
  `MEM fn observed.cu_context.ctx_functions /\ ir_supply_covers_unit fa observed` by
    (fs[o1PassContractTheory.fn_pass_step_def,
        venomFnScheduleRunnerTheory.lookup_unique_function_def, AllCaseEqs()] >>
     `MEM fn (FILTER (\f. f.fn_name = fn.fn_name)
        observed.cu_context.ctx_functions)` by simp[] >> gvs[MEM_FILTER]) >>
  `EVERY (\v. MEM v fa.irs_used_vars) (FLAT (MAP inst_ir_vars bb.bb_instructions))` by
    (fs[venomFnScheduleRunnerTheory.ir_supply_covers_unit_def,
        venomFnScheduleRunnerTheory.list_subset_def, irSupplyTheory.unit_ir_vars_def,
        irSupplyTheory.fn_ir_vars_def, irSupplyTheory.block_ir_vars_def,
        EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     fs[lambdify irSupplyTheory.block_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     metis_tac[MEM_APPEND, MEM]) >>
  `EVERY (\v. MEM v a0.irs_used_vars) (FLAT (MAP inst_ir_vars bb.bb_instructions))` by
    (drule ld_blocks_supply_used_vars_mono >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ld_configured_revert_interval_entry >> strip_tac >>
  BETA_TAC >> disj2_tac >>
  qexistsl_tac [`gb`, `copypos`, `endpos`] >> gvs[]
QED

Theorem ld_recursive_configured_revert_entry:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed fa fn out /\
  fn.fn_blocks = bpre ++ bb::bpost /\
  lower_dload_blocks_supply fa bpre = (qpre,a0) /\
  lower_dload_block_supply a0 bb = (gb,a3) /\
  in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lower_dload_insts_supply a0 (TAKE s.vs_inst_idx bb.bb_instructions) = (p,a1) /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  t.vs_inst_idx = LENGTH p /\
  get_instruction gb t.vs_inst_idx = SOME j ==>
  (^ld_recursive_candidate) vs0 CT stk un gn j t
Proof
  qspec_then `\s. T` mp_tac ld_recursive_configured_revert_anchor >>
  BETA_TAC >> pure_rewrite_tac [AND_CLAUSES] >> simp[]
QED

(* A successful singleton NEXT cannot leave the configured block. *)
Theorem ld_singleton_next_post_nonempty[local]:
  ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks) /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  gb.bb_instructions = p ++ i::tail /\
  t.vs_inst_idx = LENGTH p /\
  lower_dload_insts_supply a post = (tail,b) /\
  ~is_terminator i.inst_opcode /\ step_inst fuel CT i t = OK z /\
  active_inst gn j (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  post <> []
Proof
  strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
     gn.fn_blocks = SOME gb` by simp[] >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[active_inst_def] >> rpt strip_tac >>
  `lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
     gn.fn_blocks = SOME bb` by (irule MEM_lookup_block >> simp[]) >>
  gvs[lower_dload_insts_supply_def]
QED

Theorem ld_source_singleton_next_active[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ i::i'::rest /\
  s.vs_inst_idx = LENGTH pre /\ ~is_terminator i.inst_opcode ==>
  !s'. step_inst fuel CS i s = OK s' ==>
    active_inst fn i' (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  simp[active_inst_def] >> qexists_tac `bb` >>
  simp[EL_APPEND2] >> metis_tac[lookup_block_MEM,lookup_block_label]
QED

val ld_recursive_ordinary_zero =
  let
    val (args,body) = strip_abs ld_recursive_candidate
    val (normal,_) = dest_disj body
    val (ws,b) = strip_exists normal
    fun named s = case filter (fn v => fst(dest_var v) = s) ws of
      v::_ => v | [] => raise Fail ("missing witness " ^ s)
    val n = named "n"
    val i = named "i"
    val fnv = named "fn"
    val (_,sem_body) = dest_forall (concl ld_normal_ordinary_next_backward)
    val (sem_pre,_) = dest_imp sem_body
    val ordinary = hd (filter
      (can (match_term ``MEM (ii:instruction).inst_opcode ops``))
      (strip_conj sem_pre))
    val allowed = find_term listSyntax.is_list ordinary
    val restricted = list_mk_exists(ws,
      list_mk_conj [b, ``^n = 0``, ``MEM ^i.inst_opcode ^allowed``,
                   ``opaque_use_ok ^fnv``])
  in list_mk_abs(args,restricted) end;


Theorem ld_recursive_ordinary_next_anchor[local]:
  !Q. ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  (^ld_recursive_ordinary_zero) vs0 CT stk un gn j t /\
  ~is_terminator j.inst_opcode /\ step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) /\
  Q (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_post_anchor) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  gen_tac >> BETA_TAC >> strip_tac >>
  TRY (qpat_x_assum `0 < n` mp_tac >>
       qpat_x_assum `n = 0` SUBST1_TAC >> simp[] >> NO_TAC) >>
  qpat_x_assum `!q. q < LENGTH astk ==> _` (mk_asm "saved") >>
  `i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` by
    (qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[]) >>
  `code = [i] /\ a2 = a1` by
    (qpat_x_assum `lower_dload_inst_supply a1 i = _` mp_tac >>
     simp[lower_dload_inst_supply_def] >> metis_tac[]) >>
  `j = i` by (qpat_x_assum `j = HD code` mp_tac >> simp[]) >>
  qpat_x_assum `j = i` SUBST_ALL_TAC >>
  qpat_x_assum `i = HD code` kall_tac >>
  qpat_x_assum `t = ta` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `un = ua` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `a2 = a1` SUBST_ALL_TAC >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >>
     disch_then (mp_tac o SRULE [EVERY_MEM]) >>
     disch_then (qspec_then `fn` mp_tac) >>
     impl_tac >- simp[] >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     disch_then (mp_tac o CONJUNCT1) >>
     pure_rewrite_tac [fn_labels_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  `gb.bb_instructions = p ++ i::tail` by
    (asm_rewrite_tac [] >> pure_rewrite_tac [GSYM APPEND_ASSOC,APPEND] >> REFL_TAC) >>
  `lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
   t.vs_inst_idx = LENGTH p /\
   lower_dload_insts_supply a1 post = (tail,a3) /\
   ~is_terminator i.inst_opcode /\ step_inst fuel CT i t = OK z` by
    asm_rewrite_tac [] >>
  drule_at (Pat `lookup_block _ _ = _`) ld_singleton_next_post_nonempty >>
  disch_then drule_all >> strip_tac >>
  Cases_on `post` >- gvs[] >>
  rename1 `bb.bb_instructions = pre ++ i::i'::rest` >>
  `!s'. step_inst fuel CS i s = OK s' ==>
     active_inst fn i' (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb`
       (mp_then Any mp_tac ld_source_singleton_next_active) >>
     disch_then (fn th => rpt strip_tac >> drule_all th >> simp[])) >>
  `MEM i (fn_insts fn)` by
    (qpat_x_assum `active_inst fn i s` mp_tac >>
     simp[active_inst_def,fn_insts_def,o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==> v IN V` by
    (rpt strip_tac >> asm_rewrite_tac [] >>
     irule ld_original_operand_support >> metis_tac[]) >>
  `LIST_REL (\A g. FINITE A /\ CARD A <= LENGTH
      (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) (MAP ld_erase_frame astk))` by
    (qpat_assum `LIST_REL _ (A::suspended) _`
       (strip_assume_tac o SRULE []) >>
     simp[MAP_MAP_o,ld_erase_frame_def,combinTheory.o_DEF]) >>
  drule_all ld_normal_ordinary_next_backward >>
  disch_then (qspec_then `SUC t.vs_inst_idx` mp_tac) >> strip_tac >>
  `s'.vs_current_bb = s.vs_current_bb /\
   s'.vs_prev_bb = s.vs_prev_bb /\
   z.vs_current_bb = t.vs_current_bb /\
   z.vs_prev_bb = t.vs_prev_bb` by
    (qpat_assum `step_inst fuel CT i t = OK z` mp_tac >>
     qpat_assum `step_inst fuel CS i s = OK s'` mp_tac >>
     qpat_assum `~is_terminator i.inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule_all step_preserves_control_flow >> strip_tac >>
     qpat_x_assum `step_inst fuel CT i t = OK z` kall_tac >>
     drule_all step_preserves_control_flow >> simp[]) >>
  Cases_on `lower_dload_inst_supply a1 i'` >>
  rename1 `lower_dload_inst_supply a1 i' = (nextcode,nexta)` >>
  Cases_on `lower_dload_insts_supply nexta rest` >>
  rename1 `lower_dload_insts_supply nexta rest = (nexttail,enda)` >>
  `tail = nextcode ++ nexttail /\ enda = a3` by
    (qpat_assum `lower_dload_insts_supply a1 (i'::rest) = _`
       (mp_tac o PURE_REWRITE_RULE [Once lower_dload_insts_supply_def]) >>
     simp[] >> strip_tac >> simp[]) >>
  `nextcode <> []` by
    metis_tac[o1ContractLowerDloadTheory.lower_dload_inst_supply_nonempty] >>
  `lower_dload_insts_supply a0 (pre ++ [i]) = (p ++ [i],a1)` by
    (irule lowerDloadSupplySegmentTheory.lower_dload_insts_supply_append_forward >>
     goal_assum (drule_at Any) >>
     simp[lower_dload_insts_supply_def]) >>
  `j' = HD nextcode` by
    (`lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
        gn.fn_blocks = SOME gb` by
       (simp_tac (srw_ss()) [] >> metis_tac[]) >>
     qpat_assum `active_inst gn j' _`
       (mp_then (Pat `active_inst _ _ _`) mp_tac ld_active_lookup_el) >>
     disch_then (qspec_then `gb` mp_tac) >>
     (impl_tac >- asm_rewrite_tac []) >>
     simp[EL_APPEND2] >> Cases_on `nextcode`
     >- metis_tac[] >> simp[]) >>
  Cases_on `in_revert_forward fn (s' with vs_inst_idx := SUC s.vs_inst_idx)`
  >- suspend "revert_successor" >>
  disj1_tac >>
  qexistsl_tac [`astk`, `gstk`, `k`, `L`, `AP`, `ld_step_prov AP AG L i`,
    `step_taint i s s' tn`, `fn`, `i'`,
    `s' with vs_inst_idx := SUC s.vs_inst_idx`,
    `z with vs_inst_idx := SUC t.vs_inst_idx`, `step_taint i t z un`,
    `V`, `U`, `E`, `H`, `BP`, `ld_step_prov BP BH H i`, `live`, `keys`,
    `A`, `suspended`, `f`, `fa`, `fb`, `bb`, `gb`, `a0`, `a1`,
    `nexta`, `a3`, `pre ++ [i]`, `rest`, `p ++ [i]`, `nextcode`,
    `nexttail`, `bpre`, `bpost`, `qpre`, `qpost`, `supports`, `savedkeys`,
    `s0`, `0`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  asm "saved" (fn th => asm_rewrite_tac [th]) >>
  conj_tac
  >- (qexistsl_tac [`cpre`, `cpost`, `gpre`, `gpost`, `observed`, `out`] >>
      asm_rewrite_tac []) >>
  simp[GSYM APPEND_ASSOC] >>
  metis_tac[]
QED

Resume ld_recursive_ordinary_next_anchor[revert_successor]:
  `lookup_block (s' with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
     fn.fn_blocks = SOME bb /\
   lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
     gn.fn_blocks = SOME gb` by
    (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `lower_dload_insts_supply a0
     (TAKE (s' with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx
        bb.bb_instructions) = (p ++ [i],a1)` by
    (simp_tac (srw_ss()) [] >>
     qpat_assum `bb.bb_instructions = _` SUBST1_TAC >>
     qpat_assum `s.vs_inst_idx = _` SUBST1_TAC >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  `(z with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = LENGTH (p ++ [i])` by
    simp[] >>
  `get_instruction gb (z with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = SOME j'` by
    (simp[get_instruction_def, EL_APPEND2] >>
     Cases_on `nextcode` >- metis_tac[] >> simp[]) >>
  irule (BETA_RULE (Q.SPEC `Q` ld_recursive_configured_revert_anchor)) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `lower_dload_insts_supply _ (TAKE _ _) = _`)) >>
  goal_assum (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_dload_blocks_supply _ _ = _`)) >>
  goal_assum (drule_at (Pat `lower_dload_block_supply _ _ = _`)) >>
  asm_rewrite_tac [] >> metis_tac[]
QED

Finalise ld_recursive_ordinary_next_anchor

Theorem ld_recursive_ordinary_next:
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  (^ld_recursive_ordinary_zero) vs0 CT stk un gn j t /\
  ~is_terminator j.inst_opcode /\ step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qspec_then `\s. T` mp_tac ld_recursive_ordinary_next_anchor >>
  BETA_TAC >> pure_rewrite_tac [AND_CLAUSES] >> simp[]
QED

val ld_recursive_alloca_zero =
  let
    val (args,body) = strip_abs ld_recursive_candidate
    val (normal,_) = dest_disj body
    val (ws,b) = strip_exists normal
    fun named s = hd (filter (fn v => fst(dest_var v) = s) ws)
    val n = named "n"
    val i = named "i"
  in list_mk_abs(args,list_mk_exists(ws,
       list_mk_conj [b, ``^n = 0``, ``^i.inst_opcode = ALLOCA``])) end;

Theorem ld_recursive_alloca_next_anchor[local]:
  !Q. ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (^ld_recursive_alloca_zero) vs0 CT stk un gn j t /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) /\
  Q (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_post_anchor) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  gen_tac >> BETA_TAC >> strip_tac >>
  TRY (qpat_x_assum `0 < n` mp_tac >>
       qpat_x_assum `n = 0` SUBST1_TAC >> simp[] >> NO_TAC) >>
  qpat_x_assum `!q. q < LENGTH astk ==> _` (mk_asm "saved") >>
  `code = [i] /\ a2 = a1` by
    (qpat_x_assum `lower_dload_inst_supply a1 i = _` mp_tac >>
     simp[lower_dload_inst_supply_def] >> metis_tac[]) >>
  `j = i` by (qpat_x_assum `j = HD code` mp_tac >> simp[]) >>
  qpat_x_assum `j = i` SUBST_ALL_TAC >>
  qpat_x_assum `i = HD code` kall_tac >>
  qpat_x_assum `t = ta` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `un = ua` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `a2 = a1` SUBST_ALL_TAC >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >>
     disch_then (mp_tac o SRULE [EVERY_MEM]) >>
     disch_then (qspec_then `fn` mp_tac) >>
     impl_tac >- simp[] >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     disch_then (mp_tac o CONJUNCT1) >>
     pure_rewrite_tac [fn_labels_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  `~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
  `gb.bb_instructions = p ++ i::tail` by
    (asm_rewrite_tac [] >> pure_rewrite_tac [GSYM APPEND_ASSOC,APPEND] >> REFL_TAC) >>
  `lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
   t.vs_inst_idx = LENGTH p /\
   lower_dload_insts_supply a1 post = (tail,a3) /\
   ~is_terminator i.inst_opcode /\ step_inst fuel CT i t = OK z` by
    asm_rewrite_tac [] >>
  drule_at (Pat `lookup_block _ _ = _`) ld_singleton_next_post_nonempty >>
  disch_then drule_all >> strip_tac >>
  Cases_on `post` >- gvs[] >>
  rename1 `bb.bb_instructions = pre ++ i::i'::rest` >>
  `lo <= s.vs_alloca_next` by
    (irule ld_ptr_reachable_frontier_floor >>
     drule ld_annotated_erasure >> metis_tac[]) >>
  `?sz. i.inst_operands = [Lit sz]` by
    (qpat_x_assum `step_inst fuel CT i t = OK z` mp_tac >>
     qpat_x_assum `i.inst_opcode = ALLOCA` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `?sz. i.inst_operands = [Lit sz]` >- simp[] >>
     drule_all lowerDloadAllocaHeadroomTheory.ld_alloca_malformed_failure >>
     disch_then (qspecl_then [`t`,`fuel`,`CT`] mp_tac) >> simp[]) >>
  `?outvar. i.inst_outputs = [outvar]` by
    (qpat_x_assum `step_inst fuel CT i t = OK z` mp_tac >>
     simp[step_inst_non_invoke,step_inst_base_opcode_eqs,exec_alloca_def,
          AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `MEM i (fn_insts fn)` by
    (qpat_x_assum `active_inst fn i s` mp_tac >>
     simp[active_inst_def,fn_insts_def,o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `i.inst_id NOTIN keys` by (asm_rewrite_tac [] >> simp[MEM_MAP] >> metis_tac[]) >>
  `wf_function fn` by
    (qpat_x_assum `o1_ctx_shape CS` mp_tac >>
     simp[o1PassContractTheory.o1_ctx_shape_def,EVERY_MEM,
          o1PassContractTheory.o1_fn_shape_def] >>
     disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
  `raw_reachable vs0 CS fn i s` by
    (irule ld_frame_reachable_raw >> drule ld_annotated_erasure >> metis_tac[]) >>
  `ld_alloc_account keys (32 * SUM (MAP CARD suspended)) A s t` by
    (drule ld_normal_data_geometry >> simp[]) >>
  `CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn)) /\
   LIST_REL (\a g. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
     (fn_insts g.cf_fn))) suspended (MAP ld_erase_frame astk)` by
    (qpat_assum `LIST_REL _ (A::suspended) _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[LIST_REL_EL_EQN,ld_erase_frame_def] >>
     rpt strip_tac >> fs[EL_MAP,ld_erase_frame_def] >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[EL_MAP]) >>
  Cases_on `lower_dload_inst_supply a1 i'` >>
  rename1 `lower_dload_inst_supply a1 i' = (nextcode,nexta)` >>
  Cases_on `lower_dload_insts_supply nexta rest` >>
  rename1 `lower_dload_insts_supply nexta rest = (nexttail,enda)` >>
  `tail = nextcode ++ nexttail /\ enda = a3` by
    (qpat_assum `lower_dload_insts_supply a1 (i'::rest) = _`
       (mp_tac o PURE_REWRITE_RULE [Once lower_dload_insts_supply_def]) >>
     simp[] >> strip_tac >> simp[]) >>
  `ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
     astk (live DELETE (0,k)) keys (32 * SUM (MAP CARD suspended))
     A suspended gstk f` by (irule ld_normal_data_serial_delete >> metis_tac[]) >>
  qpat_x_assum `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ live _ _ _ _ _ _`
    kall_tac >>
  `FLOOKUP L i.inst_id = NONE ==> (0,k) NOTIN live DELETE (0,k)` by simp[] >>
  `lower_dload_insts_supply nexta rest = (nexttail,a3)` by metis_tac[] >>
  drule_all ld_configured_alloca_next_backward >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  `s'.vs_current_bb = s.vs_current_bb /\
   s'.vs_prev_bb = s.vs_prev_bb /\
   z.vs_current_bb = t.vs_current_bb /\
   z.vs_prev_bb = t.vs_prev_bb` by
    (qpat_assum `step_inst fuel CT i t = OK z` mp_tac >>
     qpat_assum `step_inst fuel CS i s = OK s'` mp_tac >>
     qpat_assum `i.inst_opcode = ALLOCA` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
     drule_all step_preserves_control_flow >> strip_tac >>
     qpat_x_assum `step_inst fuel CT i t = OK z` kall_tac >>
     drule_all step_preserves_control_flow >> simp[]) >>
  `nextcode <> []` by
    metis_tac[o1ContractLowerDloadTheory.lower_dload_inst_supply_nonempty] >>
  `j' = HD nextcode` by
    (`lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
        gn.fn_blocks = SOME gb` by
       (simp_tac (srw_ss()) [] >> metis_tac[]) >>
     qpat_assum `active_inst gn j' _`
       (mp_then (Pat `active_inst _ _ _`) mp_tac ld_active_lookup_el) >>
     disch_then (qspec_then `gb` mp_tac) >>
     (impl_tac >- asm_rewrite_tac []) >>
     simp[EL_APPEND2] >> Cases_on `nextcode`
     >- metis_tac[] >> simp[]) >>
  Cases_on `in_revert_forward fn (s' with vs_inst_idx := SUC s.vs_inst_idx)`
  >- suspend "revert_successor" >>
  disj1_tac >>
  qexistsl_tac [`astk`, `gstk`, `k'`, `L'`, `AP`, `ld_step_prov AP AG L' i`,
    `step_taint i s s' tn`, `fn`, `i'`,
    `s' with vs_inst_idx := SUC s.vs_inst_idx`,
    `z with vs_inst_idx := SUC t.vs_inst_idx`, `step_taint i t z un`,
    `V`, `U`, `E'`, `H'`, `BP`, `ld_step_prov BP BH H' i`,
    `if FLOOKUP L i.inst_id = NONE then (0,k) INSERT (live DELETE (0,k))
     else live DELETE (0,k)`, `keys`,
    `A`, `suspended`, `f`, `fa`, `fb`, `bb`, `gb`, `a0`, `a1`,
    `nexta`, `a3`, `pre ++ [i]`, `rest`, `p ++ [i]`, `nextcode`,
    `nexttail`, `bpre`, `bpost`, `qpre`, `qpost`, `supports`, `savedkeys`,
    `s0`, `0`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  asm_rewrite_tac [] >>
  conj_tac
  >- (qexistsl_tac [`cpre`, `cpost`, `gpre`, `gpost`, `observed`, `out`] >>
      asm_rewrite_tac []) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  suspend "saved_successor"
QED

Resume ld_recursive_alloca_next_anchor[revert_successor]:
  `lookup_block (s' with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
     fn.fn_blocks = SOME bb /\
   lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
     gn.fn_blocks = SOME gb` by
    (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `lower_dload_insts_supply a0
     (TAKE (s' with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx
        bb.bb_instructions) = (p ++ [i],a1)` by
    (simp_tac (srw_ss()) [] >>
     qpat_assum `bb.bb_instructions = _` SUBST1_TAC >>
     qpat_assum `s.vs_inst_idx = _` SUBST1_TAC >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  `(z with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = LENGTH (p ++ [i])` by
    simp[] >>
  `get_instruction gb (z with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = SOME j'` by
    (simp[get_instruction_def, EL_APPEND2] >>
     Cases_on `nextcode` >- metis_tac[] >> simp[]) >>
  irule (BETA_RULE (Q.SPEC `Q` ld_recursive_configured_revert_anchor)) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `lower_dload_insts_supply _ (TAKE _ _) = _`)) >>
  goal_assum (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_dload_blocks_supply _ _ = _`)) >>
  goal_assum (drule_at (Pat `lower_dload_block_supply _ _ = _`)) >>
  asm_rewrite_tac [] >> metis_tac[]
QED

Resume ld_recursive_alloca_next_anchor[saved_successor]:
  all_tac >>
  drule lowerDloadProvenanceSupportTheory.ld_annotated_active_inst >> strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (qpat_x_assum `lookup_block s.vs_current_bb _ = SOME bb` mp_tac >> simp[]) >>
  conj_tac >- (qpat_x_assum `lookup_block t.vs_current_bb _ = SOME gb` mp_tac >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (qpat_x_assum `active_inst fn i' _` mp_tac >> simp[]) >>
  qmatch_goalsub_abbrev_tac `ld_saved_embedded _ EN _ _ _ _ _` >>
  `!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
      FLOOKUP EN owner = FLOOKUP E owner` by
    (rpt strip_tac >>
     `SND owner < k` by
       (qpat_assum `ld_annotated_reachable _ _ _ k _ _ _ _ _ _ _`
          (mp_then Any mp_tac ld_annotated_serial) >>
        disch_then drule >> simp[]) >>
     `owner <> (0,k)` by (strip_tac >> gvs[]) >>
     Cases_on `FLOOKUP L i.inst_id = NONE` >>
     simp[Abbr `EN`, FLOOKUP_UPDATE]) >>
  qx_gen_tac `q` >> strip_tac >>
  `(^ld_recursive_saved) EN q` by
    (irule ld_recursive_saved_support >>
     conj_tac >- metis_tac[] >>
     qexists_tac `E` >> conj_tac
     >- (rpt strip_tac >> first_assum irule >>
         simp[ld_live_def] >> metis_tac[MEM_EL]) >>
     BETA_TAC >> asm "saved" (qspec_then `q` mp_tac) >> simp[]) >>
  pop_assum mp_tac >> BETA_TAC >> asm_rewrite_tac []
QED

Finalise ld_recursive_alloca_next_anchor

Theorem ld_recursive_alloca_next:
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (^ld_recursive_alloca_zero) vs0 CT stk un gn j t /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qspec_then `\s. T` mp_tac ld_recursive_alloca_next_anchor >>
  BETA_TAC >> pure_rewrite_tac [AND_CLAUSES] >> simp[]
QED

val ld_recursive_block_zero =
  let
    val (args,body) = strip_abs ld_recursive_candidate
    val (ws,b) = strip_exists (fst (dest_disj body))
    fun named s = hd (filter (fn v => fst(dest_var v) = s) (ws @ args))
    val n = named "n" and code = named "code" and i = named "i"
    val a2 = named "a2" and a1 = named "a1"
    val j = named "j" and t = named "t" and ta = named "ta"
    val un = named "un" and ua = named "ua"
  in list_mk_abs(args,list_mk_exists(ws,
       list_mk_conj [b, ``^n = 0``, ``^code = [^i]``, ``^a2 = ^a1``,
         ``^j = ^i``, ``^t = ^ta``, ``^un = ^ua``])) end;

Theorem ld_recursive_block_anchor:
  (^ld_recursive_candidate) vs0 CT stk un gn j t /\
  is_terminator j.inst_opcode /\ step_inst fuel CT j t = OK z ==>
  (^ld_recursive_block_zero) vs0 CT stk un gn j t
Proof
  reverse (BETA_TAC >> strip_tac)
  >- (drule_all ld_revert_pair_interval_step >>
      disch_then (qspecl_then [`z`, `t`, `ret`, `fuel`, `CT`] mp_tac) >>
      simp[]) >>
  `MEM j code` by
    (qpat_x_assum `code <> []` mp_tac >>
     qpat_x_assum `j = _` mp_tac >>
     TRY (qpat_x_assum `n < LENGTH code` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `code` >> simp[] >>
     Cases_on `n` >> simp[] >> metis_tac[MEM_EL]) >>
  `j = i` by
    (irule o1ContractLowerDloadTheory.lower_dload_inst_supply_control >>
     metis_tac[]) >>
  `code = [i] /\ a2 = a1` by
    (qpat_x_assum `lower_dload_inst_supply a1 i = _` mp_tac >>
     `i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` by
       (qpat_x_assum `is_terminator _` mp_tac >>
        qpat_x_assum `j = i` SUBST_ALL_TAC >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        rpt strip_tac >> gvs[is_terminator_def]) >>
     simp[lower_dload_inst_supply_def] >> metis_tac[]) >>
  TRY (qpat_x_assum `0 < n` mp_tac >>
       qpat_x_assum `n < LENGTH code` mp_tac >>
       qpat_x_assum `code = [i]` SUBST_ALL_TAC >> simp[] >> NO_TAC) >>
  qexistsl_tac [`astk`, `gstk`, `k`, `L`, `AP`, `AG`, `tn`, `fn`, `i`,
    `s`, `ta`, `ua`, `V`, `U`, `E`, `H`, `BP`, `BH`, `live`, `keys`, `A`,
    `suspended`, `f`, `fa`, `fb`, `bb`, `gb`, `a0`, `a1`, `a2`, `a3`,
    `pre`, `post`, `p`, `code`, `tail`, `bpre`, `bpost`, `qpre`, `qpost`,
    `supports`, `savedkeys`, `s0`, `n`] >>
  asm_rewrite_tac [] >> simp[] >>
  qexistsl_tac [`cpre`, `cpost`, `gpre`, `gpost`, `observed`, `out`] >>
  asm_rewrite_tac []
QED

val ld_recursive_block_goal =
  let val (v0::ct::rest, body) = strip_forall (List.nth(ld_recursive_clause_goals,2))
  in subst [v0 |-> mk_var("vs0", type_of v0),
            ct |-> mk_var("CT", type_of ct)]
       (list_mk_forall (rest, body))
  end;

val ld_recursive_block_anchor_goal =
  let
    val (args,body) = strip_forall ld_recursive_block_goal
    val (prem,post) = dest_imp body
    val target = List.last (snd(strip_comb post))
    val post' = subst [ld_recursive_candidate |-> ld_recursive_post_anchor] post
  in list_mk_forall(args,mk_imp(mk_conj(prem,mk_comb(mk_var("Q", ``:venom_state -> bool``),target)),post')) end;

Theorem ld_recursive_block_clause_anchor[local]:
  !Q.
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions /\
  lo = vs0.vs_alloca_next ==>
  ^ld_recursive_block_anchor_goal
Proof
  gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all ld_recursive_block_anchor >>
  qpat_x_assum `(\vs0 CT projected_stk un gn j t. _) _ _ _ _ _ _ _` kall_tac >>
  BETA_TAC >> strip_tac >>
  TRY (qpat_x_assum `0 < n` mp_tac >>
       qpat_x_assum `n = 0` SUBST1_TAC >> simp[] >> NO_TAC) >>
  qpat_x_assum `!q. q < LENGTH astk ==> _` (mk_asm "saved") >>
  qpat_x_assum `inst = i` SUBST_ALL_TAC >>
  qpat_x_assum `s = ta` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `tn = ua` (SUBST_ALL_TAC o SYM) >>
  `?plo. ptr_discipline plo CS vs0` by
    (qpat_assum `o1_src_inv D CS vs0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[o1PassContractTheory.o1_src_inv_def] >> metis_tac[]) >>
  `opaque_use_ok fn'` by
    (qpat_assum `o1_ctx_shape CS`
       (strip_assume_tac o SRULE [o1PassContractTheory.o1_ctx_shape_def,
          o1PassContractTheory.o1_fn_shape_def, EVERY_MEM]) >>
     first_x_assum (qspec_then `fn'` mp_tac) >>
     simp[unitShapeDefsTheory.fn_shape_ok_def] >> metis_tac[]) >>
  `MEM i.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[ld_successful_terminator_branch] >>
  `ld_frame_data V U E L H AP BP AG BH tn' tn s'' s` by
    metis_tac[ld_normal_data_frame] >>
  `U = {v | MEM v (fn_ir_vars fn') /\ ~retpc_var fn' v}` by simp[] >>
  qpat_x_assum `U = {v | MEM v (fn_ir_vars fn') /\ ~retpc_var fn' v}` SUBST_ALL_TAC >>
  drule_all ld_reachable_jump_backward >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  `ld_normal_data CS fn' V {v | MEM v (fn_ir_vars fn') /\ ~retpc_var fn' v}
    lo E L H AP BP AG BH tn' tn (jump_to lbl s'') (jump_to lbl s)
    astk live keys (32 * SUM (MAP CARD suspended)) A suspended gstk f` by
    (rewrite_tac[ld_normal_data_jump] >> asm_rewrite_tac[]) >>
  `s' = jump_to lbl s` by metis_tac[] >>
  `enters_block fn (jump_to lbl s) s1` by metis_tac[] >>
  `s'.vs_current_bb = (jump_to lbl s'').vs_current_bb /\
   s'.vs_prev_bb = (jump_to lbl s'').vs_prev_bb` by simp[venomStateTheory.jump_to_def] >>
  `!bb i v. MEM bb fn'.fn_blocks /\ MEM i bb.bb_instructions /\
    MEM (Var v) i.inst_operands ==> v IN V` by
    (qpat_assum `V = set (fn_ir_vars fn')` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt strip_tac >>
     irule ld_original_operand_support >> goal_assum (drule_at Any) >>
     simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `{v | MEM v (fn_ir_vars fn') /\ ~retpc_var fn' v} =
    {v | v IN V /\ ~retpc_var fn' v}` by
    (qpat_assum `V = set (fn_ir_vars fn')` SUBST1_TAC >> simp[NoAsms]) >>
  `(jump_to lbl s'').vs_current_bb = (jump_to lbl s).vs_current_bb /\
   (jump_to lbl s'').vs_prev_bb = (jump_to lbl s).vs_prev_bb` by
    simp[venomStateTheory.jump_to_def] >>
  drule_all ld_normal_data_entry_backward >> strip_tac >>
  `wf_function fn'` by
    (qpat_assum `o1_ctx_shape CS`
       (strip_assume_tac o SRULE [o1PassContractTheory.o1_ctx_shape_def,
          o1PassContractTheory.o1_fn_shape_def, EVERY_MEM]) >>
     first_x_assum (qspec_then `fn'` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all ld_wf_enters_block_fetch >> strip_tac >>
  `~vs0.vs_halted` by
    (qpat_assum `o1_run_state_ok vs0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[o1PassContractTheory.o1_run_state_ok_def,
          unitTransformDefsTheory.o1_initial_state_ok_def]) >>
  `~(jump_to lbl s'').vs_halted` by
    (simp[venomStateTheory.jump_to_def] >>
     metis_tac[ld_annotated_not_halted]) >>
  `ld_annotated_reachable vs0 CS astk k L AP
     (ld_entry_prov fn' (jump_to lbl s'') AG)
     (entry_taint_vars fn' (jump_to lbl s'') tn') fn' inst s1'` by
    (irule ld_annotated_reachable_block >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `lower_dload_blocks_supply fa fn'.fn_blocks = (fn.fn_blocks,fb)` by
    (qpat_assum `lower_dload_function_supply fa fn' = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lower_dload_function_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  drule_all lower_dload_blocks_supply_lookup_forward >> strip_tac >>
  drule_all lower_dload_blocks_supply_selected_prefix >> strip_tac >>
  rename1 `lower_dload_block_supply ac bc = (bb'',ad)` >>
  `bc = bb'` by
    (qpat_x_assum `lookup_block s1'.vs_current_bb fn'.fn_blocks = SOME bc` mp_tac >>
     qpat_x_assum `lookup_block s1'.vs_current_bb fn'.fn_blocks = SOME bb'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qpat_x_assum `bc = bb'` SUBST_ALL_TAC >>
  `s1'.vs_inst_idx = phi_prefix_length bb'.bb_instructions` by
    (qpat_assum `enters_block fn' _ s1'` mp_tac >>
     qpat_assum `lookup_block s1'.vs_current_bb fn'.fn_blocks = SOME bb'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[enters_block_def] >> rpt strip_tac >>
     drule eval_phis_only_updates_vs_vars >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_current_bb`) >>
     simp[] >> strip_tac >> fs[] >> gvs[]) >>
  `?post0. bb'.bb_instructions =
       TAKE s1'.vs_inst_idx bb'.bb_instructions ++ inst::post0` by
    (qpat_assum `get_instruction bb' s1'.vs_inst_idx = SOME inst` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[get_instruction_def] >> strip_tac >>
     qexists_tac `DROP (SUC s1'.vs_inst_idx) bb'.bb_instructions` >>
     metis_tac[rich_listTheory.TAKE_DROP_SUC]) >>
  `lower_dload_insts_supply ac bb'.bb_instructions =
     (bb''.bb_instructions,ad)` by
    (qpat_assum `lower_dload_block_supply ac bb' = (bb'',ad)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lower_dload_block_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  drule o1LowerDloadJointEntryTheory.ld_supply_phi_boundary >> strip_tac >>
  `?entrycode nexts entrytail.
     lower_dload_inst_supply ac inst = (entrycode,nexts) /\
     lower_dload_insts_supply nexts post0 = (entrytail,ad) /\
     bb''.bb_instructions = TAKE s1'.vs_inst_idx bb'.bb_instructions ++ entrycode ++ entrytail` by
    (`lower_dload_insts_supply ac (TAKE s1'.vs_inst_idx bb'.bb_instructions) =
        (TAKE s1'.vs_inst_idx bb'.bb_instructions,ac)` by metis_tac[] >>
     pop_assum mp_tac >>
     qpat_assum `lower_dload_insts_supply ac bb'.bb_instructions = _` mp_tac >>
     qpat_assum `bb'.bb_instructions = TAKE _ _ ++ inst::post0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_x_assum `lower_dload_insts_supply ac bb'.bb_instructions = _` mp_tac >>
     qpat_assum `bb'.bb_instructions = TAKE _ _ ++ inst::post0` SUBST1_TAC >>
     disch_then (strip_assume_tac o MATCH_MP o1ContractLowerDloadTheory.lower_dload_insts_supply_append) >>
     `lower_dload_insts_supply ac (TAKE s1'.vs_inst_idx bb'.bb_instructions) =
        (TAKE s1'.vs_inst_idx bb'.bb_instructions,ac)` by metis_tac[] >>
     gvs[] >>
     qpat_x_assum `lower_dload_insts_supply ac (inst::post0) = _`
       (strip_assume_tac o SRULE [Once lower_dload_insts_supply_def, AllCaseEqs()]) >>
     qpat_assum `bb'.bb_instructions = _`
       (fn th => once_rewrite_tac[GSYM th]) >>
     qexistsl_tac [`out`,`s1`,`outs`] >> simp[]) >>
  `s1'.vs_inst_idx < LENGTH bb'.bb_instructions` by
    (qpat_assum `get_instruction bb' s1'.vs_inst_idx = SOME inst` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[get_instruction_def] >> metis_tac[]) >>
  `LENGTH (TAKE s1'.vs_inst_idx bb'.bb_instructions) = s1'.vs_inst_idx` by
    (qpat_assum `s1'.vs_inst_idx < LENGTH bb'.bb_instructions` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[LENGTH_TAKE]) >>
  `lower_dload_insts_supply ac (TAKE s1'.vs_inst_idx bb'.bb_instructions) =
    (TAKE s1'.vs_inst_idx bb'.bb_instructions,ac)` by metis_tac[] >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb''` by metis_tac[] >>
  `ALL_DISTINCT (fn_labels fn)` by
    (qpat_assum `lower_dload_function_supply fa fn' = (fn,fb)` mp_tac >>
     qpat_assum `wf_function fn'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     fs[venomWfTheory.wf_function_def]) >>
  `get_instruction bb'' s1.vs_inst_idx = SOME inst'` by
    (qpat_assum `ALL_DISTINCT (fn_labels fn)` mp_tac >>
     qpat_assum `active_inst fn inst' s1` mp_tac >>
     qpat_assum `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb''` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[active_inst_def] >>
     `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> fs[fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  Cases_on `in_revert_forward fn' s1'`
  >- (irule (BETA_RULE ld_recursive_configured_revert_anchor) >>
      goal_assum (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `lower_dload_insts_supply _ (TAKE _ _) = _`)) >>
      goal_assum (drule_at (Pat `lower_dload_blocks_supply _ _ = _`)) >>
      goal_assum (drule_at (Pat `lower_dload_block_supply _ _ = _`)) >>
      qexists_tac `post'` >> rpt conj_tac >> metis_tac[]) >>
  `entrycode <> []` by metis_tac[o1ContractLowerDloadTheory.lower_dload_inst_supply_nonempty] >>
  `inst' = HD entrycode` by
    (qpat_assum `get_instruction bb'' s1.vs_inst_idx = SOME inst'` mp_tac >>
     qpat_assum `bb''.bb_instructions = TAKE _ _ ++ entrycode ++ entrytail` mp_tac >>
     qpat_assum `LENGTH (TAKE s1'.vs_inst_idx bb'.bb_instructions) = _` mp_tac >>
     qpat_assum `s1'.vs_inst_idx = s1.vs_inst_idx` mp_tac >>
     qpat_assum `entrycode <> []` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >>
     qmatch_asmsub_abbrev_tac `LENGTH pref = s1'.vs_inst_idx` >>
     Cases_on `entrycode` >> gvs[get_instruction_def, EL_APPEND2] >>
     qpat_x_assum `LENGTH pref = _` (fn th => rewrite_tac[GSYM th]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[NoAsms, EL_APPEND2]) >>
  disj1_tac >>
  qexistsl_tac [`astk`,`gstk`,`k`,`L`,`AP`,
    `ld_entry_prov fn' (jump_to lbl s'') AG`,
    `entry_taint_vars fn' (jump_to lbl s'') tn'`,`fn'`,`inst`,`s1'`,`s1`,
    `entry_taint_vars fn (jump_to lbl s) tn`,`V`,
    `{v | v IN V /\ ~retpc_var fn' v}`,`E`,`H`,`BP`,
    `ld_entry_prov fn (jump_to lbl s) BH`,`live`,`keys`,`A`,`suspended`,`f`,
    `fa`,`fb`,`bb'`,`bb''`,`ac`,`ac`,`nexts`,`ad`,
    `TAKE s1'.vs_inst_idx bb'.bb_instructions`,`post0`,
    `TAKE s1'.vs_inst_idx bb'.bb_instructions`,`entrycode`,`entrytail`,
    `pre'`,`post'`,`gp`,`gt`,`supports`,`savedkeys`,`s0`,`0`] >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (asm "saved" mp_tac >> simp[NoAsms] >> NO_TAC) >>
  TRY (qpat_assum `{v | MEM v (fn_ir_vars fn') /\ ~retpc_var fn' v} = _`
        (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `s' = jump_to lbl s` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms] >>
  FIRST [first_assum ACCEPT_TAC,
    sym_tac >> first_assum ACCEPT_TAC,
    (qpat_assum `s1'.vs_inst_idx = s1.vs_inst_idx` mp_tac >>
     qpat_assum `LENGTH (TAKE s1'.vs_inst_idx bb'.bb_instructions) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> NO_TAC),
    (qexistsl_tac [`cpre`,`cpost`,`gpre`,`gpost`,`observed`,`out`] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)]
QED

Theorem ld_recursive_block_clause:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions /\
  lo = vs0.vs_alloca_next ==>
  ^ld_recursive_block_goal
Proof
  qspec_then `\s. T` mp_tac ld_recursive_block_clause_anchor >>
  BETA_TAC >> pure_rewrite_tac [AND_CLAUSES] >> simp[]
QED

(* Completion restriction extracted from the operational normal alternative. *)
val ld_recursive_bytes_complete =
  let
    val (args,body) = strip_abs ld_recursive_candidate
    val (normal,_) = dest_disj body
    val (ws,b) = strip_exists normal
    fun named s = hd (filter (fn v => fst(dest_var v) = s) ws)
    val n = named "n"
    val i = named "i"
    val code = named "code"
  in list_mk_abs(args,list_mk_exists(ws,
       list_mk_conj [b, ``^i.inst_opcode = DLOADBYTES``,
                     ``SUC ^n = LENGTH ^code``])) end;

Theorem ld_recursive_bytes_next_anchor[local]:
  !Q. ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  mem_inv dload_offset_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  (^ld_recursive_bytes_complete) vs0 CT stk un gn j t /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) /\
  Q (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_post_anchor) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  gen_tac >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!q. q < LENGTH astk ==> _` (mk_asm "saved") >>
  `inst_wf i` by metis_tac[ld_annotated_inst_wf] >>
  `?dst off sz. i.inst_operands = [dst;off;sz] /\ i.inst_outputs = []` by
    (qpat_assum `inst_wf i` mp_tac >>
     qpat_assum `i.inst_opcode = DLOADBYTES` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     metis_tac[]) >>
  `LENGTH code = 2` by
    (qpat_assum `lower_dload_inst_supply a1 i = _` mp_tac >>
     qpat_assum `i.inst_opcode = DLOADBYTES` mp_tac >>
     qpat_assum `i.inst_operands = [dst;off;sz]` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lower_dload_inst_supply_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `n = 1` by decide_tac >>
  TRY (qpat_x_assum `n = 0` mp_tac >>
       qpat_assum `n = 1` mp_tac >> simp[NoAsms] >> NO_TAC) >>
  `?a c av. code = [a;c] /\ a.inst_opcode = ADD /\
      a.inst_operands = [off;Label "code_end"] /\ a.inst_outputs = [av] /\
      c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
      c.inst_outputs = [] /\ av NOTIN set a1.irs_used_vars` by
    (qpat_assum `lower_dload_inst_supply a1 i = _` mp_tac >>
     qpat_assum `i.inst_opcode = DLOADBYTES` mp_tac >>
     qpat_assum `i.inst_operands = [dst;off;sz]` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac irSupplyTheory.fresh_ir_var_contract >> gvs[] >> metis_tac[]) >>
  `ld_target_prefix CT code ta ua (SUC n)
     (z with vs_inst_idx := SUC t.vs_inst_idx) (step_taint j t z un)` by
    (qpat_assum `ld_target_prefix CT code ta ua n t un` mp_tac >>
     qpat_assum `j = EL n code` mp_tac >>
     qpat_assum `step_inst fuel CT j t = OK z` mp_tac >>
     qpat_assum `n < LENGTH code` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[] >> metis_tac[ld_target_prefix_rules]) >>
  `MEM fn observed.cu_context.ctx_functions /\ ir_supply_covers_unit fa observed` by
    (qpat_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[o1PassContractTheory.fn_pass_step_def,
       venomFnScheduleRunnerTheory.lookup_unique_function_def, AllCaseEqs()] >>
     rpt strip_tac >>
     `MEM fn (FILTER (\f. f.fn_name = fn.fn_name)
        observed.cu_context.ctx_functions)` by simp[] >> gvs[MEM_FILTER]) >>
  `!v. v IN V ==> MEM v fa.irs_used_vars` by
    (qpat_assum `ir_supply_covers_unit fa observed` mp_tac >>
     qpat_assum `MEM fn observed.cu_context.ctx_functions` mp_tac >>
     qpat_assum `V = set (fn_ir_vars fn)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomFnScheduleRunnerTheory.ir_supply_covers_unit_def,
       venomFnScheduleRunnerTheory.list_subset_def, irSupplyTheory.unit_ir_vars_def,
       EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `!v. v IN V ==> MEM v a1.irs_used_vars` by
    (qpat_assum `lower_dload_blocks_supply fa bpre = _`
       (mp_tac o MATCH_MP ld_blocks_supply_used_vars_mono) >>
     qpat_assum `lower_dload_insts_supply a0 pre = _`
       (mp_tac o MATCH_MP ld_insts_supply_used_vars_mono) >>
     qpat_assum `!v. v IN V ==> MEM v fa.irs_used_vars` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `av NOTIN V` by metis_tac[] >>
  `av NOTIN U` by
    (qpat_assum `av NOTIN V` mp_tac >>
     qpat_assum `U = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[] >> metis_tac[]) >>
  `raw_reachable vs0 CS fn i s` by
    (irule ld_frame_reachable_raw >> drule ld_annotated_erasure >> metis_tac[]) >>
  `dload_offset_ok CS fn i s` by
    (qpat_assum `mem_inv dload_offset_ok CS vs0` mp_tac >>
     qpat_assum `raw_reachable vs0 CS fn i s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[unitMemInvTheory.mem_inv_raw_reachable]) >>
  `code_layout_valid s` by
    (irule o1LowerDloadSuppliedSegmentResourcesTheory.ld_raw_code_layout >>
     goal_assum (drule_at Any) >>
     fs[o1PassContractTheory.o1_run_state_ok_def]) >>
  `FDOM AG SUBSET V` by
    (drule_all lowerDloadProvenanceSupportTheory.ld_annotated_prov_ir_vars >>
     qpat_assum `V = set (fn_ir_vars fn)` SUBST1_TAC >> simp[]) >>
  `!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)` by
    (drule ld_normal_data_frame >> metis_tac[lowerDloadCoverageInvariantTheory.ld_frame_data_provenance]) >>
  `av NOTIN FDOM BH` by
    (qpat_assum `!v. ld_owned_selection E _ _` (qspec_then `av` mp_tac) >>
     qpat_assum `FDOM AG SUBSET V` mp_tac >>
     qpat_assum `av NOTIN V` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lowerDloadPairedBoundaryTheory.ld_owned_selection_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `ld_shared_state tn ua s ta` by
    (drule ld_normal_data_frame >>
     metis_tac[lowerDloadCoverageInvariantTheory.ld_frame_data_shared]) >>
  `eval_operand (Label "code_end") ta =
     SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section))` by
    (qpat_assum `ld_shared_state tn ua s ta` mp_tac >>
     qpat_assum `code_layout_valid s` mp_tac >>
     drule ld_normal_data_frame >>
     disch_then (mp_tac o MATCH_MP lowerDloadCoverageInvariantTheory.ld_frame_data_vars) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lowerDloadSharedStateTheory.ld_shared_state_def,
       lowerDloadPairedBoundaryTheory.ld_owned_vars_def,
       lowerDloadDefsTheory.code_layout_valid_def, venomStateTheory.eval_operand_def] >>
     metis_tac[]) >>
  `!v. MEM (Var v) [dst;off;sz] ==> v IN U` by
    (rpt strip_tac >>
     `MEM i (fn_insts fn)` by
       (qpat_assum `active_inst fn i s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[active_inst_def,fn_insts_def,o1PassContractTheory.fn_insts_blocks_MEM] >>
        metis_tac[EL_MEM]) >>
     `opaque_use_ok fn` by
       (qpat_assum `o1_ctx_shape CS` mp_tac >>
        qpat_assum `CS.ctx_functions = cpre ++ fn::cpost` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[o1PassContractTheory.o1_ctx_shape_def, EVERY_MEM,
          o1PassContractTheory.o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def]) >>
     `MEM (Var v) i.inst_operands` by metis_tac[] >>
     `i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI /\
      ~MEM i.inst_opcode [RET;RETFMP;DRET]` by simp[] >>
     drule_all ld_original_nonopaque_operand_support >>
     simp[] >> metis_tac[]) >>
  `(!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av)` by
    (qpat_assum `!v. MEM (Var v) [dst;off;sz] ==> v IN U` mp_tac >>
     qpat_assum `av NOTIN U` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[] >> metis_tac[]) >>
  `post <> []` by
    (qpat_assum `o1_ctx_shape CS` mp_tac >>
     qpat_assum `CS.ctx_functions = cpre ++ fn::cpost` mp_tac >>
     qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `bb.bb_instructions = pre ++ i::post` mp_tac >>
     qpat_assum `i.inst_opcode = DLOADBYTES` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `wf_function fn` by fs[o1PassContractTheory.o1_ctx_shape_def,
       o1PassContractTheory.o1_fn_shape_def, EVERY_MEM] >>
     `bb_well_formed bb` by metis_tac[wf_function_def,lookup_block_MEM] >>
     Cases_on `post` >> gvs[bb_well_formed_def,LAST_APPEND,is_terminator_def]) >>
  Cases_on `post` >- gvs[] >>
  rename1 `bb.bb_instructions = pre ++ i::i'::rest` >>
  Cases_on `lower_dload_inst_supply a2 i'` >>
  rename1 `lower_dload_inst_supply a2 i' = (nextcode,nexta)` >>
  Cases_on `lower_dload_insts_supply nexta rest` >>
  rename1 `lower_dload_insts_supply nexta rest = (nexttail,enda)` >>
  `tail = nextcode ++ nexttail /\ enda = a3` by
    (qpat_assum `lower_dload_insts_supply a2 (i'::rest) = _`
       (mp_tac o PURE_REWRITE_RULE [Once lower_dload_insts_supply_def]) >>
     simp[] >> strip_tac >> simp[]) >>
  `lower_dload_insts_supply nexta rest = (nexttail,a3)` by metis_tac[] >>
  `lower_dload_inst_supply a1 i = ([a;c],a2)` by metis_tac[] >>
  `ld_target_prefix CT [a;c] ta ua (SUC (SUC 0))
     (z with vs_inst_idx := SUC t.vs_inst_idx) (step_taint j t z un)` by
    (qpat_assum `ld_target_prefix CT code ta ua (SUC n) _ _` mp_tac >>
     qpat_assum `code = [a;c]` mp_tac >> qpat_assum `n = 1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  drule_all lowerDloadCoverageBytesTheory.ld_configured_bytes_next_backward >>
  disch_then (qspec_then `fuel` (qx_choose_then `zs` strip_assume_tac)) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >>
     disch_then (mp_tac o SRULE [EVERY_MEM]) >>
     disch_then (qspec_then `fn` mp_tac) >>
     impl_tac >- simp[] >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     disch_then (mp_tac o CONJUNCT1) >>
     pure_rewrite_tac [fn_labels_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  `zs.vs_current_bb = s.vs_current_bb /\ zs.vs_prev_bb = s.vs_prev_bb` by
    (qpat_assum `step_inst fuel CS i s = OK zs` mp_tac >>
     qpat_assum `i.inst_opcode = DLOADBYTES` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule step_preserves_control_flow >> simp[is_terminator_def]) >>
  drule_all lowerDloadNormalBytesTheory.ld_bytes_normal_data_backward >>
  disch_then (qspec_then `fuel` (qx_choose_then `zs2` strip_assume_tac)) >>
  `z.vs_current_bb = s.vs_current_bb /\ z.vs_prev_bb = s.vs_prev_bb` by
    (qpat_assum `(z with vs_inst_idx := _) with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = ta`
       (fn th => mp_tac (AP_TERM ``\v:venom_state. (v.vs_current_bb,v.vs_prev_bb)`` th)) >>
     simp[] >> metis_tac[]) >>
  `lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
     gn.fn_blocks = SOME gb` by
    (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `j' = HD nextcode` by
    (qpat_assum `active_inst gn j' _`
       (mp_then (Pat `active_inst _ _ _`) mp_tac ld_active_lookup_el) >>
     disch_then (qspec_then `gb` mp_tac) >>
     (impl_tac >- asm_rewrite_tac []) >>
     qpat_assum `active_inst gn (HD nextcode) _`
       (mp_then (Pat `active_inst _ _ _`) mp_tac ld_active_lookup_el) >>
     disch_then (qspec_then `gb` mp_tac) >>
     (impl_tac >- asm_rewrite_tac []) >> metis_tac[]) >>
  `nextcode <> []` by metis_tac[o1ContractLowerDloadTheory.lower_dload_inst_supply_nonempty] >>
  `active_inst fn i' (zs with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[lowerDloadProvenanceSupportTheory.ld_annotated_active_inst] >>
  `lookup_block ta.vs_current_bb (bpre ++ bb::bpost) = SOME bb` by
    metis_tac[] >>
  Cases_on `in_revert_forward fn (zs with vs_inst_idx := SUC s.vs_inst_idx)`
  >- suspend "revert_successor" >>
  disj1_tac >>
  qexistsl_tac [`astk`, `gstk`, `k`, `L`, `AP`, `AG`,
    `step_taint i s zs tn`, `fn`, `i'`,
    `zs with vs_inst_idx := SUC s.vs_inst_idx`,
    `z with vs_inst_idx := SUC t.vs_inst_idx`, `step_taint j t z un`,
    `V`, `U`, `E`, `H`, `BP`, `BH`, `live`, `keys`,
    `A`, `suspended`, `f`, `fa`, `fb`, `bb`, `gb`, `a0`, `a2`,
    `nexta`, `a3`, `pre ++ [i]`, `rest`, `p ++ [a;c]`, `nextcode`,
    `nexttail`, `bpre`, `bpost`, `qpre`, `qpost`, `supports`, `savedkeys`,
    `s0`, `0`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  asm "saved" (fn th => asm_rewrite_tac [th]) >>
  conj_tac
  >- (qexistsl_tac [`cpre`, `cpost`, `gpre`, `gpost`, `observed`, `out`] >>
      asm_rewrite_tac []) >>
  simp[GSYM APPEND_ASSOC] >>
  metis_tac[]
QED

Resume ld_recursive_bytes_next_anchor[revert_successor]:
  `lookup_block (zs with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
     fn.fn_blocks = SOME bb` by
    (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `lower_dload_insts_supply a0
     (TAKE (zs with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx
        bb.bb_instructions) = (p ++ [a;c],a2)` by
    (simp_tac (srw_ss()) [] >>
     qpat_assum `bb.bb_instructions = _` SUBST1_TAC >>
     qpat_assum `s.vs_inst_idx = _` SUBST1_TAC >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  `get_instruction gb (z with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = SOME j'` by
    (simp[get_instruction_def, EL_APPEND2] >>
     Cases_on `nextcode` >- metis_tac[] >> simp[EL_APPEND2, EL_APPEND1]) >>
  irule (BETA_RULE (Q.SPEC `Q` ld_recursive_configured_revert_anchor)) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `lower_dload_insts_supply _ (TAKE _ _) = _`)) >>
  goal_assum (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_dload_blocks_supply _ _ = _`)) >>
  goal_assum (drule_at (Pat `lower_dload_block_supply _ _ = _`)) >>
  asm_rewrite_tac [] >> metis_tac[]
QED

Finalise ld_recursive_bytes_next_anchor

Theorem ld_recursive_bytes_next:
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  mem_inv dload_offset_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  (^ld_recursive_bytes_complete) vs0 CT stk un gn j t /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qspec_then `\s. T` mp_tac ld_recursive_bytes_next_anchor >>
  BETA_TAC >> pure_rewrite_tac [AND_CLAUSES] >> simp[]
QED

(* DLOAD COMPLETION AUDIT (diagnostic, not a closure theorem).
   This ledger refers to the OPERATIONAL ld_recursive_candidate rebound above
   (the saved out.fpo_supply=sb equation is absent), not the entry-history quote.
   No theorem, new definition, or additional invariant is asserted here.

   ENVIRONMENT / FIRST RESIDUAL:
   ld_recursive_bytes_next_anchor assumes ptr_discipline, o1_ctx_shape,
   o1_run_state_ok, mem_inv dload_offset_ok, callee_first, and the fn_ptr_ok
   family. These are NOT the full resource premises of the existing load
   producer. The frozen theorem additionally supplies
     mem_inv dload_headroom_ok CS vs0
   by o1_src_inv_def. ld_annotated_headroom instantiates this at
     astk,k,L,AP,AG,tn,fn,i,s.
   Thus a load closure using the headroom interface must explicitly take this
   extra environmental projection; it is not a consequence already supplied
   by the bytes theorem's hypothesis list. This is an interface residual,
   not a counterexample to the frozen task statement.

   PRODUCER INPUT LEDGER (CoverageLoad.ld_configured_load_next_backward):
   1. normal_data and source annotated reachability: literal candidate fields,
      with t0=ta, u0=ua and d0=32*SUM(MAP CARD suspended).
   2. ptr_discipline / fn_ptr_ok: environmental premises, unchanged.
   3. DLOAD arity: ld_annotated_inst_wf and inst_wf_def give [off]/[out].
      lower_dload_inst_supply_def then gives code=[a;b;c;d], with the exact
      ALLOCA/ADD/CODECOPY/MLOAD opcodes, operands and outputs in the producer.
      The completed restriction forces n=3; n=0 is impossible.
   4. off support: ld_original_nonopaque_operand_support, using opaque_use_ok
      projected from o1_ctx_shape and MEM i (fn_insts fn), gives off=Var v ==> v IN U.
      out IN V: ld_original_output_support. out IN U additionally uses the
      writer clause of retpc_shape_ok_def from source shape: a DLOAD writer
      cannot write a retpc variable (allowed writers are RETPC_PARAM/ASSIGN/PHI).
      Operand support alone does NOT establish the output condition.
   5. fresh av,bv: fn_pass_step_def gives membership of fn in observed and
      ir_supply_covers_unit fa observed; expanding the covers predicates
      restricts this to ir_supply_covers_fn fa fn. Reservation monotonicity
      through bpre/pre and fresh_ir_var_contract yield av<>bv and av,bv NOTIN V,
      hence NOTIN U. As in bytes-next, ld_annotated_prov_ir_vars gives
      FDOM AG SUBSET V; ld_frame_data_provenance and ld_owned_selection_def
      then give av,bv NOTIN FDOM BH. These are filtered BH facts, not assertions
      about the raw target provenance.
   6. prefix: append the actual last successful target step by
      ld_target_prefix_rules, obtaining length-four prefix at
        tplus = z with vs_inst_idx := SUC t.vs_inst_idx,
        uplus = step_taint j t z un.
      This uses the last actual j=EL 3 code; no source run is guessed.
   7. offset/layout/code_end: same interfaces as bytes-next:
      ld_annotated_erasure -> ld_frame_reachable_raw -> mem_inv_raw_reachable;
      ld_raw_code_layout with o1_run_state_ok; shared environment and owned
      definedness plus eval_operand_def for Label "code_end" at ta.
   8. a.inst_id IN keys: lower_dload_configured_scratch_member, instantiated
      at fa,fn,gn,fb,bpre,bb,bpost,qpre,a0,gb,a3,pre,i,post,p,a1,code,a2,
      using ir_supply_covers_fn fa fn from item 5 and a=HD code.
   9. STRICT FRONTIER: ld_normal_data_geometry supplies the account.
      Candidate LIST_REL tails, mapped through ld_erase_frame, give the saved
      CARD bounds over MAP ld_erase_frame astk. With item 8, source origin,
      callee_first and the EXTRA headroom projection, use
      ld_configured_scratch_headroom at q=a.inst_id, ss=suspended, s=s, t=ta.
      Its FLOOKUP ta.vs_allocas q=NONE condition is equivalent to q NOTIN A
      by ld_alloc_account_scratch_absent. This supplies BOTH strict bounds
      required by the producer. Cached case q IN A needs only ta.next<dimword;
      fresh case q NOTIN A needs ta.next+32<dimword, not merely <=.
  10. UNMATCHED GEOMETRY INPUT:
        allocas_non_overlapping ta /\ alloca_next_valid ta.
      These are explicit CoverageLoad and NormalLoad premises. The candidate
      has allocas_from f ta, frame/stack bounds and an allocation account,
      but no alloca_inv ta or target reachability conjunct. The account gives
      scratch sizes and domain, not scratch endpoint/disjointness geometry.
      ld_annotated_alloca_inv supplies SOURCE geometry at s only.
      ld_raw_reachable_alloca_inv would supply target geometry given an
      actual raw_reachable target anchor plus alloca_inv vs0; that anchor is
      NOT among the bytes-style environmental premises or projected NEXT
      induction premises. Successful cached ALLOCA alone is not such a proof.
      Smallest outstanding semantic boundary to resolve before assembly:
        [current normal alternative at anchor s,ta; actual CT configuration]
          ==> allocas_non_overlapping ta /\ alloca_next_valid ta.
      This is a requested interface shape, NOT a proved implication; review
      must decide whether target geometry needs separate induction threading
      or can be derived by a narrower existing invariant. No candidate change
      is made in this diagnostic.
  11. next configured instruction: source well-formed block and nonterminating
      DLOAD imply post<>[] exactly as in bytes-next. Split post=i'::rest and
      split its supply to provide next/tail. Candidate supplies all remaining
      block supply/lookups/index hypotheses literally.

   SUCCESSOR OUTPUT LEDGER (conditional on resolving items 9-10):
   CoverageLoad supplies source OK step zs, updated annotated reachability,
   active target HD next and advanced pre++[i], p++code/index equations.
   normal_data updates only AG to ld_set_prov AG [out] NONE, BH to
   ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE, source taint and A to
   a.inst_id INSERT A. E,L,H,AP,BP,live,astk,gstk,keys,f,suspended are unchanged.
   FINITE(insert A) follows from account finiteness. CARD(insert A) is NOT
   discharged by the old CARD A bound plus CARD_INSERT alone: use the new
   account's capacity, INSERT A SUBSET keys, CARD_SUBSET and
   lower_dload_configured_cap_bound to bound it by the function DLOAD count.
   This works for cached and fresh cases without counting loop executions.
   Saved tail LIST_REL is unchanged. Source origin is unchanged since fn and
   astk are unchanged. The entire operational ld_recursive_saved clause is
   unchanged: it depends on E and saved witnesses, NOT active AG/BH/A. Thus
   saved parameter envelopes and corrected saved supply certificates reuse
   their literal witnesses; no owner extension or saved-support transport.
   Active envelope is part of the producer's normal_data conclusion already.
   All function/context certificates and bpre/bpost supplies reuse witnesses.
   Control equality uses NormalLoad's restoration record equations (not
   shared_state, which excludes block control); source DLOAD preserves control.
   Distinct target labels identify supplied active j' with HD next as in bytes.
   Non-revert successor packages n=0, ta=tplus, ua=uplus. Revert successor uses
   ld_recursive_configured_revert_entry at advanced TAKE/supply positions,
   again as in bytes-next. No target raw PG/G equality is needed anywhere.

   RESULT: no completed-DLOAD closure is claimed. Two explicit prerequisites
   precede such a theorem: expose the already-available source headroom
   projection in its environment, and resolve target anchor allocation
   geometry. The remaining cardinality and saved-envelope differences have
   existing interfaces as listed above. No additional local load producer
   or duplicate normal_data wrapper is called for by this audit.
*)

(* Conservative refinement for the geometry probe. The old operational quote
   remains unchanged. Validity of ta is inside precisely its old witnesses. *)
val ld_recursive_geometry_candidate = ld_refine_geometry ld_recursive_candidate;

fun ld_geometry_restriction restriction =
  let
    val (args,body) = strip_abs restriction
    val (ws,b) = strip_exists body
    val ta = hd (filter (fn v => fst(dest_var v) = "ta") ws)
    val stk = List.nth(args,2)
    val t = List.last args
  in list_mk_abs(args,list_mk_conj [``alloca_inv ^t``,
       ``!f i st tv. MEM (f,i,st,tv) ^stk ==> alloca_inv st``,
       list_mk_exists(ws,mk_conj(b,``alloca_inv ^ta``))]) end;
val ld_recursive_geometry_ordinary_zero = ld_geometry_restriction ld_recursive_ordinary_zero;

Theorem ld_recursive_geometry_ordinary_input[local]:
  (^ld_recursive_geometry_ordinary_zero) vs0 CT stk un gn j t ==>
  alloca_inv t /\ (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
  (^ld_recursive_ordinary_zero) vs0 CT stk un gn j t
Proof
  BETA_TAC >>
  ho_match_mp_tac MONO_AND >> conj_tac >- simp[] >>
  ho_match_mp_tac MONO_AND >> conj_tac >- simp[] >>
  rpt (ho_match_mp_tac MONO_EXISTS >> gen_tac) >>
  disch_then (ACCEPT_TAC o CONJUNCT1)
QED

Theorem ld_recursive_post_anchor_geometry[local]:
  alloca_inv t /\ (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
  (^(ld_retain_anchor ld_recursive_candidate ``alloca_inv``)) vs0 CT stk un gn j t ==>
  (^ld_recursive_geometry_candidate) vs0 CT stk un gn j t
Proof
  BETA_TAC >> simp[]
QED

Theorem ld_step_next_alloca_inv[local]:
  alloca_inv t /\ step_inst fuel CT j t = OK z ==>
  alloca_inv (z with vs_inst_idx := (idx:num))
Proof
  strip_tac >> drule_all venomMemPropsTheory.alloca_inv_step_inst >>
  simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]
QED

Theorem ld_recursive_geometry_ordinary_next:
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  (^ld_recursive_geometry_ordinary_zero) vs0 CT stk un gn j t /\
  ~is_terminator j.inst_opcode /\ step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_geometry_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> drule ld_recursive_geometry_ordinary_input >> strip_tac >>
  `alloca_inv (z with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ld_step_next_alloca_inv >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  qspec_then `alloca_inv` mp_tac ld_recursive_ordinary_next_anchor >>
  (impl_tac >- asm_rewrite_tac []) >> disch_tac >>
  irule ld_recursive_post_anchor_geometry >> asm_rewrite_tac []
QED

val ld_recursive_geometry_alloca_zero = ld_geometry_restriction ld_recursive_alloca_zero;
val ld_recursive_geometry_bytes_complete = ld_geometry_restriction ld_recursive_bytes_complete;

Theorem ld_recursive_geometry_alloca_next:
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (^ld_recursive_geometry_alloca_zero) vs0 CT stk un gn j t /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_geometry_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `alloca_inv t /\ (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
   (^ld_recursive_alloca_zero) vs0 CT stk un gn j t` by
    (qpat_x_assum `(^ld_recursive_geometry_alloca_zero) _ _ _ _ _ _ _` mp_tac >>
     BETA_TAC >> ho_match_mp_tac MONO_AND >> conj_tac >- simp[] >>
     ho_match_mp_tac MONO_AND >> conj_tac >- simp[] >>
     rpt (ho_match_mp_tac MONO_EXISTS >> gen_tac) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `alloca_inv (z with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ld_step_next_alloca_inv >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  qspec_then `alloca_inv` mp_tac ld_recursive_alloca_next_anchor >>
  (impl_tac >- asm_rewrite_tac []) >> disch_tac >>
  irule ld_recursive_post_anchor_geometry >> asm_rewrite_tac []
QED

Theorem ld_recursive_geometry_bytes_next:
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  mem_inv dload_offset_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  (^ld_recursive_geometry_bytes_complete) vs0 CT stk un gn j t /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_geometry_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `alloca_inv t /\ (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
   (^ld_recursive_bytes_complete) vs0 CT stk un gn j t` by
    (qpat_x_assum `(^ld_recursive_geometry_bytes_complete) _ _ _ _ _ _ _` mp_tac >>
     BETA_TAC >> ho_match_mp_tac MONO_AND >> conj_tac >- simp[] >>
     ho_match_mp_tac MONO_AND >> conj_tac >- simp[] >>
     rpt (ho_match_mp_tac MONO_EXISTS >> gen_tac) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `alloca_inv (z with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ld_step_next_alloca_inv >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  qspec_then `alloca_inv` mp_tac ld_recursive_bytes_next_anchor >>
  (impl_tac >- asm_rewrite_tac []) >> disch_tac >>
  irule ld_recursive_post_anchor_geometry >> asm_rewrite_tac []
QED

Theorem ld_recursive_geometry_exceptional_next:
  alloca_inv t /\ (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st) /\
  revert_forward_pair bb copypos endpos /\
  copypos <= t.vs_inst_idx /\ t.vs_inst_idx <= endpos /\
  get_instruction bb t.vs_inst_idx = SOME j /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks) /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_geometry_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `alloca_inv (z with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ld_step_next_alloca_inv >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  qspec_then `alloca_inv` mp_tac ld_recursive_exceptional_next_anchor >>
  (impl_tac >- asm_rewrite_tac []) >> disch_tac >>
  irule ld_recursive_post_anchor_geometry >> asm_rewrite_tac []
QED

val ld_recursive_geometry_entry_goal =
  let
    val (p, body) = dest_forall (concl ld_frame_reachable_projected_ind)
    val (clauses, _) = dest_imp body
    val clause = subst [p |-> ld_recursive_geometry_candidate] (hd(strip_conj clauses))
    val (v0::ct::rest, b) = strip_forall clause
  in subst [v0 |-> mk_var("vs0", type_of v0),
            ct |-> mk_var("CT", type_of ct)] (list_mk_forall(rest,b)) end;

Theorem ld_recursive_geometry_entry_clause:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions /\
  lo = vs0.vs_alloca_next ==>
  ^ld_recursive_geometry_entry_goal
Proof
  strip_tac >> mp_tac ld_entry_geometry_history_clause >>
  (impl_tac >- simp[]) >> BETA_TAC >>
  rpt (FIRST [disch_then ACCEPT_TAC,
              disch_then (ACCEPT_TAC o CONJUNCT2),
              ho_match_mp_tac MONO_OR, ho_match_mp_tac MONO_AND,
              ho_match_mp_tac MONO_EXISTS, ho_match_mp_tac MONO_ALL,
              ho_match_mp_tac MONO_IMP, conj_tac, gen_tac]) >>
  simp[]
QED

Theorem ld_recursive_geometry_forget[local]:
  (^ld_recursive_geometry_candidate) vs0 CT stk un gn j t ==>
  (^ld_recursive_candidate) vs0 CT stk un gn j t
Proof
  BETA_TAC >> disch_then (mp_tac o CONJUNCT2 o CONJUNCT2) >>
  ho_match_mp_tac MONO_OR >> reverse conj_tac >- simp[] >>
  rpt (ho_match_mp_tac MONO_EXISTS >> gen_tac) >> simp[]
QED

val ld_recursive_geometry_block_goal =
  let
    val (p, body) = dest_forall (concl ld_frame_reachable_projected_ind)
    val (clauses, _) = dest_imp body
    val clause = subst [p |-> ld_recursive_geometry_candidate] (List.nth(strip_conj clauses,2))
    val (v0::ct::rest, b) = strip_forall clause
  in subst [v0 |-> mk_var("vs0", type_of v0),
            ct |-> mk_var("CT", type_of ct)] (list_mk_forall(rest,b)) end;

Theorem ld_recursive_geometry_block_clause:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions /\
  lo = vs0.vs_alloca_next ==>
  ^ld_recursive_geometry_block_goal
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule ld_recursive_geometry_forget >> disch_tac >>
  `alloca_inv s /\ (!f i st tv. MEM (f,i,st,tv) stk ==> alloca_inv st)` by
    (qpat_assum `(^ld_recursive_geometry_candidate) _ _ _ _ _ _ _`
       (mp_tac o BETA_RULE) >>
     disch_then (fn th => assume_tac (CONJUNCT1 th) >>
                         assume_tac (CONJUNCT1 (CONJUNCT2 th))) >>
     asm_rewrite_tac []) >>
  `alloca_inv s'` by
    (irule venomMemPropsTheory.alloca_inv_step_inst >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `alloca_inv s1` by
    (qpat_assum `enters_block fn s' s1` mp_tac >>
     qpat_assum `alloca_inv s'` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> drule ld_enters_block_allocation_fields >> strip_tac >>
     gvs[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.allocas_non_overlapping_def,
         venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  qspec_then `alloca_inv` mp_tac ld_recursive_block_clause_anchor >>
  (impl_tac >- asm_rewrite_tac []) >>
  disch_then (qspecl_then [`stk`,`tn`,`fn`,`inst`,`inst'`,`s`,`s'`,`s1`,`fuel`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac []) >> disch_tac >>
  irule ld_recursive_post_anchor_geometry >> asm_rewrite_tac []
QED

val ld_recursive_geometry_inside =
  let
    val (args,body) = strip_abs ld_recursive_geometry_candidate
    val [current,saved,alternatives] = strip_conj body
    val (normal,_) = dest_disj alternatives
    val (ws,b) = strip_exists normal
    fun named s = hd (filter (fn v => fst(dest_var v) = s) ws)
    val n = named "n"
    val code = named "code"
    val restricted = list_mk_exists(ws,mk_conj(b,``SUC ^n < LENGTH ^code``))
  in list_mk_abs(args,list_mk_conj [current,saved,restricted]) end;

Theorem ld_recursive_geometry_prefix_next:
  o1_ctx_shape CS /\
  (^ld_recursive_geometry_inside) vs0 CT stk un gn j t /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_geometry_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  qspec_then `alloca_inv` mp_tac ld_recursive_anchor_prefix_next >>
  BETA_TAC >>
  (impl_tac >- asm_simp_tac (srw_ss()) []) >>
  disch_tac >>
  (conj_tac
   >- ( `alloca_inv z` by
          metis_tac[venomMemPropsTheory.alloca_inv_step_inst] >>
        qpat_x_assum `alloca_inv z` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def,
          venomMemDefsTheory.alloca_next_valid_def])) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  disj1_tac >> first_assum ACCEPT_TAC
QED

(* ANCHOR GEOMETRY PROBE LEDGER -- not a global closure assertion.
   ld_recursive_geometry_candidate is a conservative refinement of the
   operational quotation. Forgetting is proved only in the forward direction.
   alloca_inv ta is retained INSIDE the normal existential, whereas actual
   current/saved target validity is external and also applies to revert mode.
   ld_target_prefix_alloca_inv checks forward validity along a prefix; it
   does not invert validity of its endpoint to validity of its anchor.

   Checked: intermediate NEXT retains the SAME ta and its validity, extends
   the same prefix, and advances current validity by alloca_inv_step_inst.
   No memory producer or source simulation is duplicated by this check.

   Checked ENTRY: ld_recursive_geometry_entry_clause shares the original
     entry witness construction, with ta=current entered target state and
     empty projected stack; empty initial allocations prove anchor validity.
   Checked COMPLETED NEXT: ld_recursive_geometry_ordinary_next,
     ld_recursive_geometry_alloca_next and ld_recursive_geometry_bytes_next
     retain the actual successor anchor through a single post-anchor-predicate
     packaging proof per family. Original exported statements instantiate that
     predicate to true; refined wrappers instantiate it to alloca_inv. Thus no
     anchor is recovered from an old existential conclusion, and no semantic
     producer is duplicated. ld_recursive_geometry_load_next below separately
     retains OLD anchor validity and its explicit source-headroom premise.

   Checked BLOCK: ld_recursive_geometry_block_clause shares the original
     jump/PHI/position proof and its single witness packaging via the local
     post-anchor clause. It retains Q(actual entered successor) at phase zero;
     the old clause uses Q=true and geometry uses Q=alloca_inv. Current validity
     advances through the target step and enters_block allocation fields, while
     saved validity is unchanged. The revert branch needs no anchor predicate.

   Remaining constructor obligations for the refined quotation:
   CALL: save the actual target caller state with its current validity; setup
     initializes the new callee allocation map to empty, enters_block preserves
     it. The callee normal anchor is that actual entered state. Existing call
     control/parameter-envelope producers are still required.
   RETURN: saved caller validity and return allocation-field transport supply
     actual returned target state validity (as in TargetValidity); choose that
     state as ta' at n'=0, pop saved validity. Existing matching completed-source
     callee run, output, normal-data and control obligations are NOT proved here.
   Checked exceptional NEXT: ld_recursive_geometry_exceptional_next retains
     actual/saved validity without a normal anchor. The shared exceptional
     proof is independent of the post-anchor predicate. Entry from a configured
     revert pair need not fabricate normal_data.
   Observation consumers may forget geometry using the checked implication;
   observations and global induction remain outstanding.
*)

(* Completion restriction keeps geometry of the old segment anchor. *)
val ld_recursive_geometry_load_complete =
  let
    val (args,body) = strip_abs ld_recursive_geometry_candidate
    val [current,saved,alternatives] = strip_conj body
    val (normal,_) = dest_disj alternatives
    val (ws,b) = strip_exists normal
    fun named s = hd (filter (fn v => fst(dest_var v) = s) ws)
    val n = named "n"
    val i = named "i"
    val code = named "code"
    val restricted = list_mk_exists(ws,
      list_mk_conj [b, ``^i.inst_opcode = DLOAD``,
                      ``SUC ^n = LENGTH ^code``])
  in list_mk_abs(args,list_mk_conj [current,saved,restricted]) end;

Theorem ld_recursive_geometry_load_next:
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  mem_inv dload_offset_ok CS vs0 /\ mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  (^ld_recursive_geometry_load_complete) vs0 CT stk un gn j t /\
  step_inst fuel CT j t = OK z /\
  active_inst gn j' (z with vs_inst_idx := SUC t.vs_inst_idx) ==>
  (^ld_recursive_geometry_candidate) vs0 CT stk (step_taint j t z un) gn j'
    (z with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> strip_tac >>
  qpat_x_assum `!q. q < LENGTH astk ==> _` (mk_asm "saved") >>
  `inst_wf i` by metis_tac[ld_annotated_inst_wf] >>
  `?off out. i.inst_operands = [off] /\ i.inst_outputs = [out]` by
    (qpat_assum `inst_wf i` mp_tac >>
     qpat_assum `i.inst_opcode = DLOAD` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     metis_tac[]) >>
  `LENGTH code = 4` by
    (qpat_assum `lower_dload_inst_supply a1 i = _` mp_tac >>
     qpat_assum `i.inst_opcode = DLOAD` mp_tac >>
     qpat_assum `i.inst_operands = [off]` mp_tac >>
     qpat_assum `i.inst_outputs = [out']` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lower_dload_inst_supply_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `n = 3` by decide_tac >>
  TRY (qpat_x_assum `n = 0` mp_tac >>
       qpat_assum `n = 3` mp_tac >> simp[NoAsms] >> NO_TAC) >>
  `?a b c d av bv. code = [a;b;c;d] /\
      a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
      a.inst_outputs = [av] /\
      b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
      b.inst_outputs = [bv] /\
      c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
      c.inst_outputs = [] /\
      d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\
      d.inst_outputs = [out'] /\ av <> bv /\
      av NOTIN set a1.irs_used_vars /\ bv NOTIN set a1.irs_used_vars` by
    (qpat_assum `lower_dload_inst_supply a1 i = _` mp_tac >>
     qpat_assum `i.inst_opcode = DLOAD` mp_tac >>
     qpat_assum `i.inst_operands = [off]` mp_tac >>
     qpat_assum `i.inst_outputs = [out']` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac irSupplyTheory.fresh_ir_var_contract >> gvs[] >> metis_tac[]) >>
  `ld_target_prefix CT code ta ua (SUC n)
     (z with vs_inst_idx := SUC t.vs_inst_idx) (step_taint j t z un)` by
    (qpat_assum `ld_target_prefix CT code ta ua n t un` mp_tac >>
     qpat_assum `j = EL n code` mp_tac >>
     qpat_assum `step_inst fuel CT j t = OK z` mp_tac >>
     qpat_assum `n < LENGTH code` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[] >> metis_tac[ld_target_prefix_rules]) >>
  `MEM i (fn_insts fn)` by
    (qpat_assum `active_inst fn i s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[active_inst_def,fn_insts_def,o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `opaque_use_ok fn` by
    (qpat_assum `o1_ctx_shape CS` mp_tac >>
     qpat_assum `CS.ctx_functions = cpre ++ fn::cpost` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[o1PassContractTheory.o1_ctx_shape_def, EVERY_MEM,
       o1PassContractTheory.o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def]) >>
  `!v. off = Var v ==> v IN U` by
    (rpt strip_tac >>
     `MEM (Var v) i.inst_operands` by metis_tac[MEM] >>
     `i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI /\
      ~MEM i.inst_opcode [RET;RETFMP;DRET]` by simp[] >>
     drule_all ld_original_nonopaque_operand_support >> simp[] >> metis_tac[]) >>
  `out' IN V` by
    (qpat_assum `V = set (fn_ir_vars fn)` SUBST1_TAC >>
     simp[] >> irule ld_original_output_support >>
     qexists_tac `i` >> simp[]) >>
  `retpc_shape_ok fn` by
    (qpat_assum `o1_ctx_shape CS` mp_tac >>
     qpat_assum `CS.ctx_functions = cpre ++ fn::cpost` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[o1PassContractTheory.o1_ctx_shape_def, EVERY_MEM,
       o1PassContractTheory.o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def]) >>
  `~retpc_var fn out'` by
    (qpat_assum `retpc_shape_ok fn`
       (mp_tac o Q.SPECL [`i`,`out'`] o cj 3 o
        REWRITE_RULE [unitShapeDefsTheory.retpc_shape_ok_def]) >>
     simp[]) >>
  `out' IN U` by
    (qpat_assum `out' IN V` mp_tac >>
     qpat_assum `U = _` mp_tac >>
     qpat_assum `~retpc_var fn out'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `MEM fn observed.cu_context.ctx_functions /\ ir_supply_covers_unit fa observed` by
    (qpat_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[o1PassContractTheory.fn_pass_step_def,
       venomFnScheduleRunnerTheory.lookup_unique_function_def, AllCaseEqs()] >>
     rpt strip_tac >>
     `MEM fn (FILTER (\f. f.fn_name = fn.fn_name)
        observed.cu_context.ctx_functions)` by simp[] >> gvs[MEM_FILTER]) >>
  `ir_supply_covers_fn fa fn` by
    (qpat_assum `ir_supply_covers_unit fa observed` mp_tac >>
     qpat_assum `MEM fn observed.cu_context.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomFnScheduleRunnerTheory.ir_supply_covers_unit_def,
       venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
       venomFnScheduleRunnerTheory.list_subset_def, irSupplyTheory.unit_ir_vars_def,
       irSupplyTheory.unit_ir_inst_ids_def, irSupplyTheory.unit_ir_labels_def,
       EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >> metis_tac[]) >>
  `!v. v IN V ==> MEM v a1.irs_used_vars` by
    (qpat_assum `lower_dload_blocks_supply fa bpre = _`
       (mp_tac o MATCH_MP ld_blocks_supply_used_vars_mono) >>
     qpat_assum `lower_dload_insts_supply a0 pre = _`
       (mp_tac o MATCH_MP ld_insts_supply_used_vars_mono) >>
     qpat_assum `ir_supply_covers_fn fa fn` mp_tac >>
     qpat_assum `V = set (fn_ir_vars fn)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
       venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  `av NOTIN V /\ bv NOTIN V` by metis_tac[] >>
  `av NOTIN U /\ bv NOTIN U` by
    (qpat_assum `av NOTIN V` mp_tac >>
     qpat_assum `bv NOTIN V` mp_tac >>
     qpat_assum `U = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[] >> metis_tac[]) >>
  `FDOM AG SUBSET V` by
    (drule_all lowerDloadProvenanceSupportTheory.ld_annotated_prov_ir_vars >>
     qpat_assum `V = set (fn_ir_vars fn)` SUBST1_TAC >> simp[]) >>
  `!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)` by
    (drule ld_normal_data_frame >>
     metis_tac[lowerDloadCoverageInvariantTheory.ld_frame_data_provenance]) >>
  `!v. v NOTIN V ==> v NOTIN FDOM BH` by
    (gen_tac >> disch_tac >>
     qpat_assum `!v. ld_owned_selection E _ _` (qspec_then `v` mp_tac) >>
     qpat_assum `FDOM AG SUBSET V` mp_tac >>
     qpat_assum `v NOTIN V` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lowerDloadPairedBoundaryTheory.ld_owned_selection_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `av NOTIN FDOM BH /\ bv NOTIN FDOM BH` by metis_tac[] >>
  `raw_reachable vs0 CS fn i s` by
    (irule ld_frame_reachable_raw >> drule ld_annotated_erasure >> metis_tac[]) >>
  `dload_offset_ok CS fn i s /\ dload_headroom_ok CS fn i s` by
    (qpat_assum `mem_inv dload_offset_ok CS vs0` mp_tac >>
     qpat_assum `mem_inv dload_headroom_ok CS vs0` mp_tac >>
     qpat_assum `raw_reachable vs0 CS fn i s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[unitMemInvTheory.mem_inv_raw_reachable]) >>
  `code_layout_valid s` by
    (irule o1LowerDloadSuppliedSegmentResourcesTheory.ld_raw_code_layout >>
     goal_assum (drule_at Any) >>
     fs[o1PassContractTheory.o1_run_state_ok_def]) >>
  `ld_shared_state tn ua s ta` by
    (drule ld_normal_data_frame >>
     metis_tac[lowerDloadCoverageInvariantTheory.ld_frame_data_shared]) >>
  `eval_operand (Label "code_end") ta =
     SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section))` by
    (qpat_assum `ld_shared_state tn ua s ta` mp_tac >>
     qpat_assum `code_layout_valid s` mp_tac >>
     drule ld_normal_data_frame >>
     disch_then (mp_tac o MATCH_MP lowerDloadCoverageInvariantTheory.ld_frame_data_vars) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lowerDloadSharedStateTheory.ld_shared_state_def,
       lowerDloadPairedBoundaryTheory.ld_owned_vars_def,
       lowerDloadDefsTheory.code_layout_valid_def, venomStateTheory.eval_operand_def] >>
     metis_tac[]) >>
  `a.inst_id IN keys` by
    (drule_all lower_dload_configured_scratch_member >> simp[]) >>
  drule ld_normal_data_geometry >> strip_tac >>
  `LIST_REL (\a f. CARD a <= LENGTH (FILTER (\ii. ii.inst_opcode = DLOAD)
      (fn_insts f.cf_fn))) suspended (MAP ld_erase_frame astk)` by
    (qpat_assum `LIST_REL _ (A::suspended) _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[listTheory.LIST_REL_CONS1, listTheory.LIST_REL_EL_EQN,
       listTheory.EL_MAP, lowerDloadOwnershipTheory.ld_erase_frame_def] >>
     strip_tac >> gvs[listTheory.EL_MAP] >> metis_tac[]) >>
  `ta.vs_alloca_next < dimword (:256) /\
    (FLOOKUP ta.vs_allocas a.inst_id = NONE ==>
      ta.vs_alloca_next + 32 < dimword (:256))` by
    (drule_all ld_configured_scratch_headroom >> simp[]) >>
  `a.inst_id NOTIN A ==> ta.vs_alloca_next + 32 < dimword (:256)` by
    (drule_all lowerDloadAllocationTheory.ld_alloc_account_scratch_absent >> simp[]) >>
  `allocas_non_overlapping ta /\ alloca_next_valid ta` by
    (qpat_assum `alloca_inv ta` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[venomMemDefsTheory.alloca_inv_def]) >>
  `post <> []` by
    (qpat_assum `o1_ctx_shape CS` mp_tac >>
     qpat_assum `CS.ctx_functions = cpre ++ fn::cpost` mp_tac >>
     qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `bb.bb_instructions = pre ++ i::post` mp_tac >>
     qpat_assum `i.inst_opcode = DLOAD` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `wf_function fn` by fs[o1PassContractTheory.o1_ctx_shape_def,
       o1PassContractTheory.o1_fn_shape_def, EVERY_MEM] >>
     `bb_well_formed bb` by metis_tac[wf_function_def,lookup_block_MEM] >>
     Cases_on `post` >> gvs[bb_well_formed_def,LAST_APPEND,is_terminator_def]) >>
  Cases_on `post` >- gvs[] >>
  rename1 `bb.bb_instructions = pre ++ i::i'::rest` >>
  Cases_on `lower_dload_inst_supply a2 i'` >>
  rename1 `lower_dload_inst_supply a2 i' = (nextcode,nexta)` >>
  Cases_on `lower_dload_insts_supply nexta rest` >>
  rename1 `lower_dload_insts_supply nexta rest = (nexttail,enda)` >>
  `tail = nextcode ++ nexttail /\ enda = a3` by
    (qpat_assum `lower_dload_insts_supply a2 (i'::rest) = _`
       (mp_tac o PURE_REWRITE_RULE [Once lower_dload_insts_supply_def]) >>
     simp[] >> strip_tac >> simp[]) >>
  `lower_dload_insts_supply nexta rest = (nexttail,a3)` by metis_tac[] >>
  `lower_dload_inst_supply a1 i = ([a;b;c;d],a2)` by metis_tac[] >>
  `ld_target_prefix CT [a;b;c;d] ta ua (SUC (SUC (SUC (SUC 0))))
     (z with vs_inst_idx := SUC t.vs_inst_idx) (step_taint j t z un)` by
    (qpat_assum `ld_target_prefix CT code ta ua (SUC n) _ _` mp_tac >>
     qpat_assum `code = [a;b;c;d]` mp_tac >> qpat_assum `n = 3` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qpat_assum `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ld_configured_load_next_backward) >>
  disch_then (drule_at (Pat `ld_target_prefix _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lower_dload_block_supply _ _ = _`)) >>
  disch_then (drule_at (Pat `lower_dload_insts_supply _ pre = _`)) >>
  disch_then (drule_at (Pat `lower_dload_inst_supply a1 i = _`)) >>
  disch_then (drule_at (Pat `lower_dload_inst_supply a2 i' = _`)) >>
  disch_then (fn th =>
    qpat_assum `lower_dload_insts_supply a0 pre = (p,a1)`
      (mp_then (Pat `lower_dload_insts_supply a0 _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `i.inst_operands = [_]`)) >>
  disch_then (drule_at (Pat `i.inst_outputs = [_]`)) >>
  disch_then (drule_at (Pat `a.inst_outputs = [_]`)) >>
  disch_then (drule_at (Pat `b.inst_outputs = [_]`)) >>
  disch_then (fn th =>
    qpat_assum `lookup_block ta.vs_current_bb gn.fn_blocks = SOME gb`
      (mp_then (Pat `lookup_block ta.vs_current_bb _ = SOME gb`) mp_tac th)) >>
  disch_then (drule_at (Pat `!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok _ fn`)) >>
  disch_then (fn th => qpat_assum `i.inst_operands = [off]`
    (mp_then (Pat `i.inst_operands = [_]`) mp_tac th)) >>
  disch_then (qspec_then `fuel` mp_tac) >>
  (impl_tac >- (qpat_x_assum `saved :- _` kall_tac >> simp[])) >>
  disch_then (qx_choose_then `zs` strip_assume_tac) >>
  `alloca_inv (z with vs_inst_idx := SUC t.vs_inst_idx)` by
    (`alloca_inv z` by metis_tac[venomMemPropsTheory.alloca_inv_step_inst] >>
     qpat_x_assum `alloca_inv z` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  `zs.vs_current_bb = s.vs_current_bb /\ zs.vs_prev_bb = s.vs_prev_bb` by
    (qpat_assum `step_inst fuel CS i s = OK zs` mp_tac >>
     qpat_assum `i.inst_opcode = DLOAD` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule step_preserves_control_flow >> simp[is_terminator_def]) >>
  `z.vs_current_bb = ta.vs_current_bb /\ z.vs_prev_bb = ta.vs_prev_bb` by
    (qpat_assum `ld_target_prefix CT [a;b;c;d] _ _ _ _ _`
       (mp_then Any mp_tac ld_target_prefix_control) >>
     (impl_tac >- simp[is_terminator_def]) >> simp[]) >>
  `lookup_block (z with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
     gn.fn_blocks = SOME gb` by
    (qpat_x_assum `lookup_block ta.vs_current_bb gn.fn_blocks = SOME gb` mp_tac >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >>
     disch_then (mp_tac o SRULE [EVERY_MEM]) >>
     disch_then (qspec_then `fn` mp_tac) >>
     (impl_tac >- simp[]) >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     disch_then (mp_tac o CONJUNCT1) >>
     pure_rewrite_tac [fn_labels_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  `j' = HD nextcode` by
    (qpat_assum `active_inst gn j' _`
       (mp_then (Pat `active_inst _ _ _`) mp_tac ld_active_lookup_el) >>
     disch_then (qspec_then `gb` mp_tac) >>
     (impl_tac >- (qpat_x_assum `saved :- _` kall_tac >> gvs[])) >>
     qpat_assum `active_inst gn (HD nextcode) _`
       (mp_then (Pat `active_inst _ _ _`) mp_tac ld_active_lookup_el) >>
     disch_then (qspec_then `gb` mp_tac) >>
     (impl_tac >- (qpat_x_assum `saved :- _` kall_tac >> gvs[])) >> metis_tac[]) >>
  `nextcode <> []` by metis_tac[o1ContractLowerDloadTheory.lower_dload_inst_supply_nonempty] >>
  `active_inst fn i' (zs with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[lowerDloadProvenanceSupportTheory.ld_annotated_active_inst] >>
  Cases_on `in_revert_forward fn (zs with vs_inst_idx := SUC s.vs_inst_idx)`
  >- suspend "revert_successor" >>
  disj1_tac >>
  qexistsl_tac [`astk`, `gstk`, `k`, `L`, `AP`, `ld_set_prov AG [out'] NONE`,
    `step_taint i s zs tn`, `fn`, `i'`,
    `zs with vs_inst_idx := SUC s.vs_inst_idx`,
    `z with vs_inst_idx := SUC t.vs_inst_idx`, `step_taint j t z un`,
    `V`, `U`, `E`, `H`, `BP`,
    `ld_set_prov (ld_set_prov BH [bv] NONE) [out'] NONE`, `live`, `keys`,
    `a.inst_id INSERT A`, `suspended`, `f`, `fa`, `fb`, `bb`, `gb`, `a0`, `a2`,
    `nexta`, `a3`, `pre ++ [i]`, `rest`, `p ++ [a;b;c;d]`, `nextcode`,
    `nexttail`, `bpre`, `bpost`, `qpre`, `qpost`, `supports`, `savedkeys`,
    `s0`, `0`] >>
  asm "saved" (fn th => asm_rewrite_tac [th]) >>
  (conj_tac
   >- (qexistsl_tac [`cpre`, `cpost`, `gpre`, `gpost`, `observed`, `out`] >>
       asm_rewrite_tac [])) >>
  simp[GSYM APPEND_ASSOC] >>
  (conj_tac >- (qpat_x_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` mp_tac >> simp[])) >>
  qpat_x_assum `saved :- _` kall_tac >>
  `FINITE A /\ LIST_REL (\a g. FINITE a /\
      CARD a <= LENGTH (FILTER (\ii. ii.inst_opcode = DLOAD) (fn_insts g)))
      suspended (MAP (\sf. sf.lf_fn) astk)` by
    (qpat_assum `LIST_REL _ (A::suspended) _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  simp[] >>
  drule_all lowerDloadConfiguredCapsTheory.lower_dload_configured_cap_bound >> strip_tac >>
  `CARD (a.inst_id INSERT A) <= CARD keys` by
    (irule CARD_SUBSET >>
     qpat_assum `ld_alloc_account keys _ A s ta` mp_tac >>
     qpat_assum `a.inst_id IN keys` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lowerDloadAllocationTheory.ld_alloc_account_def] >> SET_TAC[]) >>
  gvs[] >>
  qpat_x_assum `CARD _ <= _` mp_tac >>
  qpat_x_assum `(if _ then _ else _) <= _` mp_tac >> decide_tac
QED

Resume ld_recursive_geometry_load_next[revert_successor]:
  `lookup_block (zs with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
     fn.fn_blocks = SOME bb` by
    (qpat_x_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` mp_tac >> simp[]) >>
  `lower_dload_insts_supply a0
     (TAKE (zs with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx
        bb.bb_instructions) = (p ++ [a;b;c;d],a2)` by
    (simp_tac (srw_ss()) [] >>
     qpat_assum `bb.bb_instructions = _` SUBST1_TAC >>
     qpat_assum `s.vs_inst_idx = _` SUBST1_TAC >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  `get_instruction gb (z with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = SOME j'` by
    (simp[get_instruction_def, EL_APPEND2] >>
     Cases_on `nextcode` >- metis_tac[] >> simp[EL_APPEND2, EL_APPEND1]) >>
  `EVERY (\v. MEM v fa.irs_used_vars) (FLAT (MAP inst_ir_vars bb.bb_instructions))` by
    (fs[venomFnScheduleRunnerTheory.ir_supply_covers_unit_def,
        venomFnScheduleRunnerTheory.list_subset_def, irSupplyTheory.unit_ir_vars_def,
        irSupplyTheory.fn_ir_vars_def, irSupplyTheory.block_ir_vars_def,
        EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     fs[lambdify irSupplyTheory.block_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     metis_tac[MEM_APPEND, MEM]) >>
  `EVERY (\v. MEM v a0.irs_used_vars) (FLAT (MAP inst_ir_vars bb.bb_instructions))` by
    (qpat_assum `lower_dload_blocks_supply fa bpre = (qpre,a0)`
       (mp_then Any mp_tac ld_blocks_supply_used_vars_mono) >>
     qpat_assum `EVERY _ (FLAT (MAP inst_ir_vars bb.bb_instructions))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `saved :- _` kall_tac >>
  drule_all ld_configured_revert_interval_entry >> strip_tac >>
  disj2_tac >> qexistsl_tac [`gb`, `copypos`, `endpos`] >> gvs[]
QED

Finalise ld_recursive_geometry_load_next
