Theory lowerDloadRecursiveInterface
Ancestors
  lowerDloadProjectedReachability lowerDloadNormalData lowerDloadReachability
  lowerDloadRevertSuffix lowerDloadSavedExtension lowerDloadPhaseBoundary
  lowerDloadControlPosition lowerDloadOwnership lowerDloadDefs
  ptrDiscipline list finite_map pred_set words

(* Diagnostic quotation only: not a definition, theorem, or closure claim.
   This is the initial projected normal/phase and exceptional-mode core.
   The saved configured-control/parameter fields and configured context-fold
   membership are deliberately NOT yet claimed complete. See ledger below.
   Keep this single quotation as the candidate under development. *)
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
          SUBSET count 32))) \/
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

   STILL TO DO IN THIS DIAGNOSTIC:
   - Expand saved configured INVOKE positions, source origins, parameter
     envelopes and per-frame function/context-fold membership in the quote.
   - Check the five projected clauses at that ONE complete candidate,
     producing exact residual formulas assigned to existing branch owners.
   - Check strict prefix no observations and copy-mode impossible constructors.
   The current quotation is a typechecked core, not the final required output.
*)
