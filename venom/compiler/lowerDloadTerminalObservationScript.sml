Theory lowerDloadTerminalObservation
Ancestors
  lowerDloadRecursiveInterface lowerDloadResidualRead lowerDloadRevertSuffix
  lowerDloadSharedState ptrDiscipline o1PassContract venomExecSemantics

(* Terminal interface audit (not a proof of the quoted obligation).

   final_taint_def (ptrDiscipline:655) observes a reachable active instruction,
   excludes INVOKE, and requires step_inst = Halt. run_defs reduces this to
   step_inst_base, with no pre-halted shortcut. The direct Halt cases are:

   STOP: clears returndata; persistent masks are unchanged; ret_taint = {}.
   RETURN: reads relocated memory; ret_taint is the relative-position mask
     {i | i < w2n sz /\ w2n off + i IN tn.t_mem}.
   SINK: preserves returndata; ret_taint = {}.
   SELFDESTRUCT: fails in static frames, otherwise changes balances only,
     clears returndata, and leaves storage/transient/immutable masks unchanged.
   REVERT and INVALID produce Abort, not Halt. RET/DRET produce IntRet.
   Non-INVOKE call/create cases cannot Halt (exec_create_not_Halt also exported).

   Exceptional candidate: strictly after copypos, ld_revert_pair_suffix_step
   already excludes Halt. At copypos, revert_forward_pair identifies
   RETURNDATACOPY; its step_inst_base equation excludes Halt directly.
   No current normal_data or source annotation is needed in either case.

   Normal candidate: any Halt instruction in supplied code must be the
   original singleton instruction. DLOAD/DLOADBYTES expansions contain only
   ALLOCA/ADD/CODECOPY/MLOAD, hence cannot Halt at any phase. This also forces
   phase zero, so t=ta and un=ua. Required residual: a singleton Halt selector
   preserving the whole normal witness, analogous to the checked external
   singleton selection, without unpack/repack of saved certificates.

   Normal-data terminal boundary still required:
   - source annotated reachability erases to source frame_reachable;
   - target Halt of the same unchanged instruction yields source Halt;
   - source/target final storage, transient and immutable agreement is masked
     by source masks, and target step_taint masks are subsets;
   - RETURN lengths agree, clean relative bytes agree, and target ret_taint is
     a subset of source ret_taint. Do NOT require whole returned lists equal.
     Use ld_normal_data_memory, ld_byte_rel_def, owned read-range geometry,
     annotated access_ok, and ordinary (non-retpc) operand selection. The
     existing ld_normal_observation_read covers SHA3/LOG only and is not an
     applicable RETURN lemma: source taint may remain in returned bytes.
   - STOP/SINK/SELFDESTRUCT need no relocated-memory read boundary. Shared
     state provides equal old returndata for SINK. Balance updates preserve
     masked storage agreement, including beneficiary=self.

   final_taint_transport in o1ContractLowerDloadTaintScript.sml:189 is downstream
   of this leaf and can be used there without creating an import cycle. Its
   source final witness, address agreement, dead-masked storage/transient/
   immutable agreement, equal returndata length, dead-clean byte agreement,
   and four mask inclusions are sufficient. Source-mask agreement can be
   weakened to dead-mask agreement using source taint_within first. No new
   dead-set transport lemma is needed.

   Semantic residual ownership: terminal Halt selector/exclusion; normal
   terminal backward boundary (RETURN memory plus other Halt cases); final
   candidate consumer; reachable final consumer and frozen taint assembly.
   Requests are already discharged by ld_reachable_request_observation.
*)

(* Typechecked consumer-shaped contract for the remaining final conjunct.
   This is an ML term quotation only, not a HOL definition or an assumption. *)
val ld_final_observation_goal = ``
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view CS CT /\
  dead_wf D /\ o1_ctx_shape CS /\ o1_run_state_ok vs0 /\
  o1_src_inv D CS vs0 /\ callee_first names CS.ctx_functions ==>
  !t_h un R.
    final_taint vs0 CT t_h un R ==>
    un.t_stor SUBSET D.d_stor t_h.vs_call_ctx.cc_address
      (t_h.vs_accounts t_h.vs_call_ctx.cc_address).storage /\
    un.t_trans SUBSET D.d_trans t_h.vs_call_ctx.cc_address
      (t_h.vs_transient t_h.vs_call_ctx.cc_address) /\
    un.t_imm SUBSET D.d_imm t_h.vs_immutables /\
    R SUBSET D.d_ret t_h.vs_returndata``;
