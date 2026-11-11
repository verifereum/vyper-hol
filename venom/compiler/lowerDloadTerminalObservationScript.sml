Theory lowerDloadTerminalObservation
Ancestors
  lowerDloadRecursiveInterface lowerDloadResidualRead lowerDloadRevertSuffix
  lowerDloadSharedState ptrDiscipline o1PassContract venomExecSemantics
  o1LowerDloadRangeTransport lowerDloadRelocation pred_set words list venomState
  lowerDloadNormalData lowerDloadFrameCertificate lowerDloadOwnership
  lowerDloadReachableDiscipline lowerDloadOperand lowerDloadProvenanceSupport
  lowerDloadVariableTransport lowerDloadTargetGeometry finite_map memLocDefs
  pointerConfinedDefs venomInst contextCodegenRel lowerDloadOpaqueExecution
  lowerDloadCoverageInvariant lowerDloadPairedBoundary opcodeClass vfmState

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

Theorem ld_byte_rel_masked_slice:
  (!j. j < n ==> R (a+j) (b+j)) /\
  ld_byte_rel R X Y (\q. venomState$read_memory q 1 s)
    (\q. venomState$read_memory q 1 t) ==>
  LENGTH (venomState$read_memory a n s) =
    LENGTH (venomState$read_memory b n t) /\
  (!j. j < n /\ a+j NOTIN X ==>
    EL j (venomState$read_memory a n s) =
    EL j (venomState$read_memory b n t)) /\
  {j | j < n /\ b+j IN Y} SUBSET {j | j < n /\ a+j IN X}
Proof
  strip_tac >> conj_tac >- simp[ld_read_memory_length] >>
  conj_tac
  >- (rpt strip_tac >>
      `venomState$read_memory (a+j) 1 s =
       venomState$read_memory (b+j) 1 t` by
        (fs[ld_byte_rel_def] >> metis_tac[]) >>
      pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
      simp[ld_read_memory_element]) >>
  fs[ld_byte_rel_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_normal_return_observation:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  ~in_revert_forward fn s /\ i.inst_opcode = RETURN /\
  step_inst fuel CT i t = Halt th ==>
  ?sh. step_inst fuel CS i s = Halt sh /\
    LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
    (!q. q < LENGTH sh.vs_returndata /\ q NOTIN ret_taint tn i s ==>
      EL q sh.vs_returndata = EL q th.vs_returndata) /\
    ret_taint un i t SUBSET ret_taint tn i s
Proof
  strip_tac >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==> v IN U` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[]) >>
  `ld_owned_vars U E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `?off sz q n. i.inst_operands = [off;sz] /\
    eval_operand off t = SOME q /\ eval_operand sz t = SOME n` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[Once step_inst_non_invoke, SimpLHS] >>
     asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (drule_all ld_annotated_taint_ok >>
     simp[taint_ok_def] >> metis_tac[]) >>
  `ld_op_prov AG sz = NONE` by suspend "size_scalar" >>
  `eval_operand sz s = eval_operand sz t` by
    (irule ld_owned_operand_clean >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[MEM]) >>
  `?p. eval_operand off s = SOME p` by
    (Cases_on `eval_operand off s` >> simp[] >>
     metis_tac[ld_owned_operand_defined, MEM, optionTheory.NOT_SOME_NONE]) >>
  `eval_operand sz s = SOME n` by metis_tac[] >>
  suspend "observation"
QED

Resume ld_normal_return_observation[size_scalar]:
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!v. sz = Var v ==> v NOTIN fn_pv P fn` by
    (rpt strip_tac >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def] >>
     qexists_tac `v` >> Cases_on `off = Var v` >> gvs[]) >>
  drule_all ld_annotated_scalar_prov >> simp[]
QED

Resume ld_normal_return_observation[observation]:
  drule ld_normal_data_geometry >> strip_tac >>
  `!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)` by
    (rpt strip_tac >> rename1 `FLOOKUP AG v = SOME(owner,(bs,cz))` >>
     `owner IN live` by metis_tac[] >> simp[] >>
     `?bt. ld_site_entry E owner bs bt cz` by
       (qpat_x_assum `!v. ld_owned_selection E _ _` (qspec_then `v` mp_tac) >>
        simp[ld_owned_selection_def] >> metis_tac[]) >> metis_tac[]) >>
  `!j. j < w2n n ==>
    ((w2n p+j = w2n q+j /\ w2n p+j < lo) \/
      ld_site_bytes E live (w2n p+j) (w2n q+j))` by
    (gen_tac >> strip_tac >> irule ld_owned_read_range_geometry >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `ld_owned_vars _ _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`fn`,`i`,`w2n n`,
       `<|iao_ofst := off; iao_size := SOME sz; iao_max_size := SOME sz|>`] >>
     simp[mem_read_ops_def, source_memory_read_ranges_def,
          memory_range_of_operands_def] >>
     metis_tac[ld_annotated_access_ok, MEM]) >>
  `LENGTH (read_memory (w2n p) (w2n n) s) =
     LENGTH (read_memory (w2n q) (w2n n) t) /\
   (!j. j < w2n n /\ w2n p+j NOTIN tn.t_mem ==>
     EL j (read_memory (w2n p) (w2n n) s) =
     EL j (read_memory (w2n q) (w2n n) t)) /\
   {j | j < w2n n /\ w2n q+j IN un.t_mem} SUBSET
     {j | j < w2n n /\ w2n p+j IN tn.t_mem}` by
    (irule ld_byte_rel_masked_slice >>
     qexists_tac `(\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)` >>
     conj_tac >- (BETA_TAC >> asm_rewrite_tac[]) >>
     drule ld_normal_data_memory >> simp[]) >>
  suspend "execution"
QED

Resume ld_normal_return_observation[execution]:
  `th = halt_state (set_returndata (read_memory (w2n q) (w2n n) t) t)` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[Once step_inst_non_invoke, SimpLHS] >>
     asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
     simp[read_memory_def]) >>
  qexists_tac `halt_state (set_returndata (read_memory (w2n p) (w2n n) s) s)` >>
  conj_tac
  >- (simp[Once step_inst_non_invoke, SimpLHS] >>
      asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
      simp[read_memory_def]) >>
  gvs[halt_state_def, set_returndata_def, ret_taint_def,
      ld_read_memory_length] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Finalise ld_normal_return_observation

Theorem ld_noninvoke_halt_persistent:
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = Halt sh ==>
  sh.vs_call_ctx = s.vs_call_ctx /\
  (!a. (sh.vs_accounts a).storage = (s.vs_accounts a).storage) /\
  sh.vs_transient = s.vs_transient /\ sh.vs_immutables = s.vs_immutables /\
  (step_taint i s sh tn).t_stor = tn.t_stor /\
  (step_taint i s sh tn).t_trans = tn.t_trans /\
  (step_taint i s sh tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule step_inst_halt_opcodes >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[halt_state_def, set_returndata_def, lookup_account_def,
       step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def] >>
  rpt gen_tac >> rpt IF_CASES_TAC >> simp[] >>
  rw[vfmExecutionTheory.transfer_value_def, vfmStateTheory.update_account_def,
     vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  rw[]
QED

Theorem ld_normal_halt_observation:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  ~in_revert_forward fn s /\ i.inst_opcode <> INVOKE /\
  step_inst fuel CT i t = Halt th ==>
  ?sh sn Rs. final_taint vs0 CS sh sn Rs /\
    th.vs_call_ctx.cc_address = sh.vs_call_ctx.cc_address /\
    storage_agree_except sn.t_stor
      (sh.vs_accounts sh.vs_call_ctx.cc_address).storage
      (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
    storage_agree_except sn.t_trans
      (sh.vs_transient sh.vs_call_ctx.cc_address)
      (th.vs_transient th.vs_call_ctx.cc_address) /\
    FDOM sh.vs_immutables = FDOM th.vs_immutables /\
    (!q. q IN FDOM sh.vs_immutables ==>
      word_agree_except {b | (q,b) IN sn.t_imm}
        (sh.vs_immutables ' q) (th.vs_immutables ' q)) /\
    LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
    (!q. q < LENGTH sh.vs_returndata /\ q NOTIN Rs ==>
      EL q sh.vs_returndata = EL q th.vs_returndata) /\
    (step_taint i t th un).t_stor SUBSET sn.t_stor /\
    (step_taint i t th un).t_trans SUBSET sn.t_trans /\
    (step_taint i t th un).t_imm SUBSET sn.t_imm /\
    ret_taint un i t SUBSET Rs
Proof
  strip_tac >>
  `ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `?sh. step_inst fuel CS i s = Halt sh /\
    LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
    (!q. q < LENGTH sh.vs_returndata /\ q NOTIN ret_taint tn i s ==>
      EL q sh.vs_returndata = EL q th.vs_returndata) /\
    ret_taint un i t SUBSET ret_taint tn i s` by
    (Cases_on `i.inst_opcode = RETURN`
     >- (drule_all ld_normal_return_observation >> simp[])
     >> suspend "other_execution") >>
  suspend "final"
QED

Resume ld_normal_halt_observation[other_execution]:
  Cases_on `i.inst_opcode = STOP \/ i.inst_opcode = SINK`
  >- (gvs[] >>
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[Once step_inst_non_invoke, SimpLHS] >>
      asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
      strip_tac >> gvs[] >>
      simp[Once step_inst_non_invoke, SimpLHS] >>
      asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
      gvs[halt_state_def, set_returndata_def, ret_taint_def, ld_shared_state_def]) >>
  `i.inst_opcode = SELFDESTRUCT` by metis_tac[step_inst_halt_opcodes] >>
  suspend "selfdestruct"
QED

Resume ld_normal_halt_observation[selfdestruct]:
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[]) >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >>
     goal_assum (drule_at Any) >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (drule_all ld_annotated_taint_ok >> simp[taint_ok_def] >> metis_tac[]) >>
     irule ld_annotated_scalar_prov >>
     goal_assum (drule_at Any) >> simp[] >>
     `fn_ptr_ok P fn` by metis_tac[ld_annotated_fn_member] >>
     `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def] >> metis_tac[]) >>
  suspend "self_execution"
QED

Resume ld_normal_halt_observation[self_execution]:
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[ld_shared_state_environment] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `eval_operand addr_op s = SOME addr` by metis_tac[MEM] >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  gvs[eval_operands_def, halt_state_def, set_returndata_def, ret_taint_def]
QED

Resume ld_normal_halt_observation[final]:
  `final_taint vs0 CS sh (step_taint i s sh tn) (ret_taint tn i s)` by
    (drule ld_annotated_erasure >>
     drule ld_annotated_active_inst >>
     simp[final_taint_def] >> metis_tac[]) >>
  qexistsl_tac [`sh`,`step_taint i s sh tn`,`ret_taint tn i s`] >>
  simp[] >>
  `sh.vs_call_ctx = s.vs_call_ctx /\
   (!a. (sh.vs_accounts a).storage = (s.vs_accounts a).storage) /\
   sh.vs_transient = s.vs_transient /\ sh.vs_immutables = s.vs_immutables /\
   (step_taint i s sh tn).t_stor = tn.t_stor /\
   (step_taint i s sh tn).t_trans = tn.t_trans /\
   (step_taint i s sh tn).t_imm = tn.t_imm` by
    (irule ld_noninvoke_halt_persistent >> metis_tac[]) >>
  `th.vs_call_ctx = t.vs_call_ctx /\
   (!a. (th.vs_accounts a).storage = (t.vs_accounts a).storage) /\
   th.vs_transient = t.vs_transient /\ th.vs_immutables = t.vs_immutables /\
   (step_taint i t th un).t_stor = un.t_stor /\
   (step_taint i t th un).t_trans = un.t_trans /\
   (step_taint i t th un).t_imm = un.t_imm` by
    (irule ld_noninvoke_halt_persistent >> metis_tac[]) >>
  gvs[ld_shared_state_def]
QED

Finalise ld_normal_halt_observation
