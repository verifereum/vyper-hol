(* Expose the compiler sites for argument snapshots, direct ABI encoding and
 * REVERT, together with the selector frame and exact REVERT result.
 *
 * The tuple-window tail is an independent gadget. Its proofs describe a
 * payload already stored in a tuple buffer and quantify over where it lives.
 *)
Theory stmtSimCustomErrorRevert
Ancestors
  stmtLowering compileEnv fragGasPathMem abiEncoderWindowContract
  abiEncoderAdmissible abiEncoderRegisteredEffect abiEncoderProps
  exprLoweringProps venomMemDefs venomState venomExecSemantics vyperAST
  valueEncoding stmtSimCustomErrorPrefix stmtSimCustomErrorWindow
  stmtSimCustomErrorExit abiEncoderWindowRunMem abiEncoderAppend
  memContinuationExit fragExec emitHelperProps loweringHalt actualAllocExec words
  venomInst arithmetic compilerInstructionSuffix windowPhaseMem abiEncoderWindowPhase
  stmtSimCustomErrorPayloadPrepare externalReturnEncoderSites abiEncoderResultLive
  calldataDynOwned allocaSiteResource stmtSimCustomErrorTrapCompile
  stmtSimCustomErrorTrap stmtSimCustomErrorTrapPath runFromGasPathMem
  abiEncodeValuesPhases fragGasEmitCtrl ptrSafeRun ptrDiscipline instMemFrontier
  memSafeRun unitTransformDefs gasEvents gasCount venomExecProps
  valueEncodingDefs valueEncodingProofs codegenRel contextCodegenRel memLocDefs list pair

Definition custom_error_revert_tail_def:
  custom_error_revert_tail cenv id tys args_buf no_args =
    do buf_alloc <- compile_alloc_buffer
         (abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32);
       buf <- return buf_alloc.buf_operand;
       emit_void MSTORE [buf; Lit (n2w (cenv.ce_method_id (SND id) tys))];
       if no_args then
         do revert_offset <- emit_op ADD [buf; Lit 28w];
            emit_inst REVERT [revert_offset; Lit 4w] []
         od
       else
         do payload_buf <- emit_op ADD [buf; Lit 32w];
            encoded_len <- compile_abi_encode_to_buf payload_buf args_buf
              (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys));
            revert_offset <- emit_op ADD [buf; Lit 28w];
            revert_len <- emit_op ADD [Lit 4w; encoded_len];
            emit_inst REVERT [revert_offset; revert_len] []
         od
    od
End

Theorem compile_revert_with_custom_error_split:
  cenv.ce_error_info (nsid_to_string id) = SOME params /\
  args = custom_error_exprs (CustomError id positional kwargs) /\
  tys = MAP (lowered_value_type cenv) args /\
  compile_revert_with_custom_error cenv (CustomError id positional kwargs) s0 =
    ((),s1) ==>
  ?saved sa buf sm ss.
    compile_ext_call_args compile_expr cenv [] tys args s0 = (saved,sa) /\
    compile_alloc_buffer (abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32)
      sa = (buf,sm) /\
    emit_void MSTORE
      [buf.buf_operand; Lit (n2w (cenv.ce_method_id (SND id) (MAP SND params)))]
      sm = ((),ss) /\
    (if NULL args then
       ?offset sn. emit_op ADD [buf.buf_operand; Lit 28w] ss = (offset,sn) /\
                   emit_inst REVERT [offset; Lit 4w] [] sn = ((),s1)
     else
       ?dst st encoded en offset sr len sn.
         emit_op ADD [buf.buf_operand; Lit 32w] ss = (dst,st) /\
         compile_abi_encode_values_to_buf cenv dst (ZIP (saved,tys)) st = (encoded,en) /\
         emit_op ADD [buf.buf_operand; Lit 28w] en = (offset,sr) /\
         emit_op ADD [Lit 4w; encoded] sr = (len,sn) /\
         emit_inst REVERT [offset; len] [] sn = ((),s1))
Proof
  strip_tac >>
  qpat_x_assum `compile_revert_with_custom_error _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_revert_with_custom_error_def, LET_THM,
    optionTheory.option_case_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> gvs[comp_bind_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def]) >> metis_tac[]
QED

Theorem ce_trap_custom_error_revert_tail:
  custom_error_revert_tail cenv id tys args_buf no_args sm = ((),sb) ==>
  custom_error_revert_tail cenv id tys args_buf no_args (ce_trap_cs sm) =
    ((),ce_trap_cs sb)
Proof
  `ce_compile_commutes (custom_error_revert_tail cenv id tys args_buf no_args)`
    suffices_by metis_tac[ce_compile_commutes_def] >>
  rewrite_tac[custom_error_revert_tail_def] >>
  irule ce_compile_bind >> simp[ce_compile_alloc_buffer] >> gen_tac >>
  irule ce_compile_bind >> simp[ce_compile_return] >> gen_tac >>
  irule ce_compile_ignore_bind >> simp[ce_compile_emit_helpers] >>
  Cases_on `no_args` >> simp[]
  >- (irule ce_compile_bind >> simp[ce_compile_emit_helpers]) >>
  irule ce_compile_bind >> simp[ce_compile_emit_helpers] >> gen_tac >>
  irule ce_compile_bind >> simp[cj 2 ce_compile_encoder_mutual] >> gen_tac >>
  irule ce_compile_bind >> simp[ce_compile_emit_helpers] >> gen_tac >>
  irule ce_compile_bind >> simp[ce_compile_emit_helpers]
QED

Theorem custom_error_revert_tail_safe_exit:
  !ctx func cenv id tys args_buf no_args sm sb s a aid n ei at av.
    custom_error_revert_tail cenv id tys args_buf no_args sm = ((),sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32 < 2 ** 64 /\
    ei = type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys) /\
    (~no_args ==>
       abi_encoder_admissible ei /\
       eval_operand args_buf s = SOME (n2w a) /\
       (!x. args_buf = Var x ==> not_fresh_at sm x) /\
       FLOOKUP s.vs_allocas aid = SOME (a,n) /\ aid NOTIN frag_ids sm sb /\
       type_memory_bytes cenv (TupleT tys) <= n /\
       abi_encoder_window_input ei at av a (type_memory_bytes cenv (TupleT tys))
         s.vs_memory /\
       LENGTH (enc at av) <= abi_size_bound cenv.ce_struct_fields (TupleT tys)) /\
    alloca_inv s /\ alloca_room ctx func s /\
    (!inst w base sz.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==>
       sz = w2n w) /\
    ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?t fuel. run_from fuel ctx func s = Abort Revert_abort t /\
       mem_safe_run fuel ctx func s /\
       abi_encoder_registered_effect (frag_ids sm sb) [] s t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_alloc_buffer
    (abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32) sm` >>
  rename1 `_ = (buf,sa)` >>
  Cases_on `emit_void MSTORE
    [buf.buf_operand; Lit (n2w (cenv.ce_method_id (SND id) tys))] sa` >>
  rename1 `_ = (unit,sc)` >> Cases_on `unit` >>
  qpat_x_assum `custom_error_revert_tail _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [custom_error_revert_tail_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  strip_tac >> Cases_on `no_args`
  >- suspend "empty" >>
  suspend "encoded"
QED

Resume custom_error_revert_tail_safe_exit[empty]:
  gvs[] >>
  Cases_on `emit_op ADD [buf.buf_operand; Lit 28w] sc` >>
  rename1 `_ = (offset,sn)` >>
  gvs[comp_bind_def] >>
  `cs_extends sm sa /\ cs_extends sa sc /\ cs_extends sc sn /\ cs_extends sn sb` by
    metis_tac[compile_alloc_buffer_extends, cs_appends_emit_helpers,
      cs_appends_def, cs_extends_emit_inst] >>
  `cs_extends sa sb /\ cs_extends sc sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sm sa func /\ fn_has_code sa sc func /\
   fn_has_code sc sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  `abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32 < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  `!b sz. FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,sz) ==>
    sz = abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32` by
    (rpt strip_tac >>
     qpat_x_assum `!inst w base sz. _` drule >>
     simp[mk_inst_def, w2n_n2w] >> metis_tac[LESS_MOD]) >>
  drule_all (SRULE [] custom_error_selector_prefix_run) >> strip_tac >>
  `fn_has_code sn sn func` by
    (mp_tac (Q.SPECL [`sn`,`sn`,`sb`,`func`] fn_has_code_split) >>
     simp[cs_extends_refl]) >>
  `?u. gas_path_mem ctx func t 0 (Abort Revert_abort u) /\
    (?fuel. run_from fuel ctx func t = Abort Revert_abort u /\
       mem_safe_run fuel ctx func t) /\
    abi_encoder_registered_effect (frag_ids sm sb) [] t u` by
    (irule (Q.INST [`no_args` |-> `T`, `k` |-> `0`,
       `encoded_len` |-> `Lit 0w`] custom_error_revert_suffix_run) >>
     asm_simp_tac bool_ss [] >>
     goal_assum (drule_at (Pat `emit_inst REVERT _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     asm_simp_tac bool_ss [] >>
     qexistsl_tac [`0`, `d`] >> simp[] >> decide_tac) >>
  `?fuel'. run_from fuel' ctx func s = Abort Revert_abort u /\
    mem_safe_run fuel' ctx func s` by
    (irule mem_cont_sim_exit_run >> simp[exit_result_def] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `sm.cs_next_id < sb.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     imp_res_tac added_insts_emit_void >>
     imp_res_tac added_insts_emit_op >>
     imp_res_tac added_insts_emit_inst >> decide_tac) >>
  `abi_encoder_registered_effect (frag_ids sm sb) [] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`{sm.cs_next_id}`, `[]`] >>
     simp[frag_ids_def, pred_setTheory.SUBSET_DEF]) >>
  qexistsl_tac [`u`, `fuel'`] >> simp[] >>
  metis_tac[abi_encoder_registered_effect_trans]
QED
Resume custom_error_revert_tail_safe_exit[encoded]:
  gvs[] >>
  Cases_on `emit_op ADD [buf.buf_operand; Lit 32w] sc` >>
  rename1 `_ = (payload,st)` >>
  Cases_on `compile_abi_encode_to_buf payload args_buf
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys)) st` >>
  rename1 `_ = (encoded,en)` >>
  Cases_on `emit_op ADD [buf.buf_operand; Lit 28w] en` >>
  rename1 `_ = (offset,sr)` >>
  Cases_on `emit_op ADD [Lit 4w; encoded] sr` >>
  rename1 `_ = (len,sn)` >>
  gvs[comp_bind_def] >>
  `cs_extends sm sa /\ cs_extends sa sc /\ cs_extends sc st /\
   cs_extends st en /\ cs_extends en sr /\ cs_extends sr sn /\ cs_extends sn sb` by
    metis_tac[compile_alloc_buffer_extends, cs_appends_emit_helpers,
      cs_appends_def, cs_extends_emit_inst, compile_abi_encode_to_buf_extends] >>
  `cs_extends sa sb /\ cs_extends sc sb /\ cs_extends st sb /\
   cs_extends en sb /\ cs_extends sr sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sm sa func /\ fn_has_code sa sc func /\
   fn_has_code sc st func /\ fn_has_code st en func /\
   fn_has_code en sr func /\ fn_has_code sr sn func /\ fn_has_code sn sb func` by
    (mp_tac (Q.SPECL [`sm`,`sa`,`sb`,`func`] fn_has_code_split) >>
     mp_tac (Q.SPECL [`sa`,`sc`,`sb`,`func`] fn_has_code_split) >>
     mp_tac (Q.SPECL [`sc`,`st`,`sb`,`func`] fn_has_code_split) >>
     mp_tac (Q.SPECL [`st`,`en`,`sb`,`func`] fn_has_code_split) >>
     mp_tac (Q.SPECL [`en`,`sr`,`sb`,`func`] fn_has_code_split) >>
     mp_tac (Q.SPECL [`sr`,`sn`,`sb`,`func`] fn_has_code_split) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  `abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32 < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  `!b sz. FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,sz) ==>
    sz = abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32` by
    (rpt strip_tac >>
     qpat_x_assum `!inst w base sz. _` drule >>
     simp[mk_inst_def, w2n_n2w] >> metis_tac[LESS_MOD]) >>
  `sm.cs_next_id < st.cs_next_id /\ st.cs_next_id <= en.cs_next_id /\
   en.cs_next_id <= sb.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     imp_res_tac added_insts_emit_void >>
     imp_res_tac added_insts_emit_op >>
     imp_res_tac added_insts_emit_inst >>
     drule compile_abi_encode_to_buf_next_id >> decide_tac) >>
  `aid <> sm.cs_next_id` by
    (qpat_x_assum `aid NOTIN frag_ids sm sb` mp_tac >>
     simp[frag_ids_def] >> decide_tac) >>
  drule_all (SRULE [] custom_error_payload_prepare) >>
  disch_then (qx_choose_then `u` (qx_choose_then `d` strip_assume_tac)) >>
  `aid NOTIN frag_ids st en /\ sm.cs_next_id NOTIN frag_ids st en /\
   frag_ids st en SUBSET frag_ids sm sb` by
    (qpat_x_assum `aid NOTIN frag_ids sm sb` mp_tac >>
     simp[frag_ids_def, pred_setTheory.SUBSET_DEF] >> decide_tac) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32` by
    (rpt strip_tac >>
     `inst.inst_operands = [Lit 32w]` by
       metis_tac[encoder_function_alloca_shape] >>
     `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz)` by
       (qpat_x_assum `abi_encoder_registered_effect _ _ s u` mp_tac >>
        simp_tac bool_ss [abi_encoder_registered_effect_def] >>
        strip_tac >> metis_tac[pred_setTheory.IN_SING]) >>
     qpat_x_assum `!inst w base sz. _` drule >> simp[]) >>
  `abi_encoder_window_pre ctx func st en payload args_buf
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys))
    at av a (type_memory_bytes cenv (TupleT tys)) (d+32) u` by
    (irule custom_error_registered_payload_window >>
     goal_assum (drule_at (Pat `FLOOKUP _.vs_allocas aid = _`)) >>
     metis_tac[]) >>
  drule_all compile_abi_encode_to_buf_window_strong_mem >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  drule window_phase_strong_result >> strip_tac >>
  `eval_operand buf.buf_operand v = SOME (n2w d)` by
    metis_tac[window_phase_operand] >>
  `FLOOKUP v.vs_allocas sm.cs_next_id =
    SOME (d,abi_size_bound cenv.ce_struct_fields (TupleT tys)+32)` by
    (drule window_strong_result_public >> strip_tac >>
     drule abi_encoder_window_result_effect >>
     metis_tac[abi_encoder_registered_effect_allocated]) >>
  `d+(abi_size_bound cenv.ce_struct_fields (TupleT tys)+32) <= v.vs_alloca_next` by
    (drule window_phase_resources >> metis_tac[alloca_site_registered_below]) >>
  `!x. encoded = Var x ==> not_fresh_at en x` by
    (drule abi_encode_result_live >> Cases_on `encoded` >>
     simp[calldata_operand_live_not_fresh]) >>
  `?w. gas_path_mem ctx func v 0 (Abort Revert_abort w) /\
    (?fuel. run_from fuel ctx func v = Abort Revert_abort w /\
       mem_safe_run fuel ctx func v) /\
    abi_encoder_registered_effect (frag_ids sm sb) [] v w` by
    (irule (Q.INST [`no_args` |-> `F`, `st` |-> `en`,
        `sn` |-> `sr`, `sr` |-> `sn`, `en` |-> `sb`, `x` |-> `()`]
        custom_error_revert_suffix_run) >>
     simp_tac bool_ss [] >>
     conj_tac >- metis_tac[window_phase_control] >>
     goal_assum (drule_at (Pat `emit_inst REVERT _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD [Lit 4w; _] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD [_; Lit 28w] _ = _`)) >>
     simp_tac bool_ss [] >>
     qexistsl_tac [`abi_size_bound cenv.ce_struct_fields (TupleT tys)`,
       `d`, `LENGTH (enc at av)`] >>
     drule window_strong_result_public >>
     simp_tac bool_ss [abi_encoder_window_result_def] >> strip_tac >>
     drule window_phase_control >> strip_tac >>
     rpt conj_tac
     >- decide_tac
     >- first_assum ACCEPT_TAC
     >- decide_tac >> first_assum ACCEPT_TAC) >>
  `?fuel'. run_from fuel' ctx func u = Abort Revert_abort w /\
    mem_safe_run fuel' ctx func u` by
    (irule mem_cont_sim_exit_run >> simp_tac bool_ss [exit_result_def] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `?fuel''. run_from fuel'' ctx func s = Abort Revert_abort w /\
    mem_safe_run fuel'' ctx func s` by
    (irule mem_cont_sim_exit_run >> simp_tac bool_ss [exit_result_def] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `abi_encoder_registered_effect (frag_ids sm sb) [] u v` by
    (irule custom_error_payload_effect_absorb >>
     goal_assum (drule_at (Pat `FLOOKUP _.vs_allocas _ = _`)) >>
     drule window_phase_effect >>
     simp_tac bool_ss [window_alloca_sites_def] >>
     strip_tac >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (simp_tac (srw_ss()) [frag_ids_def] >> decide_tac) >>
     qpat_x_assum `frag_ids st en SUBSET frag_ids sm sb` mp_tac >>
     simp_tac (srw_ss()) [pred_setTheory.SUBSET_DEF,
       window_alloca_sites_def] >> metis_tac[]) >>
  `abi_encoder_registered_effect (frag_ids sm sb) [] s u` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`{sm.cs_next_id}`, `[]`] >>
     simp_tac (srw_ss()) [frag_ids_def, pred_setTheory.SUBSET_DEF] >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`w`, `fuel''`] >>
  metis_tac[abi_encoder_registered_effect_trans]
QED
Finalise custom_error_revert_tail_safe_exit

Theorem custom_error_revert_tail_projected_path:
  !ctx func cenv id tys args_buf no_args sm sb s a aid n ei at av.
    custom_error_revert_tail cenv id tys args_buf no_args sm = ((),sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32 < 2 ** 64 /\
    ei = type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys) /\
    (~no_args ==>
       abi_encoder_admissible ei /\
       eval_operand args_buf s = SOME (n2w a) /\
       (!x. args_buf = Var x ==> not_fresh_at sm x) /\
       FLOOKUP s.vs_allocas aid = SOME (a,n) /\ aid NOTIN frag_ids sm sb /\
       type_memory_bytes cenv (TupleT tys) <= n /\
       abi_encoder_window_input ei at av a (type_memory_bytes cenv (TupleT tys))
         s.vs_memory /\
       LENGTH (enc at av) <= abi_size_bound cenv.ce_struct_fields (TupleT tys)) /\
    alloca_inv s /\ alloca_room ctx func s /\
    (!inst w base sz.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==>
       sz = w2n w) /\
    ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?t count. gas_path_mem (ce_trap_ctx ctx) (ce_trap_fn func) s count
                (Abort Revert_abort t) /\
        abi_encoder_registered_effect (frag_ids sm sb) [] s t
Proof
  rpt gen_tac >> strip_tac >>
  `?t fuel. run_from fuel (ce_trap_ctx ctx) (ce_trap_fn func) s =
       Abort Revert_abort t /\
     mem_safe_run fuel (ce_trap_ctx ctx) (ce_trap_fn func) s /\
     abi_encoder_registered_effect (frag_ids sm sb) [] s t` by
    (mp_tac (Q.INST [`ctx` |-> `ce_trap_ctx ctx`,
                     `func` |-> `ce_trap_fn func`,
                     `sm` |-> `ce_trap_cs sm`, `sb` |-> `ce_trap_cs sb`]
       (SPEC_ALL custom_error_revert_tail_safe_exit)) >>
     simp[ce_trap_custom_error_revert_tail, ce_trap_fn_has_code,
       ce_trap_fn_inst_ids_distinct, ce_trap_frag_ids, ce_trap_alloca_room,
       ce_trap_recorded_alloca_size, ce_trap_cs_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     impl_tac >- (conj_tac
       >- gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
       drule ce_trap_recorded_alloca_size >> simp[]) >> simp[]) >>
  drule run_from_gas_path_mem >> simp[exit_result_def] >>
  strip_tac >> metis_tac[]
QED

(* The legacy tuple-buffer gadget starts after the argument stores.
   With arguments, the args tuple is a registered alloca outside this fragment,
   holding a valid encoder input whose encoding fits the ABI size bound.  A
   recorded ALLOCA keeps its literal size (the clause stmt_state_rel carries),
   so a re-entered site of this fragment reuses a region of the size it asks. *)
Theorem custom_error_revert_tail_run:
  !ctx func cenv id tys args_buf no_args sm sb s a aid n ei at av.
    custom_error_revert_tail cenv id tys args_buf no_args sm = ((),sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32 < 2 ** 64 /\
    ei = type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys) /\
    (~no_args ==>
       abi_encoder_admissible ei /\
       eval_operand args_buf s = SOME (n2w a) /\
       (!x. args_buf = Var x ==> not_fresh_at sm x) /\
       FLOOKUP s.vs_allocas aid = SOME (a,n) /\ aid NOTIN frag_ids sm sb /\
       type_memory_bytes cenv (TupleT tys) <= n /\
       abi_encoder_window_input ei at av a (type_memory_bytes cenv (TupleT tys))
         s.vs_memory /\
       LENGTH (enc at av) <= abi_size_bound cenv.ce_struct_fields (TupleT tys)) /\
    alloca_inv s /\ alloca_room ctx func s /\
    (!inst w base sz.
       MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\
       FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==>
       sz = w2n w) /\
    ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?t. gas_path_mem ctx func s 0 (Abort Revert_abort t) /\
        abi_encoder_registered_effect (frag_ids sm sb) [] s t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all custom_error_revert_tail_projected_path >> strip_tac >>
  drule custom_error_trap_path_reflect >> simp[] >>
  strip_tac >> metis_tac[]
QED

(* Preserve the complete selector word through cursor and payload writes. *)
Theorem custom_error_selector_word_frame:
  window_phase ctx func st en ids outs s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas owner = SOME (b,sz) /\ owner NOTIN ids /\
  32 <= sz /\ EVERY (\(p,n). b+32 <= p) outs /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!id p n. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  FLOOKUP t.vs_allocas owner = SOME (b,sz) /\
  mem_bytes_at b 32 t.vs_memory = mem_bytes_at b 32 s.vs_memory /\
  (!i. b <= i /\ i < b+32 /\ i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> irule abi_encode_values_registered_window >>
  qpat_assum `window_phase _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP s.vs_allocas owner = _` (irule_at Any) >>
  simp[EVERY_MEM, FORALL_PROD, venomMemDefsTheory.regions_disjoint_def] >>
  fs[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

(* The selector uses the final four bytes of the word MSTORE wrote. *)
Theorem custom_error_emit_revert_exact:
  emit_inst REVERT [Var offset;len] [] st = ((),en) /\
  fn_has_code st en func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand (Var offset) s = SOME (n2w (b+28)) /\
  eval_operand len s = SOME (n2w (4 + LENGTH bytes)) /\
  FLOOKUP G offset = SOME (b,cap) /\ b+32+LENGTH bytes <= b+cap /\
  b+cap <= s.vs_alloca_next /\ b+cap < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  op_taint tn (Var offset) = {} /\ op_taint tn len = {} /\
  mem_bytes_at b 32 s.vs_memory = word_to_bytes (selector:bytes32) T /\
  mem_bytes_at (b+32) (LENGTH bytes) s.vs_memory = bytes /\
  (!i. b+28 <= i /\ i < b+32 ==> i NOTIN tn.t_mem) /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bytes ==> i NOTIN tn.t_mem) ==>
  ?t. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort t,G,tn) /\
      t.vs_returndata = DROP 28 (word_to_bytes selector T) ++ bytes /\
      (!i. b+28 <= i /\ i < b+32+LENGTH bytes ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!i. b+28 <= i /\ i < b+32+LENGTH bytes ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> Cases_on `i < b+32` >- metis_tac[] >>
     `b+32 <= i` by decide_tac >> metis_tac[]) >>
  drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id REVERT [Var offset;len] []` >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`]) >>
  `b+28 < dimword (:256) /\ 4+LENGTH bytes < dimword (:256)` by decide_tac >>
  qabbrev_tac `ret = mem_bytes_at (b+28) (4+LENGTH bytes) s.vs_memory` >>
  qabbrev_tac `t = revert_state (set_returndata ret s)` >>
  `!fuel. step_inst fuel ctx inst s = Abort Revert_abort t` by
    (gen_tac >>
     mp_tac (Q.SPECL [`s`, `Var offset`, `len`, `st.cs_next_id`,
       `n2w (b+28):bytes32`, `n2w (4+LENGTH (bytes:word8 list)):bytes32`] step_revert_behavior) >>
     simp[Abbr `inst`, Abbr `t`, Abbr `ret`, step_inst_non_invoke, mk_inst_def,
          mem_bytes_at_def, w2n_n2w]) >>
  suspend "run"
QED

Resume custom_error_emit_revert_exact[run]:
  `source_memory_read_ranges inst s = [(b+28,4+LENGTH bytes)]` by
    simp[Abbr `inst`, source_memory_read_ranges_def, mk_inst_def,
         memory_range_of_operands_def, w2n_n2w] >>
  `inst.inst_opcode = REVERT /\ inst.inst_operands = [Var offset;len] /\
    source_memory_write_ranges inst s = [] /\
    mem_read_ops inst = SOME <|iao_ofst := Var offset; iao_size := SOME len;
      iao_max_size := SOME len |>` by
    simp[Abbr `inst`, mk_inst_def, source_memory_write_ranges_def, mem_read_ops_def] >>
  `b+28+(4+LENGTH bytes) <= b+cap /\
    b+28+(4+LENGTH bytes) <= s.vs_alloca_next` by decide_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def] >> conj_tac
     >- (qx_gen_tac `operand` >> Cases_on `operand = Var offset` >> simp[] >>
         Cases_on `operand = len` >> simp[]) >>
     disch_tac >> qx_gen_tac `i` >>
     Cases_on `b+28 <= i` >> simp[] >>
     Cases_on `i < b+(LENGTH bytes+32)` >> simp[] >>
     `i < b+32+LENGTH bytes` by decide_tac >>
     qpat_x_assum `!i. b+28 <= i /\ i < b+32+LENGTH bytes ==> _` irule >>
     simp[]) >>
  `mem_safe_step 0 ctx inst s` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def] >>
  `gas_events_step 0 ctx func.fn_name inst s = [] /\
    gas_count_step 0 ctx inst s = 0` by
    simp[Abbr `inst`, mk_inst_def, gas_events_step_def, gas_count_step_def] >>
  qexists_tac `t` >>
  conj_tac
  >- (irule exit_inst_origin_ptr >> simp[exit_result_def] >>
      qexists_tac `inst` >>
      fs[]) >>
  simp[Abbr `t`, set_returndata_def, revert_state_def, Abbr `ret`] >>
  `mem_bytes_at (b+28) 4 s.vs_memory = DROP 28 (word_to_bytes selector T)` by
    (qspecl_then [`b`,`28`,`4`,`s.vs_memory`] mp_tac mem_bytes_at_split_padded >>
     simp[] >> disch_then (mp_tac o AP_TERM ``DROP 28 : word8 list -> word8 list``) >>
     simp[DROP_APPEND2, LENGTH_mem_bytes_at_proof]) >>
  mp_tac (Q.SPECL [`b+28`, `4`, `LENGTH (bytes:word8 list)`, `s.vs_memory`]
    mem_bytes_at_split_padded) >>
  simp[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED
Finalise custom_error_emit_revert_exact
