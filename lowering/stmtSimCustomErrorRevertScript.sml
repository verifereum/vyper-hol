(*
 * The custom-error revert gadget: the Venom code compile_revert_with_custom_error
 * emits after its argument stores (stmtLowering).  It allocates a buffer of the
 * arguments' ABI size bound plus a selector word, MSTOREs the selector, ABI-encodes
 * the argument tuple behind it (when there are arguments) and REVERTs from buf+28.
 *
 * The argument stores interleave compile_expr, so each tower (S1 stmt_frag, S3
 * stmt_frag_mem, stmt_frag_ptr) simulates them with its own expression judgement;
 * the tail after them is Venom-only and has this one execution lemma, which all
 * three towers' custom-error cases use.
 *
 * TOP-LEVEL:
 *   custom_error_revert_tail_def               the code after the argument stores
 *   compile_revert_with_custom_error_split     the lowering = alloc; stores; tail
 *   custom_error_revert_tail_run (ADMITTED)    the tail reaches REVERT, writing only
 *                                              inside its own fresh allocas
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
  !cenv id positional kwargs params s0 s1.
    cenv.ce_error_info (nsid_to_string id) = SOME params /\
    compile_revert_with_custom_error cenv (CustomError id positional kwargs) s0 =
      ((),s1) ==>
    ?args_alloc sa sm.
      compile_alloc_buffer (type_memory_bytes cenv (TupleT (MAP SND params))) s0 =
        (args_alloc,sa) /\
      compile_custom_error_store_args cenv
        (custom_error_exprs (CustomError id positional kwargs))
        (MAP SND params) args_alloc.buf_operand 0 sa = ((),sm) /\
      custom_error_revert_tail cenv id (MAP SND params) args_alloc.buf_operand
        (NULL (custom_error_exprs (CustomError id positional kwargs))) sm =
        ((),s1)
Proof
  rpt strip_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv (TupleT (MAP SND params))) s0` >>
  rename1 `_ = (args_alloc,sa)` >>
  Cases_on `compile_custom_error_store_args cenv
              (custom_error_exprs (CustomError id positional kwargs))
              (MAP SND params) args_alloc.buf_operand 0 sa` >>
  rename1 `_ = (u,sm)` >> Cases_on `u` >>
  qexistsl_tac [`args_alloc`,`sa`,`sm`] >>
  gvs[compile_revert_with_custom_error_def, custom_error_revert_tail_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def]
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
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac]) >>
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

(* ADMITTED: the gadget lemma (run from the state after the argument stores).
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
