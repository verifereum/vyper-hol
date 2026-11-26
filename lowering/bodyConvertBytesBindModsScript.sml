(* Compose the forced operand with the suffix at its actual landing. *)
Theory bodyConvertBytesBindMods
Ancestors
  bodyConvertDynamicEntryMods bodyForcedStorageFrameMods bodyFullPostsMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods haltExitProj
  exprSimDefs stmtSimProps vyperState vyperStorageTrace vyperStorageFootprint fragExec words
Libs monadsyntax

local
  val expr = ``TypeBuiltin dst Convert dst [e]``
  val vv = ``LocatedValue dst (mk_ptr out LocMemory)``
in
  val bytes_convert_child_post =
    ``\H (res : value + vyperState$exception) ee G tn t. ?v pt rt w. res = INL v /\
        expr_post_mods H ctx func ce cx e es sa sm s0 ee v op t /\
        storage_well_formed_on cx ee (FST H) /\
        expr_store_bound cx (post_value_type ce e) v op t /\
        t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list))
          lo d ce cx ee G tn t /\
        ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
        ptr_val_ok cx (post_value_type ce e) v op G tn t /\ ptr_buf_ok ce e op G t /\
        ~is_word_type (post_value_type ce e) /\
        evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
        evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
        type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
        value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
        eval_operand op t = SOME w /\ op_taint tn op = {} /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem) /\
        (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next) /\
        w2n w + type_memory_size rt < dimword (:256) /\
        (0 < type_memory_size rt ==>
          ?x. op = Var x /\ not_fresh_at sm x /\ ptr_covers G tn x t (type_memory_size rt))``
  val bytes_convert_post =
    ``\H (res : eval_result + vyperState$exception) ee G tn t. ?tv. res = INL tv /\
        vv_post_mods H ctx func ce cx ^expr es sa sb s0 ee tv ^vv t /\
        vv_store_bound cx (post_value_type ce ^expr) (lowered_value_type ce ^expr)
          ee tv ^vv t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list))
          lo d ce cx ee G tn t /\
        ptr_vv_ok cx (post_value_type ce ^expr) tv ^vv ee G tn t /\
        (!v. tv = Value v /\ ~is_word_type (post_value_type ce ^expr) /\
             ~is_bytestring_type (post_value_type ce ^expr) ==>
             vv_own ce cx (post_value_type ce ^expr) sa sb ee tv ^vv t /\
             (!t' p. ^vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
        (ce.ce_is_ctor /\ vv_location ^vv = SOME LocCode ==>
         ?val. read_result cx tv ee = (INL val, ee) /\
               !rt w. evaluate_type (get_tenv cx) (post_value_type ce ^expr) = SOME rt /\
                      eval_operand (vv_operand ^vv) t = SOME w ==>
                      w2n w + type_memory_size rt <= lo /\
                      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
        (!t' op. ^vv = StackValue t' op /\ ~is_word_type (post_value_type ce ^expr) ==>
                 ptr_buf_ok ce ^expr op G t) /\
        (!t' p. ^vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                ptr_buf_ok ce ^expr p.ptr_operand G t) /\
        ghost_kept_at lo ce es sa G0 tn0 s0 G tn``
  val bytes_convert_exit =
    ``\(H : (bool # 256 word # type_value) list # num list)
        (res : 'a + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
        expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``
  val bytes_convert_child_exit = inst [alpha |-> ``:value``] bytes_convert_exit
  val bytes_convert_parent_exit = inst [alpha |-> ``:eval_result``] bytes_convert_exit
end

Theorem bytes_convert_bind_mods:
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    ^bytes_convert_child_post ^bytes_convert_child_exit /\
  (!marks v mid G tn t.
    bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid) /\
    ~t.vs_halted /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      (^bytes_convert_child_post) H (INL v) mid G tn t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
      (\ee. (sum_CASE (convert_result cx (expr_type e) dst v) (\w. INL (Value w)) INR,ee))
      (mid,t,G,tn) ^bytes_convert_post ^bytes_convert_parent_exit) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (eval_expr cx (TypeBuiltin dst Convert dst [e])) (es,s0,G0,tn0)
    ^bytes_convert_post ^bytes_convert_parent_exit
Proof
  strip_tac >> PURE_REWRITE_TAC[dynamic_convert_source_action] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      rename1 `gas_marked_exec _ _ _ _ _ (INL v) mid (OK t)` >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- irule bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`storage_trace_frame (\ee. (_,ee))`]
  >- simp[storage_trace_frame_def] >>
  qexists_tac `\H res ee G tn t. (^bytes_convert_child_post) H res ee G tn t /\
    ~t.vs_halted /\ ee.gas_obs = []` >> BETA_TAC >> conj_tac
  >- suspend "reached" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                   INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]
QED

Resume bytes_convert_bind_mods[reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G`,`tn`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  disj1_tac >> qexists_tac `v` >> (conj_tac >- REFL_TAC) >>
  qpat_assum `!marks v mid G tn t. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    irule >> BETA_TAC >> simp[] >>
  (reverse conj_tac >- (qexists_tac `marks` >> first_assum ACCEPT_TAC)) >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`valid_horizon cx st0 H
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace`
       suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``] valid_horizon_frame) >>
     qexistsl_tac [`bind (eval_expr cx e) (read_result cx)`,`INL v`,`mid`] >>
     simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then ACCEPT_TAC)
QED

Finalise bytes_convert_bind_mods
