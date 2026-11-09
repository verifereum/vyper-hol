Theory exprExtRequestOptionalGas
Ancestors
  exprExtRequestHistory exprExtRequestSourceProbe exprExtRequestReadProbe exprSafeOperand
  exprSimHash exprSimWordArgs exprLoweringProps emitHelperProps emitHelper
  venomState venomInst venomInstProofs venomExecSemantics compileEnv
  loweringPosts fragExec list rich_list arithmetic finite_map

Theorem extrequest_optional_gas_run:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
  (!g. go = SOME g ==> ?w. eval_operand g s = SOME w) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  ?t gw. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand gas t = SOME gw /\ stmt_state_rel ctx func cenv cx es t /\
    wb_frame cenv es sa s t /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  Cases_on `go`
  >- (simp[] >> strip_tac >>
      drule emitted_insts_emit_op >> strip_tac >>
      qabbrev_tac `u = s with vs_gas_readings := DROP 1 s.vs_gas_readings` >>
      qabbrev_tac `t = update_var (STRING #"%" (toString sa.cs_next_var))
        (HD (s.vs_gas_readings ++ [0w])) u` >>
      `run_inst_seq (emitted_insts sa sb) s = OK t` by
        simp[Abbr `t`, Abbr `u`, run_inst_seq_def, step_inst_def, step_GAS] >>
      `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
        (simp[Abbr `t`, Abbr `u`, lookup_var_update_var, lookup_var_def] >>
         rpt strip_tac >> gvs[not_fresh_at_def]) >>
      `(t with vs_vars := u.vs_vars) = u` by simp[Abbr `t`, update_var_def] >>
      `stmt_state_rel ctx func cenv cx es t` by
        (irule hash_readonly_state_rel >> qexists `u` >>
         simp[Abbr `u`, hash_gas_readings_state_rel] >>
         qexists `sa` >> simp[lookup_var_def]) >>
      qexists `t` >> simp[Abbr `t`, Abbr `u`, update_var_def, eval_operand_def,
        lookup_var_def, FLOOKUP_UPDATE, wb_frame_def, locals_kept_def] >>
      rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  qexists `s` >> simp[emitted_insts_def, run_inst_seq_def, wb_frame_refl]
QED

Theorem extrequest_optional_gas_path:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path F ctx func s (if IS_NONE go then 1 else 0)
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) =
     (if IS_NONE go then 1 else 0)` by
    (qpat_x_assum `(case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb)` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `go` >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]) >>
  drule_all hash_run_path >> simp[]
QED

Theorem extrequest_optional_gas_endpoint:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
  (!g. go = SOME g ==> safe_operand sa g /\ IS_SOME (eval_operand g s)) /\
  fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t gw. gas_marked_path F ctx func s (if IS_NONE go then 1 else 0) (OK t) /\
    eval_operand gas t = SOME gw /\ safe_operand sb gas /\
    stmt_state_rel ctx func cenv cx es t /\
    extrequest_history_frame cenv cx es sa s es sb t /\
    wb_frame cenv es sa s t /\ ci_mono sa sb /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    (!op w. safe_operand sa op /\ eval_operand op s = SOME w ==>
            eval_operand op t = SOME w)
Proof
  strip_tac >>
  `!g. go = SOME g ==> ?w. eval_operand g s = SOME w` by
    (rpt strip_tac >> first_x_assum drule >> Cases_on `eval_operand g s` >> simp[]) >>
  drule_all extrequest_optional_gas_run >> strip_tac >>
  drule_all extrequest_optional_gas_path >> strip_tac >>
  `ci_mono sa sb /\ safe_operand sb gas` by
    (Cases_on `go` >> gvs[]
     >- (conj_tac
         >- (mp_tac (Q.SPECL [`GAS`, `[]`, `sa`] ci_mono_emit_op) >> simp[]) >>
         metis_tac[emit_op_safe_operand]) >>
     simp[ci_mono_def, cs_extends_def]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> gvs[ci_mono_def]) >>
  qexistsl [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `gw`] >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (simp[extrequest_history_frame_def, extrequest_read_frame_def] >>
      gvs[ci_mono_def, lookup_var_def]) >>
  conj_tac
  >- gvs[wb_frame_def, locals_kept_def, lookup_var_def] >>
  rpt strip_tac >> Cases_on `op` >>
  gvs[safe_operand_def, eval_operand_def, lookup_var_def] >> metis_tac[]
QED
