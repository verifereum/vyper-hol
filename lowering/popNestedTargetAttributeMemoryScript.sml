(* Counted ADD continuation for nested target fields. *)
Theory popNestedTargetAttributeMemory
Ancestors
  targetPlaceSimMem targetPlaceSimCasesBase bodyMemEmitOpFrame
  exprLoweringProps emitHelperProps stmtSimProps compileEnv loweringPosts
  loweringStateRelDefs exprSimDefs exprSimHypsDefs fragExec
  venomExecProofs venomState venomInst exprSimBuffer

Theorem pop_nested_target_attr_add_mem:
  target_post ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
  eval_operand (FST rb) t = SOME w0 /\
  place_ptr_rel cenv cx t pv' (w0 + n2w off) (FST (SND rb)) vt' /\
  place_readable cx es1 pv' ==>
  ?q. gas_marked_path T ctx func t 0 (OK q) /\
      target_post ctx func cenv cx es sa sb s0 es1 pv' vt'
        (dst, FST (SND rb), SOME (value_type_place vt')) q /\
      q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func q /\ q.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  drule_all target_post_add >> strip_tac >>
  drule_all buffer_emit_add_run >> strip_tac >> gvs[] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es1 t` by fs[target_post_def] >>
  `step_inst_base
     (mk_inst sm.cs_next_id ADD [FST rb; Lit (n2w off)]
       [STRING #"%" (toString sm.cs_next_var)]) t =
     OK (update_var (STRING #"%" (toString sm.cs_next_var)) (w0 + n2w off) t)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  drule_at (Pat `emit_op _ _ _ = _`) emit_op_word_path_frame_mem >>
  disch_then (qspec_then `w0 + n2w off` mp_tac) >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
    (w0 + n2w off) t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[]
QED
