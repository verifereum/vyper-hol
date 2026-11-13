Theory bodyFullAttributeAdd
Ancestors
  bodyPtrAttributeAdd bodyFullGhostFrame bodyPtrDefs typedCopyPtr
  ptrSafetyTransport unitTransformDefs decoderGhostFramePtr fragExec
  contextCodegenRel codegenRel memSafeRun
  fragGasSeqPtr fragGasOriginPtr emitHelperProps loweringStateRelDefs
  compileEnv emitHelper context venomInst venomState venomExecSemantics
  ptrSafeRun ptrDiscipline finite_map list arithmetic words

(* Fresh arithmetic keeps every reserved pointer, including the constructor's
   immutable-region base.  The endpoint is fixed before choosing D. *)
Theorem attribute_fresh_full_ghost_update:
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!p. p <> STRING #"%" (toString sm.cs_next_var) ==>
     FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) ==>
  (!D lo d cx ee.
    ghost_inv_at D lo d cenv cx ee G tn s ==>
    ghost_inv_at D lo d cenv cx ee G' tn'
      (update_var (STRING #"%" (toString sm.cs_next_var)) w s with vs_inst_idx := n)) /\
  (!lo es G0 tn0 s0.
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
Proof
  strip_tac >>
  `!p. not_fresh_at sa p ==> p <> STRING #"%" (toString sm.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
      goal_assum (drule_at Any) >>
      qexists_tac `sa` >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[ghost_kept_at_def] >> metis_tac[]
QED

(* The pure ADD has one explicit endpoint, independent of the dead mask. *)
Theorem attribute_add_full_frame:
  emit_op ADD [left; Lit off] sm = (dst,sn) /\ fn_has_code sm sn func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand left s = SOME w /\ op_taint tn left = {} /\
  out = STRING #"%" (toString sm.cs_next_var) /\
  i = mk_inst sm.cs_next_id ADD [left; Lit off] [out] /\
  u = update_var out (w + off) s /\
  t = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  G' = step_prov PG G i u /\ tn' = step_taint i s u tn ==>
  dst = Var out /\
  (!D lo explicit. allocas_from lo s ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
  FLOOKUP G' out = op_prov G left /\
  op_taint tn' dst = {} /\ tn'.t_mem = tn.t_mem /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  reverse conj_tac
  >- (simp[attribute_add_provenance, copy_len_binop_ghost_frame] >>
      irule (cj 3 step_taint_nonmemory_frame) >> simp[mk_inst_def]) >>
  rpt strip_tac >>
  `sn.cs_current_bb = sm.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sm.cs_current_insts) =
    SOME (mk_inst sm.cs_next_id ADD [left; Lit off]
      [STRING #"%" (toString sm.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `step_prov PG G i u` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tn i s /\
   inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    (unabbrev_all_tac >> reverse conj_tac
     >- simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
             source_memory_write_ranges_def, inst_dload_in_section_def, mk_inst_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >> simp[] >>
     irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G i u, step_taint i s u tn)` by
    (mp_tac (straight_line_origin_ptr_edge |> Q.INST [`i` |-> `i`, `u` |-> `u`]) >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[Abbr `u`, update_var_def] >>
  drule (cj 1 gas_origin_ptr_path_rules) >> strip_tac >>
  metis_tac[cj 2 gas_origin_ptr_path_rules, APPEND]
QED
