(* The post-index array slice finishes at the element pointer or stops at
   the failing bounds check. Both use the supplier's chosen ghost pair. *)
Theory entryCreateTargetArray
Ancestors
  bodyFullTargetArraySuffix entryCreateAdminSequence entryCreatePathScope
  entryCreateCompletedCut entryCreateFocusSpec fragGasOriginPtr fragGasOrigin
  fragExec instIdxIndep venomExecSemantics venomInst exprLoweringProps
  createSizePrefixReplay createMarkedPath venomInstProps abiEncoderProps gasSummary
  list relation arithmetic

Theorem array_admin_edge_result[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  gas_origin_edge T E C f s marks r ==>
  r = (case step_inst_base i s of
         OK u => OK (u with vs_inst_idx := SUC s.vs_inst_idx)
       | x => x)
Proof
  simp[gas_origin_edge_def] >> strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `step_inst_base i s` >> gvs[exit_result_def]
QED

Theorem array_admin_abort_run[local]:
  !is s z bb.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH is /\
    (!j. j < LENGTH is ==>
         get_instruction bb (s.vs_inst_idx + j) = SOME (EL j is)) /\
    EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) is /\
    run_inst_seq is s = Abort Revert_abort z /\
    gas_origin_path T E C f s [] (Abort Revert_abort t) ==>
    create_operand_full_scope sa sb E C f s [] (Abort Revert_abort t)
Proof
  Induct_on `is` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (qpat_assum `!j. _ ==> get_instruction bb _ = _`
       (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  `s.vs_inst_idx <> LENGTH sb.cs_current_insts` by simp[] >>
  `h.inst_id IN frag_ids sa sb /\ h.inst_opcode <> INVOKE /\
   ~is_terminator h.inst_opcode` by fs[] >>
  qpat_x_assum `gas_origin_path _ _ _ _ _ _ _` mp_tac >>
  simp[Once gas_origin_path_cases, exit_result_def, APPEND_eq_NIL] >> strip_tac
  >- (`OK mid = (case step_inst_base h s of
          OK u => OK (u with vs_inst_idx := SUC s.vs_inst_idx) | x => x)` by
        (irule array_admin_edge_result >> metis_tac[]) >>
      Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
      rename1 `step_inst_base h s = OK u` >>
      `step_inst 0 C h s = OK u` by simp[step_inst_non_invoke] >>
      `u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
      qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
      `run_inst_seq is v = Abort Revert_abort (z with vs_inst_idx := SUC s.vs_inst_idx)` by
        simp[Abbr `v`, run_inst_seq_inst_idx, exec_result_map_def] >>
      `create_operand_full_scope sa sb E C f v [] (Abort Revert_abort t)` by
        (first_x_assum (qspecl_then
           [`v`,`z with vs_inst_idx := SUC s.vs_inst_idx`,`bb`] mp_tac) >>
         simp[Abbr `v`, ADD_CLAUSES] >>
         (impl_tac >- (rpt strip_tac >>
           qpat_assum `!j. _ ==> get_instruction bb _ = _`
             (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [ADD_CLAUSES])) >>
           simp[ADD_CLAUSES])) >> simp[]) >>
      `gas_origin_edge F E C f s [] (OK v)` by
        (simp[Abbr `v`] >> qpat_assum `gas_origin_edge T _ _ _ _ _ _` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[gas_origin_edge_def] >> metis_tac[]) >>
      `create_expr_prefix sa sb E C f s [] v` by
        (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
         simp[create_marked_edge_def, create_prefix_step_def] >> metis_tac[]) >>
      fs[create_operand_full_scope_def, APPEND_eq_NIL] >>
      metis_tac[SIMP_RULE (srw_ss()) []
        (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_expr_prefix_append)]) >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`left` |-> `[]`, `last` |-> `[]`] create_operand_full_scope_terminal)) >>
  simp[exit_result_def] >> qexists_tac `s` >> simp[]
QED

Theorem array_admin_abort_scope[local]:
  fn_has_code sa sb f /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  create_operand_at sa s /\ run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort z /\
  gas_origin_path T E C f s [] (Abort Revert_abort t) ==>
  create_operand_full_scope sa sb E C f s [] (Abort Revert_abort t)
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  fs[create_operand_at_def] >>
  qspecl_then [`emitted_insts sa sb`,`s`,`z`,`bb`] irule array_admin_abort_run >> simp[]
QED

Theorem target_array_suffix_scoped_cut:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 ==>
  scoped_operand_outcome
    (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
    (cx_tops cx) cx st0 sn sb (extend_place cx pv (ValueSubscript v))
    (mid2, t2, G2, tn2)
    (array_suffix_post DF lo d ctx func cenv cx es sa sb s0 vt r G0 tn0)
    (\H res ee gt q. expr_exit res q) /\
  create_operand_cut sn sb (gas_explicit_sites ctx shadow_ctx) ctx func
    (cx_tops cx) cx st0 (extend_place cx pv (ValueSubscript v)) (mid2,t2)
Proof
  strip_tac >> drule target_array_suffix_tape >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  `create_operand_at sn t2` by simp[create_operand_at_def] >>
  reverse conj_tac
  >- (irule create_admin_sequence_cut >> fs[array_admin_slice_def, same_blocks_def, EVERY_MEM]) >>
  `EVERY (\i. i.inst_id IN frag_ids sn sb /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts sn sb)` by
    fs[array_admin_slice_def, frag_ids_def, EVERY_MEM] >>
  `create_operand_full_scope sn sb (gas_explicit_sites ctx shadow_ctx) ctx func t2 [] tr` by
    (Cases_on `tr` >> gvs[]
     >- (rename1 `create_operand_full_scope _ _ _ _ _ _ [] (OK u)` >>
         `u = ((u with vs_inst_idx := LENGTH sn.cs_current_insts)
                with vs_inst_idx := LENGTH sb.cs_current_insts)` by
           simp[venomStateTheory.venom_state_component_equality] >>
         pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
         irule create_admin_sequence_scope >> fs[array_admin_slice_def, same_blocks_def]) >>
     Cases_on `a` >> gvs[] >>
     `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     first_x_assum drule >> strip_tac >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
     irule array_admin_abort_scope >>
     first_assum (irule_at Any) >> fs[array_admin_slice_def, same_blocks_def, EVERY_MEM]) >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl [`res`,`mid2`,`tr`,`G3`,`tn3`] >> simp[gas_explicit_def]
QED
