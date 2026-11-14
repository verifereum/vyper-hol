(* The field write is one joint step.  Its endpoint and ghosts are explicit,
   so the same witness is available at every valid storage horizon. *)
Theory bodyFullAssignAttrStorageStore
Ancestors
  bodyFullAssignAttrStorageGhost bodyFullUnwrapRun ptrSafetyTransport
  assignTuplePtrStorage fragGasOriginPtr fragExecMem emitHelperProps
  exprOpenPrimitives exprLoweringProps ptrDiscipline fragGasSeqPtr
  emitHelper venomExecSemantics venomInst venomState ptrSafeRun
  memSafeRun unitTransformDefs codegenRel contextCodegenRel allocaHistory
  bodyPtrDefs compileEnv finite_map list pred_set

Theorem storage_field_store_origin_ptr:
  emit_void (if tr then TSTORE else SSTORE) [dst;value] sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (root + n2w off) /\
  eval_operand value s = SOME w /\
  op_taint tn dst = {} /\ op_taint tn value = {} /\
  ghost_inv_at D lo d cenv cx es G tn s /\ dead_lo_ok H D lo cenv cx /\
  es'.scopes = es.scopes /\ MEM (tr,root,StructTV fs) (FST H) /\
  struct_field_slot fs fld = SOME (off,ftv) /\ type_slot_size ftv = 1 ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK ((if tr then tstore (root + n2w off) w s
           else sstore (root + n2w off) w s)
         with vs_inst_idx := LENGTH sb.cs_current_insts), G,
     step_taint (mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE)
       [dst;value] []) s
       (if tr then tstore (root + n2w off) w s
        else sstore (root + n2w off) w s) tn) /\
  ghost_inv_at D lo d cenv cx es' G
    (step_taint (mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE)
       [dst;value] []) s
       (if tr then tstore (root + n2w off) w s
        else sstore (root + n2w off) w s) tn)
    ((if tr then tstore (root + n2w off) w s
      else sstore (root + n2w off) w s)
     with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  alloca_history func
    ((if tr then tstore (root + n2w off) w s
      else sstore (root + n2w off) w s)
     with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~block_is_terminated sb
Proof
  strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id
    (if tr then TSTORE else SSTORE) [dst;value] []` >>
  qabbrev_tac `u = if tr then tstore (root + n2w off) w s
                  else sstore (root + n2w off) w s` >>
  qabbrev_tac `tn' = step_taint inst s u tn` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [inst]` by
    (gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, emit_def, Abbr `inst`]) >>
  `~block_is_terminated sb` by
    (drule emit_void_terminated >> Cases_on `tr` >> simp[is_terminator_def]) >>
  `step_inst_base inst s = OK u` by
    (Cases_on `tr` >> simp[Abbr `inst`, Abbr `u`, step_inst_base_def,
                          mk_inst_def, exec_write2_def]) >>
  `run_inst_seq [inst] s = OK u` by simp[run_inst_seq_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >>
     simp[Abbr `inst`] >> irule clean_storage_ptr_inst_ok >> simp[]) >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    (Cases_on `tr` >>
     simp[Abbr `inst`, inst_mem_below_frontier_def, inst_dload_in_section_def,
          mk_inst_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `step_prov PG G inst u = G` by
    simp[Abbr `inst`, step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV] >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s G tn'` by
    simp[inst_seq_ptr_def, Abbr `tn'`] >>
  `run_inst_seq_mem_ok [inst] s` by simp[run_inst_seq_mem_ok_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) [inst]` by
    (Cases_on `tr` >> simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G,tn')` by
    (irule emitted_origin_ptr_path >> simp[] >>
     qexistsl_tac [`[inst]`, `sa`] >> simp[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule emitted_alloca_history >> simp[] >>
     qexistsl_tac [`[inst]`, `s`, `sa`] >> simp[] >>
     Cases_on `tr` >> simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  `ghost_inv_at D lo d cenv cx es' G tn' u` by
    (simp[Abbr `tn'`, Abbr `inst`, Abbr `u`] >>
     irule storage_field_store_ghost_at >> simp[] >> metis_tac[]) >>
  `ghost_inv_at D lo d cenv cx es' G tn'
      (u with vs_inst_idx := LENGTH sb.cs_current_insts) =
   ghost_inv_at D lo d cenv cx es' G tn' u` by
    (Cases_on `d` >>
     simp_tac (srw_ss()) [ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def,
          lookup_var_def, stor_taint_ok_at_def, allocas_from_def] >>
     qmatch_goalsub_rename_tac `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
     simp_tac (srw_ss()) [return_buf_ptr_def, ptr_covers_def, lookup_var_def]) >>
  simp[GSYM (Abbr `inst`), GSYM (Abbr `u`), GSYM (Abbr `tn'`)]
QED
