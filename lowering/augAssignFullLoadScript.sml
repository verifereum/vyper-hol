(* Storage loads choose their concrete and ghost endpoint before the horizon. *)
Theory augAssignFullLoad
Ancestors
  typedCopyOriginPtrBase augAssignPtrStorageAddress ptrSafetyTransport
  fragGasOriginPtr ptrDiscipline ptrSafeRun codegenRel contextCodegenRel
  unitTransformDefs instMemFrontier memSafeRun
  bodyPtrDefs sourceUnitExecution accountsRelProps
  emitHelper emitHelperProps compileEnv loweringStateRelDefs
  venomExecSemantics venomInst venomState finite_map list pred_set

Theorem live_storage_head_clean_at:
  dead_lo_ok H D lo cenv cx /\ stor_taint_ok_at D tn s /\
  (!st. storage_read_live H tr st slot tv) /\ 0 < type_slot_size tv ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >>
  `!st b. ~storage_dead H tr st (w2n slot) b` by
    metis_tac[storage_read_live_head] >>
  Cases_on `tr` >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[dead_lo_ok_def, stor_taint_ok_at_def, cx_dead_def, key_taint_def,
      SUBSET_DEF, EXTENSION] >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Theorem storage_address_load_origin_ptr:
  emit_op (if tr then TLOAD else SLOAD) [addr] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr s = SOME slot /\ op_prov G addr = NONE /\
  op_taint tn addr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?t G' tn'.
    t = update_var out (if tr then tload slot s else sload slot s)
          (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (!D lo. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD)
    [addr] [out]` >>
  qabbrev_tac `u = update_var out (if tr then tload slot s else sload slot s) s` >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `step_prov PG G inst u`, `step_taint inst s u tn`] >>
  conj_tac >- simp[Abbr `u`, update_var_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `!z. ptr_inst_ok D lo 0 ctx func G tn
         (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [addr] [z]) s` by
        (gen_tac >> irule ptr_inst_ok_lower_bound_transport >> simp[] >>
         qexists_tac `0` >> simp[] >>
         irule ptr_inst_ok_storage_address_load_ptr >> simp[]) >>
      mp_tac (Q.INST
        [`opc` |-> `if tr then TLOAD else SLOAD`, `args` |-> `[addr]`,
         `a` |-> `sa`, `op` |-> `Var out`, `b` |-> `sb`, `func` |-> `func`,
         `s` |-> `s`, `w` |-> `if tr then tload slot s else sload slot s`,
         `D` |-> `D`, `lo` |-> `lo`, `ctx` |-> `ctx`, `G` |-> `G`,
         `tn` |-> `tn`, `PG` |-> `PG`, `explicit` |-> `explicit`,
         `off` |-> `0`, `len` |-> `0`] typed_copy_origin_ptr_emit_op_path) >>
      impl_tac
      >- (Cases_on `tr` >>
          simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
               inst_mem_below_frontier_def, inst_dload_in_section_def,
               source_memory_read_ranges_def, source_memory_write_ranges_def,
               is_terminator_def]) >>
      strip_tac >> gvs[Abbr `inst`, Abbr `u`, arithmeticTheory.ADD1]) >>
  `new_site_bytes s u = {}` by
    simp[Abbr `u`, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         EXTENSION, SF CONJ_ss] >>
  Cases_on `tr` >> fs[] >>
  simp[Abbr `inst`, step_taint_def, set_var_taint_def, adopt_reset_def,
       imm_taint_def, mk_inst_def, source_memory_write_ranges_def,
       step_writes_def, step_prov_def, set_prov_def, out_prov_def,
       out_taint_def, eval_operand_def, op_prov_def, op_taint_def,
       mem_taint_def, store_taint_def, range_bytes_def, written_taint_def,
       Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
