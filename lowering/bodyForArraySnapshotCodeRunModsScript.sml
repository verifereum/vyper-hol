(* The emitted immutable element copy, before binding the loop variable. *)
Theory bodyForArraySnapshotCodeRunMods
Ancestors
  bodyFullUnwrapCodeCtorRun bodyFullUnwrapCodeRuntimeRun fragGasOriginPtrDead
  exprPtrCodeCopyPost exprSimCopy exprSimStorageCopy immutableCopyExecution
  immutableConstructorRelation typedMemoryCopy ghostPcTransportPtr
  valueEncodingDefs valueEncodingProps venomMemProps venomExecSemantics venomState words arithmetic
  finite_map pred_set ptrDiscipline

Theorem snapshot_code_ctor_memory[local]:
  compile_imm_copy_to_memory T imm src (Var xd) q 0 sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa xd /\
  eval_operand src u = SOME sw /\ lookup_var xd u = SOME dw /\
  (!region. imm = SOME region ==> eval_operand region u = SOME 0w /\
    copy_old_operand sa region) /\ copy_runtime_frame sa u sb raw /\
  0 < q /\ w2n sw + 32*q <= w2n dw /\ w2n dw + 32*q < dimword (:256) ==>
  raw.vs_memory = (write_memory_with_expansion (w2n dw)
    (mem_bytes_at (w2n sw) (32*q) u.vs_memory) u).vs_memory
Proof
  strip_tac >>
  `copy_old_operand sa (Var xd) /\ eval_operand (Var xd) u = SOME dw` by
    simp[copy_old_operand_def, eval_operand_def] >>
  drule_all copy_ctor_run >> disch_then (qx_choose_then `r` strip_assume_tac) >>
  `r = raw` by fs[copy_runtime_frame_def] >>
  `w2n sw + 32*q < dimword (:256)` by decide_tac >>
  qspecl_then [`q`,`w2n sw`,`w2n dw`,`0`,`u`] mp_tac
    (Q.INST [`store` |-> `F`, `ctor` |-> `T`] immutable_memory_transfers_snapshot) >>
  simp[mcopy_def, mem_bytes_at_def] >>
  disch_tac >> metis_tac[]
QED

Theorem snapshot_code_runtime_memory[local]:
  compile_imm_copy_to_memory F imm src (Var xd) q 0 sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa xd /\
  eval_operand src u = SOME sw /\ lookup_var xd u = SOME dw /\
  copy_runtime_frame sa u sb raw /\ 0 < q /\
  w2n sw + 32*q < dimword (:256) /\ w2n dw + 32*q < dimword (:256) ==>
  raw.vs_memory = (write_memory_with_expansion (w2n dw)
    (mem_bytes_at (w2n sw) (32*q) u.vs_data_section) u).vs_memory
Proof
  strip_tac >>
  `copy_old_operand sa (Var xd) /\ eval_operand (Var xd) u = SOME dw` by
    simp[copy_old_operand_def, eval_operand_def] >>
  drule_all_then assume_tac code_copy_same_endpoint_memory >>
  qspecl_then [`q`,`w2n sw`,`w2n dw`,`0`,`u`] mp_tac
    immutable_runtime_transfers_snapshot >>
  simp[mem_bytes_at_def]
QED

Theorem snapshot_code_position_frame[local]:
  copy_runtime_frame sa u sb raw /\
  raw.vs_memory = (write_memory_with_expansion dst bs u).vs_memory /\
  z = raw with vs_inst_idx := LENGTH sb.cs_current_insts ==>
  typed_copy_state_frame sa dst (LENGTH bs) u z /\
  mem_bytes_at dst (LENGTH bs) z.vs_memory = bs
Proof
  strip_tac >> conj_tac
  >- (fs[copy_runtime_frame_def, copy_static_def, typed_copy_state_frame_def,
         venom_state_component_equality, lookup_var_def] >>
      simp[typed_copy_frame_def, write_memory_with_expansion_nondecreasing] >>
      rpt strip_tac >> irule write_memory_mem_bytes_at_disjoint >> simp[]) >>
  simp[write_memory_mem_bytes_at_same]
QED

Theorem for_array_snapshot_code_run_mods:
  compile_imm_copy_to_memory ctor imm src (Var xd) q 0 sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa xd /\
  eval_operand src u = SOME sw /\ lookup_var xd u = SOME dw /\
  op_taint tu src = {} /\ ptr_covers Gu tu xd u cap /\
  0 < q /\ 32*q <= cap /\ w2n dw + cap < dimword (:256) /\
  FLOOKUP u.vs_allocas aid = SOME (w2n dw,cap) /\
  w2n dw + 32*q <= u.vs_alloca_next /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (ctor ==> op_prov Gu src = NONE /\ w2n sw + 32*q <= lo /\ lo <= w2n dw /\
    w2n sw + 32*q <= u.vs_alloca_next /\
    !region. imm = SOME region ==> eval_operand region u = SOME 0w /\
      copy_old_operand sa region /\ op_taint tu region = {} /\ op_prov Gu region = NONE) /\
  (~ctor ==> w2n sw + 32*q <= LENGTH u.vs_data_section /\
    w2n sw + 32*q < dimword (:256)) /\
  fn_has_code sa sb func /\ ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?raw z Gf tf.
    copy_runtime_frame sa u sb raw /\
    z = raw with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gf,tf)) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~z.vs_halted /\ typed_copy_state_frame sa (w2n dw) (32*q) u z /\
    mem_bytes_at (w2n dw) (32*q) z.vs_memory =
      mem_bytes_at (w2n sw) (32*q) (if ctor then u.vs_memory else u.vs_data_section) /\
    (!i. i IN tf.t_mem <=>
      if w2n dw <= i /\ i < w2n dw + 32*q
      then ctor /\ w2n sw + (i - w2n dw) IN tu.t_mem else i IN tu.t_mem) /\
    tf.t_imm = tu.t_imm /\ tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP Gu p /\
      op_taint tf (Var p) = op_taint tu (Var p)) /\
    FLOOKUP z.vs_allocas aid = SOME (w2n dw,cap) /\
    lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z cap /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z)
Proof
  strip_tac >>
  `w2n dw + 32*q < dimword (:256)` by decide_tac >>
  (* Run against the empty dead mask and transport that same certificate
     to each D, keeping both ghost maps fixed. *)
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
                       d_imm := K {}; d_ret := K {}|>` >>
  `?raw Gf tf.
    copy_runtime_frame sa u sb raw /\
    gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (u,Gu,tu) []
      (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf) /\
    raw.vs_current_bb = sb.cs_current_bb /\ ~raw.vs_halted /\
    raw.vs_memory = (write_memory_with_expansion (w2n dw)
      (mem_bytes_at (w2n sw) (32*q) (if ctor then u.vs_memory else u.vs_data_section)) u).vs_memory /\
    (!i. i IN tf.t_mem <=>
      if w2n dw <= i /\ i < w2n dw + 32*q
      then ctor /\ w2n sw + (i - w2n dw) IN tu.t_mem else i IN tu.t_mem) /\
    tf.t_imm = tu.t_imm /\ tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP Gu p /\
      op_taint tf (Var p) = op_taint tu (Var p)) /\
    ptr_covers Gf tf xd raw cap /\ allocas_from lo raw /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp raw)` by
    (Cases_on `ctor` >> fs[] >- suspend "constructor" >> suspend "runtime") >>
  suspend "position"
QED

Resume for_array_snapshot_code_run_mods[constructor]:
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    (Q.INST [`off` |-> `0`] (SPEC_ALL code_copy_ctor_range_origin_ptr)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then mp_tac >> simp[] >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`,`D0`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`raw`] strip_assume_tac) >>
  `w2n sw + 32*q <= w2n dw` by decide_tac >>
  `raw.vs_memory = (write_memory_with_expansion (w2n dw)
    (mem_bytes_at (w2n sw) (32*q) u.vs_memory) u).vs_memory` by
    (irule snapshot_code_ctor_memory >> simp[] >>
     qexistsl [`imm`,`sa`,`sb`,`src`,`xd`] >> simp[]) >>
  qexistsl [`raw`,`Gf`,`tnf`] >> simp[]
QED

Resume for_array_snapshot_code_run_mods[runtime]:
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    (Q.INST [`off` |-> `0`] (SPEC_ALL runtime_code_copy_range_origin)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then mp_tac >> simp[] >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`,`D0`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`raw`] strip_assume_tac) >>
  `raw.vs_memory = (write_memory_with_expansion (w2n dw)
    (mem_bytes_at (w2n sw) (32*q) u.vs_data_section) u).vs_memory` by
    (irule snapshot_code_runtime_memory >> simp[] >>
     qexistsl [`imm`,`sa`,`sb`,`src`,`xd`] >> simp[]) >>
  qexistsl [`raw`,`Gf`,`tnf`] >> simp[IN_DIFF] >> metis_tac[]
QED

Resume for_array_snapshot_code_run_mods[position]:
  qabbrev_tac `z = raw with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `z = raw with vs_inst_idx := LENGTH sb.cs_current_insts` by simp[Abbr `z`] >>
  drule_all snapshot_code_position_frame >>
  disch_then (strip_assume_tac o REWRITE_RULE [LENGTH_mem_bytes_at]) >>
  qpat_x_assum `z = raw with vs_inst_idx := _` kall_tac >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> fs[Abbr `D0`, Abbr `z`]) >>
  `z.vs_allocas = u.vs_allocas` by fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  `lookup_var xd z = SOME dw` by fs[typed_copy_state_frame_def] >>
  qexistsl [`raw`,`z`,`Gf`,`tf`] >>
  simp[Abbr `z`, allocas_from_def, allocas_below_fmp_def, lookup_var_def]
QED

Finalise for_array_snapshot_code_run_mods
