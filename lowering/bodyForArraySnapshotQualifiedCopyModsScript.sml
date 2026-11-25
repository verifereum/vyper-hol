(* Copy a reached element from the current qualified immutable byte window. *)
Theory bodyForArraySnapshotQualifiedCopyMods
Ancestors
  bodyForArraySnapshotCodeRunMods bodyForArraySnapshotReadbackMods
  bodyForArraySnapshotChildMods bodyForArrayHeaderMods bodyFullShadowBodyInv
  whitelistForIterImmCopy stateRelProj exprLoweringProps exprSimCopy exprSimProps
  loweringStateRelDefs valueEncodingProps vyperTypeValues stmtLowering context
  abiDecodeStaticProps ptrDiscipline bodyFullHashKeccakFixed bodyPtrDefs
  venomExecSemantics venomState compileEnv finite_map pred_set words arithmetic
Libs
  monadsyntax

Theorem for_array_snapshot_qualified_copy_mods:
  evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV tv bd) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
  k < LENGTH vs /\ value_has_type (ArrayTV tv bd) (ArrayV av) /\
  stride = type_memory_size tv /\
  compile_iter_elem_copy c (Var out) (Var xd) stride LocCode F dty sty sa = ((),sb) /\
  w2n bw + type_memory_size (ArrayTV tv bd) < dimword (:256) /\
  (c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= lo /\
    !m. mem_agree_outside tn.t_mem u.vs_memory m ==>
      val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) m) /\
  (~c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= LENGTH u.vs_data_section /\
    val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) u.vs_data_section) /\
  lookup_var out u = SOME (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + k * stride)) /\
  not_fresh_at sa out /\ op_taint tn (Var out) = {} /\ op_prov G (Var out) = NONE /\
  for_array_item_mods c saOuter saExpr (xd,dw,capacity,aid) ee G tn u /\
  not_fresh_at sa xd /\ stride <= capacity /\
  stmt_state_rel H ctx func c cx ee u /\
  ghost_inv_at_mods Dh lo d c cx ee G tn u /\
  local_ptrs_reserved c sa /\
  fn_has_code sa sb func /\ ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v raw z Gf tf q.
    0 < q /\ stride = 32*q /\ 32*q <= capacity /\ EL k vs = Value v /\
    value_has_type tv v /\ val_wf tv v /\
    copy_runtime_frame sa u sb raw /\
    z = raw with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,G,tn) [] (OK z,Gf,tf)) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
    typed_copy_state_frame sa (w2n dw) (32*q) u z /\
    mem_bytes_at (w2n dw) (32*q) z.vs_memory =
      mem_bytes_at (w2n (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + k * stride))) (32*q)
        (if c.ce_is_ctor then u.vs_memory else u.vs_data_section) /\
    (!i. i IN tf.t_mem <=>
      if w2n dw <= i /\ i < w2n dw + 32*q
      then c.ce_is_ctor /\ w2n (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + k * stride)) +
        (i - w2n dw) IN tn.t_mem
      else i IN tn.t_mem) /\
    tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + 32*q) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    FLOOKUP z.vs_allocas aid = SOME (w2n dw,capacity) /\
    lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z capacity /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    val_in_memory tv v (w2n dw) z.vs_memory /\
    (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
      val_in_memory tv v (w2n dw) m)
Proof
  strip_tac >>
  drule_then assume_tac evaluate_type_well_formed_type_value >>
  drule_all_then (strip_assume_tac o SIMP_RULE std_ss [LET_THM])
    for_array_snapshot_child_mods >>
  drule_then assume_tac immutable_array_element_size_positive >>
  qabbrev_tac `v = EL k (array_elements (ArrayTV tv bd) av)` >>
  qabbrev_tac `delta = (case bd of Fixed _ => 0 | Dynamic _ => 32) + k * stride` >>
  qabbrev_tac `sw = bw + n2w delta` >>
  `delta + stride <= type_memory_size (ArrayTV tv bd)` by
    (qpat_assum `_ + type_memory_size tv <= type_memory_size (ArrayTV tv bd)` mp_tac >>
     simp[Abbr `delta`]) >>
  `w2n sw = w2n bw + delta` by
    (simp[Abbr `sw`, SimpLHS] >> irule w2n_add_n2w_lt >> decide_tac) >>
  `copy_old_operand sa (Var out) /\ eval_operand (Var out) u = SOME sw` by
    simp[copy_old_operand_def,eval_operand_def] >>
  qhdtm_assum `for_array_item_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_item_mods_def]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `lo <= w2n dw` by
    (qhdtm_assum `allocas_from` (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp >>
  qabbrev_tac `q = type_slot_size tv` >>
  `stride = 32*q` by simp[Abbr `q`,type_memory_size_slots] >>
  `0 < q` by (qpat_assum `0 < type_memory_size tv` mp_tac >>
    simp[GSYM (cj 1 type_memory_size_slots), Abbr `q`,type_memory_size_slots]) >>
  `32*q <= capacity /\ w2n dw + 32*q <= u.vs_alloca_next` by decide_tac >>
  `c.ce_is_ctor ==> w2n sw + 32*q <= lo /\ lo <> 0` by
    (strip_tac >> fs[] >> decide_tac) >>
  `(c.ce_is_ctor ==> op_prov G (Var out) = NONE /\ w2n sw + 32*q <= lo /\
    lo <= w2n dw /\ w2n sw + 32*q <= u.vs_alloca_next /\
    !region. c.ce_imm_alloca = SOME region ==> eval_operand region u = SOME 0w /\
      copy_old_operand sa region /\ op_taint tn region = {} /\ op_prov G region = NONE)` by
    suspend "loader" >>
  `~c.ce_is_ctor ==> w2n sw + 32*q <= LENGTH u.vs_data_section /\
    w2n sw + 32*q < dimword (:256)` by
    (strip_tac >> fs[] >> decide_tac) >>
  `compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca (Var out) (Var xd) q 0 sa = ((),sb)` by
    suspend "shape" >>
  suspend "run"
QED

Resume for_array_snapshot_qualified_copy_mods[loader]:
  strip_tac >> fs[] >>
  drule_then assume_tac stmt_state_rel_immutable_base_zero >>
  Cases >> fs[copy_old_operand_def,op_taint_def,op_prov_def,immutable_base_zero_def,
    ghost_inv_at_mods_def] >> metis_tac[local_ptrs_reserved_imm_base]
QED

Resume for_array_snapshot_qualified_copy_mods[shape]:
  Cases_on `q = SUC 0`
  >- (`stride = 32` by decide_tac >>
      qpat_x_assum `stride = 32` SUBST_ALL_TAC >>
      qpat_x_assum `q = SUC 0` SUBST_ALL_TAC >>
      qpat_x_assum `compile_iter_elem_copy _ _ _ _ LocCode F _ _ _ = _` mp_tac >>
      simp[immutable_iter_small_copy,compile_imm_copy_to_memory_def,
           compile_lit_byte_offset_def,comp_bind_def,comp_return_def,comp_ignore_bind_def,NoAsms] >>
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  `32 < stride` by decide_tac >>
  `(stride + 31) DIV 32 = q` by simp[ADD_DIV_ADD_DIV] >>
  drule immutable_iter_large_copy >>
  disch_then (fn eq =>
    qpat_x_assum `compile_iter_elem_copy _ _ _ _ LocCode F _ _ _ = _`
      (mp_tac o PURE_REWRITE_RULE [eq])) >>
  qpat_assum `(stride + 31) DIV 32 = q` (pure_rewrite_tac o single) >>
  disch_then ACCEPT_TAC
QED

Resume for_array_snapshot_qualified_copy_mods[run]:
  let
    val run_at_copy = Q.INST [`ctor` |-> `c.ce_is_ctor`, `imm` |-> `c.ce_imm_alloca`,
      `src` |-> `Var out`, `Gu` |-> `G`, `tu` |-> `tn`, `cap` |-> `capacity`]
      (SPEC_ALL for_array_snapshot_code_run_mods)
  in
    mp_tac run_at_copy
  end >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`raw`,`z`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  `!m. mem_agree_outside tf.t_mem z.vs_memory m ==> val_in_memory tv v (w2n dw) m` by
    suspend "readback" >>
  qexistsl_tac [`v`,`raw`,`z`,`Gf`,`tf`,`q`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `z.vs_memory` mp_tac) >> simp[mem_agree_outside_def]
QED

Resume for_array_snapshot_qualified_copy_mods[readback]:
  `val_footprint tv v <= 32*q` by
    (drule_then mp_tac val_footprint_le >> simp[]) >>
  gen_tac >> strip_tac >>
  irule for_array_snapshot_readback_mods >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`32*q`,`c.ce_is_ctor`,`tn.t_mem`,`tf.t_mem`,`z.vs_memory`,
                `u.vs_data_section`,`u.vs_memory`,`w2n sw`] >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!i. i IN tf.t_mem <=> _` (qspec_then `i` mp_tac) >>
      simp[]) >>
  `!mb. val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mb ==>
     val_in_memory tv v (w2n sw) mb` by
    (qpat_assum `w2n sw = _` (pure_rewrite_tac o single) >>
     qpat_assum `Abbrev (delta = _)`
       (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `stride = type_memory_size tv` (pure_rewrite_tac o single) >>
     qpat_assum `!base m. val_in_memory (ArrayTV _ _) _ base m ==> _`
       (qspec_then `w2n (bw:bytes32)` ACCEPT_TAC)) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> first_x_assum irule >> fs[])
  >- (strip_tac >> first_x_assum irule >> fs[]) >>
  first_assum ACCEPT_TAC
QED

Finalise for_array_snapshot_qualified_copy_mods
