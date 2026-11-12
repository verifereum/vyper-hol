(* The joint typed memory copy of a static array. *)
Theory typedCopyOriginPtrSArray
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy
  robustCopyTransportPtr exprLowering valueEncoding valueEncodingDefs codegenRel

Theorem typed_copy_origin_ptr_sarray_fast_path:
  compile_copy_sarray_typed cenv (Var xd) dty (Var xs) sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  type_memory_size dtv = type_memory_size stv /\
  ~is_abi_dynamic cenv.ce_struct_fields dty /\
  val_wf (ArrayTV stv (Fixed N)) v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV stv (Fixed N)) v (w2n sw) mem) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (N * type_memory_size stv = 0 \/
    w2n sw + N * type_memory_size stv <= s.vs_alloca_next) /\
  (N * type_memory_size dtv = 0 \/
    w2n dw + N * type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
    w2n dw + N * type_memory_size dtv <= w2n sw) /\
  ptr_covers G tn xs s (N * type_memory_size stv) /\
  ptr_covers G tn xd s (N * type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
          d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf) /\
    val_in_memory (ArrayTV dtv (Fixed N)) v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + N * type_memory_size dtv) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory (ArrayTV dtv (Fixed N)) v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `stv = dtv` by metis_tac[typed_copy_static_widening] >>
  qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
  `compile_copy_memory (Var xd) (Var xs) (N * type_memory_size dtv) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once contextTheory.compile_store_memory_typed_def]) >>
  qabbrev_tac `n = N * type_memory_size dtv` >>
  `n < dimword (:256)` by decide_tac >>
  `val_footprint (ArrayTV dtv (Fixed N)) v <= n` by
    (Cases_on `v` >> gvs[val_wf_def, loweringPostsTheory.val_footprint_def,
                            type_memory_size_def, Abbr `n`]) >>
  Cases_on `n = 0`
  >- suspend "zero" >>
  suspend "positive"
QED

Resume typed_copy_origin_ptr_sarray_fast_path[zero]:
  fs[contextTheory.compile_copy_memory_def, compileEnvTheory.comp_return_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (ArrayTV dtv (Fixed N)) v (w2n dw) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n sw`,
                   `tn.t_mem`, `tn.t_mem`] >>
     simp[mem_bytes_at_def]) >>
  qexistsl_tac [`s`, `G`, `tn`] >> simp[typed_copy_state_frame_def] >>
  conj_tac >- (irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  fs[mem_agree_outside_def, venomStateTheory.venom_state_component_equality]
QED

Resume typed_copy_origin_ptr_sarray_fast_path[positive]:
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY
    [Var xd; Var xs; Lit (n2w n)] []` >>
  qabbrev_tac `sc = mcopy (w2n dw) (w2n sw) n s` >>
  qabbrev_tac `tf = step_taint inst s sc tn` >>
  `step_inst_base inst s = OK sc` by
    simp[Abbr `inst`, Abbr `sc`, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomInstTheory.mk_inst_def, venomStateTheory.eval_operand_def] >>
  `step_prov PG G inst sc = G /\ tf.t_var = tn.t_var /\
   tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
   tf.t_mem = (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + n}) UNION
     {w2n dw + i | i < n /\ w2n sw + i IN tn.t_mem}` by suspend "ghost" >>
  qexistsl_tac [`sc with vs_inst_idx := LENGTH sb.cs_current_insts`, `G`, `tf`] >>
  conj_tac >- suspend "path" >>
  `!mem. mem_agree_outside tf.t_mem sc.vs_memory mem ==>
     val_in_memory (ArrayTV dtv (Fixed N)) v (w2n dw) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `sc.vs_memory`, `n`, `w2n sw`,
                   `tn.t_mem`, `tf.t_mem`] >>
     simp[Abbr `sc`, valueEncodingPropsTheory.mcopy_mem_bytes_at_same]) >>
  suspend "post"
QED

Resume typed_copy_origin_ptr_sarray_fast_path[ghost]:
  simp[Abbr `tf`, Abbr `inst`, Abbr `sc`,
       step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       venomInstTheory.mk_inst_def, set_var_taint_def,
       finite_mapTheory.DRESTRICT_UNIV, store_taint_def, adopt_reset_def,
       mem_taint_def, imm_taint_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, sized_source_write_range_def,
       written_taint_def, range_bytes_def, new_site_bytes_def,
       venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.eval_operand_def, finite_mapTheory.FLOOKUP_DEF,
       pred_setTheory.EXTENSION] >> metis_tac[]
QED

Resume typed_copy_origin_ptr_sarray_fast_path[path]:
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
   sb.cs_blocks = sa.cs_blocks` by
    (qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >> Cases_on `n` >>
     simp[contextTheory.compile_copy_memory_def, emitHelperTheory.emit_void_def,
          emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
          compileEnvTheory.comp_return_def, Abbr `inst`] >> strip_tac >> gvs[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (fs[fragExecTheory.fn_has_code_def] >>
     suspend "instruction") >>
  `ptr_inst_ok
      <| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
         d_ret := K {} |> lo 0 ctx func G tn inst s` by suspend "pointer" >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    (simp[Abbr `inst`, unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def, venomInstTheory.mk_inst_def,
          contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def,
          sized_source_write_range_def,
          venomStateTheory.eval_operand_def]) >>
  `gas_origin_ptr_edge
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
          d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (OK (sc with vs_inst_idx := SUC s.vs_inst_idx),G,tf)` by
    (`inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
       inst.inst_opcode <> GAS` by
       simp[Abbr `inst`, venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
     drule_all straight_line_origin_ptr_edge >>
     disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >> simp[Abbr `tf`]) >>
  `~sc.vs_halted` by
    simp[Abbr `sc`, venomExecSemanticsTheory.mcopy_def,
         venomStateTheory.write_memory_with_expansion_def] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Resume typed_copy_origin_ptr_sarray_fast_path[instruction]:
  markerLib.RESUME_TAC >>
  gvs[rich_listTheory.IS_PREFIX_APPEND, venomInstTheory.get_instruction_def,
      listTheory.EL_APPEND_EQN]
QED

Resume typed_copy_origin_ptr_sarray_fast_path[pointer]:
  gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, Abbr `inst`, venomInstTheory.mk_inst_def,
       venomExecSemanticsTheory.step_inst_def, taint_ok_def, op_taint_def,
       Abbr `sc`, venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def] >>
  suspend "access"
QED

Resume typed_copy_origin_ptr_sarray_fast_path[post]:
  `sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
     Cases_on `n` >>
     simp[contextTheory.compile_copy_memory_def, emitHelperTheory.emit_void_def,
          emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
          compileEnvTheory.comp_return_def] >> strip_tac >> gvs[]) >>
  simp[Abbr `sc`, op_taint_def] >> conj_tac
  >- (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  conj_tac
  >- (simp[GSYM type_memory_size_def] >>
      irule typed_copy_mcopy_state_frame) >>
  simp[venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def] >>
  rpt strip_tac >> simp[] >> metis_tac[arithmeticTheory.LE_ADD,
    arithmeticTheory.LESS_MONO_ADD, arithmeticTheory.ADD_COMM]
QED

Resume typed_copy_origin_ptr_sarray_fast_path[access]:
  markerLib.RESUME_TAC >> (
  simp[access_ok_def, source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       sized_source_write_range_def, venomStateTheory.eval_operand_def] >>
  conj_tac
  >- simp[memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def] >>
  qpat_x_assum `op_taint tn (Var xs) = {}` mp_tac >>
  qpat_x_assum `op_taint tn (Var xd) = {}` mp_tac >>
  simp[op_taint_def] >> ntac 2 disch_tac >>
  qx_gen_tac `operand` >> Cases_on `operand` >> simp[] >> metis_tac[])
QED

Finalise typed_copy_origin_ptr_sarray_fast_path

Theorem typed_copy_origin_ptr_sarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Fixed cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Fixed cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Fixed cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (ArrayT de (Fixed cap)) sty dtv stv v
Proof
  cheat
QED
