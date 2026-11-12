(* The joint typed memory copy of a dynamic array: length, check, data. *)
Theory typedCopyOriginPtrDynArray
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy representationCleanPtr

(* A single checked emitted instruction, with its concrete ghosts. *)
Theorem typed_copy_emit_inst_origin_ptr_path:
  emit_inst opc args outs sa = ((),sb) /\ fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  inst_mem_below_frontier (mk_inst sa.cs_next_id opc args outs) s /\
  inst_dload_in_section (mk_inst sa.cs_next_id opc args outs) s /\
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst sa.cs_next_id opc args outs) s /\
  step_inst_base (mk_inst sa.cs_next_id opc args outs) s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id opc args outs) u,
     step_taint (mk_inst sa.cs_next_id opc args outs) s u tn)
Proof
  strip_tac >> drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc args outs)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id opc args outs) u,
     step_taint (mk_inst sa.cs_next_id opc args outs) s u tn)` by
    (mp_tac (straight_line_origin_ptr_edge |> Q.INST
       [`i` |-> `mk_inst sa.cs_next_id opc args outs`]) >>
     simp[venomInstTheory.mk_inst_def] >> disch_then irule >> simp[]) >>
  `~u.vs_halted` by
    ( `step_inst 0 ctx (mk_inst sa.cs_next_id opc args outs) s = OK u` by
        simp[venomExecSemanticsTheory.step_inst_non_invoke, venomInstTheory.mk_inst_def] >>
      drule venomInstProofsTheory.step_preserves_halted >>
      simp[venomInstTheory.mk_inst_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem typed_copy_origin_ptr_dyn_read_path:
  emit_op MLOAD [Var xs] a = (Var lv,b) /\
  not_fresh_at a xs /\ lookup_var xs s = SOME sw /\
  ptr_covers G tn xs s 32 /\
  w2n sw + 32 < dimword (:256) /\ w2n sw + 32 <= s.vs_alloca_next /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w N) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    t.vs_alloca_next = s.vs_alloca_next /\
    eval_operand (Var lv) t = SOME (n2w N) /\ FLOOKUP Gf lv = NONE /\
    op_taint tnf (Var lv) = {} /\ t.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    typed_copy_state_frame a off len s t /\
    (!p. not_fresh_at a p ==>
       lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p n. not_fresh_at a p /\ ptr_covers G tn p s n ==>
       ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `!i. w2n sw <= i /\ i < w2n sw + 32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  `mem_word_at (w2n sw) s.vs_memory = n2w N` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id MLOAD [Var xs] [lv]] /\
   ~not_fresh_at a lv` by
    gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
        compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
        compileEnvTheory.emit_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
  qmatch_goalsub_abbrev_tac `gas_origin_ptr_path cx _ _ _` >>
  qabbrev_tac `inst = mk_inst a.cs_next_id MLOAD [Var xs] [lv]` >>
  qabbrev_tac `u = update_var lv (n2w N) s` >>
  qabbrev_tac `gf = step_prov PG G inst u` >>
  qabbrev_tac `tf = step_taint inst s u tn` >>
  `step_inst_base inst s = OK u` by
    simp[Abbr `inst`, Abbr `u`, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def,
         venomStateTheory.eval_operand_def,
         GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `ptr_inst_ok (FST cx) lo 0 ctx func G tn inst s` by
    (simp[Abbr `inst`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          venomInstTheory.mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          venomStateTheory.eval_operand_def] >>
     conj_tac >-
       (gvs[ptr_covers_def] >> rpt strip_tac >>
        gvs[memLocDefsTheory.mem_read_ops_def] >> metis_tac[]) >>
     gvs[ptr_covers_def] >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
     asm_simp_tac bool_ss
       [venomExecSemanticsTheory.step_inst_base_opcode_eqs,
        venomInstTheory.instruction_accessors,
        venomInstTheory.instruction_accfupds,
        venomInstTheory.opcode_case_def, combinTheory.K_THM] >>
     simp[venomExecSemanticsTheory.exec_read1_def,
          venomStateTheory.eval_operand_def, AllCaseEqs(),
          venomStateTheory.update_var_def] >> rpt strip_tac >> gvs[]) >>
  `emit_inst MLOAD [Var xs] [lv] a =
     ((), b with cs_next_var := a.cs_next_var)` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_return_def, compileEnvTheory.fresh_var_def,
          compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
     strip_tac >> gvs[] >>
     simp[compileEnvTheory.compile_state_component_equality]) >>
  `fn_has_code a (b with cs_next_var := a.cs_next_var) func` by
    gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, unitTransformDefsTheory.inst_mem_below_frontier_def,
         codegenRelTheory.source_memory_write_ranges_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         venomStateTheory.eval_operand_def, venomInstTheory.mk_inst_def] >>
  `gas_origin_ptr_path cx (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),gf,tf)` by
    (simp[NoAsms, Abbr `cx`, Abbr `gf`, Abbr `tf`, Abbr `inst`] >>
     irule typed_copy_emit_inst_origin_ptr_path >>
     simp[venomInstTheory.is_terminator_def] >>
     gvs[]) >>
  qexistsl [`u with vs_inst_idx := SUC s.vs_inst_idx`, `gf`, `tf`] >>
  simp[Abbr `u`, venomStateTheory.update_var_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[Abbr `gf`, Abbr `tf`, Abbr `inst`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
       op_taint_def, venomInstTheory.mk_inst_def,
       mem_word_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       venomStateTheory.update_var_def, store_taint_def, adopt_reset_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  `!p. not_fresh_at a p ==> p <> lv` by metis_tac[] >>
  `!k. k < 32 ==> k + w2n sw NOTIN tn.t_mem` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ /\ _ ==> i NOTIN _` irule >> decide_tac) >>
  simp[venomStateTheory.eval_operand_def, imm_taint_def,
       finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (simp[typed_copy_state_frame_def, typed_copy_frame_def,
          venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          venomStateTheory.venom_state_component_equality]) >>
  rpt strip_tac >>
  gvs[ptr_covers_def, op_taint_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `lv = p` >> gvs[]
QED

Theorem typed_copy_origin_ptr_dynarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (ArrayT de (Dynamic cap)) sty dtv stv v
Proof
  cheat
QED
