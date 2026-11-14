(* Actual literal-offset ADD, including its concrete joint trace. *)
Theory dispatchedDecoderOffsetJoint
Ancestors reasonCodeOffsetPtr reasonEncoderTailPtr dispatchedDecoderTrace
  typedCopyPtr reasonTupleCopyPtr context compileEnv loweringStateRelDefs emitHelper
  emitHelperProps contextCodegenRelProps exprLoweringProps bodyPtrDefs fragGasSeqPtr
  venomState venomInst venomExecSemantics finite_map words fragExec ptrDiscipline
  ptrSafetyTransport ptrSafeRun calldataOverwritePtr gasEvents gasCount

Theorem calldata_decoder_lit_offset_joint:
  compile_lit_byte_offset (Var root) off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  off < dimword(:256) /\ off + needed <= capacity /\
  w2n a + off < dimword(:256) /\ alloca_inv s /\ allocas_from lo s ==>
  ?out Gf tnf sf.
    r = Var out /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w off) /\ ptr_covers Gf tnf out sf needed /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[WORD_ADD_0, venom_state_component_equality] >> conj_tac
      >- (rpt gen_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
      gvs[ptr_covers_def] >> decide_tac) >>
  gvs[compile_lit_byte_offset_def] >>
  drule code_offset_emit_var >> strip_tac >> gvs[] >>
  drule code_offset_emit_shape >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [out]` >>
  qabbrev_tac `t = update_var out (a + n2w off) s` >>
  qabbrev_tac `Gf = step_prov PG G inst t` >>
  qabbrev_tac `tnf = step_taint inst s t tn` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := SUC s.vs_inst_idx),Gf,tnf)` by
    suspend "joint" >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  conj_tac >- suspend "covers" >> suspend "frame"
QED

Resume calldata_decoder_lit_offset_joint[covers]:
  gvs[ptr_covers_def] >>
  simp[Abbr `Gf`, Abbr `tnf`, Abbr `inst`, copy_len_binop_ghost_frame,
       ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       update_var_def, lookup_var_def, w2n_add_2, w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED

Resume calldata_decoder_lit_offset_joint[frame]:
  simp[Abbr `tnf`, Abbr `inst`, copy_len_binop_ghost_frame] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[Abbr `Gf`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `first_prov G [Var root;Lit (n2w off)]` >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Resume calldata_decoder_lit_offset_joint[joint]:
  `same_blocks sa sb` by metis_tac[emit_op_same_blocks] >>
  `emitted_insts sa sb = [inst]` by
    (drule emitted_insts_emit_op >> simp[Abbr `inst`]) >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    !k. k < LENGTH [inst] ==> get_instruction bb (LENGTH sa.cs_current_insts + k) =
      SOME (EL k [inst])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >>
     drule emitted_insts_emit_op >> fs[same_blocks_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule dispatched_decoder_joint_step >>
  conj_tac >- simp[] >>
  conj_tac >- simp[Abbr `t`, update_var_def] >>
  qexistsl_tac [`bb`, `0`, `inst`] >>
  simp[Abbr `Gf`, Abbr `tnf`, Abbr `inst`, mk_inst_def,
    step_inst_non_invoke, ghost_step_non_invoke,
    gas_events_step_def, gas_count_step_def, is_terminator_def] >>
  `op_taint tn (Var root) = {}` by fs[ptr_covers_def] >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [out]) s = OK t` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      eval_operand_def, Abbr `t`] >>
  asm_simp_tac (srw_ss()) [mk_inst_def, ghost_step_non_invoke,
    step_inst_non_invoke] >>
  conj_tac
  >- (gen_tac >> simp_tac (srw_ss()) [ptr_safe_defs] >>
      irule ptr_inst_ok_lower_bound_transport >>
      conj_tac >- simp[] >> qexists_tac `0` >> simp[] >>
      irule (SRULE [mk_inst_def] ptr_inst_ok_copy_len_binop) >>
      simp[op_taint_def]) >>
  simp[memSafeRunTheory.mem_safe_step_non_invoke,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
    mk_inst_def, Abbr `t`, update_var_def] >>
  fs[mk_inst_def, update_var_def] >>
  irule (GSYM ghost_step_non_invoke) >>
  simp[step_inst_non_invoke]
QED

Finalise calldata_decoder_lit_offset_joint
