Theory bodyFullAbiDecodeTailAdd
Ancestors
  bodyFullAbiDecodeLeafCases typedCopyOriginPtrDynArray bodyPtrMakeArrayEmission fragGasSeqPtr fragGasOriginPtr
  bodyFullGhostFrame abiDecodePtrMemberFrame allocaHistory bodyPtrDefs
  loweringStateRelDefs codegenRel freshWrites stateFrame
  exprLoweringProps emitHelperProps emitHelper compileEnv venomState venomExecSemantics venomInst
  ptrDiscipline ptrSafeRun memSafeRun unitTransformDefs contextCodegenRel memLocDefs
  words arithmetic list rich_list finite_map pred_set pair

val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid,p,b,k,bytes). not_fresh_at st p) live``;

Theorem abi_decode_tail_ptr_add_joint:
  emit_op ADD [Var p;off] sa = (res,sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa input /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  not_fresh_at sa p /\ abi_decoder_operand_live sa.cs_next_var off /\
  lookup_var p s = SOME (n2w a) /\ eval_operand off s = SOME (n2w k) /\
  FLOOKUP G p = SOME (alloc_base,alloc_cap) /\ op_taint tn (Var p) = {} /\
  op_prov G off = NONE /\ op_taint tn off = {} /\
  alloc_base <= a /\ a+k+len <= alloc_base+alloc_cap /\
  alloc_base+alloc_cap < dimword (:256) ==>
  ?r t Gf tnf.
    res = Var r /\ not_fresh_at sb r /\ ~not_fresh_at sa r /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    eval_operand res t = SOME (n2w (a+k)) /\
    FLOOKUP Gf r = SOME (alloc_base,alloc_cap) /\ op_taint tnf res = {} /\
    ptr_covers Gf tnf r t len /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `allocas_from lo s` by (fs[] >> metis_tac[ghost_inv_at_def]) >>
  drule emit_op_fetch_boundary >> disch_then drule >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  rename1 `res = Var r` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Var p;off] [r]` >>
  qabbrev_tac `u = update_var r (n2w (a+k)) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  suspend "effects"
QED

Resume abi_decode_tail_ptr_add_joint[effects]:
  `!x. not_fresh_at sa x ==> x <> r` by metis_tac[] >>
  `not_fresh_at sb r /\ sa.cs_next_var <= sb.cs_next_var /\
   sa.cs_next_id <= sb.cs_next_id` by
    (conj_tac >- metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh] >>
     drule emitted_insts_emit_op >> simp[] >> strip_tac >>
     qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_def, exec_pure2_def,
      mk_inst_def, eval_operand_def, word_add_n2w] >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`, mk_inst_def, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `!D. ptr_inst_ok D lo 0 ctx fn G tn i s` by
    (gen_tac >> simp[ptr_inst_ok_def, Abbr `i`, mk_inst_def, access_ok_def,
      taint_ok_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def,
       exec_pure2_def, eval_operand_def, update_var_def]) >>
  suspend "package"
QED

Resume abi_decode_tail_ptr_add_joint[package]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,gf,tf)` by
    (gen_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME i /\
      i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ptr_inst_ok D lo 0 ctx fn G tn i s` by
       (gvs[markerTheory.Abbrev_def, mk_inst_def, is_terminator_def]) >>
     `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,gf,tf)` by
       (simp[Abbr `t`, Abbr `gf`, Abbr `tf`] >>
        drule_all straight_line_origin_ptr_edge >>
        simp[Abbr `i`, mk_inst_def, is_terminator_def]) >>
     drule (cj 2 gas_origin_ptr_path_rules) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
     irule (cj 1 gas_origin_ptr_path_rules) >>
     simp[Abbr `t`, Abbr `u`, update_var_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    suspend "old" >>
  `tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
   tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by suspend "taint" >>
  `alloca_history fn t` by suspend "history" >>
  `(^owned_decoder_state) sb t gf tf` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- simp[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
     simp[Abbr `t`, Abbr `u`, state_frame_def, update_var_def]) >>
  qexistsl_tac [`r`, `t`, `gf`, `tf`] >> asm_rewrite_tac[] >>
  simp[Abbr `t`, Abbr `u`, update_var_def] >>
  suspend "result"
QED

Resume abi_decode_tail_ptr_add_joint[old]:
  rpt strip_tac >> `x <> r` by metis_tac[] >>
  simp[Abbr `t`, Abbr `u`, Abbr `gf`, Abbr `tf`, Abbr `i`,
    step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
    step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
    mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Resume abi_decode_tail_ptr_add_joint[taint]:
  simp[Abbr `tf`, Abbr `i`, step_taint_def, set_var_taint_def,
    out_taint_def, store_taint_def, adopt_reset_def, mem_taint_def, imm_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, mk_inst_def, Abbr `u`, update_var_def,
    new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss]
QED

Resume abi_decode_tail_ptr_add_joint[history]:
  irule abi_decode_no_alloca_endpoint_history >>
  qexistsl_tac [`s`, `sa`, `sb`] >>
  drule emitted_insts_emit_op >> strip_tac >>
  fs[] >> simp[Abbr `t`, Abbr `u`, update_var_def, Abbr `i`, mk_inst_def,
    IS_PREFIX_APPEND]
QED

Resume abi_decode_tail_ptr_add_joint[result]:
  gvs[update_var_def, ptr_covers_def, lookup_var_def] >>
  gvs[Abbr `gf`, Abbr `tf`, Abbr `i`, step_prov_def, set_prov_def,
    out_prov_def, first_prov_def, op_prov_def, step_taint_def,
    set_var_taint_def, out_taint_def, op_taint_def, mk_inst_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Finalise abi_decode_tail_ptr_add_joint
