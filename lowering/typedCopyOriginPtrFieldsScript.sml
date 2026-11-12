(* The joint typed memory copies of tuples and structs, field by field. *)
Theory typedCopyOriginPtrFields
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy
  context compileEnv loweringStateRelDefs emitHelper venomState venomInst codegenRel venomExecSemantics

Theorem typed_copy_origin_ptr_byte_offset_path:
  !root off n total sa op sb a lo explicit ctx func PG s G tn base len.
  compile_with_byte_offset (Var root) off sa = (op,sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s total /\ off + n <= total /\
  w2n a + off < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p t Gf tnf.
    op = Var p /\ lookup_var p t = SOME (n2w (w2n a + off)) /\
    not_fresh_at sb p /\ ptr_covers Gf tnf p t n /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
          d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf) /\
    t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ typed_copy_state_frame sa base len s t /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
      conj_tac >- (gvs[ptr_covers_def] >> decide_tac) >>
      irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  `?out. op = Var out` by
    (gvs[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def] >> metis_tac[]) >>
  gvs[] >>
  `not_fresh_at sb out /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]] /\
   (!q. not_fresh_at sa q ==> q <> out)` by
    (gvs[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def, not_fresh_at_def] >> metis_tac[]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]` >>
  qabbrev_tac `u = update_var out (a + n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`, `gf`, `tf`] >>
  suspend "add"
QED

Resume typed_copy_origin_ptr_byte_offset_path[add]:
  `w2n (a + n2w off) = w2n a + off` by
    (irule typed_copy_offset_nonwrap >> decide_tac) >>
  conj_tac >- simp[Abbr `u`, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, GSYM wordsTheory.word_add_n2w,
    arithmeticTheory.ADD_COMM, wordsTheory.WORD_ADD_COMM] >>
  simp[] >> conj_tac >- suspend "coverage" >>
  conj_tac >- suspend "path" >>
  suspend "frame"
QED

Resume typed_copy_origin_ptr_byte_offset_path[coverage]:
  gvs[ptr_covers_def] >>
  simp[Abbr `gf`, Abbr `tf`, Abbr `i`, Abbr `u`,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
       op_taint_def, mk_inst_def, eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  decide_tac
QED

Resume typed_copy_origin_ptr_byte_offset_path[path]:
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME i` by
    (drule_all fragExecTheory.fn_has_code_same_block >>
     simp[] >> metis_tac[arithmeticTheory.ADD_0]) >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
  `step_inst_base i s = OK u` by suspend "step" >>
  `ptr_inst_ok
    (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
        d_ret := K {} |>) lo 0 ctx func G tn i s` by suspend "ptr" >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by suspend "mem" >>
  `gas_origin_ptr_edge
    (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
        d_ret := K {} |>,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (u with vs_inst_idx := SUC s.vs_inst_idx),gf,tf)` by
    (simp[Abbr `gf`, Abbr `tf`] >>
     drule_all straight_line_origin_ptr_edge >> simp[Abbr `i`, mk_inst_def,
       is_terminator_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `u`, update_var_def]
QED

Resume typed_copy_origin_ptr_byte_offset_path[frame]:
  simp[Abbr `u`, update_var_def, allocas_from_def, typed_copy_state_frame_def,
       venom_state_component_equality] >>
  conj_tac >- gvs[allocas_from_def] >>
  conj_tac >- (rpt strip_tac >>
    `x <> out` by metis_tac[] >> simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[Abbr `tf`, Abbr `gf`, Abbr `i`, step_taint_def,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, imm_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, mk_inst_def, update_var_def] >>
  conj_tac >- simp[new_site_bytes_def, finite_mapTheory.FLOOKUP_DEF,
    pred_setTheory.EXTENSION, SF CONJ_ss] >>
  rpt strip_tac >> `q <> out` by metis_tac[] >>
  Cases_on `FLOOKUP G root` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT,
       lookup_var_def]
QED

Resume typed_copy_origin_ptr_byte_offset_path[step]:
  simp[Abbr `i`, Abbr `u`, step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def]
QED

Resume typed_copy_origin_ptr_byte_offset_path[mem]:
  simp[Abbr `i`, mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Resume typed_copy_origin_ptr_byte_offset_path[ptr]:
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, Abbr `i`, mk_inst_def, access_ok_def, taint_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       source_memory_write_ranges_def, op_taint_def] >>
  conj_tac >- (Cases >> gvs[op_taint_def] >> metis_tac[]) >>
  gvs[step_inst_non_invoke, mk_inst_def] >>
  simp[Abbr `u`, update_var_def]
QED

Finalise typed_copy_origin_ptr_byte_offset_path

Theorem typed_copy_origin_ptr_tuple_entry:
  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (TupleT dtys) sty dtv stv v
Proof
  cheat
QED

Theorem typed_copy_origin_ptr_struct_entry:
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (StructT name) sty dtv stv v
Proof
  cheat
QED
