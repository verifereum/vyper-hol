(* Contained field capacity for actual memory projections. *)
Theory bodyFieldMemory
Ancestors
  exprSimAttributeFields bodyAllocMemory
  valueEncoding compileEnv venomState words list rich_list finite_map
  exprSimAttribute exprSimHash exprSimLiteralBuffer exprOperandVar
  exprSimBuffer exprSimAggregateChildren exprSim context
  exprLowering exprLoweringProps emitHelper emitHelperProps fragExec fragExecMem instMemFrontier
  allocaHistoryFragment venomInst vyperAST vyperTyping vyperInterpreter
  exprSimHyps vyperTypeSystem vyperTypeInvariants allocLimits
  bodyMemoryDefs exprSimUnwrap vyperState exprSimLen vyperTypeExprSoundness

Theorem body_field_region_frontier:
  fields_layout fields fs /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next ==>
  addr + struct_field_offset fields id + type_memory_size ftv <= s.vs_alloca_next
Proof
  strip_tac >> drule_all struct_field_offset_le >> decide_tac
QED

Theorem body_field_source_region:
  fields_layout fields fs /\ struct_has_type fs vals /\
  fields_in_memory vals fs addr s.vs_memory /\ fields_val_wf vals fs /\
  ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next ==>
  val_in_memory ftv fv (addr + struct_field_offset fields id) s.vs_memory /\
  val_wf ftv fv /\
  addr + struct_field_offset fields id + type_memory_size ftv <= s.vs_alloca_next
Proof
  strip_tac >>
  conj_tac >- (irule fields_in_memory_field >> metis_tac[]) >>
  conj_tac >- (irule fields_val_wf_field >> metis_tac[]) >>
  irule body_field_region_frontier >> metis_tac[]
QED

Theorem body_field_address_no_wrap:
  fields_layout fields fs /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  w2n ((n2w addr : bytes32) + n2w (struct_field_offset fields id)) =
    addr + struct_field_offset fields id
Proof
  strip_tac >> drule_all body_field_region_frontier >> strip_tac >>
  `addr + struct_field_offset fields id < dimword (:256)` by decide_tac >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_FIELD_REGION_MEMORY_AUDIT OK\n"
     else raise Fail "body field region inherited admission"
  end) [body_field_region_frontier, body_field_source_region, body_field_address_no_wrap];

(* The pointer arithmetic itself has no memory ranges, including stuck prefixes. *)
Theorem attr_add_prefix_mem_ok:
  emit_op ADD ops sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem attr_add_run_post[local]:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand (vv_operand vv) s = SOME w ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
      vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
      eval_operand (vv_operand vv) q = SOME w /\
      eval_operand dst q = SOME (w + n2w off) /\
      q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> drule_all buffer_emit_add_run >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[CONJUNCT1 exprOperandVarTheory.compiler_compile_var] >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
                 (w + n2w off) s` >>
  simp[] >> rpt conj_tac
  >- (irule vv_post_update_var >> simp[] >> qexists_tac `sm` >>
      simp[not_fresh_at_def, ASCIInumbersTheory.toString_11])
  >- (qpat_x_assum `eval_operand (vv_operand vv) s = _` (SUBST1_TAC o SYM) >>
      irule exprSimLiteralBufferTheory.literal_operand_frame >>
      reverse conj_tac >- simp[update_var_def] >>
      qexists_tac `sm` >> simp[] >>
      rw[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem attr_add_history[local]:
  emit_op ADD ops sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem attr_add_frag_mem_at:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
         alloca_history func s)
    (\s. (?w. vv_post ctx func cenv cx e es sa sn s0 es' tv vv s /\
               eval_operand (vv_operand vv) s = SOME w /\
               eval_operand dst s = SOME (w + n2w off)) /\
         alloca_history func s /\ s.vs_alloca_next = entry.vs_alloca_next /\
         s.vs_allocas = entry.vs_allocas) R
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
    alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. (?w. vv_post ctx func cenv cx e es sa sn s0 es' tv vv s /\
               eval_operand (vv_operand vv) s = SOME w /\
               eval_operand dst s = SOME (w + n2w off)) /\
         alloca_history func s /\ s.vs_alloca_next = entry.vs_alloca_next /\
         s.vs_allocas = entry.vs_allocas) R` suffices_by
    (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >>
  fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND3, mk_inst_def, is_terminator_def] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac >- (simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last] >>
    irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  disj1_tac >>
  `?w. eval_operand (vv_operand vv) entry = SOME w` by
    (gvs[vv_post_def] >> Cases_on `vv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  drule_all attr_add_run_post >> strip_tac >>
  `alloca_inv entry` by gvs[vv_post_def, stmt_state_rel_def] >>
  drule_all attr_add_history >> strip_tac >>
  qexists_tac `q` >>
  simp[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
  qpat_x_assum `alloca_history func (q with vs_inst_idx := _)` mp_tac >>
  simp[mk_inst_def]
QED

Theorem attr_add_frag_mem:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
         alloca_history func s)
    (\s. (?w. vv_post ctx func cenv cx e es sa sn s0 es' tv vv s /\
               eval_operand (vv_operand vv) s = SOME w /\
               eval_operand dst s = SOME (w + n2w off)) /\
         alloca_history func s) R
Proof
  strip_tac >> drule_all attr_add_frag_mem_at >>
  disch_then (qspecl_then [`tv`, `s0`, `es'`, `es`] mp_tac) >>
  simp[frag_exec_mem_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `s` mp_tac) >>
  disch_then (qspecl_then [`cx`, `ctx`, `R`, `fn`] mp_tac) >>
  simp[] >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ATTRIBUTE_ADD_MEMORY_AUDIT OK\n"
     else raise Fail "attribute ADD inherited admission"
  end) [attr_add_prefix_mem_ok, attr_add_run_post, attr_add_history,
        attr_add_frag_mem_at, attr_add_frag_mem];

Theorem body_base_memory_holds_struct[local]:
  !cenv cx sid tv vv es s stv w.
    vv_holds cenv cx (StructT sid) tv vv es s /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME stv /\
    eval_operand (vv_operand vv) s = SOME w /\ vv_loc vv = LocMemory ==>
    ?v. read_result cx tv es = (INL v, es) /\
        val_in_memory stv v (w2n w) s.vs_memory
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_rel_def, is_word_type_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_base_memory_at_struct[local]:
  !cenv cx sid sa sb es tv vv s v stv w.
    vv_at cenv cx (StructT sid) sa sb es tv vv s /\
    read_result cx tv es = (INL v, es) /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME stv /\
    vv_loc vv = LocMemory /\ eval_operand (vv_operand vv) s = SOME w ==>
    val_wf stv v /\
    ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                 sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                 b <= w2n w /\ w2n w + val_footprint stv v <= b + sz /\
                 (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                              b + sz <= lb \/ lb + lsz <= b)) \/
     (?n b sz. local_region cenv es.scopes s n b sz /\
               b <= w2n w /\ w2n w + val_footprint stv v <= b + sz /\
               (dynarray_local cenv n ==> b + 32 <= w2n w)) \/
     val_footprint stv v = 0)
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def, is_word_type_def, dynarray_type_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem body_attr_memory_at_field[local]:
  !func cenv cx sid sa sn es1 tv bvv q w dst ann fld fs ftv vals fv tv' ctx.
    stmt_state_rel ctx func cenv cx es1 q /\
    vv_at cenv cx (StructT sid) sa sn es1 tv bvv q /\
    read_result cx tv es1 = (INL (StructV vals), es1) /\
    read_result cx tv' es1 = (INL fv, es1) /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    fields_layout
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP vals fld = SOME fv /\
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) ann = SOME ftv /\
    vv_loc bvv = LocMemory ==>
    vv_at cenv cx ann sa sn es1 tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  simp[vv_at_def, mk_ptr_def] >> strip_tac >> gvs[attr_offset_def] >>
  qabbrev_tac `fields =
    get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)` >>
  `struct_field_offset fields fld + type_memory_size ftv <=
   type_memory_size_fields fs` by
    (irule struct_field_offset_le >> simp[]) >>
  drule stmt_state_rel_region_lt >> strip_tac >>
  drule_all body_base_memory_at_struct >> strip_tac >>
  `fields_val_wf vals fs` by gvs[val_wf_def] >>
  `val_wf ftv fv` by (irule fields_val_wf_field >> metis_tac[]) >>
  `val_footprint ftv fv <= type_memory_size ftv` by simp[val_footprint_le] >>
  gvs[val_footprint_def, type_memory_size_def] >>
  `w2n (w + n2w (struct_field_offset fields fld)) =
   w2n w + struct_field_offset fields fld` by
    (irule field_ptr_w2n >>
     qexistsl [`type_memory_size ftv`, `type_memory_size_fields fs`] >>
     simp[] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS,
                         arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[] >> all_tac
  >~ [`FLOOKUP q.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_region cenv es1.scopes q n b sz`]
  >- (disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[] >>
      rpt strip_tac >>
      `b + 32 <= w2n w` by metis_tac[] >> decide_tac) >>
  disj2_tac >> disj2_tac >> decide_tac
QED

Theorem body_attr_memory_vv_post:
  !func cenv cx obj es sa sn s0 es1 tv bvv q w dst ann fld sid fs ftv tv' ctx.
    vv_post ctx func cenv cx obj es sa sn s0 es1 tv bvv q /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
    expr_type obj = StructT sid /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    fields_layout
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) ann = SOME ftv /\
    (!v. read_result cx tv es1 = (INL v, es1) ==>
         value_has_type (StructTV fs) v) /\
    (!vals. read_result cx tv es1 = (INL (StructV vals), es1) ==>
       ?fv. ALOOKUP vals fld = SOME fv /\
            read_result cx tv' es1 = (INL fv, es1)) /\
    vv_loc bvv = LocMemory ==>
    vv_post ctx func cenv cx (Attribute ann obj fld) es sa sn s0 es1 tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post ctx _ _ _ obj _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >> gvs[] >>
  drule_all body_base_memory_holds_struct >> strip_tac >>
  `value_has_type (StructTV fs) v` by metis_tac[] >>
  `?vals. v = StructV vals /\ struct_has_type fs vals` by
    (Cases_on `v` >> gvs[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  gvs[] >>
  `value_has_type ftv fv` by
    (drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >>
     strip_tac >> gvs[]) >>
  rewrite_tac[vv_post_def] >> rpt conj_tac
  >~ [`vv_holds _ _ _ _ (LocatedValue _ _) _ _`]
  >- (simp[vv_holds_def, mk_ptr_def, expr_type_def] >>
      gvs[attr_offset_def] >>
      qabbrev_tac `fields =
        get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)` >>
      `struct_field_offset fields fld + type_memory_size ftv <=
       type_memory_size_fields fs` by
        (irule struct_field_offset_le >> simp[]) >>
      drule stmt_state_rel_region_lt >> strip_tac >>
      drule_all body_base_memory_at_struct >> strip_tac >>
      gvs[val_footprint_def, type_memory_size_def] >>
      `w2n (w + n2w (struct_field_offset fields fld)) =
       w2n w + struct_field_offset fields fld` by
        (irule field_ptr_w2n >>
         qexistsl [`type_memory_size ftv`, `type_memory_size_fields fs`] >>
         simp[] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS,
                             arithmeticTheory.LESS_EQ_TRANS]) >>
      simp[] >>
      `val_in_memory ftv fv (w2n w + struct_field_offset fields fld)
         q.vs_memory` by
        (irule fields_in_memory_field >> gvs[val_in_memory_def] >> metis_tac[]) >>
      gvs[wordsTheory.WORD_ADD_0] >> strip_tac >>
      drule_all val_in_memory_word_type >> simp[wordsTheory.WORD_ADD_0])
  >~ [`vv_at _ _ _ _ _ _ _ (LocatedValue _ _) _`]
  >- (simp[expr_type_def] >>
      qpat_assum `vv_loc bvv = LocMemory`
        (fn th => pure_once_rewrite_tac[GSYM th]) >>
      irule body_attr_memory_at_field >> simp[] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ATTRIBUTE_MEMORY_POST_AUDIT OK\n"
     else raise Fail "attribute memory post inherited admission"
  end) [body_base_memory_holds_struct, body_base_memory_at_struct,
        body_attr_memory_at_field, body_attr_memory_vv_post];

Theorem body_attribute_name_compile[local]:
  !cenv ty ann sid id fld st vv st'.
    compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) st =
      (vv, st') ==>
    ?bvv st1 p.
      compile_expr cenv ty (Name (StructT sid) id) st = (bvv, st1) /\
      emit_op ADD [vv_operand bvv;
                   Lit (n2w (attr_offset cenv (StructT sid) (vv_loc bvv)
                               fld))] st1 = (p, st') /\
      vv = LocatedValue ann (mk_ptr p (vv_loc bvv))
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_attribute_def, comp_bind_def, comp_return_def,
       expr_size_def, expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_return_def, vv_loc_def, attr_offset_def]
QED

Theorem body_attribute_name_eval[local]:
  !cx ann sid id fld es.
    eval_expr cx (Attribute ann (Name (StructT sid) id) fld) es =
    (do r <- eval_expr cx (Name (StructT sid) id);
        select_result cx (StructT sid) r (AttrSubscript fld) od) es
Proof
  simp[Once evaluate_def, expr_type_def]
QED

Theorem body_attribute_name_pre[local]:
  !cenv cx env ann sid id fld es.
    expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es ==>
    expr_body_pre cenv cx env (Name (StructT sid) id) es /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME ann
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  gvs[expr_body_pre_def, well_typed_expr_def, attribute_type_ok_def,
      vyperTypeCallGraphTheory.int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm, byte_widths_expr_def,
      alloc_limits_expr_def, expr_type_def]
QED

Theorem body_base_memory_post_read_struct[local]:
  !ctx func cenv cx obj es sa sn s0 es1 tv bvv q w sid fs.
    vv_post ctx func cenv cx obj es sa sn s0 es1 tv bvv q /\
    expr_type obj = StructT sid /\ vv_loc bvv = LocMemory /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    eval_operand (vv_operand bvv) q = SOME w ==>
    ?v. read_result cx tv es1 = (INL v, es1)
Proof
  rpt strip_tac >> fs[vv_post_def] >>
  drule_all body_base_memory_holds_struct >> metis_tac[]
QED

Theorem compile_attribute_name_body_vv_sim_mem:
  !ctx func cenv cx env ty ann sid id fld es.
    expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es ==>
    expr_vv_sim_mem ctx func cenv cx ty
      (Attribute ann (Name (StructT sid) id) fld) es
Proof
  rpt gen_tac >> strip_tac >>
  drule body_attribute_name_pre >> strip_tac >>
  `expr_sim_pre cenv cx env (Name (StructT sid) id) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule compile_name_body_vv_sim_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `ty`] assume_tac) >>
  simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule body_attribute_name_compile >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty (Name (StructT sid) id) sa = (bvv, sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  gvs[body_attribute_name_eval, bind_def] >>
  Cases_on `eval_expr cx (Name (StructT sid) id) es` >>
  rename1 `_ = (er, es1)` >>
  `expr_vv_res_ok er` by
    (drule_all expr_body_pre_vv_res_ok >> simp[]) >>
  `er <> INR (Error (RuntimeError "convert empty bytes to signed"))` by
    (Cases_on `er` >> gvs[]) >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ (Name _ _) _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  Cases_on `er` >> gvs[]
  >- (rename1 `eval_expr cx (Name (StructT sid) id) es = (INL btv, es1)` >>
      drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[expr_type_def] >>
      `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
      drule_all struct_fields_layout >> strip_tac >> gvs[] >>
      drule_all attribute_type_evaluates >> strip_tac >>
      `~popped_at_field btv fld es1` by
        (irule popped_keys_indexed_not_at_field >>
         drule_all expr_body_pre_eval_result >> simp[expr_sim_inv_def]) >>
      `!m. res <> INR (Error (TypeError m))` by
        (rpt strip_tac >> gvs[expr_vv_res_ok_def]) >>
      `vv_loc bvv = LocMemory` by
        (`?ptr sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var ptr) sz)` by
           gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
         gvs[compile_expr_def, compile_name_vv_def, comp_return_def,
             vv_loc_def, vv_location_def, mk_ptr_def]) >>
      irule frag_exec_mem_seq_pointwise >>
      qexistsl [`\s. vv_post ctx func cenv cx (Name (StructT sid) id)
                   es sa sm s0 es1 btv bvv s /\
                   s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`,
                `sm`] >> simp[] >> reverse conj_tac
      >- (irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
          simp[expr_exit_def]) >>
      gen_tac >> strip_tac >>
      qmatch_asmsub_abbrev_tac `emit_op ADD [_; Lit (n2w off)] sm = _` >>
      drule_all attr_add_frag_mem_at >>
      disch_then (qspecl_then [`btv`, `s0`, `es1`, `es`] mp_tac) >>
      disch_then (qspecl_then [`t`, `cx`, `ctx`, `expr_exit res`] assume_tac) >>
      qpat_x_assum `frag_exec_mem ctx sa sm _ _ _` kall_tac >>
      qpat_x_assum `compile_expr _ _ (Attribute _ _ _) _ = _` kall_tac >>
      irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
      `?v. read_result cx btv es1 = (INL v, es1)` by
        (drule body_base_memory_post_read_struct >> simp[expr_type_def] >>
         disch_then drule_all >> simp[]) >>
      `value_has_type (StructTV fs) v` by metis_tac[] >>
      `?vals. v = StructV vals /\ struct_has_type fs vals` by
        (Cases_on `v` >> gvs[value_has_type_def] >>
         rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
      gvs[] >>
      drule_all select_attr_read >> strip_tac >> gvs[] >>
      qpat_assum `vv_loc bvv = LocMemory`
        (fn th => pure_once_rewrite_tac[GSYM th]) >>
      irule body_attr_memory_vv_post >> simp[expr_type_def, Abbr `off`] >>
      goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  irule frag_exec_mem_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ATTRIBUTE_NAME_MEMORY_AUDIT OK\n"
     else raise Fail "attribute Name memory inherited admission"
  end) [body_attribute_name_compile, body_attribute_name_eval,
        body_attribute_name_pre, body_base_memory_post_read_struct,
        compile_attribute_name_body_vv_sim_mem];

Theorem body_word_load_prefix_mem_ok:
  emit_op MLOAD [operand] sm = (op,sb) /\
  eval_operand operand s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >>
  simp[below_frontier_MLOAD]
QED

Theorem body_word_load_history[local]:
  emit_op MLOAD [operand] sm = (op,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sb) s = OK q ==>
  alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_word_load_run_post[local]:
  emit_op MLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type t /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s ==>
  ?q. run_inst_seq (emitted_insts sm sb) s = OK q /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op q /\
      q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       !tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
             mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v` by
    (gvs[vv_post_def, vv_holds_def, read_result_def, return_def] >> metis_tac[]) >>
  gvs[] >> drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `not_local_ptr cenv es'.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sm` >> simp[]) >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule step_MLOAD >>
  disch_then (qspecl_then [`sm.cs_next_id`, `out`] assume_tac) >>
  qexists_tac `update_var out (mload (w2n w) s) s` >>
  simp[run_inst_seq_def, Abbr `out`] >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  irule expr_post_of_vv_post_load >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qexists_tac `mload (w2n w) s` >>
      simp[eval_operand_def, lookup_var_update_var, GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> simp[]) >>
  qexistsl [`p`, `s`, `sm`, `expr_type e`] >>
  simp[lookup_var_update_var, update_var_def] >> metis_tac[]
QED

Theorem unwrap_memory_word_sim_mem:
  emit_op MLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type t /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
            (LocatedValue t p) s /\
         (?w. eval_operand p.ptr_operand s = SOME w /\
              w2n w + 32 <= s.vs_alloca_next) /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `P = \s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
      (LocatedValue t p) s /\
    (?w. eval_operand p.ptr_operand s = SOME w /\ w2n w + 32 <= s.vs_alloca_next) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sb P
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND3, mk_inst_def, is_terminator_def] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac >- (drule_all body_word_load_prefix_mem_ok >> simp[mk_inst_def]) >>
  disj1_tac >> drule_all body_word_load_run_post >> strip_tac >>
  `alloca_inv s` by gvs[vv_post_def, stmt_state_rel_def] >>
  drule_all body_word_load_history >> strip_tac >>
  qexists_tac `q` >> simp[] >>
  qpat_x_assum `run_inst_seq _ _ = OK q` mp_tac >>
  qpat_x_assum `alloca_history func (q with vs_inst_idx := _)` mp_tac >>
  simp[mk_inst_def] >> rpt strip_tac >>
  `is_word_type (expr_type e)` by gvs[vv_post_def, vv_holds_def] >>
  fs[expr_post_def, expr_val_rel_def, expr_val_at_def,
     stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
     local_region_def, locals_kept_def] >>
  conj_tac >> first_x_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_WORD_LOAD_MEMORY_AUDIT OK\n"
     else raise Fail "word load memory inherited admission"
  end) [body_word_load_prefix_mem_ok, body_word_load_history,
        body_word_load_run_post, unwrap_memory_word_sim_mem];

Theorem body_attribute_name_capacity[local]:
  expr_sim_pre cenv cx env (Name (StructT sid) id) es /\
  stmt_state_rel ctx func cenv cx es q /\
  compile_expr cenv ty (Name (StructT sid) id) sa = (bvv,sm) /\
  fields_layout fields fs /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  ALOOKUP fs fld = SOME ftv /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w (struct_field_offset fields fld)) ==>
  ?fw. eval_operand dst q = SOME fw /\
       w2n fw + type_memory_size ftv <= q.vs_alloca_next
Proof
  strip_tac >> drule_all body_name_source_region >> strip_tac >>
  `w2n w + type_memory_size_fields fs <= q.vs_alloca_next` by
    (gvs[compile_expr_def, compile_name_vv_def, comp_return_def,
         vv_operand_def, mk_ptr_def, eval_operand_def, type_memory_size_def] >>
     decide_tac) >>
  `q.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def] >> metis_tac[alloca_room_next_lt]) >>
  drule_all body_field_region_frontier >> strip_tac >>
  drule_all body_field_address_no_wrap >> strip_tac >>
  qexists_tac `w + n2w (struct_field_offset fields fld)` >> simp[] >>
  qpat_x_assum `w2n (n2w (w2n w) + _) = _` mp_tac >>
  simp[wordsTheory.n2w_w2n] >> decide_tac
QED

Theorem body_name_eval_state[local]:
  lookup_scopes id es.scopes = SOME entry /\
  eval_expr cx (Name ann id) es = (res,es1) ==> es1 = es
Proof
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def] >>
  strip_tac >> gvs[]
QED

Theorem compile_attribute_name_body_capacity_mem:
  expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es /\
  compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) sa = (vv,sb) /\
  eval_expr cx (Attribute ann (Name (StructT sid) id) fld) es = (res,es') /\
  expr_vv_res_ok res /\
  res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
    (\s. (?tv. res = INL tv /\
               vv_post ctx func cenv cx (Attribute ann (Name (StructT sid) id) fld)
                 es sa sb s0 es' tv vv s) /\
         vv_loc vv = LocMemory /\
         (?ftv w. evaluate_type (get_tenv cx) ann = SOME ftv /\
                  eval_operand (vv_operand vv) s = SOME w /\
                  w2n w + type_memory_size ftv <= s.vs_alloca_next) /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  strip_tac >> drule body_attribute_name_pre >> strip_tac >>
  `expr_sim_pre cenv cx env (Name (StructT sid) id) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule compile_name_body_vv_sim_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `ty`] assume_tac) >>
  drule body_attribute_name_compile >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty (Name (StructT sid) id) sa = (bvv, sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  gvs[body_attribute_name_eval, bind_def] >>
  Cases_on `eval_expr cx (Name (StructT sid) id) es` >>
  rename1 `_ = (er, es1)` >>
  `expr_vv_res_ok er` by
    (drule_all expr_body_pre_vv_res_ok >> simp[]) >>
  `er <> INR (Error (RuntimeError "convert empty bytes to signed"))` by
    (Cases_on `er` >> gvs[]) >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ (Name _ _) _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  Cases_on `er` >> gvs[]
  >- (rename1 `eval_expr cx (Name (StructT sid) id) es = (INL btv, es1)` >>
      `?entry. lookup_scopes id es.scopes = SOME entry` by
        (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
         drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> metis_tac[]) >>
      `es1 = es` by (drule_all body_name_eval_state >> simp[]) >> gvs[] >>
      drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[expr_type_def] >>
      `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
      drule_all struct_fields_layout >> strip_tac >> gvs[] >>
      drule_all attribute_type_evaluates >> strip_tac >>
      `~popped_at_field btv fld es` by
        (irule popped_keys_indexed_not_at_field >>
         fs[expr_sim_inv_def, expr_type_def]) >>
      `!m. res <> INR (Error (TypeError m))` by
        (rpt strip_tac >> gvs[expr_vv_res_ok_def]) >>
      `vv_loc bvv = LocMemory` by
        (`?ptr sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var ptr) sz)` by
           gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
         gvs[compile_expr_def, compile_name_vv_def, comp_return_def,
             vv_loc_def, vv_location_def, mk_ptr_def]) >>
      irule frag_exec_mem_seq_pointwise >>
      qexistsl [`\s. vv_post ctx func cenv cx (Name (StructT sid) id)
                   es sa sm s0 es btv bvv s /\
                   s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`,
                `sm`] >> simp[] >> reverse conj_tac
      >- (irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
          simp[expr_exit_def]) >>
      gen_tac >> strip_tac >>
      qmatch_asmsub_abbrev_tac `emit_op ADD [_; Lit (n2w off)] sm = _` >>
      drule_all attr_add_frag_mem_at >>
      disch_then (qspecl_then [`btv`, `s0`, `es`, `es`] mp_tac) >>
      disch_then (qspecl_then [`t`, `cx`, `ctx`, `expr_exit res`] assume_tac) >>
      qpat_x_assum `frag_exec_mem ctx sa sm _ _ _` kall_tac >>
      qpat_x_assum `compile_expr _ _ (Attribute _ _ _) _ = _` kall_tac >>
      irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac
      >- (qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
          `?v. read_result cx btv es = (INL v, es)` by
            (drule body_base_memory_post_read_struct >> simp[expr_type_def] >>
             disch_then drule_all >> simp[]) >>
          `value_has_type (StructTV fs) v` by metis_tac[] >>
          `?vals. v = StructV vals /\ struct_has_type fs vals` by
            (Cases_on `v` >> gvs[value_has_type_def] >>
             rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
          gvs[] >> drule_all select_attr_read >> strip_tac >> gvs[] >>
          qpat_assum `vv_loc bvv = LocMemory`
            (fn th => pure_once_rewrite_tac[GSYM th]) >>
          irule body_attr_memory_vv_post >> simp[expr_type_def, Abbr `off`] >>
          goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >> gvs[])
      >- simp[vv_loc_def, vv_location_def, mk_ptr_def] >>
      `stmt_state_rel ctx func cenv cx es s` by fs[vv_post_def] >>
      `eval_operand p s = SOME (w + n2w
        (struct_field_offset (get_struct_fields cenv.ce_struct_fields
          (nsid_to_string sid)) fld))` by fs[Abbr `off`, attr_offset_def] >>
      drule_all body_attribute_name_capacity >>
      simp[vv_operand_def, mk_ptr_def, Abbr `off`, attr_offset_def]) >>
  irule frag_exec_mem_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ATTRIBUTE_CAPACITY_MEMORY_AUDIT OK\n"
     else raise Fail "attribute capacity inherited admission"
  end) [body_attribute_name_capacity, body_name_eval_state,
        compile_attribute_name_body_capacity_mem];
