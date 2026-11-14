(* Straight-line entry resources for dynamic sparse arrays. *)
Theory fullStoreSlotsArrayPrefix
Ancestors
  fullStoreSlotsBytes fullStoreSlotsProbe fullStoreSlotsMemberStep fullStoreSlotsElementLayout
  codegenRel contextCodegenRel rich_list fragExec fullStoreSlotsMembers loweringShapeRules
  emitHelper context compileEnv exprLoweringProps loweringStateRelDefs
  typedMemoryCopy bodyPtrDefs ptrDiscipline venomState venomInst
  venomExecSemantics stateFrame fragGasOriginPtr finite_map pred_set list
  arithmetic words

Theorem store_slots_length_load_origin_ptr:
  emit_op MLOAD [Var root] sa = (len,sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa root /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  32 <= capacity /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n a+32 <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n a) m = w) ==>
  ?lv u Gf tf. len = Var lv /\ not_fresh_at sb lv /\
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand len u = SOME w /\ op_taint tf len = {} /\ op_prov Gf len = NONE /\
    ptr_covers Gf tf root u capacity /\ execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `?lv. len = Var lv /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [Var root] [lv]] /\
    not_fresh_at sb lv /\ (!x. not_fresh_at sa x ==> x <> lv)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
     simp[not_fresh_at_def] >> rpt strip_tac >> metis_tac[LESS_EQ_REFL]) >>
  gvs[] >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id MLOAD [Var root] [lv])` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  qexistsl_tac [`update_var lv w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `DRESTRICT G (COMPL {lv})`,`tn with t_var := tn.t_var |+ (lv,{})`] >>
  conj_tac >- (rpt gen_tac >> irule store_slots_robust_load_origin_ptr >>
    simp[] >> qexistsl_tac [`a`,`sa.cs_next_id`,`root`] >> simp[] >>
    gvs[ptr_covers_def] >> qexistsl_tac [`a`,`b`,`sz'`] >> simp[] >> decide_tac) >>
  `root <> lv` by metis_tac[] >>
  simp[eval_operand_def,lookup_var_def,update_var_def,op_taint_def,op_prov_def,
    FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,execution_frame_def,ptr_covers_def]
  >> gvs[ptr_covers_def,op_taint_def,lookup_var_def] >>
  rpt strip_tac >> `x <> lv` by metis_tac[] >> simp[]
QED

Theorem store_slots_dynarray_prefix_origin_ptr:
  emit_op MLOAD [Var root] sa = (len,sb) /\
  emit_op ADD [Var root;Lit 32w] sb = (src,sc) /\
  emit_op ADD [dst;Lit 1w] sc = (slot,sd) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_has_code sc sd func /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME a /\ eval_operand dst s = SOME dw /\
  op_prov G dst = NONE /\ op_taint tn dst = {} /\
  ptr_covers G tn root s capacity /\ 32+n <= capacity /\
  w2n a+32 < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ w2n a+32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n a) m = n2w len_nat) ==>
  ?lv out u Gf tf. len = Var lv /\ src = Var out /\
    not_fresh_at sd lv /\ not_fresh_at sd out /\
    (!x. slot = Var x ==> not_fresh_at sd x) /\
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand len u = SOME (n2w len_nat) /\ op_taint tf len = {} /\ op_prov Gf len = NONE /\
    lookup_var out u = SOME (a+32w) /\ ptr_covers Gf tf out u n /\
    eval_operand slot u = SOME (dw+1w) /\ op_taint tf slot = {} /\ op_prov Gf slot = NONE /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `32 <= capacity` by decide_tac >>
  drule_all store_slots_length_load_origin_ptr >>
  disch_then (qx_choose_then `lv` (qx_choose_then `p` (qx_choose_then `Gp`
    (qx_choose_then `tp` strip_assume_tac)))) >> gvs[] >>
  `compile_lit_byte_offset (Var root) 32 sb = (src,sc)` by
    simp[compile_lit_byte_offset_def] >>
  `lookup_var root p = SOME a /\ allocas_from lo p /\
    eval_operand dst p = SOME dw /\ op_taint tp dst = {} /\ op_prov Gp dst = NONE` by
    (fs[execution_frame_def,allocas_from_def] >>
     Cases_on `dst` >> gvs[eval_operand_def,op_taint_def,op_prov_def] >>
     metis_tac[]) >>
  `32+n <= capacity` by decide_tac >>
  drule_all store_slots_source_offset_origin_ptr >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gq` (qx_choose_then `tq`
    (qx_choose_then `q` strip_assume_tac)))) >> gvs[] >>
  `(!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
   (!x. not_fresh_at sb x ==> not_fresh_at sc x) /\
   (!x. not_fresh_at sc x ==> not_fresh_at sd x)` by
    (imp_res_tac typed_copy_emit_op_mono >>
     fs[ci_mono_def,not_fresh_at_def] >> rpt strip_tac >>
     metis_tac[LESS_EQ_TRANS]) >>
  `not_fresh_at sc out /\ not_fresh_at sc lv /\
   (!x. dst = Var x ==> not_fresh_at sb x)` by
    (drule_at (Pat `compile_lit_byte_offset _ _ _ = _`)
       placeStoreSlotsTheory.store_slots_lit_offset_fresh >> simp[] >> metis_tac[]) >>
  `eval_operand dst q = SOME dw /\ op_taint tq dst = {} /\
   op_prov Gq dst = NONE /\ allocas_from lo q` by
    (fs[execution_frame_def,allocas_from_def] >> Cases_on `dst` >>
     gvs[eval_operand_def,op_taint_def,op_prov_def] >> metis_tac[]) >>
  drule_all store_slots_clean_add_origin_ptr >>
  disch_then (qspec_then `Gq` (qx_choose_then `Gf` (qx_choose_then `tf`
    (qx_choose_then `u` strip_assume_tac)))) >>
  `!x. slot = Var x ==> not_fresh_at sd x` by
    (qpat_assum `emit_op ADD [dst;Lit 1w] _ = _`
      (mp_then Any strip_assume_tac emit_op_facts) >> gvs[not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- (rpt gen_tac >> metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  `ptr_covers Gf tf out u n` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  fs[execution_frame_def,eval_operand_def,op_prov_def] >>
  rpt conj_tac >> metis_tac[]
QED
