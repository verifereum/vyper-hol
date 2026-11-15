(* Joint offset boundaries for sparse member stores. *)
Theory fullStoreSlotsMembers
Ancestors
  fullStoreSlotsProbe typedCopyOriginPtrBase fragGasOriginPtr stateFrame context emitHelper
  exprLoweringProps compileEnv loweringStateRelDefs typedMemoryCopy ptrDiscipline venomState venomInst
  venomExecSemantics finite_map pred_set list arithmetic words

Theorem store_slots_add_code:
  emit_op ADD [op;Lit (n2w off)] sa = (r,sb) ==>
  ?out. r = Var out /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
    (!p. not_fresh_at sa p ==> p <> out)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[not_fresh_at_def] >> rpt strip_tac >> metis_tac[LESS_EQ_REFL]
QED

Theorem store_slots_clean_add_origin_ptr:
  emit_op ADD [op;Lit (n2w off)] sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand op s = SOME a /\ op_taint tn op = {} ==>
  ?Gf tf u.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    eval_operand r u = SOME (a+n2w off) /\ op_taint tf r = {} /\
    op_prov Gf r = op_prov G op /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule store_slots_add_code >> strip_tac >> gvs[] >>
  qexistsl_tac [
    `step_prov ARB G (mk_inst sa.cs_next_id ADD [op;Lit (n2w off)] [out])
      (update_var out (a+n2w off) s)`,
    `step_taint (mk_inst sa.cs_next_id ADD [op;Lit (n2w off)] [out]) s
      (update_var out (a+n2w off) s) tn`,
    `update_var out (a+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (rpt gen_tac >>
      `op_taint tn (Lit (n2w off)) = {}` by simp[op_taint_def] >>
      drule_at (Pat `emit_op _ _ _ = _`) typed_copy_origin_ptr_binop_path >>
      simp[eval_operand_def] >>
      disch_then drule_all >> strip_tac >>
      gvs[step_prov_def, out_prov_def, mk_inst_def]) >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `left` |-> `op`,
    `right` |-> `Lit (n2w off)`, `w` |-> `(a:bytes32)+n2w off`,
    `id` |-> `sa.cs_next_id`] typed_copy_origin_ptr_binop_ghost_frame) >>
  simp[] >> strip_tac >>
  simp[execution_frame_def, update_var_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE] >> conj_tac
  >- (Cases_on `op` >>
      simp[op_prov_def, step_prov_def, out_prov_def, first_prov_def,
        mk_inst_def, set_prov_def, FLOOKUP_DRESTRICT] >>
      rename1 `FLOOKUP G src` >> Cases_on `FLOOKUP G src` >> simp[set_prov_def, FLOOKUP_UPDATE,
        FLOOKUP_DRESTRICT]) >>
  rpt strip_tac >>
  `p <> out` by metis_tac[] >>
  gvs[GSYM update_var_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  Cases_on `first_prov G [op;Lit (n2w off)]` >>
  simp[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem store_slots_clean_offset_origin_ptr:
  compile_lit_byte_offset op off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand op s = SOME a /\ op_taint tn op = {} ==>
  ?Gf tf u.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    eval_operand r u = SOME (a+n2w off) /\ op_taint tf r = {} /\
    op_prov Gf r = op_prov G op /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`G`,`tn`,`s`] >> simp[WORD_ADD_0] >>
      rpt gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  Cases_on `op`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def, eval_operand_def] >>
      qexistsl_tac [`G`,`tn`,`s`] >> simp[eval_operand_def, op_taint_def] >>
      rpt gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  gvs[compile_lit_byte_offset_def] >>
  drule_all store_slots_clean_add_origin_ptr >>
  disch_then (qspecl_then [`G`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> gvs[execution_frame_def]
QED

Theorem store_slots_source_offset_origin_ptr:
  compile_lit_byte_offset (Var root) off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  off + n <= capacity /\ w2n a + off < dimword(:256) ==>
  ?out Gf tf u. r = Var out /\
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    lookup_var out u = SOME (a+n2w off) /\ ptr_covers Gf tf out u n /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME a /\ op_taint tn (Var root) = {}` by
    gvs[eval_operand_def, bodyPtrDefsTheory.ptr_covers_def] >>
  drule_all store_slots_clean_offset_origin_ptr >>
  disch_then (qspec_then `G` strip_assume_tac) >>
  `?out. r = Var out` by
    (Cases_on `off = 0` >- gvs[compile_lit_byte_offset_def, comp_return_def] >>
     gvs[compile_lit_byte_offset_def] >> metis_tac[store_slots_add_code]) >>
  gvs[] >> qexistsl_tac [`Gf`,`tf`,`u`] >> simp[] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, eval_operand_def, op_prov_def] >>
  `w2n (a+n2w off) = w2n a + off` by
    (simp[w2n_add_2] >> decide_tac) >>
  simp[] >> decide_tac
QED
