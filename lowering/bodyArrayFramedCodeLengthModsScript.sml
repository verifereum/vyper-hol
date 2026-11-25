(* The runtime header load, at the concrete post-key cursor. *)
Theory bodyArrayFramedCodeLengthMods
Ancestors
  bodyFullSubscriptArrayCodeOps allocasBelowFmpUpdatesProps
  context emitHelperProps exprSimCopy loweringStateRelDefs
  valueEncodingProps valueEncodingDefs vyperTyping vyperValueOperation
  ptrDiscipline venomState words arithmetic

Theorem framed_code_dynamic_length_mods:
  compile_imm_load_word F imm bop sa = (len_op,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand bop s = SOME w /\ op_taint tn bop = {} /\
  val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV av) (w2n w) s.vs_data_section /\
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av) /\
  w2n w + type_memory_size (ArrayTV etv (Dynamic cap)) <= LENGTH s.vs_data_section /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand len_op sf = SOME (n2w (array_length (ArrayTV etv (Dynamic cap)) av)) /\
    op_taint tnf len_op = {} /\ op_prov Gf len_op = NONE /\
    copy_old_operand sb len_op /\ (!l. len_op <> Label l) /\
    sa.cs_next_var <= sb.cs_next_var /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_initial_fmp = s.vs_initial_fmp /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_requests = s.vs_requests /\
    sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp sf) /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!op. copy_old_operand sa op /\ (!l. op <> Label l) ==>
      eval_operand op sf = eval_operand op s /\
      op_taint tnf op = op_taint tn op /\ op_prov Gf op = op_prov G op) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  strip_tac >>
  `w2n w <= LENGTH s.vs_data_section` by decide_tac >>
  `mem_word_at (w2n w) s.vs_data_section =
     n2w (array_length (ArrayTV etv (Dynamic cap)) av)` by
    (Cases_on `av` >> gvs[value_has_type_def, val_in_memory_dynarray, array_length_def]) >>
  drule_all compile_imm_load_word_runtime_joint_frame >>
  disch_then (qspecl_then [`PG`, `G`]
    (qx_choosel_then [`out`, `Gf`, `tnf`, `sf`] strip_assume_tac)) >>
  qpat_x_assum `len_op = Var out` SUBST_ALL_TAC >>
  `emit_op DLOAD [bop] sa = (Var out,sb)` by fs[compile_imm_load_word_runtime] >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  `not_fresh_at sb out` by gvs[not_fresh_at_def] >>
  `allocas_below_fmp sf <=> allocas_below_fmp s` by
    (irule allocas_below_fmp_fields >> simp[]) >>
  qexistsl [`Gf`,`tnf`,`sf`] >>
  gvs[GSYM mem_word_at_def, eval_operand_def, copy_old_operand_def] >>
  Cases >> simp[eval_operand_def, op_taint_def, op_prov_def]
QED
