(* A StructLit byte store retains the raw endpoint used by its typed post. *)
Theory entryCreateStructLitBytesStore
Ancestors
  bodyFullStructLitBytes entryCreateAdminSequence bytesCopyCode
  entryCreateFocusSpec exprSimBufferStore exprLoweringProps
  abiEncoderProps venomInst arithmetic list

Theorem structlit_bytes_store_layout[local]:
  compile_store_bytestring src dst sa = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  fs[same_blocks_def, bytes_copy_insts_def, mk_inst_def, is_terminator_def,
       frag_ids_def]
QED

Theorem structlit_bytes_store_site:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ is_bytestring_type dty /\ is_bytestring_type sty /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?u G2 tn2.
    create_operand_full_scope sa sb explicit ctx func s [] (OK u) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2)) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn2.t_imm = tn.t_imm /\ tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tn2.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP G2 p = FLOOKUP G p /\ op_taint tn2 (Var p) = op_taint tn (Var p))) /\
  create_operand_cut sa sb explicit ctx func tops cx st0 source (es,s)
Proof
  disch_tac >> first_assum (mp_tac o MATCH_MP (SPEC_ALL structlit_bytes_store_origin_ptr_run)) >>
  strip_tac >>
  pop_last_assum (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule structlit_bytes_store_layout >> strip_tac >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  qpat_x_assum `EVERY _ (emitted_insts _ _)`
    (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  reverse conj_tac >- (irule create_admin_sequence_cut >> simp[EVERY_CONJ]) >>
  qexistsl_tac [`u`, `G2`, `tn2`] >> simp[] >>
  `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
   LENGTH sb.cs_current_insts` by simp[] >>
  qpat_x_assum `u = raw with vs_inst_idx := _` SUBST1_TAC >>
  qpat_assum `LENGTH _ + LENGTH _ = LENGTH _` (PURE_ONCE_REWRITE_TAC o single) >>
  irule create_admin_sequence_scope >> simp[EVERY_CONJ]
QED
