(* Same-witness scope and visit cuts for the one-word and empty field stores. *)
Theory entryCreateStructLitSmallStore
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateCompletedCut
  createSizePrefixReplay logStoreDataOriginPtr bodyFullStructLitZeroStore
  abiEncoderProps emitHelperProps exprLoweringProps fragExec venomInst relation

Theorem structlit_word_store_site:
  compile_store_memory cenv src (Var xd) dty sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\
  eval_operand src s = SOME (typed_val_to_w256 dtv v) /\ op_taint tn src = {} /\
  lookup_var xd s = SOME dw /\ w2n dw + 32 < dimword (:256) /\
  w2n dw + 32 <= s.vs_alloca_next /\ ptr_covers G tn xd s 32 /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ create_operand_at sa s ==>
  ?t Gf tnf.
    create_operand_full_scope sa sb explicit ctx func s [] (OK t) /\
    create_operand_cut sa sb explicit ctx func tops cx st0 source (es,s) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) 32 s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + 32) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> fs[create_operand_at_def] >>
  drule_all compile_store_memory_word_origin_ptr_witness >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule emit_inst_extends >> strip_tac >>
  drule emitted_insts_emit_inst >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  conj_tac
  >- (qpat_x_assum `t = _` SUBST1_TAC >> irule create_admin_sequence_scope >>
      simp[create_operand_at_def, run_inst_seq_def] >>
      simp[frag_ids_def, mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- (irule create_admin_sequence_cut >>
      simp[create_operand_at_def, mk_inst_def, is_terminator_def]) >>
  simp[]
QED

Theorem structlit_zero_store_site:
  compile_store_memory cenv src (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ (is_bytestring_type dty ==> is_bytestring_type sty) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  type_memory_size stv = 0 /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xd /\ eval_operand src s = SOME sw /\ op_taint tn src = {} /\
  lookup_var xd s = SOME dw /\
  (!mem. bodyPtrDefs$mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  bodyPtrDefs$ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ create_operand_at sa s ==>
  ?t Gf tnf.
    create_operand_full_scope sa sb explicit ctx func s [] (OK t) /\
    create_operand_cut sa sb explicit ctx func tops cx st0 source (es,s) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. bodyPtrDefs$mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  pure_rewrite_tac[create_operand_at_def] >>
  disch_then (mp_tac o MATCH_MP structlit_zero_physical_store_witness) >>
  simp[] >> strip_tac >> gvs[] >> qexistsl_tac [`s`,`G`,`tn`] >>
  conj_tac
  >- simp[create_operand_full_scope_def, create_expr_prefix_marked, RTC_REFL] >>
  conj_tac
  >- (simp[create_operand_cut_def] >> rpt strip_tac >>
      drule create_interior_visit_cases >> simp[create_operand_fetch_def, frag_ids_def]) >>
  simp[]
QED
