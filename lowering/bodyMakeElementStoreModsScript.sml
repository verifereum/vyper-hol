(* A single MakeArray element store, expressed at the live output window. *)
Theory bodyMakeElementStoreMods
Ancestors
  logStoreDataOriginPtr typedCopyOriginPtr typedMemoryCopy
  bodyFullPredsMods bodyFullPostsMods
  exprLowering compileEnv loweringStateRelDefs
  gasOutcomeFull gasShadow venomState venomInst
  vyperInterpreter vyperState vyperAST context
  finite_map list pair option words

Theorem make_element_transfer_mods:
  compile_store_memory cenv (Var xs) (Var out) dty sty sa = ((),sb) /\
  ~is_word_type dty /\
  (is_bytestring_type dty ==> is_bytestring_type sty) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\
  value_has_type dtv v /\
  val_wf stv v /\
  val_wf dtv v /\
  not_fresh_at sa xs /\
  not_fresh_at sa out /\
  lookup_var xs s = SOME sw /\
  lookup_var out s = SOME dw /\
  w2n dw = b + off /\
  off + type_memory_size dtv <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/
     w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/
     w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn out s (type_memory_size dtv) /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
  allocas_from lo s /\
  lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\
  ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  irule compile_store_memory_origin_ptr_path >>
  rpt conj_tac >> metis_tac[]
QED
