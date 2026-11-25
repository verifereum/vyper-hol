(* The selected typed-store run used by the widening IfExp arm. *)
Theory entryCreateIfExpTypedStore
Ancestors
  typedCopyOriginPtr typedCopyGasOps exprSimAbiEncodeObliviousCode
  createSizeTypedCopyCode entryCreateFocusSpec
  createSizeCutCode compileEnv venomExecSemantics venomState venomInst
  fragGasOriginPtr relation list pair fragFuel abiEncoderProps
  exprSimAbiEncodeSiteResources localPtrsProps
  compileExprAllocaFresh entryCreateAddedFragMember

Theorem typed_store_safe_code[local]:
  compile_store_memory_typed ce dst dt src st a = ((),b) ==>
  entry_shape a b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a b)
Proof
  strip_tac >>
  qspec_then `\opc. ~MEM opc [INVOKE;CREATE;CREATE2]` mp_tac
    typed_copy_code_family >>
  simp[] >> disch_then (assume_tac o cj 1) >>
  qpat_x_assum `!ce dst dt src st. code_action _ _` mp_tac >>
  pure_rewrite_tac[code_action_def] >> strip_tac >>
  first_x_assum drule >> simp[code_step_def]
QED

Theorem typed_store_fetch_member[local]:
  compile_store_memory_typed ce dst dt src st a = ((),b) /\
  fn_has_code a b f /\ fn_inst_ids_distinct f /\
  create_operand_fetch a b f u i ==>
  MEM i (frag_code a b)
Proof
  strip_tac >> fs[create_operand_fetch_def] >>
  drule_all lookup_block_get_instruction_fn_insts >> strip_tac >>
  `create_cut_code {} a b` by
    metis_tac[create_store_memory_typed_cut_code, pairTheory.SND] >>
  `!j. MEM j (frag_code a b) ==> MEM j (fn_insts f)` by
    metis_tac[create_cut_code_def, abi_encode_frag_code_members] >>
  drule typed_store_safe_code >> strip_tac >>
  `?j. MEM j (frag_code a b) /\ j.inst_id = i.inst_id` by
    (drule_all compile_store_memory_typed_added_id >> strip_tac >>
     drule_all entry_shape_added_frag_member >> metis_tac[]) >>
  metis_tac[fn_inst_ids_distinct_inj]
QED

Theorem ifexp_typed_store_selected_site:
  compile_store_memory_typed cenv (Var xd) dty (Var xs) sty sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
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
  ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  create_operand_at sa s ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    create_operand_at sb t /\
    create_cut_code {} sa sb /\
    EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2])
      (frag_code sa sb) /\
    (!p d k before hit after.
      create_interior_visit sa sb explicit ctx func (p,d,k) s
        (before,hit,after) ==>
      ?key inst u. hit = (key,func,inst,u) /\
        ~MEM inst.inst_opcode [INVOKE;CREATE;CREATE2])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_memory_typed_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `SND (compile_store_memory_typed cenv (Var xd) dty (Var xs) sty sa) = sb` by
    (asm_simp_tac bool_ss [] >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >-
    (simp[create_operand_at_def] >> metis_tac[]) >-
    (qpat_assum `SND (compile_store_memory_typed _ _ _ _ _ _ ) = _`
       (fn th => rw[GSYM th]) >> irule create_store_memory_typed_cut_code) >-
    (drule typed_store_safe_code >> simp[]) >-
    (rpt gen_tac >> strip_tac >>
     `!u i. create_operand_fetch sa sb func u i ==>
            ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]` by
       (rpt gen_tac >> disch_tac >> drule_all typed_store_fetch_member >> strip_tac >>
        drule typed_store_safe_code >> rewrite_tac[EVERY_MEM] >> metis_tac[]) >>
     drule create_interior_visit_cases >> strip_tac
     >- metis_tac[] >>
     first_x_assum drule >> simp[])
QED
