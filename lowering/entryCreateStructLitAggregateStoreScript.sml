(* The positive-size nonbytes field store uses either a single layout copy
   or the shared typed-store rule. Scope follows the memory post's witness. *)
Theory entryCreateStructLitAggregateStore
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec logStoreDataOriginPtr emitHelperProps
  layoutStoreProps memoryLayoutRel memoryLayoutSource exprSimProps bodyPtrDefs context compileEnv
  exprLoweringProps abiEncoderProps venomInst venomState arithmetic list

Definition structlit_aggregate_store_pre_def:
  structlit_aggregate_store_pre ce tenv sty dty stv dtv v sa sb ctx func lo
      s G tn xs xd sw dw <=>
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
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
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    ptr_covers G tn xd s (type_memory_size dtv) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ create_operand_at sa s
End

Definition structlit_aggregate_store_post_def:
  structlit_aggregate_store_post lo E ctx func PG s G tn sa sb dtv v dw t Gf tnf <=>
    (!D. gas_origin_ptr_path (D,lo,E,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ create_operand_at sb t /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
End

Theorem structlit_bulk_store_layout[local]:
  compile_copy_memory dst src n sa = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sa sb)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, comp_return_def, emitted_insts_refl] >>
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >>
  simp[same_blocks_def, frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem structlit_bulk_store_scope[local]:
  compile_copy_memory dst src n sa = ((),sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ create_operand_at sa s /\
  run_inst_seq (emitted_insts sa sb) s = OK raw ==>
  create_operand_full_scope sa sb E ctx func s []
    (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  create_operand_cut sa sb E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule structlit_bulk_store_layout >> strip_tac >> conj_tac
  >- (irule create_admin_sequence_scope >> simp[] >> fs[EVERY_MEM]) >>
  irule create_admin_sequence_cut >> simp[] >> fs[EVERY_MEM]
QED

Theorem structlit_bulk_store_site[local]:
  compile_copy_memory (Var xd) (Var xs) (type_memory_size dtv) sa = ((),sb) /\
  memory_layout_rel dtv stv /\
  structlit_aggregate_store_pre ce tenv sty dty stv dtv v sa sb ctx func lo
    s G tn xs xd sw dw ==>
  ?t Gf tnf.
    structlit_aggregate_store_post lo E ctx func PG s G tn sa sb dtv v dw t Gf tnf /\
    create_operand_full_scope sa sb E ctx func s [] (OK t) /\
    create_operand_cut sa sb E ctx func tops cx st0 source (es,s)
Proof
  simp[structlit_aggregate_store_pre_def, create_operand_at_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `type_memory_size stv = type_memory_size dtv` by fs[memory_layout_rel_def] >>
  `val_footprint stv v <= type_memory_size dtv` by
    (qpat_x_assum `type_memory_size stv = _` (SUBST1_TAC o SYM) >>
     irule val_footprint_le >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `type_memory_size stv = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  mp_tac (Q.INST [`tv` |-> `stv`, `n` |-> `type_memory_size dtv`, `explicit` |-> `E`]
            compile_copy_memory_origin_ptr_path_run) >>
  impl_tac >- simp[AC ADD_ASSOC ADD_COMM] >> strip_tac >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
     val_in_memory dtv v (w2n dw) mem` by
    (match_mp_tac robust_val_in_memory_layout_rel >> asm_rewrite_tac[]) >>
  `val_in_memory dtv v (w2n dw) t.vs_memory` by
    (qpat_assum `!mem. _ ==> val_in_memory dtv _ _ mem` irule >> simp[mem_agree_outside_def]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  simp[structlit_aggregate_store_post_def, create_operand_at_def] >>
  metis_tac[structlit_bulk_store_scope]
QED

Theorem structlit_nonbytes_store_site:
  (!ce tenv sty dty stv dtv v sa sb ctx func lo s G tn xs xd sw dw E PG.
    compile_store_memory_typed ce (Var xd) dty (Var xs) sty sa = ((),sb) /\
    structlit_aggregate_store_pre ce tenv sty dty stv dtv v sa sb ctx func lo
      s G tn xs xd sw dw ==>
    ?t Gf tnf.
      structlit_aggregate_store_post lo E ctx func PG s G tn sa sb dtv v dw t Gf tnf /\
      create_operand_full_scope sa sb E ctx func s [] (OK t) /\
      create_operand_cut sa sb E ctx func tops cx st0 source (es,s)) /\
  compile_store_memory ce (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ 0 < type_memory_size stv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  structlit_aggregate_store_pre ce tenv sty dty stv dtv v sa sb ctx func lo
    s G tn xs xd sw dw ==>
  ?t Gf tnf.
    structlit_aggregate_store_post lo E ctx func PG s G tn sa sb dtv v dw t Gf tnf /\
    create_operand_full_scope sa sb E ctx func s [] (OK t) /\
    create_operand_cut sa sb E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> ASM_CASES_TAC ``dty <> sty /\ ~tuple_memory_layout_eq dty sty``
  >- (`compile_store_memory_typed ce (Var xd) dty (Var xs) sty sa = ((),sb)` by
        fs[compile_store_memory_def] >>
      metis_tac[]) >>
  `compile_copy_memory (Var xd) (Var xs) (type_memory_size dtv) sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac[compile_store_memory_def]) >>
  `memory_layout_key dty = memory_layout_key sty` by metis_tac[bulk_store_layout_keys] >>
  `memory_layout_rel dtv stv` by
    (irule memory_layout_key_evaluated >> fs[structlit_aggregate_store_pre_def] >> metis_tac[]) >>
  irule structlit_bulk_store_site >> rpt (first_assum (irule_at Any))
QED
