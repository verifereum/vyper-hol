(* Normalize the three actual F-argument store intervals at their landing. *)
Theory bodyIntCallBufferStoreCutMods
Ancestors
  bodyIntCallArgWordStoreMods[qualified] bodyIntCallArgBytesStoreMods[qualified]
  bodyIntCallArgAggregateStoreMods[qualified] bodyStructFieldCutsMods
  bodyFullPathHistory exprSimFullBundleProps valueTypingMemoryProps
  exprSimConvertBytes exprSimProps typedMemoryCopy context compileEnv
  bodyPtrDefs venomState venomMemDefs vyperValue vyperTyping valueEncoding
  vfmConstants finite_map words arithmetic

val _ = Parse.hide "base";

val word_store_contract = concl (GEN_ALL
  bodyIntCallArgWordStoreModsTheory.intcall_arg_word_store_mods);
val bytes_store_contract = concl (GEN_ALL
  bodyIntCallArgBytesStoreModsTheory.intcall_arg_bytes_store_mods);
val aggregate_store_contract = concl (GEN_ALL
  bodyIntCallArgAggregateStoreModsTheory.intcall_arg_aggregate_store_mods);

Theorem buffer_store_old_state[local]:
  typed_copy_state_frame cu base nw z t ==>
  t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
  (!p. not_fresh_at cu p ==> lookup_var p t = lookup_var p z)
Proof
  simp[typed_copy_state_frame_def, Once venom_state_component_equality]
QED

Theorem buffer_bytes_store_data[local]:
  is_bytestring_type dty /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) ==>
  type_memory_size dtv = type_memory_bytes ce dty /\
  val_footprint dtv v <= 32 + 32 * word_size len
Proof
  strip_tac >>
  qpat_x_assum `is_bytestring_type dty` mp_tac >>
  simp[bytestring_type_cases] >> strip_tac >>
  gvs[evaluate_type_def, type_memory_size_def, type_memory_bytes_def,
      GSYM word_size_def, value_has_type_def, loweringPostsTheory.val_footprint_def] >>
  irule le_word_size_mul
QED

Theorem bytes_store_adapter[local]:
  ^bytes_store_contract ==>
  compile_store_memory ce (Var src) (Var dst) dty sty cu = ((),cs) /\
  ~is_word_type dty /\ is_bytestring_type dty /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  fn_has_code cu cs func /\ fn_inst_ids_distinct func /\
  alloca_history func z /\ alloca_inv z /\ ~z.vs_halted /\
  z.vs_current_bb = cu.cs_current_bb /\ z.vs_inst_idx = LENGTH cu.cs_current_insts /\
  is_bytestring_type sty /\ evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type stv v /\
  value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
       val_in_memory stv v (w2n sw) m) /\
  n = 32 + 32 * word_size len /\ n < dimword (:256) /\
  not_fresh_at cu src /\ not_fresh_at cu dst /\
  lookup_var src z = SOME sw /\ lookup_var dst z = SOME dw /\
  ptr_covers G tn src z n /\ ptr_covers G tn dst z n /\
  w2n sw + n <= z.vs_alloca_next /\ w2n dw + n <= z.vs_alloca_next ==>
  ?t Gf tf.
    n <= MAX 32 (type_memory_bytes ce dty) /\
    typed_copy_state_frame cu (w2n dw) n z t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = cs.cs_current_bb /\
    t.vs_inst_idx = LENGTH cs.cs_current_insts /\ alloca_history func t /\
    t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
    (!p. not_fresh_at cu p ==> lookup_var p t = lookup_var p z /\
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + n) ==>
       (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
    val_wf dtv v /\ type_memory_size dtv <= MAX 32 (type_memory_bytes ce dty) /\
    val_footprint dtv v <= n /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
       val_in_memory dtv v (w2n dw) m)
Proof
  disch_then (mk_asm "bytes") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_x "bytes" drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `!i. ~(w2n dw <= i /\ i < w2n dw + n) ==> _`
    (mk_asm "bytes_outside") >>
  drule_then strip_assume_tac buffer_store_old_state >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
      (qspec_then `ARB` assume_tac) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `type_memory_size dtv = type_memory_bytes ce dty /\ val_footprint dtv v <= n` by
    (qpat_assum `n = _` (once_rewrite_tac o single) >>
     irule buffer_bytes_store_data >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (qexists_tac `get_tenv cx` >> first_assum ACCEPT_TAC))) >>
  `val_wf dtv v` by (irule value_has_type_memory_wf >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac
  >- (pure_rewrite_tac[MAX_LE] >> disj2_tac >>
      qpat_assum `type_memory_size dtv = type_memory_bytes ce dty`
        (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >>
    FIRST [asm "bytes_outside" ACCEPT_TAC, first_assum ACCEPT_TAC, simp[MAX_LE]]
QED

Theorem intcall_buffer_store_cut_mods:
  ^word_store_contract /\ ^bytes_store_contract /\ ^aggregate_store_contract ==>
  (if is_word_type dty then emit_void MSTORE [Var dst; op]
   else if is_bytestring_type dty then
     (do compile_store_bytestring op (Var dst); return () od)
   else compile_store_memory ce op (Var dst) dty sty) cu = ((),cs) /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  fn_has_code cu cs func /\ fn_inst_ids_distinct func /\
  alloca_history func z /\ alloca_inv z /\ ~z.vs_halted /\
  z.vs_current_bb = cu.cs_current_bb /\ z.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (if is_word_type dty then
     evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
     eval_operand op z = SOME (typed_val_to_w256 dtv v) /\ op_taint tn op = {} /\
     lookup_var dst z = SOME dw /\ w2n dw + 32 < dimword (:256) /\
     w2n dw + 32 <= z.vs_alloca_next /\ ptr_covers G tn dst z 32
   else if is_bytestring_type dty then
     ?src sw len n. op = Var src /\ is_bytestring_type sty /\
       evaluate_type (get_tenv cx) sty = SOME stv /\
       evaluate_type (get_tenv cx) dty = SOME dtv /\
       value_has_type stv v /\ value_has_type dtv v /\
       ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
        (?str. v = StringV str /\ len = LENGTH str)) /\
       (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
            val_in_memory stv v (w2n sw) m) /\
       n = 32 + 32 * word_size len /\ n < dimword (:256) /\
       not_fresh_at cu src /\ not_fresh_at cu dst /\
       lookup_var src z = SOME sw /\ lookup_var dst z = SOME dw /\
       ptr_covers G tn src z n /\ ptr_covers G tn dst z n /\
       w2n sw + n <= z.vs_alloca_next /\ w2n dw + n <= z.vs_alloca_next
   else contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env es /\
     struct_operand_mods (ce,get_tenv cx,sty,dty,stv,dtv) (op,v) (dst,w2n dw) (cu,G,tn,z) /\
     FLOOKUP z.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_bytes ce dty))) ==>
  ?t Gf tf nw.
    nw <= MAX 32 (type_memory_bytes ce dty) /\
    typed_copy_state_frame cu (w2n dw) nw z t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = cs.cs_current_bb /\
    t.vs_inst_idx = LENGTH cs.cs_current_insts /\ alloca_history func t /\
    t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
    (!p. not_fresh_at cu p ==> lookup_var p t = lookup_var p z /\
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + nw) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\ val_wf dtv v /\
    type_memory_size dtv <= MAX 32 (type_memory_bytes ce dty) /\ val_footprint dtv v <= nw /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory dtv v (w2n dw) m)
Proof
  disch_then (fn th =>
    mk_asm "word" (CONJUNCT1 th) >>
    CONJUNCTS_THEN2 (mk_asm "bytes") (mk_asm "aggregate") (CONJUNCT2 th)) >>
  Cases_on `is_word_type dty`
  >- (asm_x "bytes" kall_tac >> asm_x "aggregate" kall_tac >>
      qpat_assum `is_word_type dty` (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >> suspend "word") >>
  qpat_assum `~is_word_type dty` (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
  Cases_on `is_bytestring_type dty`
  >- (asm_x "word" kall_tac >> asm_x "aggregate" kall_tac >>
      qpat_assum `is_bytestring_type dty` (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >> suspend "bytes") >>
  asm_x "word" kall_tac >> asm_x "bytes" kall_tac >>
  qpat_assum `~is_bytestring_type dty` (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >> suspend "aggregate"
QED

Resume intcall_buffer_store_cut_mods[word]:
  `compile_store_memory ce op (Var dst) dty sty cu = ((),cs)` by
    simp[compile_store_memory_def] >>
  asm_x "word" drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tnf`] (map_every assume_tac o CONJUNCTS))) >>
  drule_then strip_assume_tac buffer_store_old_state >>
  drule_then assume_tac val_footprint_le >>
  qexistsl_tac [`t`,`Gf`,`tnf`,`32`] >> simp[]
QED

Resume intcall_buffer_store_cut_mods[bytes]:
  qpat_x_assum `?src sw len n. _`
    (qx_choosel_then [`src`,`sw`,`len`,`n`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  `compile_store_memory ce (Var src) (Var dst) dty sty cu = ((),cs)` by
    (simp[compile_store_memory_def] >>
     qpat_x_assum `(do compile_store_bytestring _ _; return () od) _ = _` mp_tac >>
     simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
     Cases_on `compile_store_bytestring (Var src) (Var dst) cu` >> simp[]) >>
  asm_x "bytes" (fn th => drule_all (MATCH_MP bytes_store_adapter th)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl_tac [`t`,`Gf`,`tf`,`n`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume intcall_buffer_store_cut_mods[aggregate]:
  asm_x "aggregate" drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tnf`] (map_every assume_tac o CONJUNCTS))) >>
  qhdtm_x_assum `struct_store_effects`
    (strip_assume_tac o PURE_REWRITE_RULE [struct_store_effects_def]) >>
  drule_then strip_assume_tac expr_sim_full_endpoint_fields >>
  drule_then strip_assume_tac buffer_store_old_state >>
  drule_then assume_tac val_footprint_le >>
  `evaluate_type (get_tenv cx) dty = SOME dtv` by fs[struct_operand_mods_def] >>
  qexistsl_tac [`t`,`Gf`,`tnf`,`type_memory_size dtv`] >> simp[]
QED

Finalise intcall_buffer_store_cut_mods
