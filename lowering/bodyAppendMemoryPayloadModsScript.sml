Theory bodyAppendMemoryPayloadMods
Ancestors
  bodyFullMemorySameTypeStore bodyFullStoreSlotsAddresses
  bodyFullAbiEncodeStore bodyPtrBytestringBuiltinsUintGhost
  bodyPtrPrecompileBuiltinsArithmeticValue robustCopyTransportPtr
  assignTuplePtrCopyLen vyperLookupStorage exprSimProps entryDecodeStaticProps
  typedCopyOriginPtrBase typedMemoryCopy exprLoweringProps freshWrites
  emitHelperProps fragExec fragGasOriginPtrLoop valueEncodingProps
  unitTransformDefs memSafeRun codegenRel contextCodegenRel
  venomState venomInst ptrDiscipline compileEnv context
  bodyPtrDefs loweringStateRelDefs finite_map pred_set words

Theorem payload_mstore[local]:
  emit_void MSTORE [Var p;op] a = ((),b) /\ fn_has_code a b func /\
  lookup_var p s = SOME bp /\ eval_operand op s = SOME w /\
  op_taint tn op = {} /\ ptr_covers G tn p s 32 /\
  w2n bp + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G,tf)) /\
    mem_word_at (w2n bp) t.vs_memory = w /\
    typed_copy_state_frame a (w2n bp) 32 s t /\
    tf.t_mem = tn.t_mem DIFF {i | w2n bp <= i /\ i < w2n bp+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm /\ tf.t_var = tn.t_var /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `b.cs_current_bb = a.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  mp_tac (Q.SPECL [`a`,`b`,`func`,`[mk_inst a.cs_next_id MSTORE [Var p;op] []]`]
    fn_has_code_same_block) >> simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst a.cs_next_id MSTORE [Var p;op] [])` by simp[] >>
  `inst_mem_below_frontier (mk_inst a.cs_next_id MSTORE [Var p;op] []) s /\
   inst_dload_in_section (mk_inst a.cs_next_id MSTORE [Var p;op] []) s` by
    simp[inst_mem_below_frontier_def,inst_dload_in_section_def,mk_inst_def,
      source_memory_write_ranges_def,source_memory_read_ranges_def,
      fixed_source_write_range_def,eval_operand_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mstore (w2n bp) w s with vs_inst_idx := SUC s.vs_inst_idx),G,
     step_taint (mk_inst a.cs_next_id MSTORE [Var p;op] []) s (mstore (w2n bp) w s) tn)` by
    (gen_tac >> irule abi_encode_mstore_origin_path >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`mstore (w2n bp) w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_taint (mk_inst a.cs_next_id MSTORE [Var p;op] []) s (mstore (w2n bp) w s) tn`] >>
  simp[typed_copy_mstore_state_frame,mstore_mem_word_at_same,clean_mstore_taint_state] >>
  simp[mstore_def,write_memory_with_expansion_def]
QED

Theorem payload_frame_byte[local]:
  typed_copy_state_frame a off len s t /\ ~(off <= i /\ i < off+len) ==>
  mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory
Proof
  rw[typed_copy_state_frame_def,typed_copy_frame_def] >>
  first_x_assum irule >> decide_tac
QED

Theorem payload_store_element[local]:
  compile_store_memory cenv src (Var xd) elem elem sa = ((),sb) /\
  evaluate_type tenv elem = SOME tv /\ type_memory_bytes cenv elem = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  value_has_type tv v /\ val_wf tv v /\
  not_fresh_at sa xd /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  lookup_var xd s = SOME dw /\ ptr_covers G tn xd s (type_memory_size tv) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size tv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type elem` >> fs[]
  >- suspend "word" >>
  `w2n dw + type_memory_size tv < dimword (:256) /\
   w2n sw + val_store_size tv v < dimword (:256)` by decide_tac >>
  qpat_x_assum `src = Var xs` SUBST_ALL_TAC >>
  `not_fresh_at sa xs` by metis_tac[] >>
  `w2n dw + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  drule_all body_full_memory_same_type_store_path >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[]
QED

Resume payload_store_element[word]:
  `type_memory_size tv = 32` by metis_tac[word_type_memory_size] >>
  `emit_void MSTORE [Var xd;src] sa = ((),sb)` by fs[compile_store_memory_def] >>
  `ptr_covers G tn xd s 32 /\ w2n dw + 32 <= s.vs_alloca_next` by fs[] >>
  drule_all payload_mstore >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`t`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G`,`tf`] >> simp[] >> conj_tac
  >- (gen_tac >> strip_tac >>
      `mem_word_at (w2n (dw:bytes32)) t.vs_memory = mem_word_at (w2n (dw:bytes32)) mem` by
        (irule clean_word_mem_agree >> goal_assum (drule_at Any) >> simp[]) >>
      drule_all val_in_memory_word >> simp[] >> metis_tac[]) >>
  fs[typed_copy_state_frame_def,op_taint_def]
QED

Finalise payload_store_element[local]

Theorem payload_write_header[local]:
  emit_op ADD [Var lenvar;Lit 1w] a = (next,b) /\
  emit_void MSTORE [Var p;next] b = ((),c) /\
  fn_has_code a b func /\ fn_has_code b c func /\
  not_fresh_at a p /\ lookup_var p s = SOME bp /\ ptr_covers G tn p s 32 /\
  lookup_var lenvar s = SOME (n2w len) /\ op_taint tn (Var lenvar) = {} /\
  w2n bp + 32 <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    mem_word_at (w2n bp) t.vs_memory = n2w (len+1) /\
    typed_copy_state_frame a (w2n bp) 32 s t /\
    tf.t_mem = tn.t_mem DIFF {i | w2n bp <= i /\ i < w2n bp+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
    t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >>
  `eval_operand (Var lenvar) s = SOME (n2w len) /\
   eval_operand (Lit 1w) s = SOME 1w /\ op_taint tn (Lit 1w) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] (qx_choose_then `out` strip_assume_tac)) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK q,_,_)` >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK q,Gq,_)` >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK q,Gq,tq)` >>
  `typed_copy_state_frame a (w2n bp) 32 s q` by
    (simp[typed_copy_state_frame_def] >> conj_tac
     >- simp[Abbr `q`,update_var_def,venom_state_component_equality] >>
     simp[Abbr `q`,typed_copy_frame_def,update_var_def]) >>
  `q.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo q /\
   ~q.vs_halted /\ q.vs_current_bb = b.cs_current_bb /\
   q.vs_inst_idx = LENGTH b.cs_current_insts` by
    simp[Abbr `q`,update_var_def,allocas_from_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  `lookup_var p q = SOME bp /\ ptr_covers Gq tq p q 32` by
    metis_tac[ptr_covers_lookup_frame] >>
  `w2n bp + 32 <= q.vs_alloca_next /\ eval_operand next q = SOME (n2w (len+1))` by
    simp[Abbr `q`,GSYM word_add_n2w,eval_operand_def,lookup_var_def,
      update_var_def,FLOOKUP_UPDATE] >>
  drule_all payload_mstore >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`t`,`tf`] strip_assume_tac)) >>
  `ci_mono a b` by metis_tac[typed_copy_emit_op_mono] >>
  `typed_copy_state_frame a (w2n bp) 32 q t` by
    metis_tac[typed_copy_state_frame_mono] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gq,tf)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  qexistsl_tac [`t`,`Gq`,`tf`] >> simp[] >>
  conj_tac >- metis_tac[typed_copy_state_frame_trans] >>
  rpt strip_tac >> fs[typed_copy_state_frame_def,op_taint_def] >> metis_tac[]
QED

Theorem append_memory_payload_writes_mods:
  compile_store_memory cenv src (Var xd) elem elem a3 = ((),a4) /\
  emit_op ADD [Var lenvar;Lit 1w] a4 = (next,a5) /\
  emit_void MSTORE [Var p;next] a5 = ((),b) /\ fn_has_code a3 b func /\
  not_fresh_at a3 p /\ not_fresh_at a3 lenvar /\ not_fresh_at a3 xd /\
  (!x. src = Var x ==> not_fresh_at a3 x) /\
  lookup_var p s = SOME bp /\ ptr_covers G tn p s (32+cap*type_memory_size tv) /\
  lookup_var lenvar s = SOME (n2w len) /\ op_taint tn (Var lenvar) = {} /\
  lookup_var xd s = SOME dw /\ ptr_covers G tn xd s (type_memory_size tv) /\
  w2n dw = w2n bp+32+len*type_memory_size tv /\ len < cap /\
  w2n bp+32+cap*type_memory_size tv <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  evaluate_type tenv elem = SOME tv /\ type_memory_bytes cenv elem = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  value_has_type tv v /\ val_wf tv v /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a3.cs_current_bb /\
  s.vs_inst_idx = LENGTH a3.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    mem_word_at (w2n bp) t.vs_memory = n2w (len+1) /\
    DISJOINT {i | w2n bp <= i /\ i < w2n bp+32} tf.t_mem /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem) /\
    w2n bp+32 <= w2n dw /\
    w2n dw+type_memory_size tv <= w2n bp+32+cap*type_memory_size tv /\
    typed_copy_state_frame a3 (w2n bp) (32+cap*type_memory_size tv) s t /\
    (!i. ~(w2n bp <= i /\ i < w2n bp+32) /\
         ~(w2n dw <= i /\ i < w2n dw+type_memory_size tv) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at a3 x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a3 a4 /\ ci_mono a4 a5 /\ ci_mono a5 b` by
    metis_tac[typed_copy_emit_op_mono,ci_mono_emit_void,ci_mono_compile_store_memory,pairTheory.SND] >>
  `cs_extends a3 a4 /\ cs_extends a4 a5 /\ cs_extends a5 b` by fs[ci_mono_def] >>
  `fn_has_code a3 a4 func /\ fn_has_code a4 a5 func /\ fn_has_code a5 b func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `!x. not_fresh_at a3 x ==> not_fresh_at a4 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `a3` >> fs[ci_mono_def]) >>
  `len*type_memory_size tv + type_memory_size tv <= cap*type_memory_size tv` by
    simp[array_index_element_end_bound] >>
  `w2n bp+32 <= w2n dw /\
   w2n dw+type_memory_size tv <= w2n bp+32+cap*type_memory_size tv /\
   w2n dw+type_memory_size tv <= s.vs_alloca_next /\ w2n bp+32 <= s.vs_alloca_next` by
    decide_tac >>
  drule_all payload_store_element >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`q`,`Gq`,`tq`] strip_assume_tac)) >>
  `q.vs_alloca_next = s.vs_alloca_next /\ q.vs_allocas = s.vs_allocas` by
    fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  `allocas_from lo q` by
    (qpat_assum `allocas_from lo s` mp_tac >> pure_rewrite_tac[allocas_from_def] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  `ptr_covers G tn p s 32` by
    (fs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  `ptr_covers Gq tq p q 32 /\ lookup_var p q = SOME bp /\
   lookup_var lenvar q = SOME (n2w len) /\ op_taint tq (Var lenvar) = {}` by
    metis_tac[ptr_covers_lookup_frame] >>
  `not_fresh_at a4 p /\ w2n bp+32 <= q.vs_alloca_next` by simp[] >>
  drule_all payload_write_header >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac)) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  suspend "posts"
QED

Resume append_memory_payload_writes_mods[posts]:
  qabbrev_tac `arrsize = 32+cap*type_memory_size tv` >>
  `typed_copy_state_frame a3 (w2n bp) arrsize s q` by
    (irule typed_copy_state_frame_subinterval >> goal_assum (drule_at Any) >>
     simp[Abbr `arrsize`] >> decide_tac) >>
  `typed_copy_state_frame a3 (w2n bp) 32 q t` by
    metis_tac[typed_copy_state_frame_mono] >>
  `typed_copy_state_frame a3 (w2n bp) arrsize q t` by
    (irule typed_copy_state_frame_subinterval >> goal_assum (drule_at Any) >>
     simp[Abbr `arrsize`]) >>
  `typed_copy_state_frame a3 (w2n bp) arrsize s t` by metis_tac[typed_copy_state_frame_trans] >>
  `!i. ~(w2n bp <= i /\ i < w2n bp+32) ==>
       mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 q.vs_memory /\
       (i IN tf.t_mem <=> i IN tq.t_mem)` by
    (rpt strip_tac >> simp[] >> metis_tac[payload_frame_byte]) >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n dw) mem` by
    (match_mp_tac robust_val_in_memory_exterior_frame >>
     qexistsl_tac [`tq.t_mem`,`q.vs_memory`,`{i | w2n bp <= i /\ i < w2n bp+32}`] >>
     simp[] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- (simp[DISJOINT_DEF,EXTENSION] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `typed_copy_state_frame a3 (w2n dw) (type_memory_size tv) s q`
    (mp_then Any irule payload_frame_byte) >>
  decide_tac
QED

Finalise append_memory_payload_writes_mods
