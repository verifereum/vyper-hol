(* Code boundaries for the two allocations and two straight instructions
   that initialize concat's result buffer and offset scratch. *)
Theory bodyMemBiConcatPrefix
Ancestors
  bodyMemAggregateAlloc bodyMemEmitOpFrame bodyDeclWordMemory
  exprSimConcatResult fragExec context emitHelper emitHelperProps
  exprLoweringProps loweringHalt compileEnv list rich_list
  fragGasMode fragGasPathMem venomMemProps freshWrites exprSimAlloc

Theorem concat_prefix_code_cuts:
  context$compile_alloc_buffer bsz sa = (buf,s1) /\
  emit_op ADD [buf.buf_operand; Lit 32w] s1 = (d,s2) /\
  context$compile_alloc_buffer 64 s2 = (ob,s3) /\
  emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = (u,s4) /\
  fn_has_code sa s4 func ==>
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func
Proof
  strip_tac >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s2 s3 /\ cs_extends s3 s4` by
    (gvs[contextTheory.compile_alloc_buffer_def, comp_bind_def,
         comp_return_def, emit_op_def, emit_void_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt conj_tac >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends s1 s4 /\ cs_extends s2 s4` by
    metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem concat_prefix_path_mem:
  context$compile_alloc_buffer bsz sa = (buf,s1) /\
  emit_op ADD [buf.buf_operand; Lit 32w] s1 = (d,s2) /\
  context$compile_alloc_buffer 64 s2 = (ob,s3) /\
  emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = (u,s4) /\
  fn_has_code sa s4 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ bsz < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s0 ==>
  ?t B ow binst oinst.
    gas_path_mem ctx func s0 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = s4.cs_current_bb /\
    t.vs_inst_idx = LENGTH s4.cs_current_insts /\
    lookup_var (STRING #"%" (toString sa.cs_next_var)) t = SOME (n2w B) /\
    lookup_var (STRING #"%" (toString (sa.cs_next_var + 1))) t =
      SOME (n2w (B + 32)) /\
    lookup_var (STRING #"%" (toString (sa.cs_next_var + 2))) t = SOME ow /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id = sa.cs_next_id /\ binst.inst_id < s4.cs_next_id /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < s4.cs_next_id /\
    FLOOKUP t.vs_allocas binst.inst_id = SOME (B, bsz) /\
    FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\ B + bsz < dimword (:256) /\
    mload (w2n ow) t = n2w 0 /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
             FLOOKUP t.vs_allocas aid = SOME a) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
       (B + bsz <= b \/ b + len <= B) /\
       (w2n ow + 64 <= b \/ b + len <= w2n ow)) /\
    (!p n. p + n <= w2n ow \/ w2n ow + 64 <= p ==>
       mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    B + bsz <= t.vs_alloca_next /\ w2n ow + 64 <= t.vs_alloca_next
Proof
  strip_tac >>
  drule_all concat_prefix_code_cuts >> strip_tac >>
  qpat_assum `context$compile_alloc_buffer bsz sa = _`
    (mp_then Any mp_tac aggregate_buffer_alloc_counted_mem_any_block) >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`bi`, `bv`, `t1`, `B`] strip_assume_tac) >>
  `step_inst_base (mk_inst s1.cs_next_id ADD
     [buf.buf_operand; Lit 32w] [STRING #"%" (toString s1.cs_next_var)]) t1 =
     OK (update_var (STRING #"%" (toString s1.cs_next_var)) (n2w B + 32w) t1)` by
    (irule step_ADD >> simp[venomStateTheory.eval_operand_def]) >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any (mp_tac o SRULE []) emit_op_word_path_frame_mem) >>
  disch_then drule_all >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_path T ctx func t1 0 (OK t2)` >>
  `~t2.vs_halted /\ t2.vs_current_bb = s2.cs_current_bb /\
   t2.vs_inst_idx = LENGTH s2.cs_current_insts` by
    simp[Abbr `t2`, venomStateTheory.update_var_def] >>
  qpat_assum `context$compile_alloc_buffer 64 s2 = _`
    (mp_then Any mp_tac aggregate_buffer_alloc_counted_mem_any_block) >>
  disch_then (mp_tac o SRULE [wordsTheory.dimword_def]) >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`oi`, `ov`, `t3`, `offbase`] strip_assume_tac) >>
  drule_all concat_prefix_code >> strip_tac >>
  suspend "finish"
QED

Resume concat_prefix_path_mem[finish]:
  `w2n (n2w offbase : bytes32) = offbase` by
    (simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >> decide_tac) >>
  `u = ()` by (Cases_on `u` >> simp[]) >>
  `alloca_inv t3 /\ offbase + 32 <= t3.vs_alloca_next` by
    (fs[stmt_state_rel_def] >> decide_tac) >>
  fs[] >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any mp_tac annassign_word_mstore_path_mem) >>
  disch_then (mp_tac o SRULE [venomStateTheory.eval_operand_def]) >>
  disch_then (qspecl_then [`n2w offbase`, `t3`, `func`, `ctx`] mp_tac) >>
  (impl_tac >- simp[venomStateTheory.eval_operand_def]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func t3 0 (OK t4)` >>
  `gas_path_mem ctx func s0 0 (OK t4)` by
    (fs[gas_marked_path_def] >>
     metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
  suspend "frames"
QED
Resume concat_prefix_path_mem[frames]:
  gvs[] >>
  qabbrev_tac `binst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  qabbrev_tac `oinst = mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 64w]
    [STRING #"%" (toString (sa.cs_next_var + 2))]` >>
  `MEM binst (fn_insts func) /\ MEM oinst (fn_insts func)` by
    (conj_tac >> irule concat_code_mem >> qexistsl_tac [`sa`, `s4`] >>
     simp[Abbr `binst`, Abbr `oinst`]) >>
  `stmt_state_rel ctx func cenv cx es t4` by
    (simp[Abbr `t4`, stmt_state_rel_inst_idx] >>
     irule literal_mstore_state_rel >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`offbase`, `oinst`, `64`] >>
     simp[Abbr `oinst`, venomInstTheory.mk_inst_def] >>
     rpt strip_tac >>
     qpat_x_assum `!name p n. local_region _ _ t2 _ _ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `t2.vs_allocas = t1.vs_allocas /\ t2.vs_alloca_next = t1.vs_alloca_next /\
   t2.vs_memory = t1.vs_memory` by
    simp[Abbr `t2`, venomStateTheory.update_var_def] >>
  `FLOOKUP t3.vs_allocas sa.cs_next_id = SOME (B,bsz)` by metis_tac[] >>
  `regions_disjoint offbase 64 B bsz` by
    (qpat_x_assum `!aid p n. aid < sa.cs_next_id + 2 /\ _ ==> _` irule >>
     qexists_tac `sa.cs_next_id` >> simp[]) >>
  suspend "result"
QED
Resume concat_prefix_path_mem[result]:
  qmatch_asmsub_abbrev_tac `gas_marked_path T ctx func t1 0 (OK t2)` >>
  `!x. not_fresh_at sa x ==> lookup_var x t3 = lookup_var x s0` by
    (rpt strip_tac >>
     `not_fresh_at s2 x` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     `not_fresh_at s1 x` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     simp[]) >>
  `!name p n. local_region cenv es.scopes t3 name p n <=>
              local_region cenv es.scopes s0 name p n` by
    (rpt gen_tac >> irule concat_local_region_vars >> qexists_tac `sa` >> simp[]) >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) t3 = SOME (n2w B) /\
   lookup_var (STRING #"%" (toString (sa.cs_next_var + 1))) t3 =
     SOME (n2w (B + 32))` by
    (`not_fresh_at s2 (STRING #"%" (toString sa.cs_next_var))` by
       simp[not_fresh_at_def] >>
     simp[] >> simp[Abbr `t2`, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_inj, wordsTheory.word_add_n2w]) >>
  qexistsl_tac [`t4`, `B`, `n2w offbase`, `binst`, `oinst`] >>
  simp[Abbr `binst`, Abbr `oinst`, venomInstTheory.mk_inst_def] >>
  suspend "remaining"
QED
Resume concat_prefix_path_mem[remaining]:
  conj_tac >- simp[Abbr `t4`, venomStateTheory.mstore_def] >>
  conj_tac >- (simp[Abbr `t4`, venomStateTheory.mstore_def] >>
    qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
    simp[emit_void_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def,
         comp_ignore_bind_def] >> strip_tac >> gvs[]) >>
  conj_tac >- simp[Abbr `t4`] >>
  conj_tac >- gvs[Abbr `t4`, venomStateTheory.mstore_def, venomStateTheory.lookup_var_def] >>
  conj_tac >- gvs[Abbr `t4`, venomStateTheory.mstore_def, venomStateTheory.lookup_var_def] >>
  conj_tac >- gvs[Abbr `t4`, venomStateTheory.mstore_def, venomStateTheory.lookup_var_def] >>
  conj_tac >- simp[Abbr `t4`, venomStateTheory.mstore_def] >>
  conj_tac >- simp[Abbr `t4`, venomStateTheory.mstore_def] >>
  suspend "disjoint"
QED
Resume concat_prefix_path_mem[disjoint]:
  conj_tac >-
    (rpt gen_tac >>
     `local_region cenv es.scopes t4 name lb lsz <=>
      local_region cenv es.scopes t3 name lb lsz` by
       simp[NoAsms, Abbr `t4`, venomStateTheory.mstore_def, local_region_def,
            venomStateTheory.lookup_var_def] >>
     simp[] >> strip_tac >>
     `local_region cenv es.scopes t2 name lb lsz` by metis_tac[] >>
     qpat_x_assum `!name p n. local_region _ _ s0 _ _ _ ==> _` drule >>
     qpat_x_assum `!name p n. local_region _ _ t2 _ _ _ ==> _` drule >>
     simp[regions_disjoint_def]) >>
  conj_tac >- (fs[regions_disjoint_def] >> decide_tac) >>
  suspend "memory"
QED
Resume concat_prefix_path_mem[memory]:
  conj_tac >-
    (`mload offbase t4 = mload offbase (mstore offbase 0w t3)` by
       simp[NoAsms, Abbr `t4`, venomStateTheory.mload_def] >>
     simp[mload_mstore_same]) >>
  conj_tac >- gvs[Abbr `t4`, venomStateTheory.mstore_def, venomStateTheory.lookup_var_def] >>
  conj_tac >-
    (simp[Abbr `t4`, venomStateTheory.mstore_def] >> metis_tac[]) >>
  suspend "oldalloc"
QED
Resume concat_prefix_path_mem[oldalloc]:
  conj_tac >-
    (rpt strip_tac >>
     `FLOOKUP t2.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
     qpat_x_assum `!aid p n. aid < sa.cs_next_id /\ _ ==> _` drule_all >>
     `aid < sa.cs_next_id + 2` by decide_tac >>
     qpat_x_assum `!aid p n. aid < sa.cs_next_id + 2 /\ _ ==> _` drule_all >>
     simp[regions_disjoint_def]) >>
  conj_tac >-
    (rpt strip_tac >>
     `mem_bytes_at p n t4.vs_memory = mem_bytes_at p n t3.vs_memory` suffices_by simp[] >>
     simp[NoAsms, Abbr `t4`] >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  simp[Abbr `t4`, venomStateTheory.mstore_def] >> decide_tac
QED
Finalise concat_prefix_path_mem
