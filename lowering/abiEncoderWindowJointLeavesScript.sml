Theory abiEncoderWindowJointLeaves
Ancestors
  exprSimAbiEncodeExecFrame abiEncoderWindowLeaves abiEncoderWindow
  valueEncodingProofs exprLoweringProps abiEncoderExtendSim
  abiEncoderRegisteredEffect abiEncoderWrites abiEncoderInputFrame
  abiEncoderMemory abiEncoderPrimitiveEffect valueEncodingProps
  abiEncoderReentryLeaves emitHelperProps emitHelper
  abiEncoderWindowContract abiEncoderInputFrame representationCleanPtr
  wordLoadStorePtr fragGasSeqPtr bodyPtrDefs ptrCoverage ptrSafetyTransport
  ghostPcTransportPtr compileEnv contextCodegenRel ptrSafeRun ptrDiscipline
  venomExecSemantics venomState venomInst words list arithmetic finite_map

Theorem window_word_joint_path:
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord st = (out,en) /\
  eval_operand (Var src) s = SOME (n2w sb) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  not_fresh_at st src /\ not_fresh_at st dst /\
  (!i. sb <= i /\ i < sb + 32 ==> i NOTIN tn.t_mem) /\
  sb + 32 <= s.vs_alloca_next /\ d + 32 <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?G' tn'.
    tn'.t_mem = tn.t_mem DIFF {i | d <= i /\ i < d + 32} /\
    (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK ((mstore d (mload sb s)
        (update_var (STRING #"%" (toString st.cs_next_var)) (mload sb s) s))
        with vs_inst_idx := LENGTH en.cs_current_insts),G',tn')
Proof
  strip_tac >>
  drule abi_encode_word_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `inst_extends st loaded_st /\ inst_extends loaded_st en` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts st en = emitted_insts st loaded_st ++ emitted_insts loaded_st en` by
    metis_tac[emitted_insts_append] >>
  qabbrev_tac `tmp = STRING #"%" (toString st.cs_next_var)` >>
  `!x. not_fresh_at st x ==> tmp <> x` by
    (simp[Abbr `tmp`, loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `tmp <> dst` by metis_tac[] >>
  `sb < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  qabbrev_tac `s1 = update_var tmp (mload sb s) s` >>
  qabbrev_tac `ld = mk_inst st.cs_next_id MLOAD [Var src] [tmp]` >>
  qabbrev_tac `wr = mk_inst (st.cs_next_id + 1) MSTORE [Var dst; Var tmp] []` >>
  qabbrev_tac `G1 = step_prov PG G ld s1` >>
  qabbrev_tac `tn1 = step_taint ld s s1 tn` >>
  `op_taint tn1 (Var tmp) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `tn1`, Abbr `ld`, Abbr `s1`] >>
     qpat_assum `eval_operand (Var src) s = _` (mp_then Any mp_tac mload_ghost_clean) >>
     simp[] >> metis_tac[]) >>
  `lookup_var dst s1 = SOME (n2w d) /\
   eval_operand (Var tmp) s1 = SOME (mload sb s)` by
    (simp[Abbr `s1`, update_var_def, lookup_var_def, eval_operand_def,
          FLOOKUP_UPDATE] >> gvs[eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `s2 = mstore d (mload sb s) s1` >>
  qabbrev_tac `G2 = step_prov PG G1 wr s2` >>
  qabbrev_tac `tn2 = step_taint wr s1 s2 tn1` >>
  `G2 = G1 /\ tn2.t_var = tn1.t_var /\
   tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
   tn2.t_mem = tn1.t_mem DIFF {i | d <= i /\ i < d + 32}` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `wr`, Abbr `s2`] >>
     qpat_assum `lookup_var dst s1 = _` (mp_then Any mp_tac mstore_ghost_frame) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`G2`, `tn2`] >>
  conj_tac >- simp[] >>
  conj_tac >-
    (rpt strip_tac >> `tmp <> x` by metis_tac[] >>
     simp[op_taint_def, Abbr `G1`, Abbr `tn1`, Abbr `ld`,
       step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  simp[] >>
  conj_tac >-
    simp[Abbr `tn2`, Abbr `tn1`, Abbr `wr`, Abbr `ld`,
      step_taint_def, imm_taint_def, mk_inst_def, step_writes_def] >>
  `ptr_covers G1 tn1 dst s1 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `ld`, Abbr `s1`] >>
     mp_tac (Q.GENL [`PG`,`G`,`tn`,`s`,`id`,`src`,`tmp`,`dst`,`n`]
       (Q.INST [`a` |-> `(n2w sb : 256 word)`]
         (SPEC_ALL (Q.INST_TYPE [`:'a` |-> `:256`] mload_preserves_ptr_covers)))) >>
     simp[] >> metis_tac[]) >>
  `step_inst_base ld s = OK s1` by
    (simp[Abbr `ld`, Abbr `s1`, mk_inst_def, step_inst_base_opcode_eqs,
       exec_read1_def]) >>
  `step_inst_base wr s1 = OK s2` by
    (simp[Abbr `wr`, Abbr `s2`, mk_inst_def, step_inst_base_opcode_eqs,
       exec_write2_def, eval_operand_def]) >>
  `run_inst_seq [ld;wr] s = OK s2` by simp[run_inst_seq_def] >>
  `emitted_insts st en = [ld;wr]` by
    simp[Abbr `ld`, Abbr `wr`] >>
  `en.cs_current_insts = st.cs_current_insts ++ [ld;wr]` by
    simp[Abbr `ld`, Abbr `wr`] >>
  `en.cs_current_bb = st.cs_current_bb` by
    (drule window_word_run >> simp[] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX [ld;wr] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code st en func` mp_tac >>
     pure_rewrite_tac[fragExecTheory.fn_has_code_def] >> strip_tac >>
     qexists_tac `bb` >> conj_tac >- metis_tac[] >>
     qpat_x_assum `isPREFIX _ _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     simp[DROP_APPEND] >> metis_tac[]) >>
  `s.vs_inst_idx + 2 = LENGTH en.cs_current_insts` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [ld;wr] /\
   FILTER (\i. i.inst_opcode = GAS) [ld;wr] = []` by
    simp[Abbr `ld`, Abbr `wr`, mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok [ld;wr] s` by
    (simp[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
     simp[Abbr `ld`, Abbr `wr`, unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, eval_operand_def, Abbr `s1`, update_var_def] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  gen_tac >>
  `inst_seq_ptr D lo ctx func PG G tn [ld;wr] s G2 tn2` by
    (simp[inst_seq_ptr_def] >> conj_tac >-
      (irule ptr_inst_ok_lower_bound_transport >>
       conj_tac >- simp[] >> qexists_tac `0` >>
       simp[Abbr `ld`, ptr_inst_ok_mload]) >>
     `allocas_from lo (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
       (simp[Abbr `s1`, update_var_def, allocas_from_def] >>
        metis_tac[allocas_from_def]) >>
     conj_tac >-
      (irule ptr_inst_ok_lower_bound_transport >>
       conj_tac >- metis_tac[] >> qexists_tac `0` >> simp[] >>
       simp[Abbr `wr`] >>
       irule fragExecPtrTheory.ptr_inst_ok_mstore >> simp[]) >>
     `step_inst_base wr (s1 with vs_inst_idx := SUC s.vs_inst_idx) =
        OK (s2 with vs_inst_idx := SUC s.vs_inst_idx)` by
       (simp[instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def,
          Abbr `wr`, mk_inst_def, is_terminator_def]) >>
     qpat_x_assum `step_inst_base wr (_ with vs_inst_idx := _) = _` mp_tac >>
     simp[] >> strip_tac >>
     simp[Abbr `G2`, Abbr `tn2`]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  simp[Abbr `s2`, Abbr `s1`, Abbr `tmp`]
QED

(* Word constructor of the approved joint ABI-window contract. *)
Theorem compile_abi_encode_to_buf_word_window_joint:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,en) /\
  abi_encoder_admissible AbiPrimWord /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input AbiPrimWord at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==>
    sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (contractABI$enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH (contractABI$enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (contractABI$enc at av) ==>
    ?p. dst = Var p /\
      ptr_covers G tn p s (LENGTH (contractABI$enc at av))) /\
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH (contractABI$enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    window_strong_result ctx func st en out at av d s t /\
    abi_encode_exec_frame func s t /\
    op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH (contractABI$enc at av) ==>
      i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH (contractABI$enc at av) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  `abi_encoder_window_input AbiPrimWord at av sb cap s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `32 <= cap /\ mem_bytes_at sb 32 s.vs_memory = enc at av` by
    fs[abi_encoder_window_word_iff] >>
  `LENGTH (enc at av) = 32` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `!i. sb <= i /\ i < sb + 32 ==> i NOTIN tn.t_mem` by
    (qspecl_then [`tn.t_mem`, `s.vs_memory`, `sb`, `32`, `enc at av`]
       mp_tac robust_mem_bytes_at_clean >>
     impl_tac >- metis_tac[abi_encoder_window_word_iff] >> simp[]) >>
  `0 < cap` by decide_tac >>
  `abi_encoder_window_pre ctx func st en dst src AbiPrimWord at av sb cap d s` by
    (pure_rewrite_tac[abi_encoder_window_pre_def] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (`sb + cap <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `!x. dst = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all window_word_run >> strip_tac >>
  `?sp. src = Var sp /\ ptr_covers G tn sp s cap` by metis_tac[] >>
  `?dp. dst = Var dp /\ ptr_covers G tn dp s 32` by
    (qpat_x_assum `0 < LENGTH _ ==> _` mp_tac >> simp[]) >>
  `ptr_covers G tn sp s 32` by
    (qpat_assum `ptr_covers G tn sp s cap` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  `sb + 32 <= s.vs_alloca_next /\ d + 32 <= s.vs_alloca_next` by
    ( `sb + cap <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  qpat_x_assum `src = Var sp` SUBST_ALL_TAC >>
  qpat_x_assum `dst = Var dp` SUBST_ALL_TAC >>
  `not_fresh_at st sp /\ not_fresh_at st dp` by metis_tac[] >>
  drule_all window_word_joint_path >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  drule_all window_word_strong_endpoint >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `G'`, `tn'`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qpat_x_assum `t = _` SUBST1_TAC >>
     rewrite_tac[abi_encode_exec_frame_inst_idx] >>
     irule abi_encode_exec_frame_trans >>
     qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (mload sb s) s` >>
     conj_tac >-
       simp_tac (srw_ss()) [abi_encode_exec_frame_def, pending_alloca_size_def,
         update_var_def, exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def] >>
     rewrite_tac[abi_encode_exec_frame_mstore]) >>
  conj_tac >- (qpat_x_assum `out = _` SUBST1_TAC >> simp_tac (srw_ss()) [op_taint_def]) >>
  conj_tac >- (qpat_x_assum `out = _` SUBST1_TAC >> simp_tac (srw_ss()) []) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `tn'.t_mem = _` SUBST_ALL_TAC >>
    qpat_x_assum `i IN _ DIFF _` mp_tac >>
    simp_tac std_ss [pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
    qpat_x_assum `LENGTH (enc at av) = 32` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
    metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `tn'.t_mem = _` SUBST_ALL_TAC >>
    simp_tac std_ss [pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
    metis_tac[LESS_LESS_EQ_TRANS, LESS_EQ_ANTISYM]) >>
  rpt conj_tac >> metis_tac[]
QED

(* Copy constructor of the approved joint ABI-window contract. *)
Theorem compile_abi_encode_to_buf_copy_window_joint:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,en) /\
  abi_encoder_admissible (AbiCopy sz) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input (AbiCopy sz) at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==>
    sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (contractABI$enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH (contractABI$enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (contractABI$enc at av) ==>
    ?p. dst = Var p /\
      ptr_covers G tn p s (LENGTH (contractABI$enc at av))) /\
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH (contractABI$enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    window_strong_result ctx func st en out at av d s t /\
    abi_encode_exec_frame func s t /\
    op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH (contractABI$enc at av) ==>
      i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH (contractABI$enc at av) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  cheat
QED
