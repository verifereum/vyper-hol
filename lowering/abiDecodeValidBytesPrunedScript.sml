(* Join the successful bounded MLOAD bytes phases before variable replay. *)
Theory abiDecodeValidBytesPruned
Ancestors
  abiDecodeValidBytesPrefix abiDecodeValidBytesTail abiDecoderValidBytes
  abiDecoderBytesPrefix abiDecoderBytesPhases abiDecoderContract
  abiDecodePtrMemberFrame assignTuplePtrLocalBytesCopy fragExecMem fragGasSeqPtr
  bodyPtrDefs ptrDiscipline loweringStateRelDefs valueCopy
  emitHelperProps exprLoweringProps compileEnv freshWrites
  venomState venomExecSemantics venomInst vyperTypeABI contractABI
  words list pred_set finite_map arithmetic

Theorem abi_decode_valid_bytes_pruned_certificate:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) sa = ((),en) /\
  abi_decoder_valid_bytes_pre n at bs payload sa pos (Var dst)
    MLOAD (Var src) hi B p d s /\
  run_inst_seq (emitted_insts sa en) s = OK raw /\
  hi <> Lit 0w /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  (!x. MEM (Var x) [pos;hi] ==> not_fresh_at sa x) /\
  abi_decode_ptr_window G tn s src (n2w B) L /\
  ptr_covers G tn dst s cap /\ eval_operand hi s = SOME (n2w L) /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  32+contractABI$ceil32 n <= cap /\
  B+L < dimword(:256) /\ d+cap < dimword(:256) /\
  B+L <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
  regions_disjoint B L d cap ==>
  ?Gf tf.
    run_inst_seq_mem_ok (emitted_insts sa en) s /\
    inst_seq_ptr
      <| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>
      0 ctx fn PG G tn (emitted_insts sa en) s Gf tf /\
    abi_decode_ptr_window Gf tf raw src (n2w B) L /\
    ptr_covers Gf tf dst raw cap /\
    abi_decode_ptr_window Gf tf raw dst (n2w d) (32+contractABI$ceil32 (LENGTH payload)) /\
    (!x. not_fresh_at sa x ==> lookup_var x raw = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    mem_agree_outside {i | d <= i /\ i < d+(32+contractABI$ceil32 (LENGTH payload))}
      raw.vs_memory s.vs_memory /\
    (!i. ~(d <= i /\ i < d+(32+contractABI$ceil32 (LENGTH payload))) ==>
          (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_bytes_facts >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `L < dimword(:256)` by decide_tac >>
  `p+32+LENGTH payload <= L` by
    (qpat_x_assum `hi = Lit 0w \/ ?h. _` mp_tac >> simp[n2w_11] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  qhdtm_assum `abi_decoder_valid_bytes_pre`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_decoder_valid_bytes_pre_def]) >>
  `lookup_var dst s = SOME (n2w d)` by fs[eval_operand_def] >>
  `32+contractABI$ceil32 (LENGTH payload) <= cap` by
    (drule ceil32_mono >> decide_tac) >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ _ sa = ((),en)` >>
  Cases_on `abi_decode_bytes_position_prefix pos MLOAD (Var src) hi n sa` >>
  rename1 `_ = (ac,cm)` >> Cases_on `ac` >> rename1 `_ = ((addr,cnt),cm)` >>
  `abi_decode_bytes_runtime_tail (Var dst) addr cnt cm = ((),en)` by
    fs[abi_decode_bytes_prefix_phases, comp_bind_def] >>
  drule_all abi_decode_valid_bytes_prefix_certificate >>
  disch_then (qspecl_then
    [`fn`, `PG`, `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |> `]
    strip_assume_tac) >>
  qpat_x_assum `addr = Var _` SUBST_ALL_TAC >>
  drule abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  `B+L <= m.vs_alloca_next /\ d+cap <= m.vs_alloca_next` by simp[] >>
  drule_all abi_decode_valid_bytes_tail_certificate >>
  disch_then (qspecl_then
    [`fn`, `PG`, `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |> `]
    strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cm en)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `emitted_insts sa en = emitted_insts sa cm ++ emitted_insts cm en` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `m.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa cm) /\
   t.vs_inst_idx = m.vs_inst_idx + LENGTH (emitted_insts cm en)` by
    (fs[inst_extends_def] >> simp[]) >>
  drule_all inst_seq_ptr_append_normalized >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `run_inst_seq_mem_ok (emitted_insts sa en) s` by
    (simp[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  `raw = t with vs_inst_idx := s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa en) s = OK raw` mp_tac >> simp[]) >>
  `sa.cs_next_var <= cm.cs_next_var` by
    (drule_all abi_decode_bytes_position_prefix_shape >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at cm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at cm x ==> _` (qspec_then `x` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!x. lookup_var x raw = lookup_var x t` by simp[lookup_var_def] >>
  `!x n. ptr_covers Gf tf x raw n <=> ptr_covers Gf tf x t n` by
    simp[ptr_covers_def, lookup_var_def] >>
  `!x b n. abi_decode_ptr_window Gf tf raw x b n <=>
            abi_decode_ptr_window Gf tf t x b n` by
    simp[abi_decode_ptr_window_def, ptr_covers_def, lookup_var_def] >>
  qexistsl [`Gf`,`tf`] >> simp[IgnAsm `raw = _`] >>
  qpat_x_assum `mem_agree_outside _ t.vs_memory m.vs_memory` mp_tac >> simp[]
QED
