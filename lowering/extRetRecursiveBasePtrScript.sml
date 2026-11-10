Theory extRetRecursiveBasePtr
Ancestors
  extRetRecursiveFramePtr extRetRecursiveResourcePtr
  extRetEvaluatedStaticChildPtr extRetEvaluatedZeroPtr
  bodyPtrDefs valueEncodingProps abiEncoder exprLowering vyperValue
  vyperTyping vyperTypeABI valueEncoding compileEnv fragExec fragGasPathPtr
  venomState ptrDiscipline words pred_set arithmetic finite_map

Theorem encoder_empty_child_resource_ptr:
  compile_abi_encode_to_buf dst src (AbiComplex []) sa = (out,sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  encoder_resource ctx fn sites q len protected s ==>
  ?sf Gf tnf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = s /\ Gf = G /\ tnf = tn /\ sb = sa /\ out = Lit 0w /\
    eval_operand out sf = SOME 0w /\ op_taint tnf out = {} /\
    encoder_resource ctx fn sites q len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf b 0)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf b 0 ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule_all ext_ret_empty_child_endpoint_ptr >> strip_tac >>
  qexistsl_tac [`s`, `G`, `tn`] >> metis_tac[mem_agree_outside_def]
QED

Theorem encoder_zero_copy_resource_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy 0) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  encoder_resource ctx fn sites q len protected s ==>
  ?sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) 0 s).vs_memory /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME 0w /\ op_taint tn out = {} /\
    (!p. lookup_var p sf = lookup_var p s) /\
    encoder_resource ctx fn sites q len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf (w2n b) 0)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf (w2n b) 0 ==>
      (i IN tn.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule_all ext_ret_zero_copy_child_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexists_tac `sf` >> simp[] >>
  conj_tac >- (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED

Theorem encoder_static_copy_resource_ptr:
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ k = type_memory_size tv /\
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy k) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\ k < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory tv v (w2n a) mem') /\
  encoder_resource ctx fn sites q len protected s ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w k) /\ op_taint tnf out = {} /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) k s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+k} /\
    (!i. w2n b <= i /\ i < w2n b+k ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf (w2n b) k)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf (w2n b) k ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all ext_ret_evaluated_static_copy_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`tnf`, `sf`] >> simp[] >>
  conj_tac >- (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac >-
    (irule encoder_memory_frame_mono >>
     qexists_tac `{i | w2n b <= i /\ i < w2n b+k}` >>
     gvs[encoder_write_envelope_def, SUBSET_DEF]) >>
  simp[encoder_write_envelope_def] >> rpt strip_tac >> simp[]
QED

(* A real mixed-layout execution, rather than an ABI-plan-domain premise. *)
Theorem encoder_nested_none_resource_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (type_to_abi_enc_info ce.ce_struct_fields ce
      (TupleT [NoneT; BaseT (UintT 256)])) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  value_has_type (TupleTV [NoneTV; BaseTV (UintT 256)]) v /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (TupleTV [NoneTV; BaseTV (UintT 256)]) v (w2n a) mem') /\
  encoder_resource ctx fn sites q len protected s ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME 32w /\ op_taint tnf out = {} /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf (w2n b) 32)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf (w2n b) 32 ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `evaluate_type FEMPTY (TupleT [NoneT; BaseT (UintT 256)]) =
     SOME (TupleTV [NoneTV; BaseTV (UintT 256)]) /\
   type_memory_size (TupleTV [NoneTV; BaseTV (UintT 256)]) = 32 /\
   ~is_dynamic (vyper_to_abi_type FEMPTY (TupleT [NoneT; BaseT (UintT 256)])) /\
   type_to_abi_enc_info ce.ce_struct_fields ce
     (TupleT [NoneT; BaseT (UintT 256)]) = AbiCopy 32 /\
   32 < dimword(:256)` by
    (EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC) >>
  fs[] >>
  mp_tac (encoder_static_copy_resource_ptr |> SPEC_ALL |>
    Q.INST [`env` |-> `FEMPTY`, `k` |-> `32`,
            `ty` |-> `TupleT [NoneT; BaseT (UintT 256)]`,
            `tv` |-> `TupleTV [NoneTV; BaseTV (UintT 256)]`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`tnf`, `sf`] >> simp[]
QED
