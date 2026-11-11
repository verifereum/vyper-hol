Theory extRetSemanticResultPtr
Ancestors
  extRetRecursiveStaticLeafPtr extRetFramedChildPtr
  extRetRecursiveResourcePtr extRetRecursiveFramePtr
  entryDecodePlanProps vyperTypeABI vyperABI vyperTyping vyperValue
  valueEncoding compileEnv abiEncoder fragGasPathPtr fragExec
  bodyPtrDefs venomState ptrDiscipline words finite_map arithmetic list

Definition encoder_semantic_framed_result_def:
  encoder_semantic_framed_result env ty v
    D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf <=>
  encoder_framed_child_result D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf /\
  ?av. vyper_to_abi env ty v = SOME av /\
       n = LENGTH (enc (vyper_to_abi_type env ty) av)
End

Theorem encoder_semantic_framed_result_projection:
  encoder_semantic_framed_result env ty v
    D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf ==>
  encoder_framed_child_result D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf
Proof
  simp[encoder_semantic_framed_result_def]
QED

Theorem encoder_semantic_framed_result_bound:
  encoder_semantic_framed_result env ty v
    D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v ==>
  n <= vyper_abi_size_bound env ty
Proof
  rw[encoder_semantic_framed_result_def] >>
  metis_tac[CONJUNCT1 vyper_to_abi_enc_length_bound]
QED

Theorem encoder_semantic_static_copy_counted_ptr:
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
  (?Gf tnf sf. encoder_semantic_framed_result env ty v
    D ctx fn PG sa sb sites q len protected (w2n b) k out k 0
    G tn s Gf tnf sf) /\ k <= vyper_abi_size_bound env ty
Proof
  strip_tac >>
  drule_all (CONJUNCT1 vyper_to_abi_total) >> strip_tac >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = k` by
    metis_tac[CONJUNCT1 vyper_to_abi_static_enc_length] >>
  `k <= vyper_abi_size_bound env ty` by
    metis_tac[CONJUNCT1 vyper_to_abi_enc_length_bound] >>
  simp[] >>
  drule_all encoder_evaluated_copy_resource_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G`, `tnf`, `sf`] >>
  simp[encoder_semantic_framed_result_def, encoder_framed_child_result_def,
       encoder_ambient_frame_def] >>
  metis_tac[]
QED

(* Both NoneTV and the evaluated empty struct use the actual zero-MCOPY
   endpoint.  In particular, no positive coverage or list-identity claim is
   added here: all physical copy/resource premises are retained. *)
Theorem encoder_semantic_zero_copy_counted_ptr:
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  (tv = NoneTV \/ tv = StructTV []) /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy 0) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 0 /\ ptr_covers G tn dst s 0 /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory tv v (w2n a) mem') /\
  encoder_resource ctx fn sites q len protected s ==>
  ?Gf tnf sf. encoder_semantic_framed_result env ty v
    D ctx fn PG sa sb sites q len protected (w2n b) 0 out 0 0
    G tn s Gf tnf sf
Proof
  strip_tac >>
  `0 = type_memory_size tv` by
    (fs[type_memory_size_def]) >>
  `0 < dimword(:256)` by simp[] >>
  drule_all encoder_semantic_static_copy_counted_ptr >> simp[]
QED
