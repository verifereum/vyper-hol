(* Actual singleton dynamic bytes encoder: finite compiler cuts. *)
Theory extRetAbiSingletonWrapperPtr
Ancestors
  extRetAbiSingletonCountedPtr abiEncoderComplexCode abiEncoderComplexPrefix
  abiEncoderMemberCode abiEncoderChildCode abiEncoderAddressReach
  extRetBulkCopyCountedPtr extRetCountedPtr fragExec fragGasPathPtr fragGasSeqPtr
  emitHelperProps exprLoweringProps compileEnv emitHelper exprLowering
  abiEncoder abiBuiltinAllocation bodyPtrDefs ptrDiscipline venomState
  words finite_map pred_set arithmetic list rich_list

Theorem abi_singleton_wrapper_context:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (AbiComplex [(AbiBytestring maxlen,32,cap,T)]) sa = (out,sb) /\
  fn_has_code sa sb fn ==>
  ?ip elem sc sd se ignored.
    abi_encode_complex_prefix [(AbiBytestring maxlen,32,cap,T)] sa = (Var ip,sc) /\
    emit_op ADD [Var src;Lit 0w] sc = (Var elem,sd) /\
    compile_abi_encode_child (Var dst) (Var elem) (AbiBytestring maxlen) T 0
      (Var ip) sd = (ignored,se) /\
    emit_op MLOAD [Var ip] se = (out,sb) /\
    fn_has_code sa sc fn /\ fn_has_code sc sd fn /\
    fn_has_code sd se fn /\ fn_has_code se sb fn /\
    not_fresh_at sc ip /\ not_fresh_at sd ip /\ not_fresh_at sd elem /\
    not_fresh_at se ip /\
    (!v. not_fresh_at sa v ==> not_fresh_at sc v) /\
    (!v. not_fresh_at sc v ==> not_fresh_at sd v) /\
    (!v. not_fresh_at sd v ==> not_fresh_at se v)
Proof
  strip_tac >>
  `EXISTS (\(_,_,_,dyn). dyn) [(AbiBytestring maxlen,32,cap,T)]` by simp[] >>
  drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `cs_extends sa prepared` by
    (irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends prepared sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa prepared fn /\ fn_has_code prepared middle fn /\
   fn_has_code middle sb fn` by metis_tac[fn_has_code_split] >>
  drule_all abi_encoder_member_cons_context >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >> gvs[] >>
  `?elem. elem_src = Var elem /\ not_fresh_at prepared' elem` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[not_fresh_at_def]) >>
  gvs[] >>
  simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac
QED
