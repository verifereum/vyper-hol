(* Boundary at the actual suffix run, parametrized by an endpoint observation. *)
Theory bodyFullConvertDynamicOriginRule
Ancestors
  bodyFullConvertBytesWordSuffix bodyFullConvertDynamicEmpty bodyFullConvertSignedOrigin
  bodyPtrTypeBuiltinsBytesWordTypes bodyFullConvertScalarFrame
  fragGasOriginPtr exprLowering exprSimConvertFromBytes
  stateFrame[qualified,ignore_grammar]

Definition convert_dynamic_origin_rule_def:
  convert_dynamic_origin_rule P lo explicit ctx fn PG <=>
  !cx src dst tv v z m b out s G tn a capacity n.
    is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
    well_formed_type (get_tenv cx) dst /\
    evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
    compile_type_convert (Var z) (mk_convert_op src dst) m = (out,b) /\
    not_fresh_at m z /\ lookup_var z s = SOME a /\
    val_in_memory tv v (w2n a) s.vs_memory /\
    ptr_covers G tn z s capacity /\ 64 <= capacity /\ w2n a + 64 <= dimword(:256) /\
    mload (w2n a) s = n2w n /\ n <= 32 /\
    (!i. w2n a <= i /\ i < w2n a+32+n ==> i NOTIN tn.t_mem) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code m b fn /\
    ~s.vs_halted /\ s.vs_current_bb = m.cs_current_bb /\
    s.vs_inst_idx = LENGTH m.cs_current_insts /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_inv s /\
    w2n a+64 <= s.vs_alloca_next ==>
    ((!vout. convert_result cx src dst v = INL vout ==>
       ?dtv t Gf tnf.
         evaluate_type (get_tenv cx) dst = SOME dtv /\ value_has_type dtv vout /\
         eval_operand out t = SOME (typed_val_to_w256 dtv vout) /\
         (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
         stateFrame$state_frame t = stateFrame$state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
         t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
         (!p. not_fresh_at m p ==> lookup_var p t = lookup_var p s /\
           FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
         tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
         tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
         op_prov Gf out = NONE /\ op_taint tnf out = {} /\ P m b s (OK t)) /\
     (!exc. convert_result cx src dst v = INR exc ==>
       (?msg. exc = Error (RuntimeError msg)) /\
       ?err t Gf tnf. P m b s (Abort err t) /\
         !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (Abort err t,Gf,tnf)))
End

Theorem convert_dynamic_origin_rule_true:
  convert_dynamic_origin_rule (\m b s r. T) lo explicit ctx fn PG
Proof
  simp_tac std_ss [convert_dynamic_origin_rule_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `(?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT`
  >- (drule_all signed_convert_origin_path >> simp[]) >>
  Q.SUBGOAL_THEN
    `dst = BaseT BoolT \/ (?k. dst = BaseT (UintT k)) \/
     dst = BaseT AddressT \/ (?k. dst = BaseT (BytesT (Fixed k)))` assume_tac
  >- (drule_all bytestring_scalar_type_partition_cases >>
      qpat_x_assum `~((?k. dst = _) \/ _)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  Cases_on `v = BytesV [] \/ v = StringV []`
  >- (drule_all bytes_word_empty_convert_origin_path >> simp[]) >>
  `v <> BytesV [] /\ v <> StringV []` by gvs[] >>
  drule_all bytes_word_convert_origin_path >> simp[]
QED
