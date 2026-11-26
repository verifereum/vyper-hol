(* Select the conversion suffix with the exact Revert exit. *)
Theory bodyConvertSelectedSuffixRevertMods
Ancestors
  bodyFullConvertSignedOrigin bodyFullConvertDynamicEmpty
  bodyFullConvertBytesWordSuffix bodyPtrTypeBuiltinsBytesWordTypes
  exprSimConvertFromBytes exprSimConvert ptrDiscipline bodyPtrDefs fragGasOriginPtr
  compileEnv exprLowering exprLoweringProps fragExec venomState
  vyperTypeSystem vyperValue vyperState finite_map words arithmetic list

Theorem convert_selected_suffix_revert_mods:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  well_formed_type (get_tenv cx) dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  compile_type_convert (Var z) (mk_convert_op src dst) sa = (out,sb) /\
  not_fresh_at sa z /\ lookup_var z s = SOME a /\
  val_in_memory tv v (w2n a) s.vs_memory /\
  ptr_covers G tn z s capacity /\ 64 <= capacity /\
  w2n a + 64 <= dimword(:256) /\
  mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_inv s /\ w2n a + 64 <= s.vs_alloca_next ==>
  ((!vout. convert_result cx src dst v = INL vout ==>
    ?dtv t Gf tnf.
      evaluate_type (get_tenv cx) dst = SOME dtv /\ value_has_type dtv vout /\
      eval_operand out t = SOME (typed_val_to_w256 dtv vout) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,Gf,tnf)) /\
      state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      op_prov Gf out = NONE /\ op_taint tnf out = {}) /\
   (!exc. convert_result cx src dst v = INR exc ==>
    (?msg. exc = Error (RuntimeError msg)) /\
    ?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `(?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT`
  >- (drule_all signed_convert_origin_path_revert >>
      disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  Q.SUBGOAL_THEN
    `dst = BaseT BoolT \/ (?k. dst = BaseT (UintT k)) \/
     dst = BaseT AddressT \/ (?k. dst = BaseT (BytesT (Fixed k)))` assume_tac
  >- (drule_all bytestring_scalar_type_partition_cases >>
      qpat_x_assum `~((?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `v = BytesV [] \/ v = StringV []`
  >- (drule_all bytes_word_empty_convert_origin_path >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> drule_all dynamic_empty_scalar_convert >> simp[]) >>
  qpat_x_assum `~(v = BytesV [] \/ v = StringV [])`
    (CONJUNCTS_THEN assume_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
  drule_all bytes_word_convert_origin_path_revert >>
  disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)
QED
