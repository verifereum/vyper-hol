(* Uniform composition of the header and normalized payload certificates. *)
Theory bodyFullConvertBytesWordSuffix
Ancestors
  typeBuiltinPrereqs
  bodyFullConvertBytesWordPrefix bodyFullConvertBytesWordNormalize
  bodyFullConvertBytesWordContinuation
  bodyPtrSignedConvertClamp bodyPtrSignedConvertBool bodyPtrSignedConvertScalarOps
  ptrDiscipline instIdxIndep instSeqPtrLo fragGasSeqPtr emitHelperProps ASCIInumbers
  bodyPtrTypeBuiltinsBytesWordParts bodyPtrTypeBuiltinsBytesWordTypes
  exprSimConvertFromBytes fragGasOriginPtr fragGasCopyLoop compileEnv exprLowering
  builtinConvertPrefix exprSimConvert vyperTypeConversions vyperValueOperation
  bodyPtrSignedConvertSourceFixed bodyPtrSignedConvertUnsignedCompose
  reasonCopySourcePtr instSeqComposePtr
  bodyPtrSignedConvertUnsignedLoad bodyPtrDefs fragExec venomState
  venomInst venomExecSemantics finite_map words arithmetic exprLoweringProps list varsExt

Theorem bytes_word_loader_run_actual:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ lookup_var src s = SOME a ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t
Proof
  strip_tac >>
  `eval_operand (Var src) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  drule_at (Pat `load_bytestring_as_word _ _ _ = _`) load_bytestring_as_word_exec >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (drule_all unsigned_loader_shape_fresh >> strip_tac >>
     simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def] >> metis_tac[]
QED

Theorem bytes_word_conversion_run_actual:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type (get_tenv cx) dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  compile_type_convert (Var z) (mk_convert_op src dst) sa = (out,sb) /\
  not_fresh_at sa z /\ lookup_var z s = SOME a /\
  w2n a+32 < dimword(:256) /\ val_in_memory tv v (w2n a) s.vs_memory ==>
  case convert_result cx src dst v of
    INL vout => ?dtv t. evaluate_type (get_tenv cx) dst = SOME dtv /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (typed_val_to_w256 dtv vout)
  | INR exc => (?msg. exc = Error (RuntimeError msg)) /\
      ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  `eval_operand (Var z) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `val_in_memory tv v (w2n a) (drop_fresh sa s).vs_memory` by
    simp[drop_fresh_def] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `dynamic_straight_fresh (compile_type_convert (Var z) (mk_convert_op src dst))` by
    (irule dynamic_scalar_straight_read_fresh >> simp[]) >>
  `dynamic_writes_fresh sa (emitted_insts sa sb)` by
    metis_tac[dynamic_straight_fresh_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (drule dynamic_writes_fresh_path_opcodes >> simp[EVERY_MEM] >> metis_tac[]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  drule_at (Pat `compile_type_convert _ _ _ = _`) dynamic_scalar_run_exact >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `well_formed_type _ _`)) >>
  disch_then (qspecl_then [`convert_result cx src dst v`,`cx`] mp_tac) >>
  simp[] >> Cases_on `convert_result cx src dst v` >> simp[] >> strip_tac >>
  gvs[vars_ext_result_def, vars_ext_def] >>
  metis_tac[eval_operand_vars_ext, optionTheory.NOT_NONE_SOME]
QED

Theorem bytes_word_loader_fixed_frame:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
  64 <= capacity /\ w2n a + 64 <= dimword(:256) /\
  mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?HG th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := q) HG th) /\
    op_prov HG out = NONE /\ op_taint th out = {} /\
    op_prov HG bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-n))) /\
    t = s with vs_vars := t.vs_vars /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP HG p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all unsigned_loader_shape_fresh >> strip_tac >>
  `ptr_covers G tn src s 64` by (irule ptr_covers_mono >> metis_tac[]) >>
  `src <> len` by fs[] >>
  drule_all bodyPtrSignedConvertSourceFixedTheory.bytestring_source_run >>
  disch_then (qspecl_then [`sa.cs_next_id+1`,`sa.cs_next_id`,`dp`] assume_tac) >>
  qabbrev_tac `u = update_var dp (a+32w) (update_var len (mload (w2n a) s) s)` >>
  `ALL_DISTINCT [src;len;dp] /\
   (!x. w2n a <= x /\ x < w2n a+32 ==> x NOTIN tn.t_mem)` by
    (conj_tac >- fs[] >> gen_tac >> disch_then strip_assume_tac >>
     qpat_x_assum `!x. _ ==> x NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all bytes_word_prefix_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  `ALL_DISTINCT [len;dp;data;sub;shift;dst]` by fs[] >>
  `w2n (a+32w) = w2n a+32` by
    (simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `!x. w2n (a+32w) <= x /\ x < w2n (a+32w)+n ==> x NOTIN tn1.t_mem` by
    (simp[] >> gen_tac >> disch_then strip_assume_tac >>
     qpat_x_assum `!x. _ /\ x < w2n a+32+n ==> _` irule >> decide_tac) >>
  `run_inst_seq [mk_inst (sa.cs_next_id+2) MLOAD [Var dp] [data];
    mk_inst (sa.cs_next_id+3) SUB [Lit 32w;Var len] [sub];
    mk_inst (sa.cs_next_id+4) MUL [Var sub;Lit 8w] [shift];
    mk_inst (sa.cs_next_id+5) SHR [Var shift;Var data] [dst]] u = OK t` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `[mk_inst (sa.cs_next_id+2) MLOAD [Var dp] [data];
       mk_inst (sa.cs_next_id+3) SUB [Lit 32w;Var len] [sub];
       mk_inst (sa.cs_next_id+4) MUL [Var sub;Lit 8w] [shift];
       mk_inst (sa.cs_next_id+5) SHR [Var shift;Var data] [dst]]` mp_tac) >> fs[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`allocas_below_fmp u <=> allocas_below_fmp s` by
       (qpat_assum `u = s with vs_vars := _` SUBST1_TAC >>
        simp[allocas_below_fmp_def]) >>
     qpat_assum `allocas_below_fmp u <=> allocas_below_fmp s`
       (fn th => PURE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all bytes_word_normalize_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`]
    (qx_choose_then `HG` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`HG`,`th`] >>
  conj_tac
  >- (gen_tac >> simp[] >>
      irule (SRULE [APPEND] (Q.INST [`xs` |->
        `[mk_inst sa.cs_next_id MLOAD [Var src] [len];
          mk_inst (sa.cs_next_id+1) ADD [Var src;Lit 32w] [dp]]`]
        inst_seq_ptr_uniform_append)) >>
      simp[is_terminator_def] >> qexistsl_tac [`G1`,`tn1`] >> simp[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `t = u with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
     qpat_x_assum `u = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `~MEM p [len;dp] /\ ~MEM p [data;sub;shift;dst]` by
    (fs[] >> metis_tac[]) >> metis_tac[]
QED

Theorem bytes_word_convert_origin_path_selected:
  is_bytestring_type src /\ valid_conversion src dst /\
  (dst = BaseT BoolT \/ (?k. dst = BaseT (UintT k)) \/
   dst = BaseT AddressT \/ (?k. dst = BaseT (BytesT (Fixed k)))) /\
  well_formed_type (get_tenv cx) dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  (v <> BytesV [] /\ v <> StringV []) /\
  compile_type_convert (Var z) (mk_convert_op src dst) sa = (out,sb) /\
  not_fresh_at sa z /\ lookup_var z s = SOME a /\
  val_in_memory tv v (w2n a) s.vs_memory /\
  ptr_covers G tn z s capacity /\ 64 <= capacity /\
  w2n a + 64 <= dimword(:256) /\
  mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa sb fn /\ ~s.vs_halted /\
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
      op_prov Gf out = NONE /\ op_taint tnf out = {} /\
      (?raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\
             t = (raw with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))) /\
   (!exc. convert_result cx src dst v = INR exc ==>
    (?msg. exc = Error (RuntimeError msg)) /\
    ?t Gf tnf.
      (?raw. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort raw) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (Abort Revert_abort t,Gf,tnf))))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `~is_bytestring_type dst` by
    (gvs[is_bytestring_type_def] >> metis_tac[]) >>
  `w2n a+32 < dimword(:256)` by decide_tac >>
  drule_at (Pat `compile_type_convert _ _ _ = _`) bytes_word_convert_parts >>
  (impl_tac >-
    (drule_all bytestring_scalar_type_partition_cases >> strip_tac >>
     gvs[mk_convert_op_def] >> metis_tac[])) >> strip_tac >>
  `eval_operand (Var z) s = SOME a` by simp[eval_operand_def] >>
  drule_all bytes_word_loader_run_actual >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule_all bytes_word_loader_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`allocas_below_fmp u <=> allocas_below_fmp s` by
       (qpat_assum `u = s with vs_vars := _` SUBST1_TAC >>
        simp[allocas_below_fmp_def]) >>
     qpat_assum `allocas_below_fmp u <=> allocas_below_fmp s`
       (fn th => PURE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  `dynamic_straight_fresh (compile_type_convert (Var z) (mk_convert_op src dst))` by
    (irule dynamic_scalar_straight_read_fresh >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   dynamic_writes_fresh sa (emitted_insts sa sb)` by
    metis_tac[dynamic_straight_fresh_def] >>
  drule_all dynamic_code_prefix >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule convert_dynamic_scalar_mem_ok >> simp[] >>
     goal_assum (drule_at (Pat `compile_type_convert _ _ _ = _`)) >>
     qexists_tac `a` >> simp[] >> metis_tac[]) >>
  `~((?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT)` by
    (qpat_x_assum `dst = _ \/ _` strip_assume_tac >> gvs[]) >>
  drule_all bytestring_scalar_unsigned_convert_op >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  Q.SUBGOAL_THEN
    `(compile_type_convert word ConvToBool sm = (out,sb) \/
      (?b. compile_int_clamp F b word sm = (out,sb)) \/
      (out = word /\ sb = sm) \/ emit_op SHL [bits;word] sm = (out,sb))`
    assume_tac
  >- (qpat_x_assum `mk_convert_op src dst = _ \/ _` strip_assume_tac >>
      metis_tac[]) >>
  `inst_extends sa sm` by metis_tac[inst_extends_load_bytestring_as_word] >>
  `inst_extends sm sb` by
    (qpat_x_assum `compile_type_convert word ConvToBool sm = _ \/ _`
      strip_assume_tac
     >- (mp_tac (Q.SPEC `word` straight_fresh_convert) >>
         simp[freshWritesTheory.straight_fresh_def, inst_extends_def] >> metis_tac[])
     >- metis_tac[inst_extends_compile_int_clamp]
     >- gvs[inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  conj_tac >- suspend "success" >> suspend "abort"
QED

Resume bytes_word_convert_origin_path_selected[success]:
  rpt strip_tac >> drule_all bytes_word_conversion_run_actual >>
  qpat_assum `convert_result cx src dst v = INL vout`
    (fn th => simp_tac std_ss [th]) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts sa sb) s = OK sf` >>
  `src <> BaseT AddressT` by
    (strip_tac >> qpat_x_assum `is_bytestring_type src` mp_tac >> simp[is_bytestring_type_def]) >>
  `evaluate_convert (get_tenv cx) v dst = INL vout` by
    (qpat_x_assum `convert_result cx src dst v = INL vout` mp_tac >>
     simp[convert_result_def, evaluate_convert_from_not_address_bytes, AllCaseEqs()]) >>
  `value_has_type dtv vout` by (drule_all evaluate_convert_well_typed >> simp[]) >>
  drule_all dynamic_run_read_fresh >> strip_tac >>
  `run_inst_seq (emitted_insts sm sb) u = OK sf` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK u`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
     metis_tac[]) >>
  drule bytes_word_continuation_uniform >>
  disch_then (qspecl_then [`u`,`tn1`,`sf`] mp_tac) >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspecl_then [`ARB`,`ctx`,`PG`,`G1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule dynamic_writes_fresh_path_opcodes >> simp[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := q) H th` by
    (gen_tac >> qpat_assum `emitted_insts sa sb = _ ++ _` (fn eq => once_rewrite_tac[eq]) >>
     irule inst_seq_ptr_uniform_append >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`G1`,`u`,`tn1`] >> simp[]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >>
     simp[] >> qpat_x_assum `!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) _ H th`
       (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
  drule dynamic_writes_fresh_path_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),H,th)` by
    (gen_tac >>
     `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by metis_tac[] >>
     `ctx_has_dalloca ctx ==>
        !pre i post u. emitted_insts sa sb = pre ++ i::post /\
          run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
       (rpt strip_tac >>
        `MEM i (emitted_insts sa sb)` by
          (qpat_assum `emitted_insts sa sb = pre ++ i::post`
            (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
        irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
        qpat_assum `dynamic_writes_fresh sa (emitted_insts sa sb)`
          (fn th => mp_tac (REWRITE_RULE [dynamic_writes_fresh_def, EVERY_MEM,
            freshWritesTheory.fresh_write_op_def] th)) >>
        strip_tac >>
        qpat_assum `!e. MEM e (emitted_insts sa sb) ==> _`
          (qspecl_then [`i`] assume_tac) >>
        qpat_assum `MEM i (emitted_insts sa sb) ==> _`
          (drule_then (mp_tac o CONJUNCT1 o BETA_RULE)) >>
          Cases_on `i.inst_opcode = DALLOCA` >> asm_simp_tac (srw_ss()) [MEM]) >>
     drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  qexistsl_tac [`dtv`,`sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`,`H`,`th`] >>
  simp[eval_operand_def, lookup_var_def] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule_all unsigned_loader_shape_fresh >>
     disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >> decide_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac
  >- (qpat_x_assum `sf = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  qpat_assum `sf = s with vs_vars := _`
    (fn eq => once_rewrite_tac[eq]) >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED

Resume bytes_word_convert_origin_path_selected[abort]:
  rpt strip_tac >> drule_all bytes_word_conversion_run_actual >>
  qpat_assum `convert_result cx src dst v = INR exc`
    (fn th => simp_tac std_ss [th]) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort sf` >>
  `run_inst_seq (emitted_insts sm sb) u = Abort Revert_abort sf` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK u`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> metis_tac[]) >>
  drule bytes_word_continuation_uniform >>
  disch_then (qspecl_then [`u`,`tn1`,`sf`,`fn`,`Revert_abort`,`ctx`,`PG`,`G1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule dynamic_writes_fresh_path_opcodes >> simp[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := q) H th` by
    (gen_tac >> qpat_assum `emitted_insts sa sb = _ ++ _` (fn eq => once_rewrite_tac[eq]) >>
     irule inst_seq_ptr_uniform_append >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`G1`,`u`,`tn1`] >> simp[]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >>
     simp[] >> qpat_x_assum `!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) _ H th`
       (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
  drule dynamic_writes_fresh_path_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >>
     `MEM i (emitted_insts sa sb)` by
       (qpat_assum `emitted_insts sa sb = pre ++ i::post`
         (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_assum `dynamic_writes_fresh sa (emitted_insts sa sb)`
       (fn th => mp_tac (REWRITE_RULE [dynamic_writes_fresh_def, EVERY_MEM,
         freshWritesTheory.fresh_write_op_def] th)) >>
     strip_tac >>
     qpat_assum `!e. MEM e (emitted_insts sa sb) ==> _`
       (qspecl_then [`i`] assume_tac) >>
     qpat_assum `MEM i (emitted_insts sa sb) ==> _`
       (drule_then (mp_tac o CONJUNCT1 o BETA_RULE)) >>
       Cases_on `i.inst_opcode = DALLOCA` >> asm_simp_tac (srw_ss()) [MEM]) >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then strip_assume_tac >>
  qexistsl_tac [`sf with vs_inst_idx := j`,`H`,`th`] >>
  metis_tac[]
QED

Finalise bytes_word_convert_origin_path_selected

Theorem bytes_word_convert_origin_path:
  is_bytestring_type src /\ valid_conversion src dst /\
  (dst = BaseT BoolT \/ (?k. dst = BaseT (UintT k)) \/
   dst = BaseT AddressT \/ (?k. dst = BaseT (BytesT (Fixed k)))) /\
  well_formed_type (get_tenv cx) dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  (v <> BytesV [] /\ v <> StringV []) /\
  compile_type_convert (Var z) (mk_convert_op src dst) sa = (out,sb) /\
  not_fresh_at sa z /\ lookup_var z s = SOME a /\
  val_in_memory tv v (w2n a) s.vs_memory /\
  ptr_covers G tn z s capacity /\ 64 <= capacity /\
  w2n a + 64 <= dimword(:256) /\
  mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa sb fn /\ ~s.vs_halted /\
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
    ?err t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort err t,Gf,tnf)))
Proof
  disch_then (mp_tac o MATCH_MP bytes_word_convert_origin_path_selected) >>
  strip_tac >> conj_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum (drule_then strip_assume_tac) >> metis_tac[]
QED
