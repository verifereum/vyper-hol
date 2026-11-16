(* Signed conversion origins on the actual child state. *)
Theory bodyFullConvertSignedOrigin
Ancestors
  bodyFullConvertBytesWordSuffix bodyFullConvertSignedLoader
  bodyFullConvertSignedClamp exprSimConvertFromBytes exprLowering
  builtinConvertPrefix exprLoweringProps emitHelperProps compileEnv finite_map words arithmetic list
  ptrDiscipline fragExec venomInst venomState fragGasSeqPtr
  bodyMemTbConvertReadSuffix instSeqPtrLo instSeqComposePtr

(* Semantic actualization is the destination-generic
   bytes_word_conversion_run_actual, including signed and empty inputs. *)
Theorem decimal_compiler_signed_normalize[local]:
  (i2w lower : bytes32) = i2w (- &(2 ** (168-1))) /\
  (i2w upper : bytes32) = i2w (&(2 ** (168-1)-1)) ==>
  compile_type_convert x (ConvBytestringToDecimal divisor lower upper n) =
  compile_type_convert x (ConvBytestringToInt T 168 n)
Proof
  strip_tac >>
  simp[compile_type_convert_def, compile_int_clamp_def] >>
  Cases_on `n*8 <= 168` >> simp[]
QED

Theorem signed_compiler_normalize[local]:
  is_bytestring_type src /\
  ((?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT) ==>
  ?b n. compile_type_convert x (mk_convert_op src dst) =
    compile_type_convert x (ConvBytestringToInt T b n)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac)
  >- (gvs[mk_convert_op_def] >> metis_tac[]) >>
  gvs[mk_convert_op_def, type_bounds_def, type_bits_def, is_signed_type_def] >>
  qexistsl [`168`,`case src of BaseT (BytesT (Dynamic n)) => n |
    BaseT (StringT n) => n | _ => 0`] >>
  irule decimal_compiler_signed_normalize >> simp[]
QED

Theorem signed_loader_compiled_uniform_frame[local]:
  load_bytestring_as_word (Var z) SAR sa = ((word,bits),sm) /\
  not_fresh_at sa z /\ ~ctx_has_dalloca ctx /\
  lookup_var z s = SOME a /\ ptr_covers G tn z s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sm) s = OK sl ==>
  ?HG th.
    same_blocks sa sm /\ cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!p. word = Var p ==> not_fresh_at sm p) /\
    (!p. bits = Var p ==> not_fresh_at sm p) /\
    (!p. not_fresh_at sa p ==> not_fresh_at sm p) /\
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm)
      (s with vs_inst_idx := q) HG th) /\
    op_prov HG word = NONE /\ op_taint th word = {} /\
    op_prov HG bits = NONE /\ op_taint th bits = {} /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    sl = s with vs_vars := sl.vs_vars /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sl = lookup_var p s /\ FLOOKUP HG p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `same_blocks sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   (!p. word = Var p ==> not_fresh_at sm p) /\
   (!p. bits = Var p ==> not_fresh_at sm p)` by
    (drule bodyPtrSignedConvertSignedLoadTheory.signed_loader_decompose >> strip_tac >>
     imp_res_tac emit_op_extends >>
     imp_res_tac emitted_insts_emit_op_local >>
     rpt conj_tac
     >- metis_tac[same_blocks_trans]
     >- decide_tac
     >> fs[loweringStateRelDefsTheory.not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >>
     fs[same_blocks_def] >>
     metis_tac[inst_extends_load_bytestring_as_word, inst_extends_def,
       rich_listTheory.IS_PREFIX_APPEND]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_all bodyPtrSignedConvertSignedLoadTheory.signed_loader_shape_fresh >> strip_tac >>
  qpat_assum `emitted_insts sa sm = _` (fn eq =>
    qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK sl`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  drule_at (Pat `run_inst_seq _ _ = _`) signed_loader_uniform_frame_raw >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `mload _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`fn`,`ctx`,`PG`] mp_tac) >> simp[] >>
  strip_tac >>
  qexistsl_tac [`HG`,`th`] >>
  qpat_x_assum `emitted_insts sa sm = _` (fn eq => pure_rewrite_tac [eq]) >>
  simp[Excl "state_frame_def"] >>
  rpt strip_tac >>
  `~MEM p [len;dp;data;empty;nonempty;selected;sub;b;dst]` by metis_tac[] >>
  fs[]
QED

Theorem signed_optional_clamp_uniform[local]:
  (if take_clamp then compile_int_clamp T b word else comp_return word) sm = (out,sb) /\
  (!p. word = Var p ==> not_fresh_at sm p) /\
  op_prov G word = NONE /\ op_taint tn word = {} /\
  ~ctx_has_dalloca ctx /\ fn_has_code sm sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (run_inst_seq (emitted_insts sm sb) s = OK t \/
   run_inst_seq (emitted_insts sm sb) s = Abort err t) ==>
  ?H th.
    (!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sm sb)
      (s with vs_inst_idx := q) H th) /\
    (!p. not_fresh_at sm p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    op_prov H out = NONE /\ op_taint th out = {}
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  reverse (Cases_on `take_clamp`)
  >- (gvs[comp_return_def, emitted_insts_def] >> qexistsl_tac [`G`,`tn`] >>
      simp[inst_seq_ptr_def]) >>
  fs[] >>
  drule bodyPtrSignedConvertClampTheory.int_clamp_signed_code >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    simp[is_terminator_def] >>
  `run_inst_seq (emitted_insts sm sb) (s with vs_inst_idx := LENGTH sm.cs_current_insts) =
    exec_result_map (\u. u with vs_inst_idx := LENGTH sm.cs_current_insts)
      (run_inst_seq (emitted_insts sm sb) s)` by
    metis_tac[run_inst_seq_inst_idx] >>
  drule convert_signed_clamp_origin_path >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `op_prov _ _ = _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = _`)) >>
  disch_then (qspec_then `s with vs_inst_idx := LENGTH sm.cs_current_insts` mp_tac) >>
  simp[Excl "state_frame_def"] >>
  disch_then (qspecl_then [`lo`,`ARB`,`ctx`,`PG`] mp_tac) >>
  fs[instIdxIndepTheory.exec_result_map_def, allocas_from_def, Excl "state_frame_def"] >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> qexistsl_tac [`Gf`,`tnf`] >>
  simp[Excl "state_frame_def"] >> metis_tac[]
QED

Theorem signed_convert_origin_path:
  is_bytestring_type src /\ valid_conversion src dst /\
  ((?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT) /\
  well_formed_type (get_tenv cx) dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  compile_type_convert (Var z) (mk_convert_op src dst) sa = (out,sb) /\
  not_fresh_at sa z /\ lookup_var z s = SOME a /\
  val_in_memory tv v (w2n a) s.vs_memory /\
  ptr_covers G tn z s capacity /\ 64 <= capacity /\
  w2n a+64 <= dimword(:256) /\
  mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_inv s /\ w2n a+64 <= s.vs_alloca_next ==>
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all signed_compiler_normalize >>
  disch_then (qspec_then `Var z` strip_assume_tac) >>
  `compile_type_convert (Var z) (ConvBytestringToInt T b n') sa = (out,sb)` by metis_tac[] >>
  qpat_x_assum `compile_type_convert (Var z) (ConvBytestringToInt T b n') sa = _` mp_tac >>
  simp[Once compile_type_convert_def, comp_bind_def] >>
  pairarg_tac >> simp[Excl "state_frame_def"] >> strip_tac >>
  PairCases_on `a'` >>
  rename1 `load_bytestring_as_word (Var z) SAR sa = ((word,bits),sm)` >>
  gns[Excl "state_frame_def"] >>
  `inst_extends sa sm` by metis_tac[inst_extends_load_bytestring_as_word] >>
  `inst_extends sm sb` by
    (Cases_on `8*n' > b`
     >- (gns[Excl "state_frame_def"] >> metis_tac[inst_extends_compile_int_clamp]) >>
     gns[comp_return_def, Excl "state_frame_def"] >> simp[inst_extends_def, emitted_insts_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `~is_bytestring_type dst` by
    (qpat_assum `(?k. dst = BaseT (IntT k)) \/ dst = BaseT DecimalT`
      strip_assume_tac >> gvs[is_bytestring_type_def]) >>
  `dynamic_straight_fresh (compile_type_convert (Var z) (mk_convert_op src dst))` by
    (irule dynamic_scalar_straight_read_fresh >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   dynamic_writes_fresh sa (emitted_insts sa sb)` by
    metis_tac[dynamic_straight_fresh_def] >>
  `compile_type_convert (Var z) (mk_convert_op src dst) sa = (out,sb)` by metis_tac[] >>
  drule_all dynamic_code_prefix >> strip_tac >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[rich_listTheory.IS_PREFIX_APPEND, APPEND_ASSOC] >>
  `w2n a+32 < dimword(:256)` by decide_tac >>
  `?sl. run_inst_seq (emitted_insts sa sm) s = OK sl` by
    (drule convert_signed_loader_uniform >>
     disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
     disch_then (drule_at (Pat `mload _ _ = _`)) >> simp[] >>
     disch_then (qspecl_then [`ctx`,`PG`] mp_tac) >> simp[] >> metis_tac[]) >>
  drule signed_loader_compiled_uniform_frame >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `mload _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`fn`,`ctx`,`PG`] mp_tac) >> simp[] >> strip_tac >>
  `sb.cs_blocks = sa.cs_blocks` by metis_tac[dynamic_straight_fresh_def] >>
  `cs_extends sm sb` by
    (irule cs_extends_same_block >> fs[same_blocks_def] >>
     metis_tac[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sm sb fn` by metis_tac[fn_has_code_split] >>
  `~sl.vs_halted /\ sl.vs_current_bb = sm.cs_current_bb /\
   allocas_from lo sl /\ lo <= sl.vs_alloca_next` by
    (qpat_assum `sl = s with vs_vars := _`
       (fn eq => once_rewrite_tac[eq]) >>
     fs[allocas_from_def, same_blocks_def, Excl "state_frame_def"] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule convert_dynamic_scalar_mem_ok >> simp[] >>
     goal_assum (drule_at (Pat `compile_type_convert _ _ _ = _`)) >>
     qexists_tac `a` >> simp[eval_operand_def] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule dynamic_writes_fresh_path_opcodes >>
     simp[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm)
    (s with vs_inst_idx := q) HG th` by
    (rpt gen_tac >> irule inst_seq_ptr_zero_to_lo >>
     simp[allocas_from_def] >>
     conj_tac >- metis_tac[allocas_from_def] >> qexists_tac `D` >> simp[]) >>
  conj_tac >- suspend "success" >> suspend "abort"
QED

Resume signed_convert_origin_path[success]:
  rpt strip_tac >> drule_all bytes_word_conversion_run_actual >>
  qpat_assum `convert_result cx src dst v = INL vout`
    (fn th => simp_tac std_ss [th]) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts sa sb) s = OK sf` >>
  `run_inst_seq (emitted_insts sm sb) sl = OK sf` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK sl`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> metis_tac[]) >>
  drule signed_optional_clamp_uniform >>
  disch_then (drule_at (Pat `op_prov _ _ = _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = _`)) >>
  disch_then (qspec_then `sf` mp_tac) >>
  disch_then (qspec_then `sl` mp_tac) >>
  disch_then (qspec_then `lo` mp_tac) >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspecl_then [`ARB`,`ctx`,`PG`] mp_tac) >>
  simp[Excl "state_frame_def"] >> strip_tac >>
  `!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := q) H th'` by
    (gen_tac >> qpat_assum `emitted_insts sa sb = _ ++ _`
       (fn eq => once_rewrite_tac[eq]) >>
     irule inst_seq_ptr_uniform_append >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`HG`,`sl`,`th`] >> simp[]) >>
  drule dynamic_writes_fresh_path_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),H,th')` by
    (gen_tac >>
     `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th'` by
       (qpat_x_assum `!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) _ H th'`
         (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
     drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  `src <> BaseT AddressT` by
    (strip_tac >> qpat_x_assum `is_bytestring_type src` mp_tac >> simp[is_bytestring_type_def]) >>
  `evaluate_convert (get_tenv cx) v dst = INL vout` by
    (qpat_x_assum `convert_result cx src dst v = INL vout` mp_tac >>
     simp[exprSimConvertTheory.convert_result_def,
       vyperValueOperationTheory.evaluate_convert_from_not_address_bytes, AllCaseEqs()]) >>
  `value_has_type dtv vout` by (drule_all vyperTypeConversionsTheory.evaluate_convert_well_typed >> simp[]) >>
  drule_all dynamic_run_read_fresh >> strip_tac >>
  qexistsl_tac [`sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`,`H`,`th'`] >>
  simp[eval_operand_def, lookup_var_def] >>
  qpat_assum `sf = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
  simp[lookup_var_def] >> metis_tac[]
QED

Resume signed_convert_origin_path[abort]:
  rpt strip_tac >> drule_all bytes_word_conversion_run_actual >>
  qpat_assum `convert_result cx src dst v = INR exc`
    (fn th => simp_tac std_ss [th]) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort sf` >>
  `run_inst_seq (emitted_insts sm sb) sl = Abort Revert_abort sf` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK sl`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> metis_tac[]) >>
  drule signed_optional_clamp_uniform >>
  disch_then (drule_at (Pat `op_prov _ _ = _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = _`)) >>
  disch_then (qspec_then `sf` mp_tac) >>
  disch_then (qspec_then `sl` mp_tac) >>
  disch_then (qspec_then `lo` mp_tac) >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspecl_then [`Revert_abort`,`ctx`,`PG`] mp_tac) >>
  simp[Excl "state_frame_def"] >> strip_tac >>
  `!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := q) H th'` by
    (gen_tac >> qpat_assum `emitted_insts sa sb = _ ++ _`
       (fn eq => once_rewrite_tac[eq]) >>
     irule inst_seq_ptr_uniform_append >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`HG`,`sl`,`th`] >> simp[]) >>
  drule dynamic_writes_fresh_path_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sa sb)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all fragGasCopyLoopTheory.run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`Revert_abort`,`sf with vs_inst_idx := j`,`H`,`th'`] >>
  gen_tac >> first_x_assum irule >>
  qpat_x_assum `!D q. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) _ H th'`
    (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]
QED

Finalise signed_convert_origin_path
