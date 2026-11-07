(* Primitive decoder certificates do not assume that the input passes its clamp. *)
Theory abiDecodePtrWord
Ancestors
  abiEncoder abiDecodePtrRead abiDecodePtrMemberFrame bodyPtrDefs
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq exprLoweringProps
  emitHelperProps compileEnv freshWrites list pred_set
  abiDecodePtrScalarAbort bodyPtrBopScalarOutcome ptrDiscipline
  venomExecSemantics venomState finite_map
  emitHelper fragExec fragExecPtr fragGasSeqPtr fragGasPathPtr
  bodyPtrBopHashSuffix abiDecodePtrHead instSeqComposePtr assignTuplePtrLocalBytesCopy
  words arithmetic rich_list exprSimAccounts abiDecodePtrNormalized venomInst instIdxIndep

Theorem abi_decode_clamp_scalar:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\ value IN A /\
  (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ A SUBSET B /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `clamp`
  >- (simp[compile_abi_clamp_basetype_def, comp_return_def] >> strip_tac >>
      gvs[] >> qexists_tac `A` >> simp[emitted_insts_def, same_blocks_def]) >>
  TRY (rename1 `IntClamp bits signed` >> Cases_on `signed`) >>
  (simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_ignore_bind_def] >> strip_tac >>
  drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. T`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule bop_scalar_compile_emit_op >> simp[]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!x. x IN R ==> not_fresh_at m x` by metis_tac[not_fresh_at_mono] >>
      `value IN B` by metis_tac[SUBSET_DEF] >>
      Cases_on `v` >> drule bop_scalar_compile_emit_checked >> simp[]) >> simp[])
QED

(* Compiler-facing replay keeps pointer-bearing live variables protected,
   while the clamp itself sees only its clean loaded word and literals. *)
Theorem abi_decode_clamp_success_ptr:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  op_prov G value = NONE /\ op_taint tn value = {} /\
  (!x. x IN R ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    op_prov G' value = NONE /\ op_taint tn' value = {} /\
    t = s with vs_vars := t.vs_vars /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `?B. bop_scalar_seq R ({value} UNION IMAGE Lit UNIV)
    (emitted_insts sa sb) B /\ ({value} UNION IMAGE Lit UNIV) SUBSET B` by
    (drule abi_decode_clamp_scalar >>
     disch_then (qspecl_then [`R`, `{value} UNION IMAGE Lit UNIV`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!op. op IN {value} UNION IMAGE Lit UNIV ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[IN_UNION, IN_SING, IN_IMAGE] >> rpt strip_tac >>
     gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >>
  rpt strip_tac >> fs[lookup_var_def] >> metis_tac[]
QED

Theorem abi_decode_clamp_abort_ptr:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  op_prov G value = NONE /\ op_taint tn value = {} /\
  (!x. x IN R ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                     FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `?B. bop_scalar_seq R ({value} UNION IMAGE Lit UNIV)
    (emitted_insts sa sb) B` by
    (drule abi_decode_clamp_scalar >>
     disch_then (qspecl_then [`R`, `{value} UNION IMAGE Lit UNIV`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!op. op IN {value} UNION IMAGE Lit UNIV ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[IN_UNION, IN_SING, IN_IMAGE] >> rpt strip_tac >>
     gvs[op_prov_def, op_taint_def]) >>
  drule_all scalar_seq_abort_replay_ptr >> simp[]
QED

Theorem abi_decode_word_success_ptr:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecPrimWord clamp) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  abi_decode_ptr_window G tn s src b h /\
  lookup_var dst s = SOME d /\ ptr_covers G tn dst s 32 /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= h /\ w2n b+h < dimword(:256) /\
  (w2n b+h <= w2n d \/ w2n d+32 <= w2n b) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    abi_decode_ptr_window G' tn' u dst d 32 /\
    abi_decode_ptr_window G' tn' u src b h /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_abi_dec_addr (Var src) pos sa` >>
  rename1 `compile_abi_dec_addr (Var src) pos sa = (addr,c1)` >>
  Cases_on `emit_op MLOAD [addr] c1` >>
  rename1 `emit_op MLOAD [addr] c1 = (value,c2)` >>
  Cases_on `compile_abi_clamp_basetype value clamp c2` >>
  rename1 `compile_abi_clamp_basetype value clamp c2 = (unit,c3)` >>
  Cases_on `unit` >>
  `emit_void MSTORE [Var dst; value] c3 = ((),sb)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
          comp_bind_def, comp_ignore_bind_def]) >>
  suspend "word_phases"
QED

Resume abi_decode_word_success_ptr[word_phases]:
  `emit_op ADD [Var src;pos] sa = (addr,c1)` by
    fs[compile_abi_dec_addr_def] >>
  `cs_extends sa c1 /\ sa.cs_next_var <= c1.cs_next_var /\
   cs_extends c1 c2 /\ c1.cs_next_var <= c2.cs_next_var /\
   cs_extends c3 sb /\ c3.cs_next_var <= sb.cs_next_var` by
    (rpt conj_tac
     >- (irule (cj 1 emit_op_extends_next_var) >> goal_assum (drule_at Any))
     >- (irule (cj 2 emit_op_extends_next_var) >> goal_assum (drule_at Any))
     >- (irule (cj 1 emit_op_extends_next_var) >> goal_assum (drule_at Any))
     >- (irule (cj 2 emit_op_extends_next_var) >> goal_assum (drule_at Any))
     >- (drule emit_void_extends >> strip_tac >>
         irule cs_extends_same_block >> fs[same_blocks_def] >>
         simp[IS_PREFIX_APPEND]) >>
     drule emitted_insts_emit_void >> simp[]) >>
  `?B. bop_scalar_seq {x | not_fresh_at c2 x} ({value} UNION IMAGE Lit UNIV)
      (emitted_insts c2 c3) B /\
    c3.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 c3 /\
    same_blocks c2 c3 /\ c2.cs_next_var <= c3.cs_next_var` by
    (drule abi_decode_clamp_scalar >>
     disch_then (qspecl_then [`{x | not_fresh_at c2 x}`,
       `{value} UNION IMAGE Lit UNIV`] mp_tac) >> simp[] >> metis_tac[]) >>
  `cs_extends c2 c3` by
    (irule cs_extends_same_block >> fs[same_blocks_def] >>
     simp[IS_PREFIX_APPEND]) >>
  `cs_extends sa c2 /\ cs_extends c2 sb` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all (abi_decode_ptr_relative_load |> Q.INST [`D` |-> `D`, `PG` |-> `PG`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `value = Var out` >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa c2) s H tm` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts sa c2) s =
    OK (t with vs_inst_idx := _)` >>
  suspend "word_clamp"
QED

Resume abi_decode_word_success_ptr[word_clamp]:
  `c2.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c2` by
    (qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emit_op_extends) >>
     qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emit_op_extends) >>
     `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
       (irule emitted_insts_append >> simp[]) >> simp[APPEND_ASSOC]) >>
  `sb.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 sb` by
    metis_tac[emit_void_extends] >>
  `emitted_insts sa sb = emitted_insts sa c2 ++
     emitted_insts c2 c3 ++ emitted_insts c3 sb` by
    (`emitted_insts c2 sb = emitted_insts c2 c3 ++ emitted_insts c3 sb` by
       (irule emitted_insts_append >> simp[]) >>
     `sb.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 sb` by
       simp[APPEND_ASSOC] >>
     `emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
       (irule emitted_insts_append >> simp[]) >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c2) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 c3) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 sb)` by
    (drule bop_scalar_seq_opcodes >> strip_tac >>
     qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     drule emitted_insts_emit_void >> strip_tac >>
     `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
       (irule emitted_insts_append >> simp[]) >>
     fs[EVERY_APPEND, EVERY_CONJ, mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts c2 c3 ++ emitted_insts c3 sb) t =
    OK (u with vs_inst_idx := t.vs_inst_idx)` by
    (`run_inst_seq (emitted_insts c2 c3 ++ emitted_insts c3 sb)
       (t with vs_inst_idx := s.vs_inst_idx) = OK u` by
       (drule run_inst_seq_append >>
        disch_then (qspec_then `emitted_insts c2 c3 ++ emitted_insts c3 sb` mp_tac) >>
        qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
        qpat_x_assum `emitted_insts sa sb = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        pure_rewrite_tac[APPEND_ASSOC] >> metis_tac[]) >>
     `t with vs_inst_idx := t.vs_inst_idx = t` by
       simp_tac (srw_ss()) [NoAsms, venom_state_component_equality] >>
     qspec_then `emitted_insts c2 c3 ++ emitted_insts c3 sb` mp_tac
       run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`t with vs_inst_idx := s.vs_inst_idx`,
       `t.vs_inst_idx`] mp_tac) >>
     simp_tac (srw_ss()) [NoAsms, exec_result_map_def] >>
     asm_rewrite_tac[exec_result_map_def] >> BETA_TAC >> rewrite_tac[]) >>
  `?v. v.vs_inst_idx = t.vs_inst_idx + LENGTH (emitted_insts c2 c3) /\
    run_inst_seq (emitted_insts c2 c3) t = OK (v with vs_inst_idx := t.vs_inst_idx) /\
    run_inst_seq (emitted_insts c3 sb) v = OK (u with vs_inst_idx := v.vs_inst_idx)` by
    (mp_tac (abi_decode_run_split_normalized |> Q.INST
       [`xs` |-> `emitted_insts c2 c3`, `ys` |-> `emitted_insts c3 sb`,
        `s` |-> `t`, `u` |-> `u with vs_inst_idx := t.vs_inst_idx`]) >> simp[]) >>
  suspend "word_store"
QED

Resume abi_decode_word_success_ptr[word_store]:
  `inst_extends c2 c3 /\ v.vs_inst_idx = LENGTH c3.cs_current_insts` by
    simp[inst_extends_def] >>
  `fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    metis_tac[fn_has_code_split] >>
  `!op. op IN {value} UNION IMAGE Lit UNIV ==>
     op_prov H op = NONE /\ op_taint tm op = {}` by
    (gen_tac >> simp_tac (srw_ss()) [IN_UNION, IN_SING, IN_IMAGE] >>
     strip_tac >- metis_tac[] >>
     qpat_x_assum `op = Lit _` SUBST1_TAC >>
     simp[NoAsms, op_prov_def, op_taint_def]) >>
  drule_all (abi_decode_scalar_compile_replay_ptr |> Q.INST
    [`G` |-> `H`, `tn` |-> `tm`, `s` |-> `t`, `t` |-> `v`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG H tm
    (emitted_insts c2 c3) t Gc tk` >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP Gc x = FLOOKUP G x /\ op_taint tk (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at c2 x` by metis_tac[not_fresh_at_mono] >>
     fs[op_taint_def] >> metis_tac[]) >>
  `abi_decode_ptr_window Gc tk v src b h /\
   lookup_var dst v = SOME d /\ ptr_covers Gc tk dst v 32` by
    (`lookup_var src v = lookup_var src s /\ FLOOKUP Gc src = FLOOKUP G src /\
      op_taint tk (Var src) = op_taint tn (Var src) /\
      lookup_var dst v = lookup_var dst s /\ FLOOKUP Gc dst = FLOOKUP G dst /\
      op_taint tk (Var dst) = op_taint tn (Var dst)` by metis_tac[] >>
     conj_tac
     >- (irule abi_decode_ptr_window_frame >>
         qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
     conj_tac >- metis_tac[] >>
     qpat_x_assum `ptr_covers G tn dst s 32` mp_tac >>
     simp_tac (srw_ss()) [ptr_covers_def] >> metis_tac[]) >>
  `eval_operand value v = SOME (mload (w2n b+p) s) /\ op_taint tk value = {}` by
    (`lookup_var out v = lookup_var out t /\
      FLOOKUP tk.t_var out = FLOOKUP tm.t_var out` by
       (qpat_x_assum `!x. x IN {x | not_fresh_at c2 x} ==> _`
         (qspec_then `out` mp_tac) >> simp[]) >>
     qpat_assum `value = Var out` (fn th => rewrite_tac[th]) >>
     conj_tac >- (simp_tac (srw_ss()) [eval_operand_def] >> metis_tac[]) >>
     qpat_x_assum `op_taint tm value = {}` mp_tac >>
     qpat_assum `value = Var out` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [op_taint_def] >> asm_rewrite_tac[]) >>
  drule_all abi_decode_ptr_store_windows >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts c3 sb) v = OK (z with vs_inst_idx := _)` >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG Gc tk
     (emitted_insts c3 sb) v Gc tz` >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c2) /\
   z.vs_inst_idx = v.vs_inst_idx + LENGTH (emitted_insts c3 sb)` by simp[] >>
  `inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa c2 ++ emitted_insts c2 c3) s Gc tk /\
   run_inst_seq (emitted_insts sa c2 ++ emitted_insts c2 c3) s =
     OK (v with vs_inst_idx := s.vs_inst_idx) /\
   v.vs_inst_idx = s.vs_inst_idx +
     LENGTH (emitted_insts sa c2 ++ emitted_insts c2 c3)` by
     metis_tac[inst_seq_ptr_append_normalized] >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gc tz /\
   run_inst_seq (emitted_insts sa sb) s = OK (z with vs_inst_idx := s.vs_inst_idx)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode)
      (emitted_insts sa c2 ++ emitted_insts c2 c3)` by simp[] >>
     drule_all inst_seq_ptr_append_normalized >> strip_tac >>
     pure_rewrite_tac[APPEND_ASSOC] >> metis_tac[APPEND_ASSOC]) >>
  `u = z with vs_inst_idx := s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK u` mp_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK (z with vs_inst_idx := _)`
       (fn th => rewrite_tac[th]) >> simp[]) >>
  qexistsl_tac [`Gc`, `tz`] >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `u = z with vs_inst_idx := _` SUBST1_TAC >>
  conj_tac
  >- (qpat_x_assum `abi_decode_ptr_window Gc tz z dst d 32` mp_tac >>
      simp[NoAsms, abi_decode_ptr_window_def, ptr_covers_def, lookup_var_def] >>
      metis_tac[optionTheory.SOME_11]) >>
  conj_tac
  >- (qpat_x_assum `abi_decode_ptr_window Gc tz z src b h` mp_tac >>
      simp[NoAsms, abi_decode_ptr_window_def, ptr_covers_def, lookup_var_def] >>
      metis_tac[optionTheory.SOME_11]) >>
  simp_tac (srw_ss()) [lookup_var_def] >> metis_tac[lookup_var_def]
QED

Finalise abi_decode_word_success_ptr
