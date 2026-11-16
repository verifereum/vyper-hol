Theory bodyFullAbiDecodeLoopSelect
Ancestors
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeMemberPrefix
  bodyFullAbiDecodeFiniteGuard abiDecodePtrBytesMember abiDecoderGuard
  abiEncoder compileEnv emitHelper emitHelperProps venomInst venomExecSemantics
  words list rich_list arithmetic venomState abiDecoderRange abiDecodePtrPrims
  abiDecoderCoherence abiDecoderReentry exprLoweringProps fragExecMem
  loweringStateRelDefs decoderArraySetupPtr

(* The array helper has a footprint guard after its no-wrap guard. *)
Theorem abi_decode_loop_select_segments[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var input) head data hi asz sa =
    (child_src,sb) /\ hi <> Lit 0w ==>
  ?addr loadval e s1 s2 s3 s4 s5.
    compile_abi_dec_addr (Var input) head sa = (addr,s1) /\
    emit_op MLOAD [addr] s1 = (loadval,s2) /\
    emit_op ADD [data;loadval] s2 = (child_src,s3) /\
    abi_decode_ge_guard child_src data s3 = ((),s4) /\
    emit_op ADD [child_src;Lit (n2w asz)] s4 = (e,s5) /\
    compile_abi_decode_range_check child_src e hi s5 = ((),sb)
Proof
  strip_tac >>
  Cases_on `compile_abi_dec_addr (Var input) head sa` >>
  rename1 `compile_abi_dec_addr (Var input) head sa = (addr,s1)` >>
  Cases_on `emit_op MLOAD [addr] s1` >>
  rename1 `emit_op MLOAD [addr] s1 = (lv,s2)` >>
  Cases_on `emit_op ADD [data;lv] s2` >>
  rename1 `emit_op ADD [data;lv] s2 = (actual,s3)` >>
  Cases_on `abi_decode_ge_guard actual data s3` >>
  rename1 `abi_decode_ge_guard actual data s3 = (unit,s4)` >>
  Cases_on `unit` >>
  Cases_on `emit_op ADD [actual;Lit (n2w asz)] s4` >>
  rename1 `emit_op ADD [actual;Lit (n2w asz)] s4 = (e,s5)` >>
  Cases_on `compile_abi_decode_range_check actual e hi s5` >>
  gvs[compile_abi_decode_dyn_elem_ptr_def,
    abi_decode_ge_guard_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (goal_assum (drule_at Any))
QED

(* The final footprint check is not implied by the preceding no-wrap check. *)
Theorem abi_decode_loop_select_range_run[local]:
  emit_op ADD [src;Lit (n2w asz)] sa = (e,sm) /\
  compile_abi_decode_range_check src e hi sm = ((),sb) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var hi /\ eval_operand src s = SOME p /\
  eval_operand hi s = SOME hw /\ asz < dimword(:256) ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       w2n p + asz <= w2n hw)
Proof
  simp[compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `!n w u. sa.cs_next_var <= n ==>
    eval_operand src (update_var (STRING #"%" (toString n)) w u) =
      eval_operand src u` by
    (rpt strip_tac >> irule bodyPtrTypeBuiltinsBoundsTheory.eval_operand_update_old >>
     qexists_tac `sa` >> conj_tac >-
       (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def]) >> simp[]) >>
  `!n w u. sa.cs_next_var <= n ==>
    eval_operand hi (update_var (STRING #"%" (toString n)) w u) =
      eval_operand hi u` by
    (rpt strip_tac >> irule bodyPtrTypeBuiltinsBoundsTheory.eval_operand_update_old >>
     qexists_tac `sa` >> conj_tac >-
       (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def]) >> simp[]) >>
  `!x y w u. eval_operand (Var x) (update_var y w u) =
     if x = y then SOME w else eval_operand (Var x) u` by
    simp[eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE, EQ_SYM_EQ] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  Cases_on `w2n p <= w2n (p+n2w asz) /\ w2n (p+n2w asz) <= w2n hw`
  >- (pop_assum strip_assume_tac >> disj2_tac >>
      simp[Once run_inst_seq_def, mk_inst_def, Once step_inst_base_def,
           exec_pure2_def, eval_operand_def] >>
      simp[Once run_inst_seq_def, Once step_inst_base_def,
           exec_pure2_def, eval_operand_update_var, bool_to_word_def] >>
      simp[Once run_inst_seq_def, Once step_inst_base_def,
           exec_pure1_def, eval_operand_update_var] >>
      simp[Once run_inst_seq_def, Once step_inst_base_def,
           exec_pure2_def, ASCIInumbersTheory.toString_inj, bool_to_word_def] >>
      simp[Once run_inst_seq_def, Once step_inst_base_def,
           exec_pure1_def, eval_operand_update_var] >>
      simp[Once run_inst_seq_def, Once step_inst_base_def,
           exec_pure2_def, ASCIInumbersTheory.toString_inj] >>
      simp[Once run_inst_seq_def, Once step_inst_base_def,
           eval_operand_update_var, WORD_AND_IDEM] >>
      simp[run_inst_seq_def] >>
      `w2n p + asz < dimword(:256)` by
        (spose_not_then assume_tac >>
         `dimword(:256) <= w2n p + w2n (n2w asz : bytes32)` by simp[] >>
         drule arithmeticPropsTheory.w2n_add_overflow >> simp[] >> decide_tac) >>
      gvs[w2n_add_2]) >>
  disj1_tac >>
  simp[Once run_inst_seq_def, mk_inst_def, Once step_inst_base_def,
       exec_pure2_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure1_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, ASCIInumbersTheory.toString_inj] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure1_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, ASCIInumbersTheory.toString_inj] >>
  Cases_on `w2n (p+n2w asz) < w2n p` >>
  Cases_on `w2n (p+n2w asz) > w2n hw` >>
  gvs[bool_to_word_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ st` >>
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+5)))) st = SOME 0w` by
    simp[Abbr `st`, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def]
QED

(* Array offsets have no no-wrap premise: the emitted guard decides it. *)
Theorem abi_decode_loop_select_actual_run[local]:
  emit_op ADD [data;offset] sa = (actual,sm) /\
  abi_decode_ge_guard actual data sm = ((),sb) /\
  eval_operand data s = SOME dw /\ eval_operand offset s = SOME ow /\
  abi_decoder_operand_live sa.cs_next_var data ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand actual t = SOME (dw+ow) /\ w2n dw <= w2n (dw+ow))
Proof
  simp[abi_decode_ge_guard_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `!n w u. sa.cs_next_var <= n ==>
    eval_operand data (update_var (STRING #"%" (toString n)) w u) =
      eval_operand data u` by
    (rpt strip_tac >> irule bodyPtrTypeBuiltinsBoundsTheory.eval_operand_update_old >>
     qexists_tac `sa` >> conj_tac >-
       (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def]) >> simp[]) >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, mk_inst_def, Once step_inst_base_def,
       exec_pure2_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure1_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       eval_operand_update_var] >>
  Cases_on `w2n (dw+ow) < w2n dw` >- simp[] >>
  disj2_tac >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[run_inst_seq_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]
QED

(* Keep one scalar certificate across both actual-position guards. *)
Theorem abi_decode_loop_select_suffix_scalar[local]:
  emit_op ADD [data;offset] sa = (actual,s1) /\
  abi_decode_ge_guard actual data s1 = ((),s2) /\
  emit_op ADD [actual;Lit (n2w asz)] s2 = (e,s3) /\
  compile_abi_decode_range_check actual e hi s3 = ((),sb) /\
  data IN A /\ offset IN A /\ hi IN A /\ Lit (n2w asz) IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ actual IN B
Proof
  strip_tac >>
  `?C. bop_scalar_seq R A (emitted_insts sa s2) C /\ actual IN C` by
    (irule abiDecodePtrHeadTheory.abi_decode_position_suffix_scalar >>
     conj_tac >- simp[] >>
     qexistsl_tac [`Lit 1w`, `s1`, `offset`, `data`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `A SUBSET C` by metis_tac[bodyPtrBopScalarCompileTheory.bop_scalar_seq_available] >>
  `inst_extends sa s2` by
    metis_tac[inst_extends_emit_op, abi_decode_ge_guard_shape, inst_extends_trans] >>
  `sa.cs_next_var <= s2.cs_next_var` by
    (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD [data;offset] _ = _` mp_tac >>
     simp[abi_decode_ge_guard_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `!x. x IN R ==> not_fresh_at s2 x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `?B. bop_scalar_seq R C (emitted_insts s2 sb) B /\ C SUBSET B /\ e IN B` by
    (irule abi_decode_add_range_scalar >> conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `compile_abi_decode_range_check _ _ _ _ = _`)) >>
     simp[] >> metis_tac[pred_setTheory.SUBSET_DEF]) >>
  pop_assum strip_assume_tac >>
  `inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op, compile_abi_decode_range_check_shape,
              inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa s2 ++ emitted_insts s2 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  qexists_tac `B` >> conj_tac
  >- (simp[] >> irule bodyPtrBopScalarCompileTheory.bop_scalar_seq_append >>
      qexists_tac `C` >> simp[]) >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

(* Alpha-identical owned-state interface, not a new predicate. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

Theorem abi_decode_loop_select_joint:
  (if dec_info_needs_offset ei then
     compile_abi_decode_dyn_elem_ptr MLOAD (Var input) head data hi asz sa
   else (head,sa)) = (child_src,sb) /\
  eval_operand data s = SOME dw /\ eval_operand head s = SOME (n2w p) /\
  eval_operand hi s = SOME (n2w h) /\
  abi_decoder_operand_live sa.cs_next_var data /\
  abi_decoder_operand_live sa.cs_next_var head /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  op_prov G data = NONE /\ op_prov G head = NONE /\ op_prov G hi = NONE /\
  op_taint tn data = {} /\ op_taint tn head = {} /\ op_taint tn hi = {} /\
  hi <> Lit 0w /\ asz < dimword(:256) /\
  p+asz <= h /\ h <= LENGTH input_bytes /\ h < dimword(:256) /\
  (dec_info_needs_offset ei ==> p+32 <= LENGTH input_bytes) /\
  w2n input_word + LENGTH input_bytes < dimword(:256) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ((?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) \/
   (?u Gu tnu q.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)) /\
     ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
     u.vs_inst_idx = LENGTH sb.cs_current_insts /\
     (^owned_decoder_state) sb u Gu tnu /\
     eval_operand child_src u = SOME (n2w q) /\ q < dimword(:256) /\
     q+asz <= h /\ eval_operand hi u = SOME (n2w h) /\
     (dec_info_needs_offset ei ==> w2n dw <= q) /\
     (~dec_info_needs_offset ei ==> child_src = head /\ q = p) /\
     op_prov Gu child_src = NONE /\ op_taint tnu child_src = {} /\
     abi_decoder_operand_live sb.cs_next_var child_src /\
     u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
     u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
     tnu.t_mem = tn.t_mem /\
     (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
       op_taint tnu (Var x) = op_taint tn (Var x))))
Proof
  reverse (Cases_on `dec_info_needs_offset ei`)
  >- (simp_tac bool_ss [COND_CLAUSES, pairTheory.PAIR_EQ] >>
      strip_tac >> gvs[] >> disj2_tac >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
      metis_tac[]) >>
  simp_tac bool_ss [COND_CLAUSES] >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all abi_decode_loop_select_segments >> strip_tac >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s2 s3 /\ cs_extends s3 s4 /\
   cs_extends s4 s5 /\ cs_extends s5 sb` by
    (metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,
       externalEntryShapeTheory.compile_abi_dec_addr_labels,
       exprSimConvertTheory.straight_fresh_extends,
       abiDecodePtrPositionTheory.abi_decode_ge_guard_straight_fresh,
       externalEntryShapeTheory.compile_abi_decode_range_check_labels,
       pairTheory.SND]) >>
  `fn_has_code sa s2 fn` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `(^owned_decoder_state) sa s G tn` by
    (asm_rewrite_tac[] >> metis_tac[]) >>
  `p+32 <= LENGTH input_bytes` by metis_tac[] >>
  drule_all abi_decode_owned_relative_load >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!op. abi_decoder_operand_live sa.cs_next_var op ==>
     eval_operand op t = eval_operand op s /\
     op_taint tnf op = op_taint tn op /\ op_prov Gf op = op_prov G op` by
    (gen_tac >> disch_tac >> irule old_operand_ghost_frame >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     qexists_tac `sa` >> asm_rewrite_tac[] >>
     rpt strip_tac >> gvs[abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `eval_operand data t = SOME dw /\ eval_operand hi t = SOME (n2w h) /\
   op_prov Gf data = NONE /\ op_prov Gf hi = NONE /\
   op_taint tnf data = {} /\ op_taint tnf hi = {}` by metis_tac[] >>
  `sa.cs_next_var <= s2.cs_next_var` by
    (`emit_op ADD [Var input;head] sa = (addr,s1)` by
       gvs[compile_abi_dec_addr_def] >>
     qpat_assum `emit_op ADD [Var input;head] _ = _`
       (mp_then Any strip_assume_tac loweringShapeRulesTheory.emit_op_facts) >>
     qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac loweringShapeRulesTheory.emit_op_facts) >> simp[]) >>
  `abi_decoder_operand_live s2.cs_next_var data /\
   abi_decoder_operand_live s2.cs_next_var hi` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `?B. bop_scalar_seq (abi_decoder_older_vars s2.cs_next_var)
      {data;loadval;hi;Lit (n2w asz)} (emitted_insts s2 sb) B /\ child_src IN B` by
    (irule abi_decode_loop_select_suffix_scalar >>
     simp[] >> conj_tac
     >- simp[abi_decoder_older_vars_def, not_fresh_at_def] >>
     qexistsl_tac [`asz`,`data`,`e`,`hi`,`loadval`,`s3`,`s4`,`s5`] >>
     simp[]) >>
  `inst_extends s2 s4 /\ inst_extends s4 sb /\ inst_extends s2 sb` by
    (qpat_x_assum `emit_op ADD [data;loadval] _ = _` mp_tac >>
     qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD [child_src;Lit _] _ = _` mp_tac >>
     qpat_x_assum `compile_abi_decode_range_check _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     imp_res_tac inst_extends_emit_op >>
     imp_res_tac abi_decode_ge_guard_shape >>
     imp_res_tac compile_abi_decode_range_check_shape >>
     metis_tac[inst_extends_trans]) >>
  `emitted_insts s2 sb = emitted_insts s2 s4 ++ emitted_insts s4 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  `fn_has_code s2 sb fn /\ sb.cs_current_bb = s2.cs_current_bb /\
   s2.cs_next_var <= sb.cs_next_var /\ s2.cs_next_id <= sb.cs_next_id` by
    (conj_tac >-
     (`cs_extends sa s2` by metis_tac[cs_extends_trans] >>
     qpat_x_assum `cs_extends sa s2` mp_tac >>
     qpat_x_assum `fn_has_code sa sb fn` mp_tac >>
     qpat_x_assum `fn_has_code sa s2 fn` mp_tac >>
     qpat_x_assum `inst_extends s2 sb` mp_tac >>
     qpat_x_assum `cs_extends s2 s3` mp_tac >>
     qpat_x_assum `cs_extends s3 s4` mp_tac >>
     qpat_x_assum `cs_extends s4 s5` mp_tac >>
     qpat_x_assum `cs_extends s5 sb` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     ntac 8 strip_tac >>
     `cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
     qpat_x_assum `emit_op ADD [data;loadval] _ = _` mp_tac >>
     qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD [child_src;Lit _] _ = _` mp_tac >>
     qpat_x_assum `compile_abi_decode_range_check _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_ge_guard_def,compile_abi_decode_range_check_def,
       emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  `(!op. op IN {data;loadval;hi;Lit (n2w asz)} ==>
     op_prov Gf op = NONE /\ op_taint tnf op = {}) /\
   allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (conj_tac
     >- (map_every (fn pat => qpat_x_assum pat mp_tac)
           [`op_prov Gf data = NONE`,`op_prov Gf loadval = NONE`,
            `op_prov Gf hi = NONE`,`op_taint tnf data = {}`,
            `op_taint tnf loadval = {}`,`op_taint tnf hi = {}`] >>
         POP_ASSUM_LIST (K all_tac) >> ntac 6 disch_tac >>
         gen_tac >> simp_tac std_ss [pred_setTheory.IN_INSERT,
           pred_setTheory.NOT_IN_EMPTY] >> strip_tac >> simp[] >>
         simp[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def]) >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `lo <= s.vs_alloca_next` mp_tac >>
     qpat_x_assum `t.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_x_assum `t.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ptrDisciplineTheory.allocas_from_def]) >>
  `(?v. run_inst_seq (emitted_insts s2 sb) t = Abort Revert_abort v) \/
   (?v q. run_inst_seq (emitted_insts s2 sb) t = OK v /\
     eval_operand child_src v = SOME (n2w q) /\ q < dimword(:256) /\
     w2n dw <= q /\ q+asz <= h)` by
    (drule_all abi_decode_loop_select_actual_run >> strip_tac
     >- (disj1_tac >> simp[run_inst_seq_append_err]) >>
     rename1 `run_inst_seq (emitted_insts s2 s4) t = OK mid` >>
     `?C. bop_scalar_seq (abi_decoder_older_vars s2.cs_next_var)
       {data;loadval;hi;Lit (n2w asz)} (emitted_insts s2 s4) C /\ child_src IN C` by
       (irule abiDecodePtrHeadTheory.abi_decode_position_suffix_scalar >>
        conj_tac >- simp[abi_decoder_older_vars_def,not_fresh_at_def] >>
        qexistsl_tac [`Lit 1w`,`s3`,`loadval`,`data`] >> simp[]) >>
     drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
     `mid.vs_labels = t.vs_labels` by
       (qpat_x_assum `mid = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     `eval_operand hi mid = SOME (n2w h)` by
       (qpat_x_assum `mid.vs_labels = t.vs_labels` mp_tac >>
        qpat_x_assum `!x. x IN abi_decoder_older_vars _ ==> FLOOKUP mid.vs_vars x = _` mp_tac >>
        qpat_x_assum `abi_decoder_operand_live s2.cs_next_var hi` mp_tac >>
        qpat_x_assum `eval_operand hi t = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `hi` >>
        simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
          eval_operand_def,lookup_var_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
     `abi_decoder_operand_live s4.cs_next_var child_src /\
      abi_decoder_operand_live s4.cs_next_var hi` by
       (qpat_x_assum `emit_op ADD [data;loadval] _ = _` mp_tac >>
        qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
        qpat_x_assum `abi_decoder_operand_live s2.cs_next_var hi` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[abi_decode_ge_guard_def,emit_op_def,emit_void_def,
          fresh_var_def,fresh_id_def,emit_def,comp_bind_def,
          comp_ignore_bind_def,comp_return_def] >> rpt strip_tac >> gvs[]
        >- (irule abiDecoderArrayInitReentryTheory.abi_decoder_generated_var_live >> simp[]) >>
        irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
     drule_all abi_decode_loop_select_range_run >> strip_tac
     >- (disj1_tac >> qexists_tac `t'` >>
         qpat_x_assum `emitted_insts s2 sb = _` (fn th => once_rewrite_tac[th]) >>
         drule run_inst_seq_append >> disch_then (qspec_then `emitted_insts s4 sb` mp_tac) >>
         asm_rewrite_tac[]) >>
     `?E. bop_scalar_seq (abi_decoder_older_vars s4.cs_next_var)
       {child_src;hi;Lit (n2w asz)} (emitted_insts s4 sb) E /\
       {child_src;hi;Lit (n2w asz)} SUBSET E /\ e IN E` by
       (irule abiDecodePtrBytesMemberTheory.abi_decode_add_range_scalar >>
        simp[abi_decoder_older_vars_def,not_fresh_at_def] >>
        qexistsl_tac [`hi`,`Lit (n2w asz)`,`s5`,`child_src`] >> simp[]) >>
     qpat_assum `bop_scalar_seq (abi_decoder_older_vars s4.cs_next_var) _ _ _`
       (mp_then Any mp_tac bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame) >>
     disch_then drule >> strip_tac >>
     `t'.vs_labels = mid.vs_labels` by
       (qpat_x_assum `t' = mid with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     `eval_operand child_src t' = eval_operand child_src mid` by
       (qpat_x_assum `t'.vs_labels = mid.vs_labels` mp_tac >>
        qpat_x_assum `!x. x IN abi_decoder_older_vars s4.cs_next_var ==> _` mp_tac >>
        qpat_x_assum `abi_decoder_operand_live s4.cs_next_var child_src` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `child_src` >>
        simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
          eval_operand_def,lookup_var_def] >> metis_tac[]) >>
     disj2_tac >> qexistsl_tac [`t'`,`w2n (dw + mload (w2n input_word+p) s)`] >>
     simp[] >> conj_tac
     >- metis_tac[run_inst_seq_append] >> gvs[])
  >- (drule_all abi_decode_scalar_guard_abort_joint >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      disj1_tac >> qexistsl_tac [`v with vs_inst_idx := j`,`Gf'`,`tnf'`] >>
      gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gf`,`t`,`tnf`] >> simp[]) >>
  drule_all (bodyPtrBopScalarSeqTheory.bop_scalar_seq_run |>
    Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG Gf tnf
      (emitted_insts s2 sb) t G' tn'` by
    (irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts s2 sb)` by
    metis_tac[bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes] >>
  `run_inst_seq_mem_ok (emitted_insts s2 sb) t` by metis_tac[bodyPtrBopScalarSeqTheory.bop_scalar_seq_mem_ok] >>
  drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `u = v with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = t.vs_allocas` by
    (simp[Abbr `u`] >>
     qpat_x_assum `v = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[stateFrameTheory.state_frame_def]) >>
  `!x. not_fresh_at s2 x ==>
     lookup_var x u = lookup_var x t /\ FLOOKUP G' x = FLOOKUP Gf x /\
     op_taint tn' (Var x) = op_taint tnf (Var x)` by
    (simp[Abbr `u`,lookup_var_def,ptrDisciplineTheory.op_taint_def,
       not_fresh_at_def,abi_decoder_older_vars_def] >> metis_tac[]) >>
  `alloca_history fn t` by fs[] >>
  `alloca_history fn u` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`t`,`s2`,`sb`] >> asm_rewrite_tac[] >>
     conj_tac >-
       (qpat_x_assum `bop_scalar_seq _ _ (emitted_insts s2 sb) _` mp_tac >>
        qpat_x_assum `emitted_insts s2 sb = _` (fn th => once_rewrite_tac[GSYM th]) >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >>
        drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_memory_checks >>
        simp[EVERY_MEM] >> metis_tac[]) >>
     fs[inst_extends_def,IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    (qpat_x_assum `sa.cs_next_var <= s2.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `(^owned_decoder_state) sb u G' tn'` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`Gf`,`t`,`s2`,`tnf`] >> asm_rewrite_tac[] >>
     rpt conj_tac
     >- (rpt strip_tac >> first_assum irule >> metis_tac[])
     >- (rpt strip_tac >> first_assum irule >> metis_tac[])
     >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
         qexists_tac `sa` >> simp[]) >>
     first_assum irule >> asm_rewrite_tac[]) >>
  pop_assum (mk_asm "owned") >>
  `u.vs_allocas = s.vs_allocas` by asm_rewrite_tac[] >>
  disj2_tac >> qexistsl_tac [`u`,`G'`,`tn'`,`q`] >>
  conj_tac
  >- (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gf`,`t`,`tnf`] >> conj_tac >- simp[] >>
      irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
      asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  conj_tac >- (asm "owned" mp_tac >>
     qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[Abbr `u`,eval_operand_def] >>
  conj_tac
  >- (qpat_x_assum `!x. not_fresh_at s2 x ==> _` mp_tac >>
      qpat_x_assum `abi_decoder_operand_live s2.cs_next_var hi` mp_tac >>
      qpat_x_assum `eval_operand hi t = _` mp_tac >>
      qpat_x_assum `state_frame u = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> Cases_on `hi` >>
      simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def,eval_operand_def,
        stateFrameTheory.state_frame_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (irule abi_decoder_operand_live_mono >> qexists_tac `s3.cs_next_var` >>
      conj_tac
      >- (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
          qpat_x_assum `emit_op ADD [child_src;Lit _] _ = _` mp_tac >>
          qpat_x_assum `compile_abi_decode_range_check _ _ _ _ = _` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          simp[abi_decode_ge_guard_def,compile_abi_decode_range_check_def,
            emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def,
            comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
          rpt strip_tac >> gvs[]) >>
      qpat_x_assum `emit_op ADD [data;loadval] s2 = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[emit_op_def,fresh_var_def,fresh_id_def,emit_def,comp_bind_def,
        comp_ignore_bind_def,comp_return_def] >> rpt strip_tac >> gvs[] >>
      irule abiDecoderArrayInitReentryTheory.abi_decoder_generated_var_live >> simp[]) >>
  conj_tac >- (fs[stateFrameTheory.state_frame_def] >> metis_tac[]) >>
  conj_tac >- (fs[stateFrameTheory.state_frame_def] >> metis_tac[]) >>
  conj_tac >- (fs[stateFrameTheory.state_frame_def] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED
