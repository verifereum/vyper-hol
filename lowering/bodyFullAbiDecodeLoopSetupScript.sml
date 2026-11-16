Theory bodyFullAbiDecodeLoopSetup
Ancestors
  bodyFullAbiDecodeLoopHeader bodyFullAbiDecodeMemberPrefix
  bodyFullAbiDecodeLoopSource bodyFullAbiDecodeLoopSelect
  bodyFullAbiDecodeLoopDestination
  bodyFullAbiDecodeFiniteGuard abiDecoderLoopSetup abiDecoderIndexedAddress
  abiEncoder compileEnv emitHelper emitHelperProps venomInst venomExecSemantics
  words list rich_list arithmetic venomState ptrDiscipline
  abiDecoderReentry loweringStateRelDefs allocaFootprint decoderArraySetupPtr

(* Split only the finite setup; no child execution is assumed. *)
Theorem abi_decode_loop_setup_segments[local]:
  abi_decode_array_element_setup ip src dst opc base_op hi ei asz msz sa =
    ((idx,child_src,child_dst),sb) ==>
  ?s1 s2 s3 s4 s5 data offset head.
    emit_op MLOAD [ip] sa = (idx,s1) /\
    emit_op ADD [src;Lit 32w] s1 = (data,s2) /\
    emit_op MUL [idx;Lit (n2w asz)] s2 = (offset,s3) /\
    emit_op ADD [data;offset] s3 = (head,s4) /\
    (if dec_info_needs_offset ei then
       compile_abi_decode_dyn_elem_ptr opc base_op head data hi asz s4
     else (head,s4)) = (child_src,s5) /\
    abi_decode_indexed_address dst idx msz s5 = (child_dst,sb)
Proof
  simp[abi_decode_array_element_setup_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >>
  Cases_on `dec_info_needs_offset ei` >> gvs[comp_return_def]
QED

(* The loop's evaluated window covers exactly the current embedded head. *)
Theorem abi_decode_loop_setup_window[local]:
  j < n /\ srcoff+32+n*asz <= h /\ h <= LENGTH (input_bytes:word8 list) ==>
  srcoff+32+j*asz+asz <= h /\
  srcoff+32+j*asz <= h /\
  srcoff+32+j*asz+asz <= LENGTH input_bytes
Proof
  strip_tac >>
  `j*asz+asz <= n*asz` by
    (`j+1 <= n` by decide_tac >>
     drule LESS_MONO_MULT2 >> disch_then (qspec_then `asz` mp_tac) >>
     simp[RIGHT_ADD_DISTRIB]) >>
  decide_tac
QED

(* Compiler-only preparation for the four finite segments. *)
Theorem abi_decode_loop_setup_code[local]:
  emit_op MLOAD [ip] sa = (idx,s1) /\
  emit_op ADD [src;Lit 32w] s1 = (data,s2) /\
  emit_op MUL [idx;Lit (n2w asz)] s2 = (offset,s3) /\
  emit_op ADD [data;offset] s3 = (head,s4) /\
  (if dec_info_needs_offset ei then
     compile_abi_decode_dyn_elem_ptr opc base_op head data hi asz s4
   else (head,s4)) = (child_src,s5) /\
  abi_decode_indexed_address dst idx msz s5 = (child_dst,sb) /\
  fn_has_code sa sb fn ==>
  cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
  cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 sb /\
  fn_has_code sa s1 fn /\ fn_has_code s1 s4 fn /\
  fn_has_code s4 s5 fn /\ fn_has_code s5 sb fn /\
  sa.cs_next_var <= s1.cs_next_var /\
  s1.cs_next_var <= s4.cs_next_var /\ s4.cs_next_var <= s5.cs_next_var
Proof
  strip_tac >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 sb` by
    (conj_tac >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
     conj_tac >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
     conj_tac >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
     conj_tac >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
     conj_tac >- (Cases_on `dec_info_needs_offset ei` >>
       gvs[] >> metis_tac[externalEntryShapeTheory.compile_abi_decode_dyn_elem_ptr_labels,
         cs_extends_refl, pairTheory.SND]) >>
     gvs[abi_decode_indexed_address_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var, cs_extends_trans]) >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 s4 fn /\
   fn_has_code s4 s5 fn /\ fn_has_code s5 sb fn` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `sa.cs_next_var <= s1.cs_next_var` by
    metis_tac[placeMemoryCodeLayoutTheory.emit_op_next_var, arithmeticTheory.LE_ADD] >>
  `s1.cs_next_var <= s4.cs_next_var` by
    (qpat_assum `emit_op ADD [src;Lit 32w] s1 = _` mp_tac >>
     qpat_assum `emit_op MUL _ s2 = _` mp_tac >>
     qpat_assum `emit_op ADD [data;offset] s3 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     imp_res_tac placeMemoryCodeLayoutTheory.emit_op_next_var >> decide_tac) >>
  `s4.cs_next_var <= s5.cs_next_var` by
    (qpat_assum `(if dec_info_needs_offset ei then _ else _) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `dec_info_needs_offset ei` >>
     Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
     simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
       compile_abi_decode_range_check_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  simp[]
QED

(* Shared quotation, not a new HOL definition. *)
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

Theorem abi_decode_loop_setup_joint:
  abi_decode_array_element_setup (Var counter) src (Var dst) MLOAD
    (Var input) hi ei asz msz sa = ((idx,child_src,child_dst),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w srcoff) /\
  eval_operand hi s = SOME (n2w h) /\
  lookup_var dst s = SOME (n2w d) /\ lookup_var counter s = SOME (n2w cell) /\
  ptr_covers G tn counter s 32 /\ mem_word_at cell s.vs_memory = n2w j /\
  (!i. cell <= i /\ i < cell+32 ==> i NOTIN tn.t_mem) /\
  cell+32 <= s.vs_alloca_next /\ cell < dimword (:256) /\
  ptr_covers G tn dst s (32+n*msz) /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\
  output_base <= d /\ d+32+n*msz <= output_base+output_cap /\
  j<n /\ n<dimword (:256) /\ asz<dimword (:256) /\
  hi <> Lit 0w /\ srcoff+32+n*asz <= h /\ h <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (dec_info_needs_offset ei ==> 32 <= asz) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  abi_decoder_operand_live sa.cs_next_var (Var dst) /\
  abi_decoder_operand_live sa.cs_next_var (Var counter) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn src = {} /\ op_taint tn hi = {} /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var counter) = {} /\
  (!name b k. local_region ce es.scopes s name b k ==>
    cell+32 <= b \/ b+k <= cell) ==>
  (?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) \/
  (?u Gu tnu q child.
    child_dst = Var child /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gu,tnu)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gu tnu /\
    eval_operand idx u = SOME (n2w j) /\
    op_prov Gu idx = NONE /\ op_taint tnu idx = {} /\
    abi_decoder_operand_live sb.cs_next_var idx /\
    eval_operand child_src u = SOME (n2w q) /\
    q < dimword (:256) /\ q+asz <= h /\
    op_prov Gu child_src = NONE /\ op_taint tnu child_src = {} /\
    abi_decoder_operand_live sb.cs_next_var child_src /\
    eval_operand hi u = SOME (n2w h) /\
    eval_operand child_dst u = SOME (n2w (d+32+j*msz)) /\
    ptr_covers Gu tnu child u msz /\
    FLOOKUP Gu child = SOME (output_base,output_cap) /\
    op_taint tnu child_dst = {} /\
    abi_decoder_operand_live sb.cs_next_var child_dst /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
    tnu.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tnu (Var x) = op_taint tn (Var x)) /\
    (!name b k. local_region ce es.scopes u name b k ==>
      cell+32 <= b \/ b+k <= cell))
Proof
  strip_tac >>
  drule abi_decode_loop_setup_segments >> strip_tac >>
  drule_all abi_decode_loop_setup_code >> strip_tac >>
  `?out. idx = Var out` by
    metis_tac[placeMemoryCodeLayoutTheory.emit_op_next_var] >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `idx = Var out` SUBST_ALL_TAC >>
  `(!i. w2n (n2w cell:bytes32) <= i /\
         i < w2n (n2w cell:bytes32)+32 ==> i NOTIN tn.t_mem) /\
   w2n (n2w cell:bytes32)+32 <= s.vs_alloca_next` by simp[] >>
  drule_all abi_decode_loop_counter_load >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `not_fresh_at s1 input /\ local_ptrs_reserved ce s1 /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   abi_decoder_operand_live s1.cs_next_var src /\
   abi_decoder_operand_live s1.cs_next_var (Var out)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,
      exprLoweringPropsTheory.local_ptrs_reserved_next_var,
      abiDecoderReentryTheory.abi_decoder_operand_live_mono,
      abiDecoderReentryTheory.abi_decoder_operand_live_emit] >>
  `eval_operand src t = SOME (n2w srcoff) /\
   op_prov Gf src = NONE /\ op_taint tnf src = {}` by
    (`eval_operand src t = eval_operand src s /\
      op_taint tnf src = op_taint tn src /\ op_prov Gf src = op_prov G src` by
       (irule old_operand_ghost_frame >> reverse conj_tac >- metis_tac[] >>
        qexists_tac `sa` >>
        conj_tac >- (rpt strip_tac >>
          qpat_assum `abi_decoder_operand_live sa.cs_next_var src` mp_tac >>
          qpat_assum `src = Var x` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
          rpt strip_tac >> gvs[abi_decoder_operand_live_def,
             abi_decoder_older_vars_def, not_fresh_at_def]) >> metis_tac[]) >>
     metis_tac[]) >>
  `eval_operand (Var out) t = SOME (n2w j)` by
    metis_tac[valueEncodingPropsTheory.mem_word_at_eq_mload, w2n_n2w,
      arithmeticTheory.LESS_MOD] >>
  `allocas_from lo t` by metis_tac[allocas_from_def] >>
  drule_all abi_decode_loop_source_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `not_fresh_at s4 input /\ local_ptrs_reserved ce s4 /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x) /\
   abi_decoder_operand_live s4.cs_next_var hi` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,
      exprLoweringPropsTheory.local_ptrs_reserved_next_var,
      abiDecoderReentryTheory.abi_decoder_operand_live_mono] >>
  `eval_operand hi u = SOME (n2w h) /\
   op_prov Gu hi = NONE /\ op_taint tnu hi = {}` by
    (`!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     `eval_operand hi u = eval_operand hi s /\
      op_taint tnu hi = op_taint tn hi /\ op_prov Gu hi = op_prov G hi` by
       (irule old_operand_ghost_frame >> reverse conj_tac >- metis_tac[] >>
        qexists_tac `sa` >>
        conj_tac >- (rpt strip_tac >>
          qpat_assum `abi_decoder_operand_live sa.cs_next_var hi` mp_tac >>
          qpat_assum `hi = Var x` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
          rpt strip_tac >> gvs[abi_decoder_operand_live_def,
             abi_decoder_older_vars_def, not_fresh_at_def]) >> metis_tac[]) >>
     metis_tac[]) >>
  `allocas_from lo u` by metis_tac[allocas_from_def] >>
  `srcoff+32+j*asz+asz <= h /\
   srcoff+32+j*asz <= h /\
   srcoff+32+j*asz+asz <= LENGTH input_bytes` by
    metis_tac[abi_decode_loop_setup_window] >>
  `h < dimword (:256) /\
   (dec_info_needs_offset ei ==> srcoff+32+j*asz+32 <= LENGTH input_bytes)` by
    (conj_tac >- decide_tac >> strip_tac >> res_tac >> decide_tac) >>
  drule_all abi_decode_loop_select_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac)
  >- (disj1_tac >> qexistsl_tac [`t'`,`Gf'`,`tnf'`] >> gen_tac >>
      qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
      qpat_assum `!D. gas_origin_ptr_path _ (t,Gf,tnf) _ _` (qspec_then `D` mp_tac) >>
      qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tnu) _ _` (qspec_then `D` mp_tac) >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  `sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_var <= s5.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u' = lookup_var x s /\
     FLOOKUP Gu' x = FLOOKUP G x /\ op_taint tnu' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at s1 x /\ not_fresh_at s4 x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >> metis_tac[]) >>
  `not_fresh_at s5 input /\ local_ptrs_reserved ce s5 /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
   abi_decoder_operand_live s5.cs_next_var (Var dst) /\
   abi_decoder_operand_live s5.cs_next_var (Var out)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,
      exprLoweringPropsTheory.local_ptrs_reserved_next_var,
      abiDecoderReentryTheory.abi_decoder_operand_live_mono] >>
  `not_fresh_at sa dst /\ not_fresh_at s1 out` by
    (conj_tac >-
       (qpat_assum `abi_decoder_operand_live sa.cs_next_var (Var dst)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
     qpat_assum `abi_decoder_operand_live s1.cs_next_var (Var out)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `lookup_var dst u' = SOME (n2w d) /\
   FLOOKUP Gu' dst = SOME (output_base,output_cap) /\
   ptr_covers Gu' tnu' dst u' (32+n*msz)` by
    (conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> metis_tac[]) >>
  `!x. not_fresh_at s1 x ==> lookup_var x u' = lookup_var x t /\
     FLOOKUP Gu' x = FLOOKUP Gf x /\
     op_taint tnu' (Var x) = op_taint tnf (Var x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (Var out) u' = SOME (n2w j) /\
   op_prov Gu' (Var out) = NONE /\ op_taint tnu' (Var out) = {}` by
    (qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x u' = _ /\ _` drule >>
     strip_tac >>
     qpat_assum `eval_operand (Var out) t = SOME (n2w j)` mp_tac >>
     qpat_assum `op_prov Gf (Var out) = NONE` mp_tac >>
     qpat_assum `op_taint tnf (Var out) = {}` mp_tac >>
     qpat_assum `lookup_var out u' = _` mp_tac >>
     qpat_assum `FLOOKUP Gu' out = _` mp_tac >>
     qpat_assum `op_taint tnu' (Var out) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[eval_operand_def, op_prov_def]) >>
  `allocas_from lo u'` by metis_tac[allocas_from_def] >>
  drule_all abi_decode_loop_destination_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!op. abi_decoder_operand_live s5.cs_next_var op ==>
      eval_operand op u'' = eval_operand op u' /\
      op_taint tnu'' op = op_taint tnu' op /\
      op_prov Gu'' op = op_prov Gu' op` by
    (gen_tac >> strip_tac >> irule old_operand_ghost_frame >>
     reverse conj_tac >- asm_rewrite_tac[] >> qexists_tac `s5` >>
     conj_tac >- (rpt strip_tac >>
       qpat_assum `abi_decoder_operand_live s5.cs_next_var op` mp_tac >>
       qpat_assum `op = Var x` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
       rpt strip_tac >> gvs[abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def]) >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live s5.cs_next_var hi` by
    metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono] >>
  `eval_operand (Var out) u'' = SOME (n2w j) /\
   op_prov Gu'' (Var out) = NONE /\ op_taint tnu'' (Var out) = {} /\
   eval_operand child_src u'' = SOME (n2w q) /\
   op_prov Gu'' child_src = NONE /\ op_taint tnu'' child_src = {} /\
   eval_operand hi u'' = SOME (n2w h)` by metis_tac[] >>
  `s5.cs_next_var <= sb.cs_next_var` by
    (drule abi_decode_indexed_address_counters >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u'' = lookup_var x s /\
     FLOOKUP Gu'' x = FLOOKUP G x /\
     op_taint tnu'' (Var x) = op_taint tn (Var x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!name b k. local_region ce es.scopes u'' name b k ==>
     cell+32 <= b \/ b+k <= cell` by
    (rpt strip_tac >>
     `local_region ce es.scopes s name b k` by
       metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
     metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`u''`,`Gu''`,`tnu''`,`q`,`child`] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- (gen_tac >>
    qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
    qpat_assum `!D. gas_origin_ptr_path _ (t,Gf,tnf) _ _` (qspec_then `D` mp_tac) >>
    qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tnu) _ _` (qspec_then `D` mp_tac) >>
    qpat_assum `!D. gas_origin_ptr_path _ (u',Gu',tnu') _ _` (qspec_then `D` mp_tac) >>
    POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
    metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  asm_rewrite_tac[] >>
  metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono]
QED
