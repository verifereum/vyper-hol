Theory bodyFullAbiDecodeBytesCase
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeBytesPrefix
  bodyFullAbiDecodeBytesTail abiDecoderBytesPhases abiDecoderBytestringCases
  abiDecoderCoherence abiEncoder compileEnv words list rich_list finite_map

val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\ ptr_covers G tn output s output_cap /\
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

val owned_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\ base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off <= h /\ h <= LENGTH input_bytes) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/ write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val owned_decoder_post = ``\start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))) \/
     (?t. r = Abort Revert_abort t))``;

val owned_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\ info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\
       off + abi_member_head_size (vyper_to_abi_type env ty) <= h /\ h <= LENGTH input_bytes) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d d (type_memory_size tv) s G tn``;

val owned_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^owned_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==> (^owned_decoder_post) start finish s G tn``;

val guarded_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\ base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
     off < dimword (:256) /\ h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/ write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\ info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
       off < dimword (:256) /\ h <= LENGTH input_bytes /\
       ((?clamp. info = DecPrimWord clamp) ==>
         off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^guarded_decoder_pre) start finish dst src opc base_op hi d d (type_memory_size tv) s G tn``;

val guarded_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==> (^owned_decoder_post) start finish s G tn``;

Theorem abi_decode_bytes_guarded_joint:
  !dst src opc base_op hi n.
    (^guarded_to_buf_motive) dst src opc base_op hi (DecBytestring n)
Proof
  BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_size tv = 32+32*((n+31) DIV 32)` by
    (drule abi_decoder_bytestring_cases >>
     disch_then (qspec_then `n` mp_tac) >> simp[] >>
     strip_tac >> gvs[valueEncodingTheory.type_memory_size_def,
       vfmConstantsTheory.word_size_def]) >>
  `n+31 < dimword (:256)` by
    (mp_tac (abiDecoderBytesRuntimeTheory.abi_decode_bytes_round_bounds |> Q.INST [`c` |-> `n`]) >>
     decide_tac) >>
  qpat_x_assum `?off h. _ /\ _ /\ _ /\ _ /\ _` kall_tac >>
  qpat_x_assum `?off h. _` (qx_choose_then `off` (qx_choose_then `h` strip_assume_tac)) >>
  qpat_x_assum `?p. dst = Var p /\ _` (qx_choose_then `dstv` strip_assume_tac) >>
  qpat_x_assum `dst = Var dstv` SUBST_ALL_TAC >>
  qpat_x_assum `base_op = Var input` SUBST_ALL_TAC >>
  qpat_x_assum `opc = MLOAD` SUBST_ALL_TAC >>
  drule_all abiDecodePtrBytesMemberTheory.abi_decode_bytes_member_phases >>
  disch_then (qx_choose_then `head` (qx_choose_then `addr`
    (qx_choose_then `cnt` (qx_choose_then `sh` (qx_choose_then `sl`
      (qx_choose_then `sc` (qx_choose_then `sg` (qx_choose_then `sb` strip_assume_tac)))))))) >>
  `inst_extends start sb /\ same_blocks start sb` by
    metis_tac[emitHelperPropsTheory.inst_extends_trans,
      exprLoweringPropsTheory.same_blocks_def] >>
  `cs_extends start sb /\ cs_extends sb finish'` by
    (rpt conj_tac >> irule cs_extends_same_block >>
     fs[exprLoweringPropsTheory.same_blocks_def, emitHelperPropsTheory.inst_extends_def,
        IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `h < dimword (:256)` by decide_tac >>
  `(^owned_decoder_state) start s G tn` by (simp[] >> metis_tac[]) >>
  `allocas_from lo s` by metis_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `not_fresh_at start input` by
    fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       loweringStateRelDefsTheory.not_fresh_at_def] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all abi_decode_bytes_prefix_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu`
      (qx_choose_then `c` (qx_choose_then `ar` (qx_choose_then `out`
        (map_every assume_tac o CONJUNCTS)))))))
    (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `tnz` assume_tac))))
  >- (qpat_x_assum `cnt = Var out` SUBST_ALL_TAC >>
      qpat_x_assum `addr = Var ar` SUBST_ALL_TAC >>
      `abiDecoderBytesPrefix$abi_decode_bytes_position_prefix src MLOAD (Var input) hi n start =
        ((Var ar,Var out),sb)` by
        (simp[abiDecoderBytesPrefixTheory.abi_decode_bytes_position_prefix_trace] >>
         qexists_tac `sg` >> simp[] >>
         qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
         simp[abiDecoderGuardsTheory.abi_decode_count_guard_def,
              abiDecoderGuardTheory.abi_decode_le_guard_def,
              comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
         rpt (pop_assum kall_tac) >>
         rpt (pairarg_tac >> gvs[])) >>
      `start.cs_next_var <= sb.cs_next_var` by
        metis_tac[abiDecoderBytesPrefixTheory.abi_decode_bytes_position_prefix_shape,
          abiDecoderContractTheory.abi_decode_source_opcode_def] >>
      `not_fresh_at start dstv` by
        fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
           abiDecoderReentryTheory.abi_decoder_older_vars_def,
           loweringStateRelDefsTheory.not_fresh_at_def] >>
      `lookup_var dstv u = lookup_var dstv s /\
       FLOOKUP Gu dstv = FLOOKUP G dstv /\
       op_taint tnu (Var dstv) = op_taint tn (Var dstv)` by metis_tac[] >>
      `ptr_covers Gu tnu dstv u (32+32*((n+31) DIV 32))` by
        (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
         qexistsl_tac [`G`, `s`, `tn`] >> simp[] >>
         qpat_x_assum `ptr_covers G tn dstv s _` mp_tac >> simp[]) >>
      `lookup_var dstv u = SOME (n2w d)` by
        fs[venomStateTheory.eval_operand_def] >>
      `local_ptrs_reserved ce sb` by
        metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
      `not_fresh_at sb input /\ not_fresh_at sb dstv /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x)` by
        (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
      `abi_decoder_operand_live sb.cs_next_var (Var out)` by
        fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
           abiDecoderReentryTheory.abi_decoder_older_vars_def,
           loweringStateRelDefsTheory.not_fresh_at_def] >>
      `input_word + n2w off = n2w (w2n input_word + off)` by simp[GSYM word_add_n2w] >>
      `abi_decode_ptr_window Gu tnu u ar (n2w (w2n input_word+off)) (32+c)` by metis_tac[] >>
      `w2n input_word <= w2n input_word+off /\
       w2n input_word+off+32+c <= w2n input_word+LENGTH input_bytes` by decide_tac >>
      `d+32+32*((n+31) DIV 32) <= output_base+output_cap /\
       (w2n input_word+LENGTH input_bytes <= d \/
        d+32+32*((n+31) DIV 32) <= w2n input_word)` by decide_tac >>
      `EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+32+32*((n+31) DIV 32) <= b) live` by
        (qpat_x_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ (b+k <= d \/ _)) live` mp_tac >>
         qpat_x_assum `type_memory_size tv = _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
      `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+32+32*((n+31) DIV 32) <= b) protected` by
        (qpat_x_assum `EVERY (\(a,bytes). a+LENGTH bytes <= d \/ _) protected` mp_tac >>
         qpat_x_assum `type_memory_size tv = _` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[]) >>
      `FLOOKUP Gu dstv = SOME (output_base,output_cap) /\ op_taint tnu (Var dstv) = {}` by simp[] >>
      `?t Gf tnf.
        (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
          (u,Gu,tnu) [] (OK t,Gf,tnf)) /\
        ~t.vs_halted /\ t.vs_current_bb = finish'.cs_current_bb /\
        t.vs_inst_idx = LENGTH finish'.cs_current_insts /\
        (^owned_decoder_state) finish' t Gf tnf /\
        (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x u /\
          FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tnf (Var x) = op_taint tnu (Var x))` by
        (irule abi_decode_bytes_tail_owned_joint >>
         asm_rewrite_tac[] >>
         qexistsl_tac [`w2n input_word+off`, `ar`, `c`, `Var out`, `d`, `dstv`, `n`] >>
         asm_rewrite_tac[]) >>
      qexistsl_tac [`OK t`, `Gf`, `tnf`] >>
      (conj_tac >- (rpt strip_tac >>
        irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
        qexistsl_tac [`Gu`, `u`, `tnu`] >> metis_tac[])) >>
      disj1_tac >> qexists_tac `t` >> asm_rewrite_tac[] >>
      (conj_tac >-
        (qpat_x_assum `(^owned_decoder_state) finish' t Gf tnf` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[] >> metis_tac[])) >>
      rpt strip_tac >>
      `not_fresh_at sb x` by
        (qpat_x_assum `not_fresh_at start x` mp_tac >>
         qpat_x_assum `start.cs_next_var <= sb.cs_next_var` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
      metis_tac[]) >>
  qexistsl_tac [`Abort Revert_abort z`, `Gz`, `tnz`] >> simp[]
QED

Theorem abi_decode_bytes_case_joint:
  !dst src opc base_op hi n.
    (^owned_to_buf_motive) dst src opc base_op hi (DecBytestring n)
Proof
  BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_member_head_size (vyper_to_abi_type env ty) = 32` by
    (drule abi_decoder_bytestring_cases >>
     disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     simp[vyperABITheory.vyper_to_abi_type_def,
          abiDecodeRangesTheory.abi_member_head_size_def]) >>
  qpat_x_assum `?off h. _ /\ _ /\ off + _ <= h /\ _`
    (qx_choose_then `off` (qx_choose_then `h` strip_assume_tac)) >>
  `off < dimword (:256) /\ h < dimword (:256) /\ 0 < h` by decide_tac >>
  `hi <> Lit 0w` by
    (strip_tac >>
     qpat_x_assum `eval_operand hi s = _` mp_tac >>
     asm_rewrite_tac[venomStateTheory.eval_operand_def] >>
     simp[n2w_11] >> decide_tac) >>
  irule (abi_decode_bytes_guarded_joint |> BETA_RULE) >>
  rpt (FIRST [conj_tac, first_assum ACCEPT_TAC]) >>
  qexistsl_tac [`base_op`, `d`, `dst`, `env`, `hi`, `n`, `opc`, `sf`, `src`, `tv`, `ty`] >>
  rpt (FIRST [conj_tac, first_assum ACCEPT_TAC]) >>
  qexistsl_tac [`off`, `h`] >> simp[]
QED
