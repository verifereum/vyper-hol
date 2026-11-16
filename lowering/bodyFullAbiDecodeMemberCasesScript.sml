Theory bodyFullAbiDecodeMemberCases
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeComplexPrefix
  bodyFullAbiDecodeMemberPrefix bodyFullAbiDecodeDecoderBase fragGasOriginPtrLoop
  abiDecoderMemberInfos abiDecoderCoherence abiEncoder
  compileEnv words list rich_list finite_map

(* Syntactic interfaces from Interface, not additional HOL definitions. *)
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
       FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\
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
  (w2n input_word+LENGTH input_bytes <= write_start \/
    write_start+size <= w2n input_word) /\
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

val guarded_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
     h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/
    write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
       h <= LENGTH input_bytes /\
       ((?clamp. info = DecPrimWord clamp) ==>
         off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^guarded_decoder_pre) start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn``;

val guarded_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==>
    (^owned_decoder_post) start finish s G tn``;

val bounded_member_entry = ``\dst src opc base_op hi elems ao vo env sf pretys pretvs tys tvs live protected start finish s G tn d.
    LIST_REL (abi_decoder_coherent ce env sf) (pretys++tys) (pretvs++tvs) /\
    LENGTH pretys = LENGTH pretvs /\
    elems = abi_decoder_member_infos sf ce tys /\
    ao = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pretys) /\
    vo = SUM (MAP (type_memory_bytes ce) pretys) /\
    hi <> Lit 0w /\
    (?off h. eval_operand src s = SOME (n2w off) /\
      eval_operand hi s = SOME (n2w h) /\
      off+ao+SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys) <= h /\
      h <= LENGTH input_bytes) /\
    compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo start =
      ((),finish) /\
    eval_operand dst s = SOME (n2w d) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d (d+vo)
      (SUM (MAP (type_memory_bytes ce) tys)) s G tn``;

val bounded_complex_elems_motive = ``\dst src opc base_op hi elems ao vo.
  !env sf pretys pretvs tys tvs live protected start finish s G tn d.
    (^bounded_member_entry) dst src opc base_op hi elems ao vo env sf
      pretys pretvs tys tvs live protected start finish s G tn d ==>
    (^owned_decoder_post) start finish s G tn``;

Theorem abi_decode_complex_guarded_conditional:
  (^bounded_complex_elems_motive) dst src opc base_op hi infos 0 0 ==>
  (^guarded_to_buf_motive) dst src opc base_op hi (DecComplex dyn infos)
Proof
  BETA_TAC >> disch_tac >> rpt gen_tac >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) o
    MATCH_MP (BETA_RULE abi_decode_complex_prefix_joint))
  >- (qexistsl_tac [`Abort Revert_abort t`, `Gf`, `tnf`] >> simp[]) >>
  first_x_assum (qspecl_then [`env'`, `sf'`, `[]`, `[]`] mp_tac) >>
  disch_then (qspecl_then [`tys`, `tvs`, `live`, `protected`] mp_tac) >>
  disch_then (qspecl_then [`sb`, `finish'`, `t`] mp_tac) >>
  disch_then (qspecl_then [`Gf`, `tnf`, `d`] mp_tac) >>
  simp_tac bool_ss [APPEND, MAP, SUM, LENGTH, arithmeticTheory.ADD_CLAUSES] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qexistsl_tac [`r`, `G'`, `tn'`] >> conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gf`, `t`, `tnf`] >> simp[]) >>
  `start.cs_next_var <= sb.cs_next_var` by
    metis_tac[abiDecodePtrPrimsTheory.abi_decode_complex_header_shape] >>
  `!x. not_fresh_at start x ==> not_fresh_at sb x` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `(?u. r = OK u /\ _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac
      (fn th => disj2_tac >> ACCEPT_TAC th)) >>
  disj1_tac >> qexists_tac `t'` >>
  ASM_SIMP_TAC bool_ss [] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[]
QED

Theorem abi_decode_member_bounded_conditional:
  ((elems = []) \/
   (?ei asz msz rest. elems = (ei,asz,msz)::rest /\
     (!elem_dst elem_src.
       (^guarded_to_buf_motive) elem_dst elem_src opc base_op hi ei) /\
     (^bounded_complex_elems_motive) dst src opc base_op hi rest
       (ao+asz) (vo+msz))) ==>
  (^bounded_complex_elems_motive) dst src opc base_op hi elems ao vo
Proof
  BETA_TAC >> disch_then (DISJ_CASES_THEN2 SUBST_ALL_TAC strip_assume_tac)
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gnvs[abiDecoderSingletonSetupTheory.abi_decode_complex_nil,
          comp_return_def] >>
      qexistsl_tac [`OK s`, `G`, `tn`] >> conj_tac
      >- (rpt strip_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
      disj1_tac >> qexists_tac `s` >> simp[] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >>
  Cases_on `tys`
  >- (qpat_x_assum `LIST_REL _ _ _ /\ _` (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) >>
      simp[abi_decoder_member_infos_def]) >>
  Cases_on `tvs`
  >- (qpat_x_assum `LIST_REL _ _ _ /\ _`
        (fn th => mp_tac (CONJUNCT1 th) >>
          mp_tac (CONJUNCT1 (CONJUNCT2 th))) >>
      POP_ASSUM_LIST (K all_tac) >>
      strip_tac >> disch_then (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  qpat_assum `LIST_REL _ _ _ /\ _`
    (mp_tac o MATCH_MP (BETA_RULE abi_decode_member_prefix_joint)) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `(?rstate Gr tnr. _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac
      (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- (qexistsl_tac [`Abort Revert_abort rstate`, `Gr`, `tnr`] >> simp[]) >>
  qpat_x_assum `LIST_REL _ _ _ /\ _`
    (assume_tac o SRULE [abi_decoder_member_infos_def, MAP] o
       CONJUNCT1 o CONJUNCT2 o CONJUNCT2) >>
  qpat_x_assum `elems = _` SUBST_ALL_TAC >>
  qpat_x_assum `(_::_) = (_::_)` mp_tac >>
  simp_tac bool_ss [CONS_11, pairTheory.PAIR_EQ] >>
  disch_tac >>
  qpat_x_assum `!elem_dst elem_src env sf ty tv live protected start finish s G tn d. _`
    (qspecl_then [`elem_dst`, `elem_src`, `env`, `sf`] mp_tac) >>
  disch_then (qspecl_then [`h`, `h'`, `live`, `protected`] mp_tac) >>
  disch_then (qspecl_then [`head_start`, `tail_start`, `u`, `Gu`, `tnu`, `d+vo`] assume_tac) >>
  qpat_x_assum `!env sf pretys pretvs tys tvs live protected start finish s G tn d. _`
    (qspecl_then [`env`, `sf`, `pretys ++ [h]`, `pretvs ++ [h']`] mp_tac) >>
  disch_then (qspecl_then [`t`, `t'`, `live`, `protected`] assume_tac) >>
  qpat_x_assum `(_ = _ /\ _) /\ _`
    (fn th => mk_asm "schema"
      (GSYM (PURE_REWRITE_RULE [GSYM abi_decoder_member_infos_def] th))) >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _ /\ _ ==> _` mp_tac >>
  asm "schema" (fn th => simp_tac bool_ss [th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qpat_x_assum `(?t. r = OK t /\ _) \/ _`
    (DISJ_CASES_THEN2
      (qx_choose_then `head_state` (map_every assume_tac o CONJUNCTS))
      (qx_choose_then `abort_state` assume_tac))
  >- (qpat_x_assum `r = OK _` SUBST_ALL_TAC >>
      qpat_x_assum `!t Gt tnt. P t Gt tnt`
        (qspecl_then [`head_state`, `G'`, `tn'`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
      qpat_x_assum `!start finish s G tn d. _`
        (qspecl_then [`tail_start`, `finish'`, `head_state`, `G'`, `tn'`, `d`] mp_tac) >>
      asm "schema" (fn th => simp_tac bool_ss [APPEND_ASSOC, th]) >>
      (impl_tac >- (qpat_x_assum `LIST_REL _ _ _ /\ _`
        (ACCEPT_TAC o SIMP_RULE bool_ss [APPEND_ASSOC]))) >>
      disch_then (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
      qexistsl_tac [`r`, `G''`, `tn''`] >> conj_tac
      >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
          qexistsl_tac [`Gu`, `u`, `tnu`] >> conj_tac >- simp[] >>
          irule gas_origin_ptr_path_trans >>
          qexistsl_tac [`G'`, `head_state`, `tn'`] >> simp[]) >>
      `head_start.cs_next_var <= tail_start.cs_next_var` by
        (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ head_start = _` mp_tac >>
         qspecl_then [`elem_dst`, `elem_src`, `opc`, `base_op`, `hi`,
           `type_to_abi_dec_info sf ce h`, `head_start`] mp_tac
           (cj 1 exprLoweringPropsTheory.ci_mono_compile_abi_decode) >>
         POP_ASSUM_LIST (K all_tac) >>
         rpt strip_tac >> gvs[exprLoweringPropsTheory.ci_mono_def]) >>
      `!x. not_fresh_at start x ==> not_fresh_at head_start x /\ not_fresh_at tail_start x` by
        (qpat_x_assum `start.cs_next_var <= head_start.cs_next_var` mp_tac >>
         qpat_x_assum `head_start.cs_next_var <= tail_start.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
         metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      qpat_x_assum `(?t. r = OK t /\ _) \/ _`
        (DISJ_CASES_THEN2
          (qx_choose_then `final_state` (map_every assume_tac o CONJUNCTS))
          (fn th => disj2_tac >> ACCEPT_TAC th)) >>
      disj1_tac >> qexists_tac `final_state` >>
      ASM_SIMP_TAC bool_ss [] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`r`, `G'`, `tn'`] >> conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gu`, `u`, `tnu`] >> simp[]) >>
  disj2_tac >> qexists_tac `abort_state` >> first_assum ACCEPT_TAC
QED
