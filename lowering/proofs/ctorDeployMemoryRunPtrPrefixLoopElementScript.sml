(* Zero-hi element preparation: concrete code boundaries for paired execution. *)
Theory ctorDeployMemoryRunPtrPrefixLoopElement
Ancestors
  ctorDeployMemoryRunPtrPrefixLoopHeader ctorDeployMemoryRunPtrPrefixMemberSetup
  ctorDeployMemoryRunPtrPrefixBoolBody ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixWordRead
  ctorDeployMemoryRunPtrPrefixLoopIteration ctorAbiActualArrayBody
  ctorAbiActualArrayIteration abiDecoderTypedContract
  abiDecoderLoopSetup abiDecoderIndexedAddress abiEncoder abiDecoderContract abiDecoderReentry
  compileEnv emitHelper exprLoweringProps ASCIInumbers
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  finite_map words list rich_list arithmetic pred_set codegenRel

Theorem prefix_loop_element_setup_code:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) di asz msz st = (ops,middle) ==>
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      id = st.cs_next_id
  in
    if dec_info_needs_offset di then
      ops = (Var (x 0),Var (x 5),Var (x 8)) /\
      emitted_insts st middle =
       [mk_inst id MLOAD [ip] [x 0];
        mk_inst (id+1) ADD [src;Lit 32w] [x 1];
        mk_inst (id+2) MUL [Var (x 0);Lit (n2w asz)] [x 2];
        mk_inst (id+3) ADD [Var (x 1);Var (x 2)] [x 3];
        mk_inst (id+4) DLOAD [Var (x 3)] [x 4];
        mk_inst (id+5) ADD [Var (x 1);Var (x 4)] [x 5];
        mk_inst (id+6) ADD [dst;Lit 32w] [x 6];
        mk_inst (id+7) MUL [Var (x 0);Lit (n2w msz)] [x 7];
        mk_inst (id+8) ADD [Var (x 6);Var (x 7)] [x 8]]
    else
      ops = (Var (x 0),Var (x 3),Var (x 6)) /\
      emitted_insts st middle =
       [mk_inst id MLOAD [ip] [x 0];
        mk_inst (id+1) ADD [src;Lit 32w] [x 1];
        mk_inst (id+2) MUL [Var (x 0);Lit (n2w asz)] [x 2];
        mk_inst (id+3) ADD [Var (x 1);Var (x 2)] [x 3];
        mk_inst (id+4) ADD [dst;Lit 32w] [x 4];
        mk_inst (id+5) MUL [Var (x 0);Lit (n2w msz)] [x 5];
        mk_inst (id+6) ADD [Var (x 4);Var (x 5)] [x 6]]
Proof
  Cases_on `dec_info_needs_offset di` >>
  simp[abi_decode_array_element_setup_def,abi_decode_indexed_address_def,
    compile_abi_decode_dyn_elem_ptr_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,
    emit_def,LET_THM] >> strip_tac >>
  qpat_x_assum `_ = middle` (SUBST1_TAC o SYM) >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,DROP_LENGTH_APPEND] >> REFL_TAC
QED

Theorem prefix_loop_element_arith_block:
  (opc = ADD \/ opc = MUL) /\
  eval_operand a s = SOME u /\ eval_operand c s = SOME v /\
  op_taint tn a = {} /\ op_taint tn c = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid opc [a;c] [x]) ==>
  let i = mk_inst iid opc [a;c] [x];
      t = update_var x (if opc = ADD then u+v else u*v) s;
      H = set_prov G [x] (if opc = ADD then first_prov G [a;c] else NONE);
      qt = step_taint i s t tn
  in
    (ptr_safe_block D lo fuel ctx fn PG H qt bb
       (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  mp_tac (Q.INST [`b` |-> `c`, `f` |-> `fuel`]
    prefix_bool_body_arith_certificate) >>
  asm_simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  `~is_terminator (mk_inst iid opc [a;c] [x]).inst_opcode` by
    (gvs[mk_inst_def,is_terminator_def]) >>
  drule_all ptr_safe_block_step >> simp[]
QED

Theorem prefix_loop_element_mul_taint:
  op_taint tn a = {} /\ op_taint tn c = {} ==>
  step_taint (mk_inst iid MUL [a;c] [x]) s (update_var x w s) tn =
    tn with t_var := tn.t_var |+ (x,{})
Proof
  strip_tac >>
  simp[step_taint_def,mk_inst_def,set_var_taint_def,mem_taint_def,
    store_taint_def,imm_taint_def,adopt_reset_def,update_var_def,
    new_site_bytes_def,step_writes_def,written_taint_def,
    source_memory_write_ranges_def,range_bytes_def,FLOOKUP_DEF,
    out_taint_def,taint_component_equality,EXTENSION,SF CONJ_ss] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem prefix_loop_element_indexed_pair:
  eval_operand dst s = SOME d /\ eval_operand idx s = SOME j /\
  op_taint tn dst = {} /\ op_taint tn idx = {} /\
  op_prov G dst = prov /\
  ALL_DISTINCT [x;y;z] /\ dst <> Var x /\ dst <> Var y /\
  idx <> Var x /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq
    [mk_inst iid ADD [dst;Lit 32w] [x];
     mk_inst (iid+1) MUL [idx;Lit stride] [y];
     mk_inst (iid+2) ADD [Var x;Var y] [z]] s = OK t ==>
  ?H qt.
    FLOOKUP H z = prov /\ FLOOKUP H x = prov /\
    op_taint qt (Var x) = {} /\ op_taint qt (Var y) = {} /\
    op_taint qt (Var z) = {} /\
    eval_operand (Var x) t = SOME (d+32w) /\
    eval_operand (Var z) t = SOME (d+32w+j*stride) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. ~MEM v [x;y;z] ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
      get_instruction bb s.vs_inst_idx = SOME (mk_inst iid ADD [dst;Lit 32w] [x]) /\
      get_instruction bb (s.vs_inst_idx+1) = SOME (mk_inst (iid+1) MUL [idx;Lit stride] [y]) /\
      get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (iid+2) ADD [Var x;Var y] [z]) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := s.vs_inst_idx+3) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var x (d+32w) s` >>
  qabbrev_tac `s2 = update_var y (j*stride) s1` >>
  qabbrev_tac `s3 = update_var z (d+32w+j*stride) s2` >>
  qabbrev_tac `g1 = set_prov G [x] (prov)` >>
  qabbrev_tac `g2 = set_prov g1 [y] NONE` >>
  qabbrev_tac `g3 = set_prov g2 [z] (prov)` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  qabbrev_tac `q2 = q1 with t_var := q1.t_var |+ (y,{})` >>
  qabbrev_tac `q3 = q2 with t_var := q2.t_var |+ (z,{})` >>
  `eval_operand idx s1 = SOME j /\ op_taint q1 idx = {}` by
    (Cases_on `idx` >> gvs[Abbr `s1`,Abbr `q1`,eval_operand_def,
      lookup_var_def,update_var_def,op_taint_def,FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iid ADD [dst;Lit 32w] [x]) s = OK s1 /\
   step_inst_base (mk_inst (iid+1) MUL [idx;Lit stride] [y]) s1 = OK s2 /\
   step_inst_base (mk_inst (iid+2) ADD [Var x;Var y] [z]) s2 = OK s3` by
    (conj_tac >- (simp[Abbr `s1`] >> irule prefix_bool_body_add_step >> simp[eval_operand_def]) >>
     conj_tac >- (simp[Abbr `s2`] >> irule prefix_bool_body_mul_step >> simp[eval_operand_def]) >>
     simp[Abbr `s3`] >> irule prefix_bool_body_add_step >>
     gvs[Abbr `s2`,Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE,ALL_DISTINCT]) >>
  `t = s3` by gvs[run_inst_seq_def] >>
  qexistsl [`g3`,`q3`] >>
  conj_tac >- (Cases_on `prov` >> simp[Abbr `g3`,set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]) >>
  conj_tac >- (Cases_on `prov` >> gvs[Abbr `g3`,Abbr `g2`,Abbr `g1`,
    set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,ALL_DISTINCT]) >>
  conj_tac >- gvs[Abbr `q3`,Abbr `q2`,Abbr `q1`,op_taint_def,FLOOKUP_UPDATE,ALL_DISTINCT] >>
  conj_tac >- gvs[Abbr `q3`,Abbr `q2`,Abbr `q1`,op_taint_def,FLOOKUP_UPDATE,ALL_DISTINCT] >>
  conj_tac >- simp[Abbr `q3`,op_taint_def,FLOOKUP_UPDATE] >>
  conj_tac >- gvs[Abbr `s3`,Abbr `s2`,Abbr `s1`,eval_operand_def,
    lookup_var_def,update_var_def,FLOOKUP_UPDATE,ALL_DISTINCT] >>
  conj_tac >- simp[Abbr `s3`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  simp[Abbr `q3`,Abbr `q2`,Abbr `q1`] >>
  conj_tac >- (rpt strip_tac >> Cases_on `prov` >> gvs[Abbr `g3`,Abbr `g2`,Abbr `g1`,
    set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,op_taint_def]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule prefix_member_add_block >> simp[] >>
  qexistsl [`dst`,`Lit 32w`,`iid`,`d`,`32w`,`x`] >>
  simp[eval_operand_def,first_prov_def,Abbr `g1`] >>
  simp[op_taint_def] >>
  irule (SRULE [LET_THM] (Q.INST [`opc` |-> `MUL`] prefix_loop_element_arith_block)) >>
  simp[] >>
  conj_tac >- (fs[Abbr `s1`,allocas_from_def,update_var_def] >> metis_tac[]) >>
  qexistsl [`idx`,`Lit stride`,`iid+1`,`j`,`stride`,`y`] >>
  simp[eval_operand_def,op_taint_def,Abbr `s1`,allocas_from_def,update_var_def] >>
  simp[ADD1] >>
  qmatch_goalsub_abbrev_tac `step_taint _ us ut tq` >>
  `ut = update_var y (j*stride) us` by
    simp[Abbr `ut`,Abbr `us`,update_var_def] >>
  `op_taint tq idx = {} /\ op_taint tq (Lit stride) = {}` by
    simp[Abbr `tq`,op_taint_def] >>
  `step_taint (mk_inst (iid+1) MUL [idx;Lit stride] [y]) us ut tq =
     tq with t_var := tq.t_var |+ (y,{})` by
    (simp[] >> irule prefix_loop_element_mul_taint >> simp[op_taint_def]) >>
  simp[] >>
  irule prefix_member_add_block >> simp[] >>
  conj_tac >- (fs[allocas_from_def,Abbr `us`,update_var_def] >> metis_tac[]) >>
  qexistsl [`Var x`,`Var y`,`iid+2`,`d+32w`,`j*stride`,`z`] >>
  gvs[Abbr `us`,Abbr `tq`,Abbr `s2`,Abbr `s3`,Abbr `g3`,Abbr `g2`,
    eval_operand_def,lookup_var_def,update_var_def,op_taint_def,
    first_prov_def,op_prov_def,set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,
    ALL_DISTINCT,ADD1,ADD_ASSOC] >>
  Cases_on `op_prov G dst` >>
  gvs[op_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]
QED

Theorem prefix_loop_element_mload_pair:
  eval_operand (Var ip) s = SOME p /\
  FLOOKUP G ip = SOME (b,sz) /\ b <= w2n p /\ w2n p+32 <= b+sz /\
  op_taint tn (Var ip) = {} /\
  (!k. k < 32 ==> w2n p+k NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid MLOAD [Var ip] [x];
      t = update_var x (mload (w2n p) s) s;
      H = DRESTRICT G (COMPL {x});
      qt = step_taint i s t tn
  in
    step_inst_base i s = OK t /\ step_inst fuel ctx i s = OK t /\
    ptr_safe_step D lo fuel ctx fn PG G tn i s /\
    ghost_step fuel ctx PG G tn i s = (H,qt) /\
    op_taint qt (Var x) = {} /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint qt (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  conj_tac >- (irule prefix_mload_step >> simp[]) >>
  conj_tac >- (simp[step_inst_non_invoke,mk_inst_def] >>
    pure_rewrite_tac[GSYM mk_inst_def] >> irule prefix_mload_step >> simp[]) >>
  conj_tac >- (irule prefix_mload_ptr_step >> simp[]) >>
  conj_tac >- (irule (SRULE [LET_THM] prefix_mload_ghost_step) >> simp[]) >>
  conj_tac >- (irule prefix_mload_output_clean >> simp[] >> metis_tac[ADD_COMM]) >>
  simp[SRULE [LET_THM] prefix_mload_taint_frame] >>
  rpt strip_tac >> simp[FLOOKUP_DRESTRICT,op_taint_def,
    SRULE [LET_THM] prefix_mload_taint_frame]
QED

Theorem prefix_loop_element_mload_block:
  eval_operand (Var ip) s = SOME p /\
  FLOOKUP G ip = SOME (b,sz) /\ b <= w2n p /\ w2n p+32 <= b+sz /\
  op_taint tn (Var ip) = {} /\
  (!k. k < 32 ==> w2n p+k NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid MLOAD [Var ip] [x]) ==>
  let i = mk_inst iid MLOAD [Var ip] [x];
      t = update_var x (mload (w2n p) s) s;
      H = DRESTRICT G (COMPL {x});
      qt = step_taint i s t tn
  in
    (ptr_safe_block D lo fuel ctx fn PG H qt bb
       (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  mp_tac prefix_loop_element_mload_pair >>
  asm_simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  `~is_terminator (mk_inst iid MLOAD [Var ip] [x]).inst_opcode` by
    simp[mk_inst_def,is_terminator_def] >>
  drule_all ptr_safe_block_step >> simp[]
QED

Theorem prefix_loop_element_dynamic_pair:
  eval_operand head s = SOME a /\ eval_operand base_op s = SOME c /\
  op_taint tn head = {} /\ op_taint tn base_op = {} /\
  base_op <> Var x /\ x <> y /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst iid DLOAD [head] [x];
    mk_inst (iid+1) ADD [base_op;Var x] [y]] s = OK t ==>
  ?H qt.
    op_taint qt (Var y) = {} /\
    eval_operand (Var y) t = SOME (c+abi_decode_load DLOAD a s) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x /\ v <> y ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
      get_instruction bb s.vs_inst_idx = SOME (mk_inst iid DLOAD [head] [x]) /\
      get_instruction bb (s.vs_inst_idx+1) = SOME (mk_inst (iid+1) ADD [base_op;Var x] [y]) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := s.vs_inst_idx+2) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  qabbrev_tac `w = abi_decode_load DLOAD a s` >>
  qabbrev_tac `s1 = update_var x w s` >>
  qabbrev_tac `s2 = update_var y (c+w) s1` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {x})` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  `eval_operand base_op s1 = SOME c /\ op_taint q1 base_op = {}` by
    (Cases_on `base_op` >> gvs[Abbr `s1`,Abbr `q1`,eval_operand_def,
      lookup_var_def,update_var_def,op_taint_def,FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iid DLOAD [head] [x]) s = OK s1` by
    (simp[Abbr `s1`,Abbr `w`] >>
     qpat_assum `eval_operand head s = SOME a` (mp_then Any mp_tac prefix_dload_step) >>
     disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     simp[abi_decode_load_def,abi_decode_source_def]) >>
  `step_inst_base (mk_inst (iid+1) ADD [base_op;Var x] [y]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule prefix_bool_body_add_step >>
     simp[Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `t = s2` by gvs[run_inst_seq_def] >>
  qexistsl [`set_prov g1 [y] (first_prov g1 [base_op;Var x])`,
    `q1 with t_var := q1.t_var |+ (y,{})`] >>
  simp[Abbr `q1`,op_taint_def,FLOOKUP_UPDATE,Abbr `s2`,
    eval_operand_def,lookup_var_def,update_var_def,Abbr `w`] >>
  conj_tac >- (rpt strip_tac >> Cases_on `first_prov g1 [base_op;Var x]` >>
    simp[Abbr `g1`,set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule prefix_member_dload_block >> simp[] >>
  qexistsl [`a`,`iid`,`head`,`x`] >>
  simp[Abbr `g1`] >>
  irule prefix_member_add_block >> simp[] >>
  conj_tac >- (fs[Abbr `s1`,update_var_def,allocas_from_def] >> metis_tac[]) >>
  qexistsl [`base_op`,`Var x`,`iid+1`,`c`,`abi_decode_load DLOAD a s`,`y`] >>
  gvs[Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,
    op_taint_def,FLOOKUP_UPDATE,ADD1,ADD_ASSOC]
QED

(* The indexed trace only writes its three named results.  This frame is
   used when threading the live slot and destination through source setup. *)
Theorem prefix_loop_element_indexed_frame:
  eval_operand base_op s = SOME d /\ eval_operand idx s = SOME j /\
  idx <> Var x /\ ALL_DISTINCT [x;y;z] /\
  run_inst_seq
    [mk_inst iid ADD [base_op;Lit 32w] [x];
     mk_inst (iid+1) MUL [idx;Lit stride] [y];
     mk_inst (iid+2) ADD [Var x;Var y] [z]] s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_inst_idx = s.vs_inst_idx /\
  (!op. (!v. MEM v [x;y;z] ==> op <> Var v) ==>
     eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var x (d+32w) s` >>
  qabbrev_tac `s2 = update_var y (j*stride) s1` >>
  qabbrev_tac `s3 = update_var z (d+32w+j*stride) s2` >>
  `eval_operand idx s1 = SOME j` by
    (Cases_on `idx` >> gvs[Abbr `s1`,eval_operand_def,lookup_var_def,
      update_var_def,FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iid ADD [base_op;Lit 32w] [x]) s = OK s1` by
    (simp[Abbr `s1`] >> irule prefix_bool_body_add_step >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst (iid+1) MUL [idx;Lit stride] [y]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule prefix_bool_body_mul_step >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst (iid+2) ADD [Var x;Var y] [z]) s2 = OK s3` by
    (simp[Abbr `s3`] >> irule prefix_bool_body_add_step >>
     gvs[Abbr `s1`,Abbr `s2`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `t = s3` by gvs[run_inst_seq_def] >>
  simp[Abbr `s3`,Abbr `s2`,Abbr `s1`,update_var_def] >>
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]
QED

Theorem prefix_loop_indexed_code:
  abi_decode_indexed_address base_op idx stride st = (address,st') ==>
  let v0 = "%" ++ toString st.cs_next_var;
      v1 = "%" ++ toString (st.cs_next_var+1);
      v2 = "%" ++ toString (st.cs_next_var+2)
  in address = Var v2 /\ emitted_insts st st' =
    [mk_inst st.cs_next_id ADD [base_op;Lit 32w] [v0];
     mk_inst (st.cs_next_id+1) MUL [idx;Lit (n2w stride)] [v1];
     mk_inst (st.cs_next_id+2) ADD [Var v0;Var v1] [v2]]
Proof
  simp[abi_decode_indexed_address_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
    emit_op_def,fresh_var_def,fresh_id_def,emit_def,LET_THM] >>
  strip_tac >> qpat_x_assum `_ = st'` (SUBST1_TAC o SYM) >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,DROP_LENGTH_APPEND] >> REFL_TAC
QED

Theorem prefix_loop_indexed_compiled_pair:
  abi_decode_indexed_address base_op idx stride st = (address,st') /\
  eval_operand base_op s = SOME d /\ eval_operand idx s = SOME j /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var idx /\
  op_taint tn base_op = {} /\ op_taint tn idx = {} /\
  op_prov G base_op = prov /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    op_prov H address = prov /\ op_taint qt address = {} /\
    eval_operand address t = SOME (d+32w+j*n2w stride) /\
    op_prov H (Var ("%" ++ toString st.cs_next_var)) = prov /\
    op_taint qt (Var ("%" ++ toString st.cs_next_var)) = {} /\
    eval_operand (Var ("%" ++ toString st.cs_next_var)) t = SOME (d+32w) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (s.vs_inst_idx+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> drule prefix_loop_indexed_code >> simp[] >> strip_tac >> fs[] >>
  qabbrev_tac `v0 = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (st.cs_next_var+1)` >>
  qabbrev_tac `v2 = "%" ++ toString (st.cs_next_var+2)` >>
  `ALL_DISTINCT [v0;v1;v2] /\ base_op <> Var v0 /\ base_op <> Var v1 /\ idx <> Var v0` by
    (simp[Abbr `v0`,Abbr `v1`,Abbr `v2`,toString_11] >>
     Cases_on `base_op` >> Cases_on `idx` >>
     fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
     metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  fs[Abbr `v0`,Abbr `v1`,Abbr `v2`] >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_loop_element_indexed_pair >>
  simp[toString_11] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_loop_element_indexed_frame >>
  simp[toString_11] >> strip_tac >>
  qexistsl_tac [`H`,`qt`] >> simp[op_prov_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!v. _ ==> FLOOKUP H v = _ /\ _` irule >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qpat_assum `!k. k < 3 ==> _` (qspec_then `0` assume_tac) >>
  qpat_assum `!k. k < 3 ==> _` (qspec_then `1` assume_tac) >>
  qpat_x_assum `!k. k < 3 ==> _` (qspec_then `2` assume_tac) >> fs[EL,ADD_COMM]
QED

Theorem prefix_loop_mload_compiled_pair:
  emit_op MLOAD [Var ip] st = (loaded,st') /\
  eval_operand (Var ip) s = SOME p /\
  FLOOKUP G ip = SOME (b,sz) /\ b <= w2n p /\ w2n p+32 <= b+sz /\
  op_taint tn (Var ip) = {} /\
  (!k. k < 32 ==> w2n p+k NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    op_taint qt loaded = {} /\ eval_operand loaded t = SOME (mload (w2n p) s) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (s.vs_inst_idx+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  `loaded = Var ("%" ++ toString st.cs_next_var) /\
   emitted_insts st st' = [mk_inst st.cs_next_id MLOAD [Var ip]
     ["%" ++ toString st.cs_next_var]]` by
    (fs[emit_op_def,fresh_var_def,fresh_id_def,emit_def,
      comp_bind_def,comp_ignore_bind_def,comp_return_def,emitted_insts_def] >>
     qpat_x_assum `_ = st'` (SUBST1_TAC o SYM) >>
     simp[DROP_LENGTH_APPEND]) >>
  drule_all prefix_loop_element_mload_pair >>
  disch_then (qspecl_then [`"%" ++ toString st.cs_next_var`,`st.cs_next_id`,
    `0`,`fn`,`PG`,`D`] mp_tac) >> simp[LET_THM] >> strip_tac >>
  `t = update_var ("%" ++ toString st.cs_next_var) (mload (w2n p) s) s` by
    fs[run_inst_seq_def] >>
  qexistsl [`DRESTRICT G (COMPL {"%" ++ toString st.cs_next_var})`,
    `step_taint (mk_inst st.cs_next_id MLOAD [Var ip] ["%" ++ toString st.cs_next_var])
      s (update_var ("%" ++ toString st.cs_next_var) (mload (w2n p) s) s) tn`] >>
  simp[] >>
  conj_tac
  >- simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
        eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
      metis_tac[LESS_EQ_REFL]) >>
  conj_tac
  >- (gen_tac >> disch_tac >> first_x_assum irule >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  rpt gen_tac >> disch_tac >>
  drule_all prefix_loop_element_mload_block >> simp[LET_THM,ADD1]
QED

Theorem prefix_loop_dynamic_code:
  compile_abi_decode_dyn_elem_ptr DLOAD head base_op (Lit 0w) stride st =
    (address,st') ==>
  address = Var ("%" ++ toString (st.cs_next_var+1)) /\
  emitted_insts st st' =
    [mk_inst st.cs_next_id DLOAD [head] ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id+1) ADD
       [base_op;Var ("%" ++ toString st.cs_next_var)]
       ["%" ++ toString (st.cs_next_var+1)]]
Proof
  simp[compile_abi_decode_dyn_elem_ptr_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,emit_op_def,fresh_var_def,fresh_id_def,emit_def,LET_THM] >>
  strip_tac >> qpat_x_assum `_ = st'` (SUBST1_TAC o SYM) >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,DROP_LENGTH_APPEND] >> REFL_TAC
QED

Theorem prefix_loop_element_dynamic_frame:
  eval_operand head s = SOME a /\ eval_operand base_op s = SOME c /\
  base_op <> Var x /\ x <> y /\
  run_inst_seq [mk_inst iid DLOAD [head] [x];
    mk_inst (iid+1) ADD [base_op;Var x] [y]] s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_inst_idx = s.vs_inst_idx /\
  (!op. op <> Var x /\ op <> Var y ==> eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var x (abi_decode_load DLOAD a s) s` >>
  qabbrev_tac `s2 = update_var y (c+abi_decode_load DLOAD a s) s1` >>
  `eval_operand base_op s1 = SOME c` by
    (Cases_on `base_op` >> gvs[Abbr `s1`,eval_operand_def,
      lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iid DLOAD [head] [x]) s = OK s1` by
    (simp[Abbr `s1`] >>
     qpat_assum `eval_operand head s = SOME a` (mp_then Any mp_tac prefix_dload_step) >>
     disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     simp[abi_decode_load_def,abi_decode_source_def]) >>
  `step_inst_base (mk_inst (iid+1) ADD [base_op;Var x] [y]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule prefix_bool_body_add_step >>
     simp[Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `t = s2` by gvs[run_inst_seq_def] >>
  simp[Abbr `s2`,Abbr `s1`,update_var_def] >>
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]
QED

Theorem prefix_loop_dynamic_compiled_pair:
  compile_abi_decode_dyn_elem_ptr DLOAD head base_op (Lit 0w) stride st =
    (address,st') /\
  eval_operand head s = SOME a /\ eval_operand base_op s = SOME c /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  op_taint tn head = {} /\ op_taint tn base_op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    op_taint qt address = {} /\
    eval_operand address t = SOME (c+abi_decode_load DLOAD a s) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (s.vs_inst_idx+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> drule prefix_loop_dynamic_code >> strip_tac >> fs[] >>
  `base_op <> Var ("%" ++ toString st.cs_next_var)` by
    (Cases_on `base_op` >>
     fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
     metis_tac[LESS_EQ_REFL]) >> fs[] >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_loop_element_dynamic_pair >>
  simp[toString_11] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_loop_element_dynamic_frame >>
  simp[toString_11] >> strip_tac >>
  qexistsl [`H`,`qt`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> Cases_on `op` >>
      fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
      metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!v. _ ==> FLOOKUP H v = _ /\ _` irule >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qpat_assum `!k. k < 2 ==> _` (qspec_then `0` assume_tac) >>
  qpat_x_assum `!k. k < 2 ==> _` (qspec_then `1` assume_tac) >> fs[EL,ADD_COMM]
QED

Theorem prefix_loop_element_compiled_stages:
  emit_op MLOAD [ip] st = (idx,c1) /\
  abi_decode_indexed_address src idx abi_sz c1 = (head,c2) /\
  (if dec_info_needs_offset di then
     compile_abi_decode_dyn_elem_ptr opc head
       (Var ("%" ++ toString c1.cs_next_var)) hi abi_sz c2
   else comp_return head c2) = (child_src,c3) /\
  abi_decode_indexed_address dst idx mem_sz c3 = (child_dst,c4) ==>
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st =
    ((idx,child_src,child_dst),c4)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_indexed_address src idx abi_sz c1 = _` mp_tac >>
  simp[abi_decode_indexed_address_def,emit_op_def,fresh_var_def,fresh_id_def,
    emit_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >> strip_tac >>
  gvs[] >>
  fs[abi_decode_array_element_setup_def,emit_op_def,fresh_var_def,fresh_id_def,
    emit_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  Cases_on `dec_info_needs_offset di` >> gvs[comp_return_def]
QED

Theorem prefix_loop_element_compiled_decompose:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st =
    ((idx,child_src,child_dst),c4) ==>
  ?c1 head c2 c3.
    emit_op MLOAD [ip] st = (idx,c1) /\
    abi_decode_indexed_address src idx abi_sz c1 = (head,c2) /\
    (if dec_info_needs_offset di then
       compile_abi_decode_dyn_elem_ptr opc head
         (Var ("%" ++ toString c1.cs_next_var)) hi abi_sz c2
     else comp_return head c2) = (child_src,c3) /\
    abi_decode_indexed_address dst idx mem_sz c3 = (child_dst,c4)
Proof
  strip_tac >> Cases_on `emit_op MLOAD [ip] st` >>
  rename1 `emit_op MLOAD [ip] st = (i,s1)` >>
  Cases_on `abi_decode_indexed_address src i abi_sz s1` >>
  rename1 `abi_decode_indexed_address src i abi_sz s1 = (h,s2)` >>
  Cases_on `if dec_info_needs_offset di then
    compile_abi_decode_dyn_elem_ptr opc h (Var ("%" ++ toString s1.cs_next_var))
      hi abi_sz s2 else comp_return h s2` >>
  rename1 `(if dec_info_needs_offset di then _ else _) = (cs,s3)` >>
  Cases_on `abi_decode_indexed_address dst i mem_sz s3` >>
  rename1 `abi_decode_indexed_address dst i mem_sz s3 = (cd,s4)` >>
  `abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st =
    ((i,cs,cd),s4)` by
    (rule_assum_tac (SRULE []) >> irule prefix_loop_element_compiled_stages >> simp[] >>
     qexists `s3` >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem prefix_loop_element_taint_idx:
  MEM i.inst_opcode [MLOAD;DLOAD;ADD;MUL] ==>
  step_taint i (s with vs_inst_idx := k) (t with vs_inst_idx := k) tn =
  step_taint i s t tn
Proof
  strip_tac >>
  simp[step_taint_def,mem_taint_def,new_site_bytes_def,step_writes_def,
    written_taint_def,out_taint_def,store_taint_def,imm_taint_def,
    source_memory_write_ranges_def,fixed_source_write_range_def,instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem prefix_loop_element_mload_cursor_block:
  eval_operand (Var ip) s = SOME p /\
  FLOOKUP G ip = SOME (b,sz) /\ b <= w2n p /\ w2n p+32 <= b+sz /\
  op_taint tn (Var ip) = {} /\
  (!k. k < 32 ==> w2n p+k NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb cursor = SOME (mk_inst iid MLOAD [Var ip] [x]) ==>
  let i = mk_inst iid MLOAD [Var ip] [x];
      t = update_var x (mload (w2n p) s) s;
      H = DRESTRICT G (COMPL {x});
      qt = step_taint i s t tn
  in
    (ptr_safe_block D lo fuel ctx fn PG H qt bb
       (t with vs_inst_idx := cursor+1) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >> simp[LET_THM] >>
  `eval_operand (Var ip) (s with vs_inst_idx := cursor) = SOME p /\
   allocas_from lo (s with vs_inst_idx := cursor)` by
    (fs[eval_operand_def,lookup_var_def,allocas_from_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := cursor`]
    prefix_loop_element_mload_block) >>
  simp[LET_THM,allocas_from_def] >>
  `mload (w2n p) (s with vs_inst_idx := cursor) = mload (w2n p) s` by
    simp[mload_def] >>
  `update_var x (mload (w2n p) s) (s with vs_inst_idx := cursor) =
    (update_var x (mload (w2n p) s) s) with vs_inst_idx := cursor` by
    simp[update_var_def] >>
  simp[prefix_loop_element_taint_idx,mk_inst_def,ADD1]
QED

Theorem prefix_loop_element_arith_cursor_block:
  (opc = ADD \/ opc = MUL) /\
  eval_operand a s = SOME u /\ eval_operand c s = SOME v /\
  op_taint tn a = {} /\ op_taint tn c = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb cursor = SOME (mk_inst iid opc [a;c] [x]) ==>
  let i = mk_inst iid opc [a;c] [x];
      t = update_var x (if opc = ADD then u+v else u*v) s;
      H = set_prov G [x] (if opc = ADD then first_prov G [a;c] else NONE);
      qt = step_taint i s t tn
  in
    (ptr_safe_block D lo fuel ctx fn PG H qt bb
       (t with vs_inst_idx := cursor+1) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >> simp[LET_THM] >>
  `eval_operand a (s with vs_inst_idx := cursor) = SOME u /\
   eval_operand c (s with vs_inst_idx := cursor) = SOME v /\
   allocas_from lo (s with vs_inst_idx := cursor)` by
    (fs[instIdxIndepTheory.eval_op_inst_idx,allocas_from_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := cursor`]
    prefix_loop_element_arith_block) >>
  simp[LET_THM] >>
  `update_var x (if opc = ADD then u+v else u*v) (s with vs_inst_idx := cursor) =
    (update_var x (if opc = ADD then u+v else u*v) s) with vs_inst_idx := cursor` by
    simp[update_var_def] >>
  Cases_on `opc = ADD` >> gvs[] >>
  simp[prefix_loop_element_taint_idx,mk_inst_def,ADD1]
QED

Theorem prefix_loop_element_dload_cursor_block:
  eval_operand off s = SOME a /\ op_taint tn off = {} /\
  abi_decode_load DLOAD a s = w /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  get_instruction bb cursor = SOME (mk_inst iid DLOAD [off] [x]) ==>
  (ptr_safe_block D lo fuel ctx fn PG (DRESTRICT G (COMPL {x}))
     (tn with t_var := tn.t_var |+ (x,{})) bb
     ((update_var x w s) with vs_inst_idx := cursor+1) ==>
   ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := cursor`]
    prefix_member_dload_block) >>
  fs[instIdxIndepTheory.eval_op_inst_idx,abi_decode_load_def,
    abi_decode_source_def,allocas_from_def,update_var_def,ADD1] >>
  metis_tac[]
QED

Theorem prefix_loop_element_dynamic_uniform_pair:
  eval_operand head s = SOME a /\ eval_operand base_op s = SOME c /\
  op_taint tn head = {} /\ op_taint tn base_op = {} /\
  base_op <> Var x /\ x <> y /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst iid DLOAD [head] [x];
    mk_inst (iid+1) ADD [base_op;Var x] [y]] s = OK t ==>
  ?H qt.
    op_taint qt (Var y) = {} /\
    eval_operand (Var y) t = SOME (c+abi_decode_load DLOAD a s) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x /\ v <> y ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      get_instruction bb cursor = SOME (mk_inst iid DLOAD [head] [x]) /\
      get_instruction bb (cursor+1) = SOME (mk_inst (iid+1) ADD [base_op;Var x] [y]) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := cursor+2) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >>
  qabbrev_tac `w = abi_decode_load DLOAD a s` >>
  qabbrev_tac `s1 = update_var x w s` >>
  qabbrev_tac `s2 = update_var y (c+w) s1` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {x})` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  `eval_operand base_op s1 = SOME c /\ op_taint q1 base_op = {}` by
    (Cases_on `base_op` >> gvs[Abbr `s1`,Abbr `q1`,eval_operand_def,
      lookup_var_def,update_var_def,op_taint_def,FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iid DLOAD [head] [x]) s = OK s1` by
    (simp[Abbr `s1`,Abbr `w`] >>
     qpat_assum `eval_operand head s = SOME a` (mp_then Any mp_tac prefix_dload_step) >>
     disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     simp[abi_decode_load_def,abi_decode_source_def]) >>
  `step_inst_base (mk_inst (iid+1) ADD [base_op;Var x] [y]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule prefix_bool_body_add_step >>
     simp[Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `t = s2` by gvs[run_inst_seq_def] >>
  qexistsl [`set_prov g1 [y] (first_prov g1 [base_op;Var x])`,
    `q1 with t_var := q1.t_var |+ (y,{})`] >>
  simp[Abbr `q1`,op_taint_def,FLOOKUP_UPDATE,Abbr `s2`,
    eval_operand_def,lookup_var_def,update_var_def,Abbr `w`] >>
  conj_tac >- (rpt strip_tac >> Cases_on `first_prov g1 [base_op;Var x]` >>
    simp[Abbr `g1`,set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule prefix_loop_element_dload_cursor_block >> simp[] >>
  qexistsl [`a`,`iid`,`head`,`x`] >> simp[Abbr `g1`] >>
  irule (SRULE [LET_THM] (Q.INST [`opc` |-> `ADD`]
    prefix_loop_element_arith_cursor_block)) >> simp[] >>
  conj_tac >- (fs[Abbr `s1`,update_var_def,allocas_from_def] >> metis_tac[]) >>
  qexistsl [`base_op`,`Var x`,`iid+1`,`c`,`abi_decode_load DLOAD a s`,`y`] >>
  gvs[Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,
    op_taint_def,FLOOKUP_UPDATE,ADD1,ADD_ASSOC] >>
  qmatch_goalsub_abbrev_tac `step_taint _ us ut tq` >>
  `ut = update_var y (c+abi_decode_load DLOAD a s) us` by
    simp[Abbr `ut`,Abbr `us`,update_var_def] >>
  `op_taint tq base_op = {} /\ op_taint tq (Var x) = {}` by
    simp[Abbr `tq`,op_taint_def,FLOOKUP_UPDATE] >>
  simp[prefix_member_add_taint,Abbr `tq`]
QED

Theorem prefix_loop_element_indexed_uniform_pair:
  eval_operand dst s = SOME d /\ eval_operand idx s = SOME j /\
  op_taint tn dst = {} /\ op_taint tn idx = {} /\
  op_prov G dst = prov /\
  ALL_DISTINCT [x;y;z] /\ dst <> Var x /\ dst <> Var y /\ idx <> Var x /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq
    [mk_inst iid ADD [dst;Lit 32w] [x];
     mk_inst (iid+1) MUL [idx;Lit stride] [y];
     mk_inst (iid+2) ADD [Var x;Var y] [z]] s = OK t ==>
  ?H qt.
    FLOOKUP H z = prov /\ FLOOKUP H x = prov /\
    op_taint qt (Var x) = {} /\ op_taint qt (Var y) = {} /\ op_taint qt (Var z) = {} /\
    eval_operand (Var x) t = SOME (d+32w) /\
    eval_operand (Var z) t = SOME (d+32w+j*stride) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. ~MEM v [x;y;z] ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      get_instruction bb cursor = SOME (mk_inst iid ADD [dst;Lit 32w] [x]) /\
      get_instruction bb (cursor+1) = SOME (mk_inst (iid+1) MUL [idx;Lit stride] [y]) /\
      get_instruction bb (cursor+2) = SOME (mk_inst (iid+2) ADD [Var x;Var y] [z]) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb (t with vs_inst_idx := cursor+3) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >>
  qabbrev_tac `s1 = update_var x (d+32w) s` >>
  qabbrev_tac `s2 = update_var y (j*stride) s1` >>
  qabbrev_tac `s3 = update_var z (d+32w+j*stride) s2` >>
  qabbrev_tac `g1 = set_prov G [x] prov` >>
  qabbrev_tac `g2 = set_prov g1 [y] NONE` >>
  qabbrev_tac `g3 = set_prov g2 [z] prov` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  qabbrev_tac `q2 = q1 with t_var := q1.t_var |+ (y,{})` >>
  qabbrev_tac `q3 = q2 with t_var := q2.t_var |+ (z,{})` >>
  `eval_operand idx s1 = SOME j /\ op_taint q1 idx = {}` by
    (Cases_on `idx` >> gvs[Abbr `s1`,Abbr `q1`,eval_operand_def,
      lookup_var_def,update_var_def,op_taint_def,FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst iid ADD [dst;Lit 32w] [x]) s = OK s1 /\
   step_inst_base (mk_inst (iid+1) MUL [idx;Lit stride] [y]) s1 = OK s2 /\
   step_inst_base (mk_inst (iid+2) ADD [Var x;Var y] [z]) s2 = OK s3` by
    (conj_tac >- (simp[Abbr `s1`] >> irule prefix_bool_body_add_step >> simp[eval_operand_def]) >>
     conj_tac >- (simp[Abbr `s2`] >> irule prefix_bool_body_mul_step >> simp[eval_operand_def]) >>
     simp[Abbr `s3`] >> irule prefix_bool_body_add_step >>
     gvs[Abbr `s2`,Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE,ALL_DISTINCT]) >>
  `t = s3` by gvs[run_inst_seq_def] >>
  qexistsl [`g3`,`q3`] >>
  conj_tac >- (Cases_on `prov` >> simp[Abbr `g3`,set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]) >>
  conj_tac >- (Cases_on `prov` >> gvs[Abbr `g3`,Abbr `g2`,Abbr `g1`,
    set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,ALL_DISTINCT]) >>
  conj_tac >- gvs[Abbr `q3`,Abbr `q2`,Abbr `q1`,op_taint_def,FLOOKUP_UPDATE,ALL_DISTINCT] >>
  conj_tac >- gvs[Abbr `q3`,Abbr `q2`,Abbr `q1`,op_taint_def,FLOOKUP_UPDATE,ALL_DISTINCT] >>
  conj_tac >- simp[Abbr `q3`,op_taint_def,FLOOKUP_UPDATE] >>
  conj_tac >- gvs[Abbr `s3`,Abbr `s2`,Abbr `s1`,eval_operand_def,
    lookup_var_def,update_var_def,FLOOKUP_UPDATE,ALL_DISTINCT] >>
  conj_tac >- simp[Abbr `s3`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  simp[Abbr `q3`,Abbr `q2`,Abbr `q1`] >>
  conj_tac >- (rpt strip_tac >> Cases_on `prov` >> gvs[Abbr `g3`,Abbr `g2`,Abbr `g1`,
    set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT,op_taint_def]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  irule (SRULE [LET_THM] (Q.INST [`opc` |-> `ADD`]
    prefix_loop_element_arith_cursor_block)) >> simp[] >>
  qexistsl [`dst`,`Lit 32w`,`iid`,`d`,`32w`,`x`] >>
  simp[eval_operand_def,first_prov_def,Abbr `g1`,op_taint_def] >>
  `step_taint (mk_inst iid ADD [dst;Lit 32w] [x]) s s1 tn =
    tn with t_var := tn.t_var |+ (x,{})` by
    (simp[Abbr `s1`] >> irule prefix_member_add_taint >> simp[op_taint_def]) >>
  `first_prov G [dst;Lit 32w] = prov` by
    (simp[first_prov_def,op_prov_def] >> Cases_on `prov` >> simp[]) >>
  simp[op_prov_def] >>
  ` (case prov of NONE => NONE | SOME site => SOME site) = prov` by
    (Cases_on `prov` >> simp[]) >> simp[] >>
  irule (SRULE [LET_THM] (Q.INST [`opc` |-> `MUL`]
    prefix_loop_element_arith_cursor_block)) >> simp[] >>
  conj_tac >- (fs[Abbr `s1`,allocas_from_def,update_var_def] >> metis_tac[]) >>
  qexistsl [`idx`,`Lit stride`,`iid+1`,`j`,`stride`,`y`] >>
  simp[eval_operand_def,op_taint_def,ADD_ASSOC] >>
  `step_taint (mk_inst (iid+1) MUL [idx;Lit stride] [y]) s1 s2
     (tn with t_var := tn.t_var |+ (x,{})) =
     tn with t_var := tn.t_var |+ (x,{}) |+ (y,{})` by
    simp[Abbr `s2`,prefix_loop_element_mul_taint,op_taint_def] >>
  simp[] >>
  irule (SRULE [LET_THM] (Q.INST [`opc` |-> `ADD`]
    prefix_loop_element_arith_cursor_block)) >> simp[] >>
  conj_tac >- (fs[Abbr `s2`,Abbr `s1`,allocas_from_def,update_var_def] >> metis_tac[]) >>
  qexistsl [`Var x`,`Var y`,`iid+2`,`d+32w`,`j*stride`,`z`] >>
  gvs[Abbr `s2`,Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,
    op_taint_def,FLOOKUP_UPDATE,ALL_DISTINCT,ADD_ASSOC] >>
  qmatch_goalsub_abbrev_tac `step_taint _ us ut tq` >>
  `ut = update_var z (d+32w+j*stride) us` by
    simp[Abbr `ut`,Abbr `us`,Abbr `s3`,update_var_def] >>
  `op_taint tq (Var x) = {} /\ op_taint tq (Var y) = {}` by
    simp[Abbr `tq`,op_taint_def,FLOOKUP_UPDATE] >>
  simp[prefix_member_add_taint,Abbr `tq`] >>
  gvs[Abbr `g3`,Abbr `g2`,first_prov_def,op_prov_def,
    set_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT] >>
  Cases_on `op_prov G dst` >> gvs[op_prov_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]
QED

Theorem prefix_loop_indexed_compiled_uniform_pair:
  abi_decode_indexed_address base_op idx stride st = (address,st') /\
  eval_operand base_op s = SOME d /\ eval_operand idx s = SOME j /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var idx /\
  op_taint tn base_op = {} /\ op_taint tn idx = {} /\
  op_prov G base_op = prov /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    op_prov H address = prov /\ op_taint qt address = {} /\
    eval_operand address t = SOME (d+32w+j*n2w stride) /\
    op_prov H (Var ("%" ++ toString st.cs_next_var)) = prov /\
    op_taint qt (Var ("%" ++ toString st.cs_next_var)) = {} /\
    eval_operand (Var ("%" ++ toString st.cs_next_var)) t = SOME (d+32w) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := cursor+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >> drule prefix_loop_indexed_code >> simp[] >> strip_tac >> fs[] >>
  qabbrev_tac `v0 = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (st.cs_next_var+1)` >>
  qabbrev_tac `v2 = "%" ++ toString (st.cs_next_var+2)` >>
  `ALL_DISTINCT [v0;v1;v2] /\ base_op <> Var v0 /\ base_op <> Var v1 /\ idx <> Var v0` by
    (simp[Abbr `v0`,Abbr `v1`,Abbr `v2`,toString_11] >>
     Cases_on `base_op` >> Cases_on `idx` >>
     fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
     metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  fs[Abbr `v0`,Abbr `v1`,Abbr `v2`] >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_loop_element_indexed_uniform_pair >>
  simp[toString_11] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_loop_element_indexed_frame >>
  simp[toString_11] >> strip_tac >>
  qexistsl_tac [`H`,`qt`] >> simp[op_prov_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!v. _ ==> FLOOKUP H v = _ /\ _` irule >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qpat_assum `!k. k < 3 ==> _` (qspec_then `0` assume_tac) >>
  qpat_assum `!k. k < 3 ==> _` (qspec_then `1` assume_tac) >>
  qpat_x_assum `!k. k < 3 ==> _` (qspec_then `2` assume_tac) >> fs[EL,ADD_COMM]
QED

Theorem prefix_loop_dynamic_compiled_uniform_pair:
  compile_abi_decode_dyn_elem_ptr DLOAD head base_op (Lit 0w) stride st =
    (address,st') /\
  eval_operand head s = SOME a /\ eval_operand base_op s = SOME c /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  op_taint tn head = {} /\ op_taint tn base_op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    op_taint qt address = {} /\
    eval_operand address t = SOME (c+abi_decode_load DLOAD a s) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := cursor+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >> drule prefix_loop_dynamic_code >> strip_tac >> fs[] >>
  `base_op <> Var ("%" ++ toString st.cs_next_var)` by
    (Cases_on `base_op` >>
     fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
     metis_tac[LESS_EQ_REFL]) >> fs[] >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_loop_element_dynamic_uniform_pair >>
  simp[toString_11] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = _`) prefix_loop_element_dynamic_frame >>
  simp[toString_11] >> strip_tac >>
  qexistsl [`H`,`qt`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> Cases_on `op` >>
      fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
      metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!v. _ ==> FLOOKUP H v = _ /\ _` irule >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qpat_assum `!k. k < 2 ==> _` (qspec_then `0` assume_tac) >>
  qpat_x_assum `!k. k < 2 ==> _` (qspec_then `1` assume_tac) >> fs[EL,ADD_COMM]
QED

Theorem prefix_loop_mload_compiled_uniform_pair:
  emit_op MLOAD [Var ip] st = (loaded,st') /\
  eval_operand (Var ip) s = SOME p /\
  FLOOKUP G ip = SOME (b,sz) /\ b <= w2n p /\ w2n p+32 <= b+sz /\
  op_taint tn (Var ip) = {} /\
  (!k. k < 32 ==> w2n p+k NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    op_taint qt loaded = {} /\ eval_operand loaded t = SOME (mload (w2n p) s) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := cursor+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >>
  `loaded = Var ("%" ++ toString st.cs_next_var) /\
   emitted_insts st st' = [mk_inst st.cs_next_id MLOAD [Var ip]
     ["%" ++ toString st.cs_next_var]]` by
    (fs[emit_op_def,fresh_var_def,fresh_id_def,emit_def,
      comp_bind_def,comp_ignore_bind_def,comp_return_def,emitted_insts_def] >>
     qpat_x_assum `_ = st'` (SUBST1_TAC o SYM) >>
     simp[DROP_LENGTH_APPEND]) >>
  drule_all prefix_loop_element_mload_pair >>
  disch_then (qspecl_then [`"%" ++ toString st.cs_next_var`,`st.cs_next_id`,
    `0`,`fn`,`PG`,`D`] mp_tac) >> simp[LET_THM] >> strip_tac >>
  `t = update_var ("%" ++ toString st.cs_next_var) (mload (w2n p) s) s` by
    fs[run_inst_seq_def] >>
  qexistsl [`DRESTRICT G (COMPL {"%" ++ toString st.cs_next_var})`,
    `step_taint (mk_inst st.cs_next_id MLOAD [Var ip] ["%" ++ toString st.cs_next_var])
      s (update_var ("%" ++ toString st.cs_next_var) (mload (w2n p) s) s) tn`] >>
  simp[] >>
  conj_tac
  >- simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
        eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
      metis_tac[LESS_EQ_REFL]) >>
  conj_tac
  >- (gen_tac >> disch_tac >> first_x_assum irule >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  rpt gen_tac >> disch_tac >>
  drule_all prefix_loop_element_mload_cursor_block >> simp[LET_THM,ADD1]
QED

(* Uniform continuations compose on the raw middle state.  Only their
   block-safety arguments, never the raw execution endpoints, move cursor. *)
Theorem prefix_loop_element_uniform_append:
  (!cursor fuel bb.
    (!k. k < LENGTH xs ==> get_instruction bb (cursor+k) = SOME (EL k xs)) ==>
    ptr_safe_block D lo fuel ctx fn PG H qt bb
      (m with vs_inst_idx := cursor+LENGTH xs) ==>
    ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor)) /\
  (!cursor fuel bb.
    (!k. k < LENGTH ys ==> get_instruction bb (cursor+k) = SOME (EL k ys)) ==>
    ptr_safe_block D lo fuel ctx fn PG J rt bb
      (t with vs_inst_idx := cursor+LENGTH ys) ==>
    ptr_safe_block D lo fuel ctx fn PG H qt bb (m with vs_inst_idx := cursor)) ==>
  !cursor fuel bb.
    (!k. k < LENGTH (xs++ys) ==>
      get_instruction bb (cursor+k) = SOME (EL k (xs++ys))) ==>
    ptr_safe_block D lo fuel ctx fn PG J rt bb
      (t with vs_inst_idx := cursor+LENGTH (xs++ys)) ==>
    ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor)
Proof
  rpt strip_tac >>
  qpat_x_assum `!cursor fuel bb. _ ==> _ ==> ptr_safe_block _ _ _ _ _ _ G tn _ _` irule >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k. k < LENGTH (xs++ys) ==> _` (qspec_then `k` mp_tac) >>
      simp[EL_APPEND1]) >>
  qpat_x_assum `!cursor fuel bb. _ ==> _ ==> _` irule >>
  reverse conj_tac
  >- (qpat_x_assum `ptr_safe_block _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [LENGTH_APPEND,ADD_ASSOC]) >>
  rpt strip_tac >>
  qpat_x_assum `!k. k < LENGTH (xs++ys) ==> _`
    (qspec_then `LENGTH xs+k` mp_tac) >>
  qpat_x_assum `ptr_safe_block _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `LENGTH xs+k < LENGTH (xs++ys)` by simp[] >>
  `EL (LENGTH xs+k) (xs++ys) = EL k ys` by simp[EL_APPEND2] >>
  pure_asm_rewrite_tac [ADD_ASSOC] >> simp_tac bool_ss []
QED

Theorem prefix_loop_element_stage_layout:
  emit_op MLOAD [ip] st = (idx,c1) /\
  abi_decode_indexed_address src idx abi_sz c1 = (head,c2) /\
  (if dec_info_needs_offset di then
     compile_abi_decode_dyn_elem_ptr DLOAD head
       (Var ("%" ++ toString c1.cs_next_var)) (Lit 0w) abi_sz c2
   else comp_return head c2) = (child_src,c3) /\
  abi_decode_indexed_address dst idx mem_sz c3 = (child_dst,c4) ==>
  c1.cs_next_var = st.cs_next_var+1 /\
  c2.cs_next_var = c1.cs_next_var+3 /\
  c3.cs_next_var = c2.cs_next_var + (if dec_info_needs_offset di then 2 else 0) /\
  c4.cs_next_var = c3.cs_next_var+3 /\
  abi_decoder_operand_live c1.cs_next_var idx /\
  abi_decoder_operand_live c2.cs_next_var head /\
  abi_decoder_operand_live c3.cs_next_var child_src /\
  abi_decoder_operand_live c4.cs_next_var child_dst /\
  emitted_insts st c4 = emitted_insts st c1 ++ emitted_insts c1 c2 ++
    emitted_insts c2 c3 ++ emitted_insts c3 c4
Proof
  Cases_on `dec_info_needs_offset di` >>
  simp[abi_decode_indexed_address_def,compile_abi_decode_dyn_elem_ptr_def,
    emit_op_def,fresh_var_def,fresh_id_def,emit_def,
    comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def,abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,DROP_LENGTH_APPEND] >>
  simp[DROP_APPEND2]
QED

Theorem prefix_loop_element_live_ghost_frame[local]:
  (!v. not_fresh_at st v ==>
    FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) ==>
  !op. abi_decoder_operand_live st.cs_next_var op ==>
    op_prov H op = op_prov G op /\ op_taint qt op = op_taint tn op
Proof
  strip_tac >> Cases >>
  simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,
    not_fresh_at_def,op_prov_def,op_taint_def] >> metis_tac[not_fresh_at_def]
QED

Theorem prefix_loop_optional_compiled_uniform_pair:
  (if dyn then compile_abi_decode_dyn_elem_ptr DLOAD head base_op (Lit 0w) stride st
   else comp_return head st) = (address,st') /\
  eval_operand head s = SOME a /\ eval_operand base_op s = SOME c /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  op_taint tn head = {} /\ op_taint tn base_op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?H qt.
    op_taint qt address = {} /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := cursor+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  Cases_on `dyn` >> simp[] >> strip_tac
  >- (drule_all prefix_loop_dynamic_compiled_uniform_pair >>
      disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
      qexistsl [`H`,`qt`] >> simp[]) >>
  gvs[comp_return_def,emitted_insts_def,DROP_LENGTH_NIL,run_inst_seq_def] >>
  qexistsl [`G`,`tn`] >> simp[]
QED

Theorem prefix_loop_element_setup_uniform_pair:
  abi_decode_array_element_setup (Var ip) src dst DLOAD (Lit 0w)
    di abi_sz mem_sz st = ((idx,child_src,child_dst),c4) /\
  eval_operand (Var ip) s = SOME p /\
  FLOOKUP G ip = SOME (ib,isz) /\ ib <= w2n p /\ w2n p+32 <= ib+isz /\
  op_taint tn (Var ip) = {} /\ (!k. k < 32 ==> w2n p+k NOTIN tn.t_mem) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\ op_prov G dst = prov /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts st c4) s = OK t ==>
  ?H qt.
    op_taint qt idx = {} /\ op_taint qt child_src = {} /\
    op_taint qt child_dst = {} /\ op_prov H child_dst = prov /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      (!k. k < LENGTH (emitted_insts st c4) ==>
        get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st c4))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := cursor+LENGTH (emitted_insts st c4)) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >> drule prefix_loop_element_compiled_decompose >> strip_tac >>
  drule_all prefix_loop_element_stage_layout >> strip_tac >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  asm_rewrite_tac [] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  disch_then (strip_assume_tac o MATCH_MP prefix_member_seq_split) >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  dxrule_at (Pat `run_inst_seq (_ ++ _) _ = _`) prefix_member_seq_split >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  dxrule_at (Pat `run_inst_seq (_ ++ _) _ = _`) prefix_member_seq_split >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  drule_all prefix_loop_mload_compiled_uniform_pair >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H1` (qx_choose_then `q1` strip_assume_tac))) >>
  drule prefix_loop_element_live_ghost_frame >> disch_tac >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst /\
   eval_operand src s1 = SOME a /\ eval_operand dst s1 = SOME d /\
   op_taint q1 src = {} /\ op_taint q1 dst = {} /\ op_prov H1 dst = prov /\
   allocas_from lo s1` by
    (gs[allocas_from_def] >> metis_tac[abi_decoder_operand_live_mono,LESS_EQ_ADD]) >>
  rev_drule_at (Pat `abi_decode_indexed_address _ _ _ _ = _`)
    prefix_loop_indexed_compiled_uniform_pair >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`H1`,`D`]
    (qx_choose_then `H2` (qx_choose_then `q2` strip_assume_tac))) >>
  qpat_assum `!v. not_fresh_at c1 v ==> _`
    (mp_then Any assume_tac prefix_loop_element_live_ghost_frame) >>
  `abi_decoder_operand_live c2.cs_next_var
     (Var ("%" ++ toString c1.cs_next_var))` by
    simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,toString_11] >>
  `abi_decoder_operand_live c2.cs_next_var idx /\
   abi_decoder_operand_live c2.cs_next_var dst /\
   eval_operand idx s2 = SOME (mload (w2n p) s) /\ eval_operand dst s2 = SOME d /\
   op_taint q2 idx = {} /\ op_taint q2 dst = {} /\ op_prov H2 dst = prov /\
   allocas_from lo s2` by
    (gs[allocas_from_def] >>
     conj_tac >- (irule abi_decoder_operand_live_mono >>
       qexists `st.cs_next_var+1` >> simp[]) >>
     conj_tac >- (irule abi_decoder_operand_live_mono >>
       qexists `st.cs_next_var+1` >> simp[]) >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `(if _ then _ else _) = _`) prefix_loop_optional_compiled_uniform_pair >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >> simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`H2`,`D`]
    (qx_choose_then `H3` (qx_choose_then `q3` strip_assume_tac))) >>
  qpat_assum `!v. not_fresh_at c2 v ==> _`
    (mp_then Any assume_tac prefix_loop_element_live_ghost_frame) >>
  `abi_decoder_operand_live c3.cs_next_var idx /\
   abi_decoder_operand_live c3.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists `c2.cs_next_var` >> simp[]) >>
  `eval_operand idx s3 = SOME (mload (w2n p) s) /\ eval_operand dst s3 = SOME d /\
   op_taint q3 idx = {} /\ op_taint q3 dst = {} /\ op_prov H3 dst = prov /\
   allocas_from lo s3` by
    (gs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `abi_decode_indexed_address _ _ _ _ = _`)
    prefix_loop_indexed_compiled_uniform_pair >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >> simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`fn`,`PG`,`H3`,`D`]
    (qx_choose_then `H4` (qx_choose_then `q4` strip_assume_tac))) >>
  qpat_assum `!v. not_fresh_at c3 v ==> _`
    (mp_then Any assume_tac prefix_loop_element_live_ghost_frame) >>
  qexistsl [`H4`,`q4`] >> simp[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `not_fresh_at c1 v /\ not_fresh_at c2 v /\ not_fresh_at c3 v` by
        (fs[not_fresh_at_def] >> rpt strip_tac >>
         qpat_x_assum `!n. st.cs_next_var <= n ==> _` (qspec_then `n` mp_tac) >>
         (impl_tac >- (Cases_on `dec_info_needs_offset di` >> fs[] >> decide_tac)) >> simp[]) >>
      simp[]) >>
  qpat_assum `!cursor fuel bb. _ ==> _ ==> ptr_safe_block _ _ _ _ _ _ G tn _ _`
    (mp_then Any (qspecl_then [`emitted_insts c1 c2`,`s2`,`q2`,`H2`] mp_tac)
      prefix_loop_element_uniform_append) >>
  simp_tac bool_ss [GSYM AND_IMP_INTRO] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  qpat_x_assum `!cursor fuel bb. _ ==> _ ==> ptr_safe_block _ _ _ _ _ _ G tn _ _`
    (mp_then Any (qspecl_then [`emitted_insts c2 c3`,`s3`,`q3`,`H3`] mp_tac)
      prefix_loop_element_uniform_append) >>
  simp_tac bool_ss [GSYM AND_IMP_INTRO] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  qpat_x_assum `!cursor fuel bb. _ ==> _ ==> ptr_safe_block _ _ _ _ _ _ G tn _ _`
    (mp_then Any (qspecl_then [`emitted_insts c3 c4`,`t`,`q4`,`H4`] mp_tac)
      prefix_loop_element_uniform_append) >>
  simp_tac bool_ss [GSYM AND_IMP_INTRO] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[APPEND_ASSOC]

QED

Theorem prefix_loop_element_setup_labels_pair:
  abi_decode_array_element_setup (Var ip) src dst DLOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = ((idx,child_src,child_dst),st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges DLOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) s.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  eval_operand (Var ip) s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  FLOOKUP G ip = SOME (ib,isz) /\ ib <= w2n p /\ w2n p+32 <= ib+isz /\
  op_taint tn (Var ip) = {} /\ (!k. k < 32 ==> w2n p+k NOTIN tn.t_mem) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\ op_prov G dst = prov /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?t H qt.
    run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand idx t = SOME (n2w (LENGTH pre)) /\
    eval_operand child_src t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
    eval_operand child_dst t = SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var idx /\
    abi_decoder_operand_live st'.cs_next_var child_src /\
    abi_decoder_operand_live st'.cs_next_var child_dst /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [] s t /\
    op_taint qt idx = {} /\ op_taint qt child_src = {} /\
    op_taint qt child_dst = {} /\ op_prov H child_dst = prov /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := cursor+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  drule_all ctor_actual_array_setup_labels >> simp[] >> strip_tac >>
  `eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d)` by
    fs[abi_decoder_ranges_def] >>
  drule_all prefix_loop_element_setup_uniform_pair >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl [`t`,`H`,`qt`] >> simp[]
QED

val _ = export_theory();
