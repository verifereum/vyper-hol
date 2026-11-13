(* Successful member induction.  Unlike the rejection-permitting member rule,
   this rule preserves an arbitrary composable relation at one chosen endpoint.
   The source/resource instantiation is developed separately below. *)
Theory calldataSourceMemberFold
Ancestors
  calldataMembers calldataSafeIteration abiDecoderMemberCons abiDecoderMemberCode abiEncoder
  compileEnv emitHelper emitHelperProps fragExec venomState venomExecSemantics
  abiDecoderValidMemberCursor calldataValidMemberEndpoint
  calldataMemberResourceFrame exprLoweringProps abiDecoderTypedContract abiDecoderContract
  abiDecoderReentry abiDecoderMembers abiDecoderMemberInfos abiEncoderInput abiDecoderCoherence
  abiDecoderAppend abiDecoderCode abiDecoderCounters abiDecoderMemberSetup abiDecoderOffsetHead
  valueEncodingTyping words list rich_list pair arithmetic

Theorem calldata_members_success_relation[local]:
  !fn dst src I R.
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!xs ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!ei az mz rest ao vo a b s.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I ((ei,az,mz)::rest) ao vo a s ==>
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ I rest (ao+az) (vo+mz) b t /\ R s t) ==>
  !xs ao vo a b s.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I xs ao vo a s ==>
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      I [] (ao+SUM (MAP (\(ei,az,mz). az) xs))
           (vo+SUM (MAP (\(ei,az,mz). mz) xs)) b t /\ R s t
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (simp[compile_abi_decode_to_buf_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >> simp[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `compile_abi_decode_to_buf elem_dst elem_src CALLDATALOAD (Lit 0w) (Lit 0w) h0 cs'' = ((),middle)` >>
  `(do ep <- compile_getelemptr_abi src (dec_info_needs_offset h0) ao CALLDATALOAD (Lit 0w) (Lit 0w);
       dp <- emit_op ADD [dst; Lit (n2w vo)];
       compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) h0 od) a = ((),middle)` by
    simp[comp_bind_def, comp_ignore_bind_def] >>
  `cs_extends a middle /\ cs_extends middle b` by metis_tac[] >>
  drule_all fn_has_code_split >> strip_tac >>
  qpat_x_assum `!ei az mz rest ao vo a b s. _` drule >>
  disch_then (qspecl_then [`h1`,`h2`,`xs`,`s`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  first_x_assum drule >> disch_then (qspec_then `t` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `t'` >>
  simp_tac (srw_ss()) [MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC] >>
  metis_tac[]
QED

(* Neither conjunct implies the other: Safe excludes Error continuations,
   whereas Pull constrains every finite prefix. *)
Theorem calldata_member_transfers_composable[local]:
  let Safe = \s t. !fuel r.
        run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s)
  in
    (!s. Safe s s /\ Pull s s) /\
    (!s t u. (Safe s t /\ Pull s t) /\ (Safe t u /\ Pull t u) ==>
      Safe s u /\ Pull s u)
Proof
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  conj_tac >- (gen_tac >> conj_tac
    >- (rpt strip_tac >> qexists_tac `fuel` >> simp[]) >> simp[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[calldata_safe_transfer_trans] >>
  metis_tac[]
QED


Theorem calldata_members_success_transfers[local]:
  !ctx fn dst src I.
  let Safe = \s t. !fuel r.
        run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s)
  in
  (!xs ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!ei az mz rest ao vo a b s.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I ((ei,az,mz)::rest) ao vo a s ==>
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ I rest (ao+az) (vo+mz) b t /\
      Safe s t /\ Pull s t) ==>
  !xs ao vo a b s.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I xs ao vo a s ==>
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      I [] (ao+SUM (MAP (\(ei,az,mz). az) xs))
           (vo+SUM (MAP (\(ei,az,mz). mz) xs)) b t /\ Safe s t /\ Pull s t
Proof
  rpt gen_tac >> simp_tac pure_ss [LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  ho_match_mp_tac calldata_members_success_relation >>
  asm_rewrite_tac[] >>
  mp_tac calldata_member_transfers_composable >>
  simp_tac pure_ss [LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  metis_tac[]
QED

(* A successful child advances the source cursor and the completed-value
   prefix together.  The prefix is positional, so equal decoder descriptors
   never identify distinct source values. *)
Theorem calldata_source_member_prefix_advance[local]:
  abi_decoder_members ce env sf (ty::tys) (tv::tvs)
    (abi_decode_members (MAP (vyper_to_abi_type env) (ty::tys)) bs
      (DROP (SUM (MAP abi_member_head_size
        (MAP (vyper_to_abi_type env) pretys))) bs)) (v::vs) /\
  abi_decode_footprint_frame ((d,type_memory_size tv)::scratch) s t /\
  alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (oid < lo \/ hi <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  d + type_memory_size tv <= base_addr+cap /\
  base_addr <= d /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  EVERY (\(tv,x,p). base_addr <= p /\ p+type_memory_size tv <= d /\
    val_wf tv x /\ val_in_memory tv x p s.vs_memory) prefix /\
  val_wf tv v /\ val_in_memory tv v d t.vs_memory ==>
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs
      (DROP (SUM (MAP abi_member_head_size
        (MAP (vyper_to_abi_type env) (pretys ++ [ty])))) bs)) vs /\
  EVERY (\(tv,x,p). base_addr <= p /\
    p+type_memory_size tv <= d+type_memory_size tv /\
    val_wf tv x /\ val_in_memory tv x p t.vs_memory)
    (prefix ++ [(tv,v,d)])
Proof
  strip_tac >> drule abi_decoder_valid_member_cursor >> strip_tac >>
  conj_tac >- simp[] >>
  `d <= base_addr+cap` by decide_tac >>
  `EVERY (\(tv,x,p). base_addr <= p /\ p+type_memory_size tv <= d /\
     val_wf tv x /\ val_in_memory tv x p t.vs_memory) prefix` by
    (irule calldata_member_prefix_preserved >>
     qpat_assum `abi_decode_footprint_frame _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >>
     qexistsl_tac [`lo`,`hi`] >> asm_rewrite_tac[]) >>
  simp[EVERY_APPEND] >> fs[EVERY_MEM] >>
  rpt gen_tac >> strip_tac >> PairCases_on `e` >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >> simp[]
QED

(* Positions, not descriptor equality, determine the completed source values. *)
Definition calldata_source_member_cursor_def:
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    ao0 vo0 first final initial rest ao vo a s <=>
  ?n scratch.
    n <= LENGTH xs /\ rest = DROP n xs /\
    ao = ao0 + SUM (MAP (\(ei,az,mz). az) (TAKE n xs)) /\
    vo = vo0 + SUM (MAP (\(ei,az,mz). mz) (TAKE n xs)) /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) rest ao vo a = ((),final) /\
    cs_extends first a /\ cs_extends a final /\ ci_mono first a /\ ci_mono a final /\
    abi_decoder_operand_live a.cs_next_var src /\
    abi_decoder_operand_live a.cs_next_var dst /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap s /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    calldata_member_resource_frame ctx fn site limit_st first.cs_next_id
      final.cs_next_id first.cs_next_var d outsz initial s scratch /\
    abi_decoder_members ce env sf (DROP n tys) (DROP n tvs)
      (abi_decode_members (MAP (vyper_to_abi_type env) (DROP n tys)) bs
        (DROP (SUM (MAP abi_member_head_size
          (MAP (vyper_to_abi_type env) (TAKE n tys)))) bs)) (DROP n vs) /\
    EVERY (\i. val_wf (EL i tvs) (EL i vs) /\
      val_in_memory (EL i tvs) (EL i vs)
        (d+vo0+SUM (MAP type_memory_size (TAKE i tvs))) s.vs_memory)
      (GENLIST I n)
End

Theorem calldata_source_member_cursor_initial[local]:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao0 vo0 first = ((),final) /\
  cs_extends first final /\ ci_mono first final /\
  abi_decoder_operand_live first.cs_next_var src /\
  abi_decoder_operand_live first.cs_next_var dst /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  fresh_vars_wrt limit_st initial /\ alloca_inv initial /\
  alloca_frontier_inv ctx fn site initial /\
  calldata_member_own fn first.cs_next_id final.cs_next_id initial /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs ==>
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    ao0 vo0 first final initial xs ao0 vo0 first initial
Proof
  strip_tac >> rewrite_tac[calldata_source_member_cursor_def] >>
  qexistsl_tac [`0`,`[]`] >>
  simp[cs_extends_refl, ci_mono_refl] >>
  irule calldata_member_resource_identity >> simp[]
QED

Theorem calldata_source_member_cursor_terminal[local]:
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    ao0 vo0 first final initial [] ao vo a s /\ LENGTH tvs = LENGTH xs ==>
  ?scratch.
    calldata_member_resource_frame ctx fn site limit_st first.cs_next_id
      final.cs_next_id first.cs_next_var d outsz initial s scratch /\
    EVERY (\i. val_wf (EL i tvs) (EL i vs) /\
      val_in_memory (EL i tvs) (EL i vs)
        (d+vo0+SUM (MAP type_memory_size (TAKE i tvs))) s.vs_memory)
      (GENLIST I (LENGTH tvs)) /\
    ao = ao0 + SUM (MAP (\(ei,az,mz). az) xs) /\
    vo = vo0 + SUM (MAP (\(ei,az,mz). mz) xs)
Proof
  rewrite_tac[calldata_source_member_cursor_def] >> strip_tac >>
  `n = LENGTH xs` by (fs[DROP_EQ_NIL] >> decide_tac) >>
  gvs[] >> qexists_tac `scratch` >> simp[]
QED

(* Navigation supplies the recursive child with its actual source window and
   a resource frame at that same endpoint; no successful continuation is used. *)
Theorem calldata_source_member_navigation[local]:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,ready) /\
  fn_has_code st ready fn /\ abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz base_addr cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ calldata_member_own fn lo hi s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t.
    abi_decoder_valid_pre ce env sf ty tv childbs v ready (FST ops) (SND ops)
      CALLDATALOAD (Lit 0w) (Lit 0w) 0 (sb+off) (d+vo) base_addr cap t /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    calldata_member_resource_frame ctx fn site limit_st lo hi st.cs_next_var
      (d+vo) (type_memory_size tv) s t [] /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] calldata_valid_member_address_endpoint) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `calldata_member_resource_frame ctx fn site limit_st lo hi st.cs_next_var
    (d+vo) (type_memory_size tv) s endpoint []` by
    (irule calldata_member_resource_unchanged >> simp[]) >>
  qexists_tac `endpoint` >> simp[]
QED

Theorem calldata_source_member_position[local]:
  n < LENGTH tys /\ LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tys /\
  abi_decoder_members ce env sf (DROP n tys) (DROP n tvs)
    (abi_decode_members (MAP (vyper_to_abi_type env) (DROP n tys)) bs
      (DROP (SUM (MAP abi_member_head_size
        (MAP (vyper_to_abi_type env) (TAKE n tys)))) bs)) (DROP n vs) ==>
  abi_decoder_coherent ce env sf (EL n tys) (EL n tvs) /\
  abi_to_vyper env (EL n tys)
    (dec (vyper_to_abi_type env (EL n tys))
      (abi_decode_member_bytes (vyper_to_abi_type env (EL n tys)) bs
        (DROP (SUM (MAP abi_member_head_size
          (MAP (vyper_to_abi_type env) (TAKE n tys)))) bs))) = SOME (EL n vs) /\
  value_has_type (EL n tvs) (EL n vs) /\
  type_memory_size (EL n tvs) = type_memory_bytes ce (EL n tys) /\
  abi_embedded_static_size ce.ce_struct_fields (EL n tys) =
    abi_member_head_size (vyper_to_abi_type env (EL n tys)) /\
  abi_decoder_members ce env sf (DROP (SUC n) tys) (DROP (SUC n) tvs)
    (abi_decode_members (MAP (vyper_to_abi_type env) (DROP (SUC n) tys)) bs
      (DROP (SUM (MAP abi_member_head_size
        (MAP (vyper_to_abi_type env) (TAKE (SUC n) tys)))) bs)) (DROP (SUC n) vs)
Proof
  strip_tac >>
  `DROP n tys = EL n tys::DROP (SUC n) tys /\
   DROP n tvs = EL n tvs::DROP (SUC n) tvs /\
   DROP n vs = EL n vs::DROP (SUC n) vs` by
    simp[DROP_EL_CONS, ADD1] >>
  gvs[] >> drule (SIMP_RULE bool_ss [MAP] abi_decoder_valid_member_cursor) >>
  simp[TAKE_SUC, EL_TAKE]
QED

Theorem calldata_source_member_memory_advance[local]:
  calldata_member_resource_frame ctx fn site limit_st lo hi live q sz s t scratch /\
  (oid < lo \/ hi <= oid) /\ FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (!i. i < n ==> base_addr <= d+vo0+SUM (MAP type_memory_size (TAKE i tvs)) /\
    d+vo0+SUM (MAP type_memory_size (TAKE i tvs))+type_memory_size (EL i tvs) <= q) /\
  q <= base_addr+cap /\
  EVERY (\i. val_wf (EL i tvs) (EL i vs) /\
    val_in_memory (EL i tvs) (EL i vs)
      (d+vo0+SUM (MAP type_memory_size (TAKE i tvs))) s.vs_memory) (GENLIST I n) /\
  val_wf (EL n tvs) (EL n vs) /\
  val_in_memory (EL n tvs) (EL n vs)
    (d+vo0+SUM (MAP type_memory_size (TAKE n tvs))) t.vs_memory ==>
  EVERY (\i. val_wf (EL i tvs) (EL i vs) /\
    val_in_memory (EL i tvs) (EL i vs)
      (d+vo0+SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory) (GENLIST I (SUC n))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule calldata_member_resource_endpoint >> strip_tac >>
  drule calldata_member_resource_observations >> strip_tac >>
  rule_assum_tac (SIMP_RULE bool_ss [EVERY_GENLIST, combinTheory.I_THM, ADD_ASSOC]) >>
  simp_tac bool_ss [EVERY_GENLIST, combinTheory.I_THM, ADD_ASSOC] >> gen_tac >> disch_tac >>
  Cases_on `i = n` >- gvs[] >>
  `i < n` by decide_tac >>
  `val_wf (EL i tvs) (EL i vs) /\
   val_in_memory (EL i tvs) (EL i vs)
    (d+vo0+SUM (MAP type_memory_size (TAKE i tvs))) s.vs_memory` by simp[] >>
  simp[] >> irule calldata_member_value_preserved >>
  qpat_assum `abi_decode_footprint_frame _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >>
  qexistsl_tac [`lo`,`hi`] >>
  fs[calldata_member_wit_def] >> metis_tac[LESS_EQ_TRANS]
QED

(* The inline-empty branch is a complete successful member, not an offset
   navigation followed by an assumed recursive call. *)
Theorem calldata_source_empty_member_resources[local]:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) middle = ((),last) /\
  fn_has_code st last fn /\ abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) childbs) = SOME v /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ calldata_member_own fn lo hi s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t.
    val_in_memory tv v (d+vo) t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    calldata_member_resource_frame ctx fn site limit_st lo hi st.cs_next_var
      (d+vo) (type_memory_size tv) s t [] /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >> drule_all calldata_empty_member_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `calldata_member_resource_frame ctx fn site limit_st lo hi st.cs_next_var
    (d+vo) (type_memory_size tv) s endpoint []` by
    (irule calldata_member_resource_unchanged >> simp[]) >>
  qexists_tac `endpoint` >> simp[]
QED

(* CALLDATALOAD inputs are persistent across recursive scratch allocation and
   destination writes; the destination owner and reservation are distinct. *)
Theorem calldata_source_member_inputs_preserved[local]:
  calldata_member_resource_frame ctx fn site limit_st lo hi live p len s t scratch /\
  abi_decoder_operand_live live src /\ abi_decoder_operand_live live dst /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) ==>
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap t /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD t) = bs /\
  FLOOKUP t.vs_allocas oid = SOME (base_addr,cap)
Proof
  strip_tac >> drule calldata_member_resource_observations >> strip_tac >>
  `eval_operand src t = eval_operand src s /\ eval_operand dst t = eval_operand dst s` by
    metis_tac[] >>
  fs[abi_decoder_ranges_def, abi_decode_source_def, eval_operand_def] >>
  first_x_assum irule >> simp[]
QED

(* Deterministic cursor reconstruction after a successful member.  The actual
   navigation/child rule must supply RF and the typed child, not this cursor. *)
Theorem calldata_source_member_cursor_advance[local]:
  let n = LENGTH xs - LENGTH ((ei,az,mz)::rest) in
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    ao0 vo0 first final initial ((ei,az,mz)::rest) ao vo a s /\
  LENGTH tys = LENGTH xs /\ LENGTH tvs = LENGTH xs /\ LENGTH vs = LENGTH xs /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    rest (ao+az) (vo+mz) next = ((),final) /\
  cs_extends a next /\ cs_extends next final /\ ci_mono a next /\ ci_mono next final /\
  calldata_member_resource_frame ctx fn site limit_st a.cs_next_id next.cs_next_id
    a.cs_next_var (d+vo) (type_memory_size (EL n tvs)) s t scratch /\
  (oid < a.cs_next_id \/ next.cs_next_id <= oid) /\
  vo + type_memory_size (EL n tvs) <= outsz /\ d+vo <= base_addr+cap /\
  (!i. i < n ==> base_addr <= d+vo0+SUM (MAP type_memory_size (TAKE i tvs)) /\
    d+vo0+SUM (MAP type_memory_size (TAKE i tvs))+type_memory_size (EL i tvs) <= d+vo) /\
  val_wf (EL n tvs) (EL n vs) /\
  val_in_memory (EL n tvs) (EL n vs)
    (d+vo0+SUM (MAP type_memory_size (TAKE n tvs))) t.vs_memory ==>
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    ao0 vo0 first final initial rest (ao+az) (vo+mz) next t
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `calldata_source_member_cursor`
    (strip_assume_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >>
  `LENGTH ((ei,az,mz)::rest) = LENGTH (DROP n xs)` by metis_tac[] >>
  `n < LENGTH xs /\ LENGTH xs - LENGTH ((ei,az,mz)::rest) = n` by
    (qpat_x_assum `LENGTH (_::rest) = _` mp_tac >> simp[LENGTH_DROP] >> decide_tac) >>
  qpat_x_assum `LENGTH xs - LENGTH (_::rest) = n`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  `n < LENGTH tys /\ LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tys` by decide_tac >>
  drule_all calldata_source_member_position >> strip_tac >>
  suspend "reconstruct"
QED

Resume calldata_source_member_cursor_advance[reconstruct]:
  qhdtm_x_assum `abi_decoder_coherent` kall_tac >>
  qhdtm_x_assum `abi_to_vyper` kall_tac >>
  qhdtm_x_assum `value_has_type` kall_tac >>
  qpat_x_assum `type_memory_size _ = _` kall_tac >>
  qpat_x_assum `abi_embedded_static_size _ _ = _` kall_tac >>
  drule_all calldata_source_member_inputs_preserved >> strip_tac >>
  drule_all calldata_source_member_memory_advance >> disch_tac >>
  `first.cs_next_id <= a.cs_next_id /\ a.cs_next_id <= next.cs_next_id /\
   next.cs_next_id <= final.cs_next_id /\ first.cs_next_var <= a.cs_next_var /\
   a.cs_next_var <= next.cs_next_var /\ d <= d+vo /\
   d+vo+type_memory_size (EL n tvs) <= d+outsz` by
    (gns[ci_mono_def] >> decide_tac) >>
  `calldata_member_resource_frame ctx fn site limit_st first.cs_next_id final.cs_next_id
    first.cs_next_var d outsz initial t (scratch' ++ scratch)` by
    (drule_all calldata_member_resource_extend >> disch_then ACCEPT_TAC) >>
  suspend "lists"
QED

Resume calldata_source_member_cursor_advance[lists]:
  `EL n xs = (ei,az,mz) /\ rest = DROP (SUC n) xs` by
    (qpat_x_assum `_::rest = DROP n xs` mp_tac >>
     simp[Once DROP_EL_CONS, GSYM ADD1] >> metis_tac[]) >>
  `cs_extends first next` by metis_tac[cs_extends_trans] >>
  `ci_mono first next` by (gns[ci_mono_def] >> decide_tac) >>
  `abi_decoder_operand_live next.cs_next_var src /\
   abi_decoder_operand_live next.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  rewrite_tac[calldata_source_member_cursor_def] >>
  qexistsl_tac [`SUC n`,`scratch' ++ scratch`] >>
  asm_simp_tac (srw_ss()) [TAKE_SUC, EL_TAKE, MAP_APPEND, SUM_APPEND, ADD_ASSOC] >> decide_tac
QED
Finalise calldata_source_member_cursor_advance

(* Apply the successful recursive contract at the state actually reached by
   navigation.  Both transfers and RF use that very same child witness. *)
Theorem calldata_source_member_child_endpoint[local]:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs);
      Safe = \s t. !fuel r.
        run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s)
  in
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,ready) /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\ val_wf tv v /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),last) /\
  fn_has_code st last fn /\
  (ready.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  calldata_member_own fn st.cs_next_id last.cs_next_id s /\

  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d+vo /\ d+vo+type_memory_size tv <= base_addr+cap /\
  d+vo+type_memory_size tv < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!u.
    compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) ready = ((),last) /\
    fn_has_code ready last fn /\
    (ready.cs_blocks = last.cs_blocks \/
      !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    last.cs_next_var <= limit_st.cs_next_var /\
    (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
    base_addr <= d+vo /\ d+vo+type_memory_size tv <= base_addr+cap /\
    d+vo+type_memory_size tv < dimword (:256) /\
    abi_decoder_valid_pre ce env sf ty tv childbs v ready (FST ops) (SND ops)
      CALLDATALOAD (Lit 0w) (Lit 0w) 0 (sb+off) (d+vo) b reserve_cap u /\
    fresh_vars_wrt limit_st u /\ alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    calldata_member_own fn ready.cs_next_id last.cs_next_id u /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    ~u.vs_halted /\ u.vs_current_bb = ready.cs_current_bb /\
    u.vs_inst_idx = LENGTH ready.cs_current_insts ==>
    ?t scratch. ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
      t.vs_inst_idx = LENGTH last.cs_current_insts /\
      val_wf tv v /\ val_in_memory tv v (d+vo) t.vs_memory /\
      calldata_member_resource_frame ctx fn site limit_st ready.cs_next_id last.cs_next_id
        ready.cs_next_var (d+vo) (type_memory_size tv) u t scratch /\ Safe u t /\ Pull u t) ==>
  ?t scratch. ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    val_wf tv v /\ val_in_memory tv v (d+vo) t.vs_memory /\
    calldata_member_resource_frame ctx fn site limit_st st.cs_next_id last.cs_next_id
      st.cs_next_var (d+vo) (type_memory_size tv) s t scratch /\ Safe s t /\ Pull s t
Proof
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule_all abi_decoder_to_buf_code >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  `cs_extends st ready` by (irule cs_extends_same_block >> simp[]) >>
  `st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= last.cs_next_id /\
   st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= limit_st.cs_next_var` by
    (Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` >>
     fs[abi_decoder_code_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- suspend "empty" >>
  `(is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)` by
    (strip_tac >> drule_all abi_decoder_nonempty_readable_head >> simp[]) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] calldata_source_member_navigation) >>
  strip_tac >> suspend "child"
QED

Resume calldata_source_member_child_endpoint[child]:
  qhdtm_x_assum `abi_decode_member_setup` kall_tac >>
  qhdtm_x_assum `abi_decoder_coherent` kall_tac >>
  qhdtm_x_assum `vyper_decode_valid_enc_tuple` kall_tac >>
  qhdtm_x_assum `abi_to_vyper` kall_tac >>
  qhdtm_x_assum `abi_decoder_ranges` kall_tac >>
  qhdtm_x_assum `mem_bytes_at` kall_tac >>
  rename1 `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s u []` >>
  drule calldata_member_resource_endpoint >> strip_tac >>
  drule calldata_member_resource_observations >> strip_tac >>
  `calldata_member_own fn ready.cs_next_id last.cs_next_id u` by
    (irule calldata_member_own_nested >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!u. compile_abi_decode_to_buf _ _ _ _ _ _ _ = _ /\ _ ==> _`
    (qspec_then `u` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `calldata_member_resource_frame ctx fn site limit_st st.cs_next_id last.cs_next_id
    st.cs_next_var (d+vo) (type_memory_size tv) s t ([] ++ scratch)` by
    (irule calldata_member_resource_extend >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s u []` (irule_at Any) >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ u t scratch` (irule_at Any) >>
     simp[]) >>
  qexistsl_tac [`t`,`scratch`] >> gnvs[APPEND] >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx fn u <> Error e) ==> _` mp_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx fn t <> Error e) ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[calldata_safe_transfer_trans]
QED

Resume calldata_source_member_child_endpoint[empty]:
  `eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d)` by
    fs[abi_decoder_ranges_def] >>
  drule_all calldata_source_empty_member_resources >> strip_tac >>
  qexistsl_tac [`t`,`[]`] >> simp[]
QED
Finalise calldata_source_member_child_endpoint

(* Positional layout is recovered from the compiler's actual member list.
   The earlier-value bound permits zero-sized members and equal addresses. *)
Theorem calldata_source_member_layout[local]:
  xs = abi_decoder_member_infos sf ce tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  n < LENGTH tys /\ (ei,az,mz)::rest = DROP n xs /\
  ao = SUM (MAP (\(ei,az,mz). az) (TAKE n xs)) /\
  vo = SUM (MAP (\(ei,az,mz). mz) (TAKE n xs)) ==>
  n < LENGTH tvs /\ ei = type_to_abi_dec_info sf ce (EL n tys) /\
  az = abi_member_head_size (vyper_to_abi_type env (EL n tys)) /\
  mz = type_memory_size (EL n tvs) /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (TAKE n tys))) /\
  vo = SUM (MAP type_memory_size (TAKE n tvs)) /\
  (!i. i < n ==> SUM (MAP type_memory_size (TAKE i tvs)) +
    type_memory_size (EL i tvs) <= vo)
Proof
  strip_tac >>
  `LENGTH tvs = LENGTH tys` by metis_tac[LIST_REL_LENGTH] >>
  `EL n xs = (ei,az,mz)` by
    (qpat_x_assum `_::rest = DROP n xs` mp_tac >>
     simp[Once DROP_EL_CONS, abi_decoder_member_infos_def, GSYM ADD1] >> metis_tac[]) >>
  `!i. i < LENGTH tys ==> abi_decoder_coherent ce env sf (EL i tys) (EL i tvs)` by
    fs[LIST_REL_EL_EQN] >>
  `!i. i < LENGTH tys ==>
    abi_embedded_static_size ce.ce_struct_fields (EL i tys) =
      abi_member_head_size (vyper_to_abi_type env (EL i tys))` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  suspend "maps"
QED

Resume calldata_source_member_layout[maps]:
  `MAP (abi_embedded_static_size ce.ce_struct_fields) (TAKE n tys) =
   MAP (\ty. abi_member_head_size (vyper_to_abi_type env ty)) (TAKE n tys)` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     `x < n /\ x < LENGTH tys` by fs[LENGTH_TAKE] >> simp[EL_TAKE]) >>
  `vo = SUM (MAP type_memory_size (TAKE n tvs))` by
    (qpat_assum `MAP type_memory_size tvs = _` (mp_tac o AP_TERM ``TAKE n : num list -> num list``) >>
     simp[GSYM MAP_TAKE] >> strip_tac >>
     simp[abi_decoder_member_infos_def, GSYM MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]) >>
  `ei = type_to_abi_dec_info sf ce (EL n tys) /\
   az = abi_member_head_size (vyper_to_abi_type env (EL n tys)) /\
   mz = type_memory_size (EL n tvs)` by
    (qpat_x_assum `EL n xs = _` mp_tac >>
     qpat_assum `MAP type_memory_size tvs = _` (mp_tac o AP_TERM ``EL n : num list -> num``) >>
     simp[abi_decoder_member_infos_def, EL_MAP] >> metis_tac[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (asm_simp_tac (srw_ss()) [abi_decoder_member_infos_def, GSYM MAP_TAKE,
        MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]) >>
  rpt strip_tac >>
  qspecl_then [`type_memory_size`,`TAKE n tvs`,`i`] mp_tac abi_encoder_prefix_sum_bound >>
  simp[LENGTH_TAKE, EL_TAKE, TAKE_TAKE] >> decide_tac
QED
Finalise calldata_source_member_layout

(* Conservative names for the two independent transfers and their common
   source-valued resource endpoint. *)
Definition calldata_member_transfers_def:
  calldata_member_transfers ctx fn s t <=>
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s)
End

Definition calldata_member_success_def:
  calldata_member_success ctx fn site limit_st first last p len tv v s t scratch <=>
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    val_wf tv v /\ val_in_memory tv v p t.vs_memory /\
    calldata_member_resource_frame ctx fn site limit_st first.cs_next_id last.cs_next_id
      first.cs_next_var p len s t scratch /\ calldata_member_transfers ctx fn s t
End

Definition calldata_member_child_contract_def:
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv <=>
  !bytes v src dst sb p b reserve_cap oid base_addr cap first last s.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) first = ((),last) /\
    fn_has_code first last fn /\
    (first.cs_blocks = last.cs_blocks \/
      !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    last.cs_next_var <= limit_st.cs_next_var /\
    (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
    base_addr <= p /\ p+type_memory_size tv <= base_addr+cap /\
    p+type_memory_size tv < dimword (:256) /\
    abi_decoder_valid_pre ce env sf ty tv bytes v first src dst
      CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb p b reserve_cap s /\
    fresh_vars_wrt limit_st s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    calldata_member_own fn first.cs_next_id last.cs_next_id s /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    ~s.vs_halted /\ s.vs_current_bb = first.cs_current_bb /\
    s.vs_inst_idx = LENGTH first.cs_current_insts ==>
    ?t scratch. calldata_member_success ctx fn site limit_st first last p
      (type_memory_size tv) tv v s t scratch
End

Theorem calldata_member_child_contract_apply:
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) first = ((),last) /\
  fn_has_code first last fn /\
  (first.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  last.cs_next_var <= limit_st.cs_next_var /\
  (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= p /\ p+type_memory_size tv <= base_addr+cap /\
  p+type_memory_size tv < dimword (:256) /\
  abi_decoder_valid_pre ce env sf ty tv bytes v first src dst
    CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb p b reserve_cap s /\
  fresh_vars_wrt limit_st s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  calldata_member_own fn first.cs_next_id last.cs_next_id s /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  ~s.vs_halted /\ s.vs_current_bb = first.cs_current_bb /\
  s.vs_inst_idx = LENGTH first.cs_current_insts ==>
  ?t scratch. calldata_member_success ctx fn site limit_st first last p
    (type_memory_size tv) tv v s t scratch
Proof
  rewrite_tac[calldata_member_child_contract_def] >> metis_tac[]
QED

Theorem calldata_member_success_observations:
  calldata_member_success ctx fn site limit_st first last p len tv v s t scratch ==>
  ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
  t.vs_inst_idx = LENGTH last.cs_current_insts /\ val_wf tv v /\
  val_in_memory tv v p t.vs_memory /\
  calldata_member_resource_frame ctx fn site limit_st first.cs_next_id last.cs_next_id
    first.cs_next_var p len s t scratch /\ calldata_member_transfers ctx fn s t
Proof
  simp[calldata_member_success_def]
QED

Theorem calldata_source_member_success[local]:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),last) /\
  fn_has_code st last fn /\
  (ready.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\ val_wf tv v /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  calldata_member_own fn st.cs_next_id last.cs_next_id s /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d+vo /\ d+vo+type_memory_size tv <= base_addr+cap /\
  d+vo+type_memory_size tv < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv ==>
  ?t scratch. calldata_member_success ctx fn site limit_st st last (d+vo)
    (type_memory_size tv) tv v s t scratch
Proof
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [calldata_member_success_def, calldata_member_transfers_def] >>
  irule (SIMP_RULE bool_ss [LET_THM] calldata_source_member_child_endpoint) >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `vyper_decode_valid_enc_tuple _ _ _` (irule_at Any) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP s.vs_allocas oid = _` (irule_at Any) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  drule_all calldata_member_child_contract_apply >>
  simp[calldata_member_success_def, calldata_member_transfers_def]
QED

(* A cursor's source position fixes the head type and both byte offsets. *)
Theorem calldata_source_cursor_head[local]:
  let n = LENGTH xs - LENGTH ((ei,az,mz)::rest) in
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    0 0 first final initial ((ei,az,mz)::rest) ao vo a s /\
  xs = abi_decoder_member_infos sf ce tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  LENGTH vs = LENGTH tys ==>
  n < LENGTH tys /\ n < LENGTH tvs /\
  ei = type_to_abi_dec_info sf ce (EL n tys) /\
  az = abi_member_head_size (vyper_to_abi_type env (EL n tys)) /\
  mz = type_memory_size (EL n tvs) /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (TAKE n tys))) /\
  vo = SUM (MAP type_memory_size (TAKE n tvs)) /\
  abi_decoder_coherent ce env sf (EL n tys) (EL n tvs) /\
  abi_to_vyper env (EL n tys)
    (dec (vyper_to_abi_type env (EL n tys))
      (abi_decode_member_bytes (vyper_to_abi_type env (EL n tys)) bs (DROP ao bs))) =
    SOME (EL n vs) /\ val_wf (EL n tvs) (EL n vs) /\
  (!i. i < n ==> SUM (MAP type_memory_size (TAKE i tvs)) +
    type_memory_size (EL i tvs) <= vo)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qhdtm_x_assum `calldata_source_member_cursor`
    (strip_assume_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >>
  `LENGTH xs = LENGTH tys /\ LENGTH tvs = LENGTH tys` by
    (fs[abi_decoder_member_infos_def] >> metis_tac[LIST_REL_LENGTH]) >>
  `LENGTH ((ei,az,mz)::rest) = LENGTH (DROP n xs)` by metis_tac[] >>
  `n < LENGTH tys /\ LENGTH xs - LENGTH ((ei,az,mz)::rest) = n` by
    (qpat_x_assum `LENGTH (_::rest) = _` mp_tac >> simp[LENGTH_DROP] >> decide_tac) >>
  qpat_x_assum `LENGTH xs - LENGTH (_::rest) = n` SUBST1_TAC >>
  fs[ADD_CLAUSES] >>
  drule_all calldata_source_member_layout >> strip_tac >>
  drule_all calldata_source_member_position >> strip_tac >>
  simp[] >> metis_tac[value_has_type_val_wf]
QED

(* Recover the actual compiler phases needed by the cursor successor. *)
Theorem calldata_source_cursor_compilation[local]:
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    0 0 first final initial ((ei,az,mz)::rest) ao vo a s /\
  xs = abi_decoder_member_infos sf ce tys /\
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)];
      compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),next) /\
  fn_has_code a final fn /\
  (a.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  ?ops ready.
    abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (dec_info_needs_offset ei) ao vo a = (ops,ready) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w) ei ready = ((),next) /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      rest (ao+az) (vo+mz) next = ((),final) /\
    cs_extends a next /\ cs_extends next final /\
    fn_has_code a next fn /\
    a.cs_next_id < ready.cs_next_id /\ ready.cs_next_id <= next.cs_next_id /\
    next.cs_next_id <= final.cs_next_id /\ next.cs_next_var <= final.cs_next_var /\
    (ready.cs_blocks = next.cs_blocks \/
      !bb. lookup_block next.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `(do ep <- _; _ od) a = ((),next)` mp_tac >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_getelemptr_abi src _ ao CALLDATALOAD (Lit 0w) (Lit 0w) a = (ep,middle)` >>
  rename1 `emit_op ADD _ middle = (dp,ready)` >>
  `abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset ei) ao vo a = ((ep,dp),ready)` by
    simp[abi_decode_member_setup_def, comp_bind_def, comp_return_def] >>
  `compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    rest (ao+az) (vo+mz) next = ((),final)` by
    (qhdtm_assum `calldata_source_member_cursor`
      (mp_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >>
     simp[abi_decode_complex_member_phases, comp_bind_def, comp_ignore_bind_def] >>
     metis_tac[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_member_cons_code >> simp_tac bool_ss [FST,SND] >>
  disch_then drule_all >> strip_tac >>
  `?tailtys. rest = abi_decoder_member_infos sf ce tailtys` by
    (qhdtm_x_assum `calldata_source_member_cursor`
      (strip_assume_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >>
     qexists_tac `DROP (SUC n) tys` >>
     `SUC n <= LENGTH xs` by
       (qpat_assum `_::rest = DROP n xs`
          (mp_tac o AP_TERM ``LENGTH : (abi_dec_info # num # num) list -> num``) >>
        simp[LENGTH_DROP] >> decide_tac) >>
     `rest = DROP (SUC n) xs` by
       (qpat_x_assum `_::rest = DROP n xs`
          (mp_tac o AP_TERM ``DROP 1 : (abi_dec_info # num # num) list -> (abi_dec_info # num # num) list``) >>
        qpat_x_assum `xs = _` kall_tac >>
        simp[DROP_DROP, ADD1, ADD_COMM]) >>
     simp[abi_decoder_member_infos_def, MAP_DROP]) >>
  qpat_x_assum `rest = abi_decoder_member_infos _ _ _` SUBST_ALL_TAC >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_members_child_phi >> strip_tac >>
  qexistsl_tac [`(ep,dp)`,`ready`] >> fs[ADD_COMM]
QED

Theorem calldata_source_member_cursor_step[local]:
  calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    0 0 first final initial ((ei,az,mz)::rest) ao vo a s /\
  xs = abi_decoder_member_infos sf ce tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)];
      compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),next) /\
  fn_has_code a final fn /\
  (a.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  (oid < first.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d /\ d + SUM (MAP type_memory_size tvs) <= base_addr+cap /\
  SUM (MAP type_memory_size tvs) <= outsz /\
  d + SUM (MAP type_memory_size tvs) < dimword(:256) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!i. i < LENGTH tys ==> calldata_member_child_contract ce env sf ctx fn site limit_st
    (EL i tys) (EL i tvs)) ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = next.cs_current_bb /\
    t.vs_inst_idx = LENGTH next.cs_current_insts /\
    calldata_source_member_cursor ce env sf ctx fn site limit_st
      xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
      0 0 first final initial rest (ao+az) (vo+mz) next t /\
    calldata_member_transfers ctx fn s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all calldata_source_cursor_compilation >>
  disch_then (qx_choose_then `ops` (qx_choose_then `ready`
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] calldata_source_cursor_head) >> strip_tac >>
  qabbrev_tac `n = LENGTH (abi_decoder_member_infos sf ce tys) - LENGTH ((ei,az,mz)::rest)` >>
  suspend "child"
QED

Resume calldata_source_member_cursor_step[child]:

  `vo + type_memory_size (EL n tvs) <= SUM (MAP type_memory_size tvs)` by
    (qpat_assum `vo = _` (fn th => rewrite_tac[th]) >>
     irule abi_encoder_prefix_sum_bound >> simp[]) >>
  `ci_mono first a /\ abi_decoder_operand_live a.cs_next_var src /\
   abi_decoder_operand_live a.cs_next_var dst /\
   abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap s /\
   mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
   FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
   fresh_vars_wrt limit_st s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
   calldata_member_own fn first.cs_next_id final.cs_next_id s` by
    (qhdtm_assum `calldata_source_member_cursor`
      (strip_assume_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >>
     drule calldata_member_resource_endpoint >> simp[]) >>
  `calldata_member_own fn a.cs_next_id next.cs_next_id s` by
    (irule calldata_member_own_nested >>
     qhdtm_assum `calldata_member_own` (irule_at Any) >>
     fs[ci_mono_def]) >>
  `type_memory_size (EL n tvs) = type_memory_bytes ce (EL n tys)` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  suspend "apply"
QED

Resume calldata_source_member_cursor_step[apply]:
  `?t scratch. calldata_member_success ctx fn site limit_st a next (d+vo)
    (type_memory_size (EL n tvs)) (EL n tvs) (EL n vs) s t scratch` suffices_by
    (strip_tac >> suspend "advance") >>
  qhdtm_x_assum `calldata_source_member_cursor` kall_tac >>
  qpat_x_assum `(do ep <- _; _ od) a = _` kall_tac >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  `MAP (vyper_to_abi_type env) tys =
    MAP (vyper_to_abi_type env) (TAKE n tys) ++
    vyper_to_abi_type env (EL n tys)::MAP (vyper_to_abi_type env) (DROP (SUC n) tys)` by
    (`DROP n tys = EL n tys::DROP (SUC n) tys` by simp[DROP_EL_CONS, ADD1] >>
     pure_rewrite_tac[GSYM MAP, GSYM MAP_APPEND] >> AP_TERM_TAC >>
     qpat_x_assum `DROP n tys = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[TAKE_DROP]) >>
  `d+vo+type_memory_size (EL n tvs) < dimword(:256) /\
   next.cs_next_var <= limit_st.cs_next_var /\ base_addr <= d+vo /\
   d+vo+type_memory_size (EL n tvs) <= base_addr+cap /\
   vo+type_memory_bytes ce (EL n tys) <= outsz /\
   (oid < ready.cs_next_id \/ next.cs_next_id <= oid)` by
    (gns[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  qpat_x_assum `ao = _` SUBST_ALL_TAC >>
  qpat_x_assum `vo = _` kall_tac >>
  qpat_x_assum `type_memory_size (EL n tvs) = _` kall_tac >>
  irule (SIMP_RULE bool_ss [LET_THM] calldata_source_member_success) >>
  asm_simp_tac bool_ss [] >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `FLOOKUP s.vs_allocas oid = _` (irule_at Any) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`env`,`MAP (vyper_to_abi_type env) (DROP (SUC n) tys)`] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `MAP (vyper_to_abi_type env) tys = _`
    (fn th => pure_rewrite_tac[GSYM th]) >> asm_rewrite_tac[]
QED

Resume calldata_source_member_cursor_step[advance]:
  drule calldata_member_success_observations >> strip_tac >>
  `a.cs_next_var <= ready.cs_next_var` by
    (drule abi_decode_member_setup_counters >> simp[]) >>
  `ready.cs_next_var <= next.cs_next_var` by
    (mp_tac (cj 1 abi_decoder_vars_mono_mutual) >>
     rewrite_tac[abi_decoder_vars_mono_def] >>
     disch_then (qspecl_then [`SND ops`,`FST ops`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`ei`,`ready`] mp_tac) >>
     simp[]) >>
  `ci_mono a next /\ ci_mono next final` by
    (gns[ci_mono_def] >> decide_tac) >>
  `LENGTH tys = LENGTH xs /\ LENGTH tvs = LENGTH xs /\ LENGTH vs = LENGTH xs` by
    (fs[abi_decoder_member_infos_def, LIST_REL_EL_EQN]) >>
  `n = LENGTH xs - LENGTH ((ei,az,mz)::rest)` by simp[Abbr `n`] >>
  qexists_tac `t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule (SIMP_RULE bool_ss [LET_THM] calldata_source_member_cursor_advance) >>
  qhdtm_assum `calldata_source_member_cursor` (irule_at Any) >>
  qexists_tac `scratch` >>
  qpat_x_assum `n = LENGTH xs - _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `xs = _` kall_tac >>
  qpat_x_assum `vo = _` (fn th => assume_tac (SYM th)) >>
  qpat_x_assum `type_memory_size (EL n tvs) = _` kall_tac >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- decide_tac >>
  conj_tac >- (gns[ci_mono_def] >> decide_tac) >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED
Finalise calldata_source_member_cursor_step

Theorem calldata_source_members_owned_success:
  let xs = abi_decoder_member_infos sf ce tys in
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs 0 0 first = ((),final) /\
  fn_has_code first final fn /\
  (first.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  MAP type_memory_size tvs = MAP (type_memory_bytes ce) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  abi_decoder_operand_live first.cs_next_var src /\
  abi_decoder_operand_live first.cs_next_var dst /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  fresh_vars_wrt limit_st initial /\ alloca_inv initial /\
  alloca_frontier_inv ctx fn site initial /\
  calldata_member_own fn first.cs_next_id final.cs_next_id initial /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < first.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d /\ d + SUM (MAP type_memory_size tvs) <= base_addr+cap /\
  SUM (MAP type_memory_size tvs) <= outsz /\
  d + SUM (MAP type_memory_size tvs) < dimword(:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = first.cs_current_bb /\
  initial.vs_inst_idx = LENGTH first.cs_current_insts /\
  (!i. i < LENGTH tys ==> calldata_member_child_contract ce env sf ctx fn site limit_st
    (EL i tys) (EL i tvs)) ==>
  ?t scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    calldata_member_resource_frame ctx fn site limit_st first.cs_next_id final.cs_next_id
      first.cs_next_var d outsz initial t scratch /\
    EVERY (\i. val_wf (EL i tvs) (EL i vs) /\
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory)
      (GENLIST I (LENGTH tvs)) /\
    calldata_member_transfers ctx fn initial t
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `xs = abi_decoder_member_infos sf ce tys` >>
  `cs_extends first final` by
    metis_tac[cj 2 cs_appends_abi_decode_mutual, cs_appends_def] >>
  `first.cs_next_var <= final.cs_next_var` by
    (mp_tac (cj 2 abi_decoder_vars_mono_mutual) >>
     rewrite_tac[abi_decoder_vars_mono_def] >>
     disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`xs`,`0`,`0`,`first`] mp_tac) >>
     simp[]) >>
  `ci_mono first final` by
    (`first.cs_next_id <= final.cs_next_id` by
       (mp_tac (cj 2 abi_decoder_code_mutual) >>
        disch_then (qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`xs`,`0`,`0`] mp_tac) >>
        simp[] >> disch_then (qspec_then `first` mp_tac) >>
        simp[abi_decoder_code_def]) >>
     simp[ci_mono_def]) >>
  `calldata_source_member_cursor ce env sf ctx fn site limit_st
    xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
    0 0 first final initial xs 0 0 first initial` by
    (irule calldata_source_member_cursor_initial >> asm_rewrite_tac[]) >>
  `?t. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    calldata_source_member_cursor ce env sf ctx fn site limit_st
      xs tys tvs vs bs dst src sb d outsz b reserve_cap base_addr cap oid
      0 0 first final initial []
      (0+SUM (MAP (\(ei,az,mz). az) xs))
      (0+SUM (MAP (\(ei,az,mz). mz) xs)) final t /\
    calldata_member_transfers ctx fn initial t` suffices_by
    (strip_tac >> drule calldata_source_member_cursor_terminal >>
     impl_tac >- fs[Abbr `xs`, abi_decoder_member_infos_def, LIST_REL_EL_EQN] >>
     strip_tac >> qexistsl_tac [`t`,`scratch`] >> fs[]) >>
  suspend "iteration"
QED

Resume calldata_source_members_owned_success[iteration]:
  irule calldata_members_success_relation >>
  conj_tac >- (mp_tac calldata_member_transfers_composable >>
    simp_tac bool_ss [LET_THM, calldata_member_transfers_def] >> metis_tac[]) >>
  conj_tac >- (mp_tac calldata_member_transfers_composable >>
    simp_tac bool_ss [LET_THM, calldata_member_transfers_def] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`first`,`dst`,`fn`,`src`] >>
  conj_tac >- suspend "head_extends" >>
  conj_tac >- suspend "step" >>
  conj_tac >- metis_tac[abi_decoder_members_extends] >>
  asm_rewrite_tac[]
QED
Resume calldata_source_members_owned_success[head_extends]:
  rpt gen_tac >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  `cs_extends a cs'` by
    metis_tac[cs_appends_abi_member_pointer, cs_appends_def] >>
  `cs_extends cs' cs''` by metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  metis_tac[cs_extends_trans]
QED

Resume calldata_source_members_owned_success[step]:
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `cs_extends first a /\ cs_extends a final` by
    (qhdtm_assum `calldata_source_member_cursor`
      (strip_assume_tac o REWRITE_RULE [calldata_source_member_cursor_def]) >> simp[]) >>
  `fn_has_code a final fn` by metis_tac[fn_has_code_split] >>
  `a.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (Cases_on `first.cs_blocks = final.cs_blocks`
     >- (disj1_tac >>
         qpat_x_assum `cs_extends first a` mp_tac >>
         qpat_x_assum `cs_extends a final` mp_tac >>
         qpat_x_assum `first.cs_blocks = final.cs_blocks` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[cs_extends_def] >> rpt strip_tac >>
         qpat_assum `final.cs_blocks = _ ++ _`
           (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``) >>
         qpat_assum `a.cs_blocks = _ ++ _`
           (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``) >>
         simp_tac list_ss [] >> rpt strip_tac >>
         `LENGTH new' = 0` by decide_tac >>
         `new' = []` by metis_tac[LENGTH_NIL] >>
         qpat_x_assum `a.cs_blocks = _` mp_tac >> simp[]) >>
     disj2_tac >> metis_tac[]) >>
  irule calldata_source_member_cursor_step >>
  qhdtm_assum `calldata_source_member_cursor` (irule_at Any) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    disj1_tac >> first_assum ACCEPT_TAC,
    disj2_tac >> first_assum ACCEPT_TAC,
    simp[Abbr `xs`]]
QED
Finalise calldata_source_members_owned_success
