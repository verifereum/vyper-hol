(* Successful member induction.  Unlike the rejection-permitting member rule,
   this rule preserves an arbitrary composable relation at one chosen endpoint.
   The source/resource instantiation is developed separately below. *)
Theory calldataSourceMemberFold
Ancestors
  calldataMembers calldataSafeIteration abiDecoderMemberCons abiDecoderMemberCode abiEncoder
  compileEnv emitHelper emitHelperProps fragExec venomState venomExecSemantics
  abiDecoderValidMemberCursor calldataValidMemberEndpoint
  words list pair arithmetic

Theorem calldata_members_success_relation[local]:
  !fn dst src I R.
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!xs ao vo a b.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) xs ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!ei az mz rest ao vo a b s.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) ei od) a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I ((ei,az,mz)::rest) ao vo a s ==>
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ I rest (ao+az) (vo+mz) b t /\ R s t) ==>
  !xs ao vo a b s.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) xs ao vo a = ((),b) /\
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
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `compile_abi_decode_to_buf elem_dst elem_src CALLDATALOAD (Lit 0w) h0 cs'' = ((),middle)` >>
  `(do ep <- compile_getelemptr_abi src (dec_info_needs_offset h0) ao CALLDATALOAD (Lit 0w);
       dp <- emit_op ADD [dst; Lit (n2w vo)];
       compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) h0 od) a = ((),middle)` by
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
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) xs ao vo a = ((),b) ==>
    cs_extends a b) /\
  (!ei ao vo a b.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) ei od) a = ((),b) ==>
    cs_extends a b) /\
  (!ei az mz rest ao vo a b s.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) ei od) a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I ((ei,az,mz)::rest) ao vo a s ==>
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ I rest (ao+az) (vo+mz) b t /\
      Safe s t /\ Pull s t) ==>
  !xs ao vo a b s.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) xs ao vo a = ((),b) /\
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
