Theory calldataExactMembers
Ancestors
  calldataMembers abiEncoder compileEnv fragExec list arithmetic

Theorem calldata_members_fixed_fn_bad_invariant_rule:
  !ctx fn dst src I Bad.
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
    (Bad /\ ?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s) \/
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ I rest (ao+az) (vo+mz) b t /\
      !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) ==>
  !xs ao vo a b s.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo a = ((),b) /\
    fn_has_code a b fn /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ I xs ao vo a s ==>
    (Bad /\ ?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s) \/
    ?t. ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      I [] (ao+SUM (MAP (\(ei,az,mz). az) xs))
           (vo+SUM (MAP (\(ei,az,mz). mz) xs)) b t /\
      !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> disj2_tac >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> qexists_tac `fuel` >> simp[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `?mid.
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset h0) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) h0 od) a = ((),mid) /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      xs (ao+h1) (vo+h2) mid = ((),b)` by
    (qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
       compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
     strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends a mid /\ cs_extends mid b` by metis_tac[] >>
  drule_all fn_has_code_split >> strip_tac >>
  qpat_x_assum `!ei az mz rest ao vo a b s. _` drule >>
  disch_then (qspecl_then [`h1`,`h2`,`xs`,`s`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  first_x_assum drule >>
  disch_then (qspec_then `t` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> conj_tac >- simp[] >>
      qpat_x_assum `!fuel r. _` drule >> simp[] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `t'` >>
  simp_tac (srw_ss()) [MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC] >>
  metis_tac[]
QED
