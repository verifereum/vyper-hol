(* Operational suffix composition, independent of the canonical value invariant. *)
Theory entryReachBodyMemberIteration
Ancestors
  entryReachBodyMemberSetup entryReachBodyOperationalPath abiDecoderMemberSetup
  abiEncoder emitHelper exprLoweringProps compileEnv list pair arithmetic

Theorem entry_members_path_iteration:
  !dst src ctx fn I.
  (!ei az mz rest ao vo a m s.
    (do ops <- abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
                 (dec_info_needs_offset ei) ao vo;
        compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w) ei od)
      a = ((),m) /\ I ((ei,az,mz)::rest) ao vo a s ==>
    ?u. entry_decode_path ctx fn s u /\ I rest (ao+az) (vo+mz) m u) ==>
  !xs ao vo st last s.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs ao vo st = ((),last) /\
    I xs ao vo st s ==>
    ?t. entry_decode_path ctx fn s t /\
      I [] (ao + SUM (MAP (\(ei,az,mz). az) xs))
           (vo + SUM (MAP (\(ei,az,mz). mz) xs)) last t
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (simp[Once compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[entry_decode_path_refl]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_decode_complex_member_phases, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  `(do ops <- abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
                 (dec_info_needs_offset h0) ao vo;
       compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w) h0 od)
      st = ((),cs'')` by simp[comp_bind_def] >>
  qpat_x_assum `!ei az mz rest ao vo a m s. _` drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `t` >> conj_tac
  >- (irule entry_decode_path_trans >> qexists_tac `u` >> simp[]) >>
  qpat_x_assum `I' [] _ _ last t` mp_tac >>
  simp_tac bool_ss [ADD_ASSOC]
QED

Theorem entry_member_path_intro:
  !I H dst src ei ao vo st ops addr mid ctx fn az mz rest.
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset ei) ao vo st = (ops,addr) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w) ei addr = ((),mid) /\
  (!s. I ((ei,az,mz)::rest) ao vo st s ==>
    ?u. entry_decode_path ctx fn s u /\ H u) /\
  (!u. H u ==> ?t. entry_decode_path ctx fn u t /\
    I rest (ao+az) (vo+mz) mid t) ==>
  (do ops <- abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
               (dec_info_needs_offset ei) ao vo;
      compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w) ei od)
    st = ((),mid) /\
  (!s. I ((ei,az,mz)::rest) ao vo st s ==>
    ?t. entry_decode_path ctx fn s t /\ I rest (ao+az) (vo+mz) mid t)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >- simp[comp_bind_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule entry_decode_path_trans >> qexists_tac `u` >> simp[]
QED
