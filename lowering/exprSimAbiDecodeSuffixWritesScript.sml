Theory exprSimAbiDecodeSuffixWrites
Ancestors
  exprSimAbiDecodeShape abiEncoder abiDecoderCounters abiDecoderAppend abiDecoderReentry
  exprSimAbiGasBridge fragExec exprLoweringProps compileEnv emitHelper context venomInst
  arithmetic pair list rich_list sorting

Theorem abi_decode_front_append[local]:
  ys <> [] ==> FRONT (xs ++ ys) = xs ++ FRONT ys
Proof
  Cases_on `ys` >- simp[] >>
  strip_tac >> MATCH_ACCEPT_TAC FRONT_APPEND
QED

Theorem abi_decode_mem_drop[local]:
  MEM x (DROP n xs) ==> MEM x xs
Proof
  simp[MEM_DROP, MEM_EL] >> metis_tac[]
QED

Theorem abi_decode_mem_front_last[local]:
  !xs x. xs <> [] ==> (MEM x xs <=> MEM x (FRONT xs) \/ x = LAST xs)
Proof
  Induct >- simp[] >> Cases_on `xs` >> simp[] >> metis_tac[]
QED

Theorem abi_decode_frag_code_split:
  cs_extends sa sb /\ cs_extends sb sc ==>
  !i. MEM i (frag_code sa sc) ==>
      MEM i (frag_code sa sb) \/ MEM i (frag_code sb sc)
Proof
  simp[cs_extends_def] >> strip_tac >>
  `emitted_blocks sa sb = new` by metis_tac[emitted_blocks_append] >>
  `emitted_blocks sb sc = new'` by metis_tac[emitted_blocks_append] >>
  `emitted_blocks sa sc = new' ++ new` by
    (irule emitted_blocks_append >> simp[APPEND_ASSOC]) >>
  Cases_on `new = []` >> Cases_on `new' = []` >>
  gvs[frag_code_def, NULL_EQ, emitted_insts_def, LAST_APPEND_NOT_NIL,
      abi_decode_front_append, MEM_APPEND, MEM_FLAT, MEM_MAP, IS_PREFIX_APPEND,
      DROP_APPEND, APPEND_ASSOC]
  >- (rpt strip_tac >> imp_res_tac abi_decode_mem_drop >> metis_tac[])
  >- (rpt strip_tac >> imp_res_tac abi_decode_mem_drop >> metis_tac[]) >>
  `!bb. MEM bb (emitted_blocks sb sc) ==>
    MEM bb (FRONT (emitted_blocks sb sc)) \/ bb = LAST (emitted_blocks sb sc)` by
    metis_tac[abi_decode_mem_front_last] >>
  rpt strip_tac >> gvs[]
  >- (qpat_x_assum `!bb. _` (qspec_then `bb` mp_tac) >> simp[] >>
      strip_tac >> gvs[MEM_APPEND] >> metis_tac[]) >>
  metis_tac[]
QED

Definition abi_decode_fresh_writes_def:
  abi_decode_fresh_writes (action : 'a compiler) <=>
    !st v st'. action st = (v,st') ==>
      cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
      !i x. MEM i (frag_code st st') /\ MEM x i.inst_outputs ==>
        ?n. st.cs_next_var <= n /\ x = STRING #"%" (toString n)
End

Theorem abi_decode_fresh_writes_bind:
  abi_decode_fresh_writes action /\
  (!v. abi_decode_fresh_writes (next v)) ==>
  abi_decode_fresh_writes (comp_bind action next)
Proof
  rewrite_tac[abi_decode_fresh_writes_def] >> strip_tac >>
  rpt gen_tac >> simp[comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- metis_tac[LESS_EQ_TRANS] >>
  rpt strip_tac >> drule_all abi_decode_frag_code_split >> strip_tac >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem abi_decode_fresh_writes_ignore_bind:
  abi_decode_fresh_writes action /\ abi_decode_fresh_writes next ==>
  abi_decode_fresh_writes (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule abi_decode_fresh_writes_bind >> simp[]
QED

Theorem abi_decode_fresh_writes_return:
  abi_decode_fresh_writes (comp_return v)
Proof
  simp[abi_decode_fresh_writes_def, comp_return_def, cs_extends_refl,
    frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem abi_decode_fresh_writes_prims:
  (!opc ops. abi_decode_fresh_writes (emit_op opc ops)) /\
  (!opc ops. abi_decode_fresh_writes (emit_void opc ops)) /\
  (!opc ops. abi_decode_fresh_writes (emit_inst opc ops [])) /\
  (!prefix. abi_decode_fresh_writes (fresh_label prefix)) /\
  (!lbl. abi_decode_fresh_writes (new_block lbl))
Proof
  simp[abi_decode_fresh_writes_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def, LET_THM,
    frag_code_def, emitted_blocks_def, emitted_insts_def, mk_inst_def,
    cs_extends_def, DROP_APPEND] >>
  rpt strip_tac >> gvs[] >> metis_tac[LESS_EQ_REFL]
QED

val writes_simps = [abi_decode_fresh_writes_return, abi_decode_fresh_writes_prims];
val WRITES_BIND_WITH = fn extra => ho_match_mp_tac abi_decode_fresh_writes_bind >> conj_tac
  >- simp (extra @ writes_simps) >> rpt gen_tac;
val WRITES_BIND = WRITES_BIND_WITH [];
val WRITES_IGNORE = ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- simp writes_simps;

Theorem abi_decode_fresh_writes_clamp:
  !c v. abi_decode_fresh_writes (compile_abi_clamp_basetype v c)
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, abi_decode_fresh_writes_return]
  >- (rpt gen_tac >> IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >>
      ntac 2 WRITES_BIND >> simp writes_simps)
  >- (rpt gen_tac >> ntac 2 WRITES_BIND >> simp writes_simps) >>
  rpt gen_tac >> ntac 2 WRITES_BIND >> simp writes_simps
QED

Theorem abi_decode_fresh_writes_static:
  (!v. abi_decode_fresh_writes (clamp v)) ==>
  abi_decode_fresh_writes (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  WRITES_BIND >> WRITES_IGNORE >> simp writes_simps
QED

Theorem abi_decode_fresh_writes_alloc_buffer:
  abi_decode_fresh_writes (compile_alloc_buffer n)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> WRITES_BIND >> simp writes_simps
QED

Theorem abi_decode_fresh_writes_addr:
  abi_decode_fresh_writes (compile_abi_dec_addr base_op pos)
Proof
  simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >> simp writes_simps
QED

Theorem abi_decode_fresh_writes_member_pointer:
  abi_decode_fresh_writes (compile_getelemptr_abi src dyn off opc base_op hi)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >> WRITES_BIND >> Cases_on `dyn` >>
  simp[abi_decode_fresh_writes_return] >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_addr] >> ntac 2 WRITES_BIND >>
  ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_fresh_writes_return] >>
      ntac 2 WRITES_BIND >> simp writes_simps) >>
  simp[abi_decode_fresh_writes_return]
QED

Theorem abi_decode_fresh_writes_range_check:
  abi_decode_fresh_writes (compile_abi_decode_range_check start_op end_op hi_op)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 WRITES_BIND >> simp writes_simps
QED

Theorem abi_decode_fresh_writes_head_check:
  abi_decode_fresh_writes
    (if hi = Lit 0w then comp_return (Lit 0w)
     else do head_end <- emit_op ADD [src; Lit 32w];
             compile_abi_decode_range_check src head_end hi;
             comp_return head_end
          od)
Proof
  IF_CASES_TAC >> simp[abi_decode_fresh_writes_return] >> WRITES_BIND >>
  ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- simp[abi_decode_fresh_writes_range_check] >> simp writes_simps
QED

Theorem abi_decode_fresh_writes_array_pointer:
  abi_decode_fresh_writes (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz)
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_addr] >> ntac 2 WRITES_BIND >>
  ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_fresh_writes_return] >>
      ntac 2 WRITES_BIND >> WRITES_IGNORE >>
      WRITES_BIND >> simp[abi_decode_fresh_writes_range_check]) >>
  simp[abi_decode_fresh_writes_return]
QED

Theorem abi_decode_fresh_writes_mutual:
  (!dst src opc base_op hi info. abi_decode_fresh_writes (compile_abi_decode_to_buf dst src opc base_op hi info)) /\
  (!dst src opc base_op hi elems ao vo.
    abi_decode_fresh_writes (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo)) /\
  (!dst src opc base_op hi ei asz msz ip cnt.
    abi_decode_fresh_writes (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume abi_decode_fresh_writes_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_addr] >>
  irule abi_decode_fresh_writes_static >> simp[abi_decode_fresh_writes_clamp]
QED

Resume abi_decode_fresh_writes_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_head_check] >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_addr] >>
  ntac 3 WRITES_BIND >> WRITES_IGNORE >>
  ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_fresh_writes_return] >>
      WRITES_BIND >> simp[abi_decode_fresh_writes_range_check]) >>
  IF_CASES_TAC
  >- (Cases_on `opc` >> simp writes_simps) >>
  ntac 4 WRITES_BIND >> WRITES_IGNORE >> WRITES_BIND >> simp writes_simps
QED

Resume abi_decode_fresh_writes_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_head_check] >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_addr] >>
  ntac 3 WRITES_BIND >> WRITES_IGNORE >>
  ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_fresh_writes_return] >>
      ntac 2 WRITES_BIND >> simp[abi_decode_fresh_writes_range_check]) >>
  WRITES_BIND >> WRITES_IGNORE >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 2 WRITES_BIND >> WRITES_BIND_WITH [abi_decode_fresh_writes_addr] >>
      WRITES_BIND >> Cases_on `opc` >> simp writes_simps) >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_alloc_buffer] >>
  WRITES_IGNORE >> first_x_assum irule >> simp[]
QED

Resume abi_decode_fresh_writes_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (first_x_assum (qspec_then `FOLDR (\(_,abi_sz:num,_) acc. abi_sz + acc) 0 elems`
        mp_tac) >> simp[]) >>
  WRITES_BIND >>
  ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- simp[abi_decode_fresh_writes_range_check] >>
  first_x_assum (qspec_then `FOLDR (\(_,abi_sz:num,_) acc. abi_sz + acc) 0 elems`
    mp_tac) >> simp[]
QED

Resume abi_decode_fresh_writes_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> simp[abi_decode_fresh_writes_return]
QED

Resume abi_decode_fresh_writes_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_member_pointer] >>
  WRITES_BIND >> ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  first_x_assum (irule o SRULE[]) >> simp[]
QED

Resume abi_decode_fresh_writes_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> ntac 3 WRITES_BIND >>
  WRITES_IGNORE >> WRITES_IGNORE >> WRITES_BIND >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_addr] >> ntac 3 WRITES_BIND >>
  WRITES_IGNORE >> WRITES_IGNORE >> ntac 4 WRITES_BIND >>
  ho_match_mp_tac abi_decode_fresh_writes_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_fresh_writes_array_pointer, abi_decode_fresh_writes_return]) >>
  rpt gen_tac >> ntac 3 WRITES_BIND >> ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  WRITES_BIND >> WRITES_IGNORE >> WRITES_IGNORE >> WRITES_IGNORE >>
  simp[abi_decode_fresh_writes_return]
QED

Finalise abi_decode_fresh_writes_mutual

Theorem abi_decode_to_buf_output_writes:
  compile_abi_decode_to_buf dst src opc base_op hi info ready = ((),final) ==>
  !i x. MEM i (frag_code ready final) /\ MEM x i.inst_outputs ==>
    ?n. ready.cs_next_var <= n /\ x = STRING #"%" (toString n)
Proof
  mp_tac (cj 1 abi_decode_fresh_writes_mutual) >>
  simp[abi_decode_fresh_writes_def] >> metis_tac[]
QED

Theorem abi_decode_to_buf_older_outputs_disjoint:
  compile_abi_decode_to_buf dst src opc base_op hi info ready = ((),final) /\
  MEM i (frag_code ready final) /\
  x IN abi_decoder_older_vars ready.cs_next_var ==>
  ~MEM x i.inst_outputs
Proof
  strip_tac >> drule abi_decode_to_buf_output_writes >>
  gvs[abi_decoder_older_vars_def] >> metis_tac[]
QED
