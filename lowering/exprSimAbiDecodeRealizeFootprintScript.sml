Theory exprSimAbiDecodeRealizeFootprint
Ancestors
  exprSimAbiDecodeRealizeSource exprSimAbiDecodeSizeProbe exprLowering
  abiEncoder builtinAbi context compileEnv emitHelper vyperCompiler venomInst list

(* Multiplicities matter: this is a list projection, not code membership. *)
Definition abi_decode_realize_alloc_ops_def:
  abi_decode_realize_alloc_ops is =
    FILTER (\i. MEM i.inst_opcode [ALLOCA; DALLOCA; INVOKE]) is
End

Definition abi_decode_realize_code_def:
  abi_decode_realize_code st =
    FLAT (MAP (\b. b.bb_instructions) (REVERSE st.cs_blocks)) ++
    st.cs_current_insts
End

Definition abi_decode_realize_alloc_projection_def:
  abi_decode_realize_alloc_projection st =
    abi_decode_realize_alloc_ops (abi_decode_realize_code st)
End

Definition abi_decode_realize_alloc_charge_def:
  abi_decode_realize_alloc_charge is =
    SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) is))
End

Theorem abi_decode_realize_projection_emit:
  ~MEM opc [ALLOCA; DALLOCA; INVOKE] ==>
  abi_decode_realize_alloc_projection (SND (emit_op opc ops st)) =
    abi_decode_realize_alloc_projection st /\
  abi_decode_realize_alloc_projection (SND (emit_void opc ops st)) =
    abi_decode_realize_alloc_projection st
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def,
       abi_decode_realize_alloc_projection_def, abi_decode_realize_code_def,
       abi_decode_realize_alloc_ops_def, FILTER_APPEND_DISTRIB, mk_inst_def]
QED

Theorem abi_decode_realize_projection_return:
  abi_decode_realize_alloc_projection (SND (comp_return v st)) =
    abi_decode_realize_alloc_projection st
Proof
  simp[comp_return_def]
QED

Theorem abi_decode_realize_projection_bind:
  (!st. abi_decode_realize_alloc_projection (SND (f st)) =
          abi_decode_realize_alloc_projection st) /\
  (!v st. abi_decode_realize_alloc_projection (SND (g v st)) =
          abi_decode_realize_alloc_projection st) ==>
  abi_decode_realize_alloc_projection (SND (comp_bind f g st)) =
    abi_decode_realize_alloc_projection st
Proof
  rpt strip_tac >> simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND]
QED

Theorem abi_decode_realize_projection_ignore_bind:
  (!st. abi_decode_realize_alloc_projection (SND (f st)) =
          abi_decode_realize_alloc_projection st) /\
  (!st. abi_decode_realize_alloc_projection (SND (g st)) =
          abi_decode_realize_alloc_projection st) ==>
  abi_decode_realize_alloc_projection (SND (comp_ignore_bind f g st)) =
    abi_decode_realize_alloc_projection st
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule abi_decode_realize_projection_bind >> simp[]
QED

Definition abi_decode_realize_alloc_free_def:
  abi_decode_realize_alloc_free f <=>
    !st. abi_decode_realize_alloc_projection (SND (f st)) =
      abi_decode_realize_alloc_projection st
End

Theorem abi_decode_realize_alloc_free_bind:
  abi_decode_realize_alloc_free f /\
  (!v. abi_decode_realize_alloc_free (g v)) ==>
  abi_decode_realize_alloc_free (comp_bind f g)
Proof
  simp[abi_decode_realize_alloc_free_def] >> rpt strip_tac >>
  irule abi_decode_realize_projection_bind >> simp[]
QED

Theorem abi_decode_realize_alloc_free_ignore_bind:
  abi_decode_realize_alloc_free f /\ abi_decode_realize_alloc_free g ==>
  abi_decode_realize_alloc_free (comp_ignore_bind f g)
Proof
  simp[abi_decode_realize_alloc_free_def] >> rpt strip_tac >>
  irule abi_decode_realize_projection_ignore_bind >> simp[]
QED

Theorem abi_decode_realize_alloc_free_primitives:
  abi_decode_realize_alloc_free (comp_return v) /\
  (~MEM opc [ALLOCA; DALLOCA; INVOKE] ==>
    abi_decode_realize_alloc_free (emit_op opc ops) /\
    abi_decode_realize_alloc_free (emit_void opc ops))
Proof
  simp[abi_decode_realize_alloc_free_def, abi_decode_realize_projection_return,
       abi_decode_realize_projection_emit]
QED

Theorem abi_decode_realize_alloc_free_range:
  abi_decode_realize_alloc_free (compile_abi_decode_range_check lo hi lim)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (ho_match_mp_tac abi_decode_realize_alloc_free_bind >>
    conj_tac >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac) >>
  simp[abi_decode_realize_alloc_free_primitives]
QED

Theorem abi_decode_realize_alloc_free_addr:
  abi_decode_realize_alloc_free (compile_abi_dec_addr base_op src)
Proof
  simp[compile_abi_dec_addr_def, abi_decode_realize_alloc_free_primitives] >>
  IF_CASES_TAC >> simp[abi_decode_realize_alloc_free_primitives]
QED

Theorem abi_decode_realize_bytes_projection:
  abi_decode_realize_alloc_free
    (compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n))
Proof
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_alloc_free_primitives] >>
      ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
      >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac >>
      irule abi_decode_realize_alloc_free_ignore_bind >>
      simp[abi_decode_realize_alloc_free_range,
           abi_decode_realize_alloc_free_primitives]) >>
  gen_tac >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_addr] >> gen_tac >>
  ntac 3 (ho_match_mp_tac abi_decode_realize_alloc_free_bind >>
    conj_tac >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac) >>
  irule abi_decode_realize_alloc_free_ignore_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_primitives] >>
  irule abi_decode_realize_alloc_free_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_alloc_free_primitives] >>
      ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
      >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac >>
      simp[abi_decode_realize_alloc_free_range]) >>
  IF_CASES_TAC >- simp[abi_decode_realize_alloc_free_primitives] >>
  ntac 4 (ho_match_mp_tac abi_decode_realize_alloc_free_bind >>
    conj_tac >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac) >>
  irule abi_decode_realize_alloc_free_ignore_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_primitives] >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac >>
  simp[abi_decode_realize_alloc_free_primitives]
QED

Theorem abi_decode_realize_alloc_free_getelem:
  abi_decode_realize_alloc_free
    (compile_getelemptr_abi src dyn off MLOAD base_op hi)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac >>
  IF_CASES_TAC >- simp[abi_decode_realize_alloc_free_primitives] >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_addr] >> gen_tac >>
  ntac 2 (ho_match_mp_tac abi_decode_realize_alloc_free_bind >>
    conj_tac >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac) >>
  irule abi_decode_realize_alloc_free_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_alloc_free_primitives] >>
      ntac 2 (ho_match_mp_tac abi_decode_realize_alloc_free_bind >>
        conj_tac >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac) >>
      simp[abi_decode_realize_alloc_free_primitives]) >>
  simp[abi_decode_realize_alloc_free_primitives]
QED

Theorem abi_decode_realize_alloc_free_singleton:
  (!dst src base_op hi. abi_decode_realize_alloc_free
    (compile_abi_decode_to_buf dst src MLOAD base_op hi ei)) ==>
  abi_decode_realize_alloc_free
    (compile_abi_decode_complex_elems dst src MLOAD base_op hi [(ei,asz,msz)] ao vo)
Proof
  strip_tac >> rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_getelem] >> gen_tac >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac >>
  irule abi_decode_realize_alloc_free_ignore_bind >> conj_tac
  >- simp[] >>
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp[abi_decode_realize_alloc_free_primitives]
QED

Theorem abi_decode_realize_alloc_free_wrapper:
  (!dst src base_op hi. abi_decode_realize_alloc_free
    (compile_abi_decode_to_buf dst src MLOAD base_op hi ei)) ==>
  abi_decode_realize_alloc_free
    (compile_abi_decode_to_buf dst src MLOAD base_op hi
      (DecComplex dyn [(ei,asz,msz)]))
Proof
  strip_tac >> rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM, listTheory.FOLDR] >> BETA_TAC >>
  IF_CASES_TAC >- simp[abi_decode_realize_alloc_free_singleton] >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac >>
  irule abi_decode_realize_alloc_free_ignore_bind >>
  simp[abi_decode_realize_alloc_free_range, abi_decode_realize_alloc_free_singleton]
QED

Theorem abi_decode_realize_decoder_projection:
  !k dst src base_op hi.
    abi_decode_realize_alloc_free
      (compile_abi_decode_to_buf dst src MLOAD base_op hi
        (type_to_abi_dec_info sf ce (abi_decode_size_probe_type k)))
Proof
  Induct
  >- simp[abi_decode_size_probe_type_def, type_to_abi_dec_info_def,
          abi_decode_realize_bytes_projection] >>
  rpt gen_tac >>
  simp[abi_decode_size_probe_type_def, Once type_to_abi_dec_info_def] >>
  irule abi_decode_realize_alloc_free_wrapper >> simp[]
QED

(* Allocation effects forget IDs, but retain opcode, size, and multiplicity. *)
Definition abi_decode_realize_alloc_summary_def:
  abi_decode_realize_alloc_summary st =
    MAP (\i. (i.inst_opcode, alloca_size i))
      (abi_decode_realize_alloc_projection st)
End

Definition abi_decode_realize_alloc_effect_def:
  abi_decode_realize_alloc_effect f xs <=>
    !st. abi_decode_realize_alloc_summary (SND (f st)) =
      abi_decode_realize_alloc_summary st ++ xs
End

Theorem abi_decode_realize_effect_free:
  abi_decode_realize_alloc_free f ==>
  abi_decode_realize_alloc_effect f []
Proof
  simp[abi_decode_realize_alloc_free_def, abi_decode_realize_alloc_effect_def,
       abi_decode_realize_alloc_summary_def]
QED

Theorem abi_decode_realize_effect_bind:
  abi_decode_realize_alloc_effect f xs /\
  (!v. abi_decode_realize_alloc_effect (g v) ys) ==>
  abi_decode_realize_alloc_effect (comp_bind f g) (xs ++ ys)
Proof
  simp[abi_decode_realize_alloc_effect_def] >> rpt strip_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND, APPEND_ASSOC]
QED

Theorem abi_decode_realize_effect_ignore_bind:
  abi_decode_realize_alloc_effect f xs /\
  abi_decode_realize_alloc_effect g ys ==>
  abi_decode_realize_alloc_effect (comp_ignore_bind f g) (xs ++ ys)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule abi_decode_realize_effect_bind >> simp[]
QED

Theorem abi_decode_realize_effect_alloc:
  abi_decode_realize_alloc_effect (compile_alloc_buffer n)
    [(ALLOCA, w2n (n2w n : bytes32))]
Proof
  simp[abi_decode_realize_alloc_effect_def, abi_decode_realize_alloc_summary_def,
       compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def,
       abi_decode_realize_alloc_projection_def, abi_decode_realize_code_def,
       abi_decode_realize_alloc_ops_def, FILTER_APPEND_DISTRIB, mk_inst_def,
       MAP_APPEND, alloca_size_def]
QED

Theorem abi_decode_realize_effect_free_bind:
  abi_decode_realize_alloc_free f /\
  (!v. abi_decode_realize_alloc_effect (g v) ys) ==>
  abi_decode_realize_alloc_effect (comp_bind f g) ys
Proof
  strip_tac >>
  mp_tac (Q.INST [`xs` |-> `[]`] abi_decode_realize_effect_bind) >>
  simp[abi_decode_realize_effect_free]
QED

Theorem abi_decode_realize_effect_free_ignore:
  abi_decode_realize_alloc_free f /\ abi_decode_realize_alloc_effect g ys ==>
  abi_decode_realize_alloc_effect (comp_ignore_bind f g) ys
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule abi_decode_realize_effect_free_bind >> simp[]
QED

Theorem abi_decode_realize_effect_free_suffix:
  abi_decode_realize_alloc_effect f xs /\
  (!v. abi_decode_realize_alloc_free (g v)) ==>
  abi_decode_realize_alloc_effect (comp_bind f g) xs
Proof
  strip_tac >>
  mp_tac (Q.INST [`ys` |-> `[]`] abi_decode_realize_effect_bind) >>
  simp[abi_decode_realize_effect_free]
QED

Theorem abi_decode_realize_lower_projection:
  abi_decode_realize_alloc_effect
    (lower_abi_decode data
      (type_to_abi_dec_info sf ce (abi_decode_size_probe_type k)) lo hi sz)
    [(ALLOCA, w2n (n2w sz : bytes32))]
Proof
  rewrite_tac[lower_abi_decode_def] >>
  ntac 2 (ho_match_mp_tac abi_decode_realize_effect_free_bind >>
    conj_tac >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac) >>
  irule abi_decode_realize_effect_free_ignore >> conj_tac
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac abi_decode_realize_alloc_free_bind >>
          simp[abi_decode_realize_alloc_free_primitives]) >>
      ntac 5 (ho_match_mp_tac abi_decode_realize_alloc_free_bind >>
        conj_tac >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac) >>
      simp[abi_decode_realize_alloc_free_primitives]) >>
  ho_match_mp_tac abi_decode_realize_effect_free_suffix >> conj_tac
  >- simp[abi_decode_realize_effect_alloc] >> gen_tac >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac >>
  irule abi_decode_realize_alloc_free_ignore_bind >>
  simp[abi_decode_realize_decoder_projection, abi_decode_realize_alloc_free_primitives]
QED

Theorem abi_decode_realize_chunks_free:
  !p bs off. abi_decode_realize_alloc_free
    (compile_store_byte_chunks p bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  rewrite_tac[Once compile_store_byte_chunks_def] >>
  simp_tac (srw_ss()) [LET_THM, abi_decode_realize_alloc_free_primitives] >>
  ho_match_mp_tac abi_decode_realize_alloc_free_bind >> conj_tac
  >- simp[abi_decode_realize_alloc_free_primitives] >> gen_tac >>
  irule abi_decode_realize_alloc_free_ignore_bind >>
  simp[abi_decode_realize_alloc_free_primitives] >>
  first_x_assum (mp_tac o SIMP_RULE (srw_ss()) []) >> simp[]
QED

Theorem abi_decode_realize_literal_projection:
  abi_decode_realize_alloc_effect
    (compile_literal_vv (BaseT (BytesT (Dynamic 32)))
      (BytesL (REPLICATE 32 0w))) [(ALLOCA,64)]
Proof
  simp_tac (srw_ss()) [compile_literal_vv_def] >>
  ho_match_mp_tac abi_decode_realize_effect_free_suffix >> conj_tac
  >- (simp[compile_bytelike_literal_def] >>
      ho_match_mp_tac abi_decode_realize_effect_free_suffix >> conj_tac
      >- (mp_tac (Q.SPEC `64` (GEN_ALL abi_decode_realize_effect_alloc)) >>
          simp[wordsTheory.dimword_def]) >> gen_tac >>
      irule abi_decode_realize_alloc_free_ignore_bind >> conj_tac
      >- simp[abi_decode_realize_alloc_free_primitives] >>
      irule abi_decode_realize_alloc_free_ignore_bind >>
      simp[abi_decode_realize_chunks_free, abi_decode_realize_alloc_free_primitives]) >>
  simp[abi_decode_realize_alloc_free_primitives]
QED

Theorem abi_decode_realize_arg_compile:
  compile_expr ce (expr_type abi_decode_realize_arg) abi_decode_realize_arg =
    compile_literal_vv (BaseT (BytesT (Dynamic 32))) (BytesL (REPLICATE 32 0w))
Proof
  simp[FUN_EQ_THM, abi_decode_realize_arg_def, Once compile_expr_def,
       vyperASTTheory.expr_type_def]
QED

Theorem abi_decode_realize_literal_unwrap:
  compile_literal_vv (BaseT (BytesT (Dynamic 32))) (BytesL bs) st = (vv,st') ==>
  ?p. unwrap_value ce vv st' = (p,st')
Proof
  simp[compile_literal_vv_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  gvs[unwrap_value_def, compileEnvTheory.is_word_type_def, base_ptr_def, comp_return_def]
QED

Theorem abi_decode_realize_effect_result:
  abi_decode_realize_alloc_effect f xs /\ f st = (v,st') ==>
  abi_decode_realize_alloc_summary st' = abi_decode_realize_alloc_summary st ++ xs
Proof
  simp[abi_decode_realize_alloc_effect_def] >> metis_tac[pairTheory.SND]
QED

Theorem abi_decode_realize_lower_effect64:
  abi_decode_realize_alloc_effect
    (lower_abi_decode data
      (type_to_abi_dec_info sf ce (abi_decode_size_probe_type k)) lo hi 64)
    [(ALLOCA,64)]
Proof
  mp_tac (Q.INST [`sz` |-> `64`] abi_decode_realize_lower_projection) >>
  simp[wordsTheory.dimword_def]
QED

Theorem abi_decode_realize_expr_projection:
  abi_decode_realize_alloc_summary
    (SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
       (abi_decode_realize_expr k) st)) =
  abi_decode_realize_alloc_summary st ++ [(ALLOCA,64); (ALLOCA,64)]
Proof
  simp_tac (srw_ss()) [abi_decode_realize_expr_def, vyperASTTheory.expr_type_def,
    Once compile_expr_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_component_eq, LET_THM] >>
  simp[abi_decode_realize_arg_compile] >> pairarg_tac >>
  drule abi_decode_realize_literal_unwrap >>
  disch_then (qspec_then `ce` strip_assume_tac) >> simp[] >>
  simp[abi_decode_size_probe_memory] >>
  qmatch_goalsub_abbrev_tac `as_ptr_val _ _ result` >>
  Cases_on `result` >> simp[as_ptr_val_def] >>
  qpat_x_assum `Abbrev _` (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_at Any abi_decode_realize_effect_result >>
  disch_then (qspec_then `[(ALLOCA,64)]` mp_tac) >>
  simp[abi_decode_realize_lower_effect64] >> disch_then SUBST1_TAC >>
  qpat_x_assum `lower_abi_decode _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  drule_at Any abi_decode_realize_effect_result >>
  disch_then (qspec_then `[(ALLOCA,64)]` mp_tac) >>
  simp[abi_decode_realize_literal_projection, APPEND_ASSOC]
QED

Theorem abi_decode_realize_charge_summary:
  !is. abi_decode_realize_alloc_charge is =
    SUM (MAP SND (FILTER (\p. FST p = ALLOCA)
      (MAP (\i. (i.inst_opcode, alloca_size i)) (abi_decode_realize_alloc_ops is))))
Proof
  Induct >- simp[abi_decode_realize_alloc_charge_def, abi_decode_realize_alloc_ops_def] >>
  gen_tac >> Cases_on `h.inst_opcode = ALLOCA`
  >- gvs[abi_decode_realize_alloc_charge_def, abi_decode_realize_alloc_ops_def] >>
  Cases_on `h.inst_opcode = DALLOCA`
  >- gvs[abi_decode_realize_alloc_charge_def, abi_decode_realize_alloc_ops_def] >>
  Cases_on `h.inst_opcode = INVOKE` >>
  gvs[abi_decode_realize_alloc_charge_def, abi_decode_realize_alloc_ops_def]
QED

Theorem abi_decode_realize_summary_mem:
  MEM i is /\ MEM i.inst_opcode [ALLOCA; DALLOCA; INVOKE] ==>
  MEM (i.inst_opcode, alloca_size i)
    (MAP (\i. (i.inst_opcode, alloca_size i)) (abi_decode_realize_alloc_ops is))
Proof
  simp[abi_decode_realize_alloc_ops_def, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem abi_decode_realize_initial_projection:
  abi_decode_realize_alloc_summary
    (SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
       (abi_decode_realize_expr k) (initial_compile_state entry))) =
    [(ALLOCA,64); (ALLOCA,64)]
Proof
  simp[abi_decode_realize_expr_projection, abi_decode_realize_alloc_summary_def,
    abi_decode_realize_alloc_projection_def, abi_decode_realize_alloc_ops_def,
    abi_decode_realize_code_def, initial_compile_state_def]
QED

Theorem abi_decode_realize_expr_charge:
  abi_decode_realize_alloc_charge
    (abi_decode_realize_code
      (SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
       (abi_decode_realize_expr k) (initial_compile_state entry)))) = 128
Proof
  rewrite_tac[abi_decode_realize_charge_summary] >>
  rewrite_tac[GSYM abi_decode_realize_alloc_projection_def,
    GSYM abi_decode_realize_alloc_summary_def, abi_decode_realize_initial_projection] >>
  simp[]
QED

Theorem abi_decode_realize_expr_no_dynamic_or_invoke:
  MEM i (abi_decode_realize_code
      (SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
       (abi_decode_realize_expr k) (initial_compile_state entry)))) ==>
  i.inst_opcode <> DALLOCA /\ i.inst_opcode <> INVOKE
Proof
  strip_tac >>
  Cases_on `MEM i.inst_opcode [DALLOCA; INVOKE]`
  >- (`MEM i.inst_opcode [ALLOCA; DALLOCA; INVOKE]` by gvs[] >>
      drule_all abi_decode_realize_summary_mem >>
      rewrite_tac[GSYM abi_decode_realize_alloc_projection_def,
        GSYM abi_decode_realize_alloc_summary_def, abi_decode_realize_initial_projection] >>
      gvs[]) >> gvs[]
QED
