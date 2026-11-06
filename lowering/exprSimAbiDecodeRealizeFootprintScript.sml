Theory exprSimAbiDecodeRealizeFootprint
Ancestors
  exprSimAbiDecodeRealizeSource exprSimAbiDecodeSizeProbe exprLowering
  abiEncoder compileEnv emitHelper vyperCompiler venomInst list

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
