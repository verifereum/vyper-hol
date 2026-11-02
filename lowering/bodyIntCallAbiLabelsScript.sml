(* Structural ABI compiler boundaries, independent of source layout. *)
Theory bodyIntCallAbiLabels
Ancestors
  bodyIntCallContextLabels bodyIntCallLabelFrame bodyIntCallLabelReservations
  abiEncoder compileEnv pred_set

Theorem compiler_block_tail_abi_int_clamp:
  compiler_block_tail (compile_abi_int_clamp v bits signed)
Proof
  simp[compile_abi_int_clamp_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_int_clamp:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_abi_int_clamp v bits signed)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_abi_int_clamp_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_abi_bytes_clamp:
  compiler_block_tail (compile_abi_bytes_clamp v m)
Proof
  simp[compile_abi_bytes_clamp_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_bytes_clamp:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_abi_bytes_clamp v m)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_abi_bytes_clamp_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_abi_clamp_basetype:
  compiler_block_tail (compile_abi_clamp_basetype v c)
Proof
  Cases_on `c` >> simp[compile_abi_clamp_basetype_def,
    compiler_block_tail_abi_int_clamp, compiler_block_tail_abi_bytes_clamp,
    comp_ignore_bind_def, compiler_block_tail_primitives] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_clamp_basetype:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_abi_clamp_basetype v c)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `c` >> simp[compile_abi_clamp_basetype_def,
    compiler_label_hoare_abi_int_clamp, compiler_label_hoare_abi_bytes_clamp,
    comp_ignore_bind_def, compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_abi_decode_static:
  (!v. compiler_block_tail (clamp v)) ==>
  compiler_block_tail (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >> simp[compile_abi_decode_static_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_decode_static:
  (!v. compiler_label_hoare (compiler_label_reservation origin pending)
    (clamp v) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_abi_decode_static src dst opc clamp)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[compile_abi_decode_static_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_abi_element_ptrs:
  compiler_block_tail (compile_get_element_ptr src off) /\
  compiler_block_tail (compile_get_dynarray_elem_ptr src idx sz)
Proof
  simp[compile_get_element_ptr_def, compile_get_dynarray_elem_ptr_def,
       compiler_block_tail_primitives] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_element_ptrs:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_element_ptr src off)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_dynarray_elem_ptr src idx sz)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_get_element_ptr_def, compile_get_dynarray_elem_ptr_def,
       compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_getelemptr_abi:
  compiler_block_tail (compile_getelemptr_abi src dyn off opc hi)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac) >>
  simp[compiler_block_tail_primitives] >>
  ho_match_mp_tac compiler_block_tail_bind >> conj_tac
  >- (rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
           >- simp[compiler_block_tail_primitives] >> gen_tac) >>
      simp[compiler_block_tail_primitives]) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_getelemptr_abi:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_getelemptr_abi src dyn off opc hi)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_context_primitives,
       compiler_label_hoare_typed_primitives] >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
  >- (rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
           >- simp[compiler_label_hoare_context_primitives,
                   compiler_label_hoare_typed_primitives] >> gen_tac) >>
      simp[compiler_label_hoare_typed_primitives]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_abi_decode_dyn_elem_ptr:
  compiler_block_tail (compile_abi_decode_dyn_elem_ptr opc src data hi sz)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac) >>
  simp[compiler_block_tail_primitives] >>
  ho_match_mp_tac compiler_block_tail_bind >> conj_tac
  >- (rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
           >- simp[compiler_block_tail_primitives] >> gen_tac) >>
      simp[compiler_block_tail_primitives]) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_decode_dyn_elem_ptr:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_abi_decode_dyn_elem_ptr opc src data hi sz)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_context_primitives,
       compiler_label_hoare_typed_primitives] >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
  >- (rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
           >- simp[compiler_label_hoare_context_primitives,
                   compiler_label_hoare_typed_primitives] >> gen_tac) >>
      simp[compiler_label_hoare_typed_primitives]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

(* The callback is deliberately quantified over all reservations: the loop's
   exit is still pending while the nested decoder is compiled. *)
Theorem compiler_abi_decode_loop_boundary:
  (!dst src. compiler_block_tail (decode dst src)) /\
  (!origin pending dst src.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (decode dst src) (\r out. compiler_label_reservation origin pending out)) ==>
  let loop =
    do hdr <- fresh_label "dec_dyn_hdr";
       body <- fresh_label "dec_dyn_body";
       exit <- fresh_label "dec_dyn_exit";
       emit_inst JMP [Label hdr] [];
       new_block hdr;
       i <- emit_op MLOAD [ip];
       count <- emit_op opc [src];
       cmp <- emit_op LT [i; count];
       done <- emit_op ISZERO [cmp];
       emit_inst JNZ [done; Label exit; Label body] [];
       new_block body;
       i2 <- emit_op MLOAD [ip];
       data <- emit_op ADD [src; Lit 32w];
       off <- emit_op MUL [i2; Lit (n2w asz)];
       esrc <- emit_op ADD [data; off];
       actual <- (if dyn then
         compile_abi_decode_dyn_elem_ptr opc esrc data hi asz
         else return esrc);
       ddata <- emit_op ADD [dst; Lit 32w];
       doff <- emit_op MUL [i2; Lit (n2w msz)];
       edst <- emit_op ADD [ddata; doff];
       decode edst actual;
       next <- emit_op ADD [i2; Lit 1w];
       emit_void MSTORE [ip; next];
       emit_inst JMP [Label hdr] [];
       new_block exit;
       return ()
    od
  in compiler_block_tail loop /\
     !origin pending.
       compiler_label_hoare (compiler_label_reservation origin pending) loop
         (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[LET_THM, comp_ignore_bind_def] >> conj_tac
  >- (Cases_on `dyn` >> simp[] >>
      rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
           >- simp[compiler_block_tail_primitives,
                   compiler_block_tail_abi_decode_dyn_elem_ptr] >> gen_tac) >>
      simp[compiler_block_tail_primitives]) >>
  rpt gen_tac >>
  ntac 3 (irule compiler_label_hoare_fresh_bind >>
          gen_tac >> strip_tac >> BETA_TAC) >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> BETA_TAC >> gvs[NoAsms] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> BETA_TAC >> gvs[NoAsms] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_label_hoare_abi_decode_dyn_elem_ptr,
                          compiler_label_hoare_context_primitives,
                          compiler_label_hoare_typed_primitives]) >>
  gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC) >>
  simp[DELETE_INSERT] >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> BETA_TAC >>
  simp[DELETE_INSERT] >>
  rename1 `compiler_label_reservation origin (pending DELETE h DELETE b DELETE e)` >>
  `pending DELETE h DELETE b DELETE e = pending` by ASM_SET_TAC [] >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_abi_encode_static:
  compiler_block_tail (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_encode_static:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_abi_encode_static dst src)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_abi_encode_static_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_abi_encode_static_info:
  compiler_block_tail (compile_abi_encode_static_info dst src info)
Proof
  Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, compiler_block_tail_abi_encode_static,
       comp_ignore_bind_def, compiler_block_tail_primitives] >>
  ho_match_mp_tac compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_encode_static_info:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_abi_encode_static_info dst src info)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, compiler_label_hoare_abi_encode_static,
       comp_ignore_bind_def, compiler_label_hoare_context_primitives,
       compiler_label_hoare_typed_primitives] >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_abi_encode_dyn_static_loop:
  compiler_block_tail (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  simp[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def] >>
  ho_match_mp_tac compiler_block_tail_bind >> conj_tac
  >- simp[compiler_block_tail_alloc_buffer] >> gen_tac >> simp[] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives,
               compiler_block_tail_abi_encode_static_info] >> gen_tac) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_abi_encode_dyn_static_loop:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def] >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
  >- simp[compiler_label_hoare_storage_primitives] >> gen_tac >> simp[] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC >>
  ntac 3 (irule compiler_label_hoare_fresh_bind >>
          gen_tac >> strip_tac >> BETA_TAC) >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> BETA_TAC >> gvs[NoAsms] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> BETA_TAC >> gvs[NoAsms] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives,
               compiler_label_hoare_abi_encode_static_info] >> gen_tac >> BETA_TAC) >>
  simp[DELETE_INSERT] >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> BETA_TAC >>
  simp[DELETE_INSERT] >>
  rename1 `compiler_label_reservation origin (pending DELETE h DELETE b DELETE e)` >>
  `pending DELETE h DELETE b DELETE e = pending` by ASM_SET_TAC [] >> simp[] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac) >>
  simp[compiler_label_hoare_context_primitives]
QED
