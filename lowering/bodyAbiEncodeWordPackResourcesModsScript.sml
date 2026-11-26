Theory bodyAbiEncodeWordPackResourcesMods
Ancestors
  exprSimAbiEncodeBytesOwnership bodyFullAbiEncodeResultResources
  exprSimProps valueEncodingProps exprLowering typeLayoutProps
  vyperTypeSystem vyperAST abiBuiltinEncodeMethod compileEnv words list

(* Interpret the allocation and its clean reads at a fixed endpoint.  The
   annotation bounds the source value, independently of the rounded capacity. *)
Theorem abi_encode_word_pack_resources_mods:
  let E = TypeBuiltin ann (AbiEncode F mid) ty [e];
      selector = OPTION_MAP bytes_method_id_word mid;
      k = (case selector of NONE => 0 | SOME _ => 4);
      cap = 32 + 32 * word_size (32 + k);
      payload = abi_encode_method_id_bytes mid ++ enc at av
  in
    ann = BaseT (BytesT (Dynamic N)) /\
    well_typed_type_builtin_args (AbiEncode F mid) ty [expr_type e] /\
    LENGTH payload <= N /\ LENGTH (enc at av) = 32 /\
    lowered_value_type ce e = expr_type e /\
    abi_size_bound ce.ce_struct_fields (expr_type e) = 32 /\
    eval_operand (Var q) z = SOME (n2w p) /\ ptr_covers Gz tz q z cap /\
    p + cap <= z.vs_alloca_next /\ z.vs_alloca_next < dimword (:256) /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
       mem_word_at p mem = n2w (32 + k) /\
       mem_bytes_at (p + 32 + k) 32 mem = enc at av /\
       (case selector of NONE => T | SOME w =>
          mem_bytes_at (p + 32) 4 mem = abi_builtin_encode_method_bytes w)) ==>
    type_memory_bytes ce (lowered_value_type ce E) = cap /\
    val_store_size (BaseTV (BytesT (Dynamic N))) (BytesV payload) = cap /\
    32 + LENGTH payload <= cap /\
    w2n (n2w p : bytes32) = p /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
       val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) p mem) /\
    vv_store_bound cx (post_value_type ce E) (lowered_value_type ce E) ee
      (Value (BytesV payload)) (LocatedValue ann (mk_ptr (Var q) LocMemory)) z /\
    ptr_vv_ok cx (post_value_type ce E) (Value (BytesV payload))
      (LocatedValue ann (mk_ptr (Var q) LocMemory)) ee Gz tz z /\
    ptr_buf_ok ce E (Var q) Gz z
Proof
  PURE_REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qabbrev_tac `k = case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4` >>
  qabbrev_tac `cap = 32 + 32 * word_size (32 + k)` >>
  strip_tac >>
  `LENGTH (abi_encode_method_id_bytes mid) = k` by
    (Cases_on `mid` >> fs[Abbr `k`, abi_encode_method_id_bytes_def,
                          well_typed_type_builtin_args_def]) >>
  conj_asm1_tac
  >- (Cases_on `mid` >>
      simp[Once lowered_value_type_def, Abbr `cap`, Abbr `k`,
           type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  conj_asm1_tac
  >- (simp[Abbr `cap`, val_store_size_def, LENGTH_APPEND] >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >> simp[]) >>
  conj_tac
  >- (`LENGTH (abi_encode_method_id_bytes mid ++ enc at av) = 32 + k` by
        (simp[LENGTH_APPEND] >> decide_tac) >>
      simp[Abbr `cap`, le_word_size_mul]) >>
  conj_asm1_tac
  >- (`p < dimword (:256)` by decide_tac >> simp[w2n_n2w]) >>
  conj_asm1_tac
  >- (rpt strip_tac >>
      qpat_assum `!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> _`
        (qspec_then `mem` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      irule (SRULE [GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]
        (Q.INST [`actual` |-> `z with vs_memory := mem`]
          abi_encode_tuple_result_memory)) >>
      conj_tac
      >- (qexists `OPTION_MAP bytes_method_id_word mid` >>
          qunabbrev_tac `k` >> asm_rewrite_tac[]) >>
      qexistsl [`F`, `ty`, `[expr_type e]`] >> first_assum ACCEPT_TAC) >>
  irule abi_encode_bytes_full_resources >>
  qexistsl [`N`, `cap`, `n2w p`] >> simp[expr_type_def]
QED
