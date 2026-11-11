(* Local ABI layout arithmetic, independent of runtime decoding. *)
Theory abiDecoderLayoutBounds
Ancestors
  compileEnv abiDecoderCoherence abiEncoderInput exprLowering
  list arithmetic words

Theorem abi_decoder_layout_sum_le[local]:
  !xs f g. (!x. MEM x xs ==> f x <= g x) ==>
    SUM (MAP f xs) <= SUM (MAP g xs)
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`f`, `g`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  `f h <= g h` by metis_tac[] >> decide_tac
QED

Theorem abi_static_size_le_size_bound:
  abi_static_size sf ty <= abi_size_bound sf ty
Proof
  Cases_on `ty` >>
  simp[Once abi_size_bound_def, Once abi_static_size_def,
       abi_embedded_static_size_def] >>
  TRY (Cases_on `b` >> simp[abi_size_bound_def, abi_static_size_def])
  >~ [`BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> simp[abi_static_size_def, abi_size_bound_def])
  >~ [`SUM (MAP _ _) <= SUM (MAP _ _)`]
  >- (irule abi_decoder_layout_sum_le >> simp[])
  >~ [`n = 0 \/ _`]
  >- simp[abi_embedded_static_size_def]
  >~ [`FLOOKUP sf key`]
  >- (Cases_on `FLOOKUP sf key` >> simp[] >>
      irule abi_decoder_layout_sum_le >> simp[])
  >> simp[abi_static_size_def]
QED

Theorem abi_decoder_static_primitive_array_product_bound:
  abi_embedded_static_size sf elem = 32 /\
  ~is_abi_dynamic sf elem /\
  abi_size_bound sf (ArrayT elem (Dynamic n)) < dimword (:256) ==>
  32 * n < dimword (:256)
Proof
  strip_tac >>
  qpat_x_assum `abi_size_bound _ _ < _` mp_tac >>
  asm_simp_tac bool_ss [Once abi_size_bound_def, ADD_CLAUSES] >>
  once_rewrite_tac[MULT_COMM] >> decide_tac
QED

(* Reuse the encoder's general prefix theorem rather than duplicate it. *)
Theorem abi_decoder_primitive_member_head_bound:
  i < LENGTH tys /\ abi_embedded_static_size sf (EL i tys) = 32 ==>
  SUM (MAP (abi_embedded_static_size sf) (TAKE i tys)) + 32 <=
    SUM (MAP (abi_embedded_static_size sf) tys)
Proof
  strip_tac >> drule abi_encoder_prefix_sum_bound >>
  disch_then (qspec_then `abi_embedded_static_size sf` mp_tac) >> simp[]
QED

Theorem abi_decoder_primitive_minimum_cap:
  abi_static_size sf ty = 32 ==> 32 <= abi_size_bound sf ty
Proof
  metis_tac[abi_static_size_le_size_bound]
QED

Theorem abi_decoder_primitive_base_stride:
  type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp ==>
  ~is_abi_dynamic sf (BaseT bt) /\
  abi_embedded_static_size sf (BaseT bt) = 32
Proof
  Cases_on `bt` >>
  simp[type_to_abi_dec_info_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def] >>
  Cases_on `b` >>
  simp[type_to_abi_dec_info_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def]
QED

Theorem abi_decoder_primitive_flag_stride:
  ~is_abi_dynamic sf (FlagT nsid) /\
  abi_embedded_static_size sf (FlagT nsid) = 32
Proof
  simp[is_abi_dynamic_def, abi_embedded_static_size_def, abi_static_size_def]
QED

Theorem abi_decoder_tuple_primitive_head_bound:
  i < LENGTH tys /\ abi_embedded_static_size sf (EL i tys) = 32 ==>
  SUM (MAP (abi_embedded_static_size sf) (TAKE i tys)) + 32 <=
    abi_static_size sf (TupleT tys)
Proof
  strip_tac >> drule_all abi_decoder_primitive_member_head_bound >>
  simp[Once abi_static_size_def, GSYM abi_embedded_static_size_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

(* Empty arrays do not impose a size bound on their unvisited element. *)
Theorem abi_decoder_zero_capacity_probe:
  abi_size_bound sf (ArrayT (BaseT (BytesT (Dynamic n))) (Dynamic 0)) = 32 /\
  abi_size_bound sf (ArrayT (BaseT (BytesT (Dynamic n))) (Fixed 0)) = 0
Proof
  conj_tac >> simp[Once abi_size_bound_def]
QED
