(* First failure in the common dynamic-array guards, or entry to the loop arm. *)
Theory abiDecodeRejectArrayPrefix
Ancestors
  abiDecodeRejectArrayLayout abiDecodeRejectArrayCountLoad abiDecodeRejectArraySpan
  abiDecodeRejectBulkDomain abiMalformedAggregateFirstBadChild
  abiDecoderRecursiveArray abiMalformedBoundedContract abiDecoderCoherence
  abiMalformedRecursiveInterface valueEncodingProps fragGasOriginPtr
  abiDecoderReentry exprLowering contractABI vyperABI words list arithmetic

(* Use the exact closed propositions that FirstFailure will discharge. *)
val (layout_cut, _) =
  boolSyntax.dest_conj (#1 (boolSyntax.dest_imp (concl malformed_dynarray_guard_layout)));
val (head_cut, load_imp) = boolSyntax.dest_imp (concl malformed_dynarray_head_load_outcome);
val (load_cut, _) = boolSyntax.dest_imp load_imp;
val (compare_cut, abort_imp) = boolSyntax.dest_imp (concl malformed_dynarray_compare_span_abort);
val (abort_cut, _) = boolSyntax.dest_imp abort_imp;

(* Notation for the selected arm of malformed_aggregate_first_bad_child. *)
val abi_view = ``\a q. if is_dynamic a then DROP q (xs:word8 list)
                         else TAKE (static_length a) (DROP q xs)``;
val abi_ok = ``\e t z. vyper_decode_valid_enc (vyper_to_abi_type e t) z /\
                       abi_vyper_admissible e t (dec (vyper_to_abi_type e t) z)``;
val head_prefix = ``\e ts j. SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type e) (TAKE j ts)))``;
val member_position = ``\ce (f:string |-> (string # type # num) list) b ao t. b +
  (if dec_info_needs_offset (type_to_abi_dec_info f ce t)
   then abi_head_word (DROP (b+ao) xs) else ao)``;
val member_meta = ``\ce e f par v0 ts j.
  abi_decode_bytes_widths e (EL j ts) /\
  (?u. abi_decoder_coherent ce e f (EL j ts) u /\
       type_memory_size u = type_memory_bytes ce (EL j ts)) /\
  abi_size_bound f (EL j ts) < dimword (:256) /\
  v0 + SUM (MAP (type_memory_bytes ce) (TAKE j ts)) + type_memory_bytes ce (EL j ts) <=
    type_memory_bytes ce par``;
val member_good = ``\ce e f b ao t.
  (b + ao + abi_member_head_size (vyper_to_abi_type e t) <= LENGTH xs /\
   (^abi_ok) e t
     (abi_decode_member_bytes (vyper_to_abi_type e t) (DROP b xs) (DROP (b+ao) xs))) /\
  (^member_position) ce f b ao t <= LENGTH xs /\
  (is_dynamic (vyper_to_abi_type e t) \/
   (^member_position) ce f b ao t + static_length (vyper_to_abi_type e t) <= LENGTH xs) /\
  vyper_decode_valid_enc (vyper_to_abi_type e t) (DROP ((^member_position) ce f b ao t) xs) /\
  dec (vyper_to_abi_type e t)
    (abi_decode_member_bytes (vyper_to_abi_type e t) (DROP b xs) (DROP (b+ao) xs)) =
  dec (vyper_to_abi_type e t) (DROP ((^member_position) ce f b ao t) xs) /\
  (?v. abi_to_vyper e t
         (dec (vyper_to_abi_type e t) (DROP ((^member_position) ce f b ao t) xs)) = SOME v)``;
val member_bad = ``\ce e f b ao t.
  LENGTH xs < b + ao + abi_member_head_size (vyper_to_abi_type e t) \/
  (b + ao + abi_member_head_size (vyper_to_abi_type e t) <= LENGTH xs /\
   ~(^abi_ok) e t
     (abi_decode_member_bytes (vyper_to_abi_type e t) (DROP b xs) (DROP (b+ao) xs)) /\
   ~(^abi_ok) e t ((^abi_view) (vyper_to_abi_type e t) ((^member_position) ce f b ao t)) /\
   (dimword (:256) <= (^member_position) ce f b ao t \/
    (LENGTH xs < (^member_position) ce f b ao t /\
     (^member_position) ce f b ao t < dimword (:256)) \/
    (^member_position) ce f b ao t <= LENGTH xs))``;
val member_scan = ``\ce e f par b v0 ts.
  LENGTH ts < dimword (:256) /\ ?i. i < LENGTH ts /\
  (!j. j < i ==> (^member_meta) ce e f par v0 ts j /\
     (^member_good) ce e f b ((^head_prefix) e ts j) (EL j ts)) /\
  (^member_meta) ce e f par v0 ts i /\
  (^member_bad) ce e f b ((^head_prefix) e ts i) (EL i ts)``;

Theorem malformed_dynarray_prefix_or_bulk_joint:
  ^layout_cut ==> ^head_cut ==> ^load_cut ==> ^compare_cut ==> ^abort_cut ==>
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic cap)) (ArrayTV tv (Dynamic cap)) /\
  abi_decode_bytes_widths env (ArrayT ty (Dynamic cap)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic cap)) =
    DecDynArray ei stride mem_sz elem_dyn cap /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecDynArray ei stride mem_sz elem_dyn cap) st = ((),en) /\
  fn_has_code st en func /\
  (?av. has_type (vyper_to_abi_type env (ArrayT ty (Dynamic cap))) av) /\
  assignable_type env (ArrayT ty (Dynamic cap)) /\
  type_memory_size (ArrayTV tv (Dynamic cap)) < dimword(:256) /\
  abi_size_bound sf (ArrayT ty (Dynamic cap)) < dimword(:256) /\
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi pos (Var output) B L xs p d
    (type_memory_bytes ce (ArrayT ty (Dynamic cap))) s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~(^abi_ok) env (ArrayT ty (Dynamic cap)) (DROP p xs) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ abi_decode_ptr_window G tn s source (n2w B) L /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\ allocas_from lo s ==>
  (?u H z.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,H,z))) \/
  ((elem_dyn \/ dec_info_needs_clamp ei) /\ p+32 <= L /\ ?n.
    n = abi_head_word (DROP p xs) /\ n = w2n (mload (B+p) s) /\
    n <= cap /\ p+32+n*stride <= L /\
    (^member_scan) ce env sf (ArrayT ty (Dynamic cap)) (p+32) 32 (REPLICATE n ty))
Proof
  BETA_TAC >> ntac 5 disch_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `hi <> Lit 0w /\ p < dimword(:256) /\ abi_malformed_allocated_window live B L xs s`
    by fs[abi_malformed_entry_def] >>
  `mem_bytes_at B L s.vs_memory = xs /\ B+L < dimword(:256)`
    by fs[abi_malformed_allocated_window_def] >>
  `LENGTH xs = L /\ L < dimword(:256)` by
    (conj_tac >- metis_tac[LENGTH_mem_bytes_at] >> decide_tac) >>
  drule_all malformed_dynarray_guard_layout >> strip_tac >>
  drule_all malformed_dynarray_head_load_outcome >>
  disch_then (qspec_then `PG`
    (DISJ_CASES_THEN2 (fn th => disj1_tac >> ACCEPT_TAC th) STRIP_ASSUME_TAC)) >>
  qabbrev_tac `n = w2n (mload (B+p) s)` >>
  Cases_on `n <= cap /\ p+32+n*stride <= L`
  >- (qpat_x_assum `n <= cap /\ _` strip_assume_tac >>
      `n = w2n (mload (B+p) s)` by simp[Abbr `n`] >>
      drule_all_then assume_tac malformed_dynarray_passing_not_bulk >>
      disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `n` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- REFL_TAC >>
      ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
      `~(^abi_ok) env (ArrayT ty (Dynamic cap))
           ((^abi_view) (vyper_to_abi_type env (ArrayT ty (Dynamic cap))) p)` by
        (simp_tac bool_ss [vyper_to_abi_type_def, is_dynamic_def, optionTheory.IS_NONE_DEF] >>
         qpat_assum `~(vyper_decode_valid_enc _ _ /\ _)`
           (ACCEPT_TAC o SIMP_RULE bool_ss [vyper_to_abi_type_def])) >>
      `LENGTH xs < dimword(:256)` by asm_rewrite_tac[] >>
      RULE_ASSUM_TAC BETA_RULE >>
      `~(LENGTH xs < p+32) /\ ~(cap < n)` by decide_tac >>
      drule_all (BETA_RULE malformed_aggregate_first_bad_child) >>
      disch_then (mp_tac o SIMP_RULE bool_ss
        [TypeBase.case_def_of ``:type``, vyperASTTheory.bound_case_def, LET_THM]) >>
      qpat_assum `n = abi_head_word _` (pure_once_rewrite_tac o single o SYM) >>
      qpat_assum `~(LENGTH xs < p+32)` (rewrite_tac o single) >>
      qpat_assum `~(cap < n)` (rewrite_tac o single) >>
      simp_tac bool_ss [LET_THM] >>
      disch_then (fn th => ACCEPT_TAC (List.last (CONJUNCTS th)))) >>
  disj1_tac >>
  `cap < dimword(:256)` by metis_tac[abi_decoder_coherent_array_capacity] >>
  `cap*stride < dimword(:256)` by
    (qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _`
       (strip_assume_tac o REWRITE_RULE[abi_decoder_coherent_array_iff]) >>
     `stride = abi_member_head_size (vyper_to_abi_type env ty)` by
       (qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [type_to_abi_dec_info_def]) >>
        qpat_assum `abi_decoder_coherent _ _ _ ty _`
          (mp_then Any mp_tac abi_decoder_coherent_header) >>
        simp[abi_decoder_header_def]) >>
     drule_all abi_malformed_array_capacity >>
     simp[vyperASTTheory.bound_case_def]) >>
  `n <= cap ==> n*stride < dimword(:256) /\ L < p+32+n*stride` by
    (strip_tac >> `n*stride <= cap*stride` by simp[LE_MULT_RCANCEL] >> decide_tac) >>
  `p+32 < dimword(:256)` by decide_tac >>
  `!op. op IN {head;cnt;hi} ==> op_prov H op = NONE /\ op_taint z op = {}` by
    simp[DISJ_IMP_THM] >>
  qunabbrev_tac `n` >>
  drule_all malformed_dynarray_compare_span_abort >>
  disch_then (qspec_then `PG`
    (qx_choose_then `u` (qx_choose_then `HG` (qx_choose_then `tz` strip_assume_tac)))) >>
  qexistsl_tac [`u`,`HG`,`tz`] >> simp[] >>
  rpt gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
