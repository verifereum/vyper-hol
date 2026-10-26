(*
 * Entry argument decoding: word arguments (#639)
 *
 * TOP-LEVEL:
 *   calldata_encodes_word_arg — calldata that encodes a call holds, at a
 *     word argument's head offset, typed_val_to_w256 of the argument
 *   word_arg_clamp_ok — that word passes the argument's ABI clamp
 *   compile_decode_word_arg_frag — the is_prim path of compile_decode_args
 *     (CALLDATALOAD, clamp, MSTORE) as a fragment: it stores the loaded word
 *     when the clamp accepts it and reverts otherwise
 *   compile_decode_word_arg_correct — for a well-typed source value at the
 *     argument's offset, the decode reaches its end with the value in
 *     memory at the destination (val_in_memory)
 *
 * Helpers: abi_clamp_ok, abi_head_size, enc_tuple_heads,
 *   enc_tuple_static_head, val_in_memory_word, vyper_to_abi_word_enc,
 *   bind_arguments_word_arg, abi_head_size_word_prefix,
 *   abi_embedded_static_size_word
 *
 * The decoder's head offset (compile_register_positional_args adds
 * abi_embedded_static_size for each argument) agrees with the ABI's
 * (abi_head_size) when the earlier arguments are words
 * (abi_head_size_word_prefix, abi_embedded_static_size_word).  For
 * earlier static or dynamic arguments of other types, the agreement needs
 * the compile env's struct metadata to match the type environment; that
 * belongs to the static/dynamic decoding items.
 *)
Theory entryDecodeProps
Ancestors
  arithmetic list rich_list words integer integer_word
  valueEncodingProofs valueEncodingProps loweringHalt exprSimConvert
  moduleLoweringProps abiEncoderProps entryDispatchProps
  moduleLowering abiEncoder compileEnv compileVyper exprLowering
  valueEncoding selectorDispatch fragExec emitHelper emitHelperProps
  venomExecSemantics venomState venomInst venomMemProps
  vyperABI vyperABIRoundtrip vyperTyping vyperValue vyperValueOperation
  vyperInterpreter exprSimArith contractABI byte vfmTypes vyperCall
Libs
  wordsLib intLib dep_rewrite

(* ===== What the clamp accepts ===== *)

(* The words compile_abi_clamp_basetype lets through, stated with the
   operations its code runs (SHR, SIGNEXTEND, SHL on literal shifts). *)
Definition abi_clamp_ok_def:
  abi_clamp_ok NoClamp (w : bytes32) = T /\
  abi_clamp_ok (IntClamp bits is_signed) w =
    (if is_signed then sign_extend (n2w (bits DIV 8 - 1)) w = w
     else word_lsr w (w2n (n2w bits : bytes32)) = 0w) /\
  abi_clamp_ok (BytesMClamp m) w =
    (word_lsl w (w2n (n2w (m * 8) : bytes32)) = 0w) /\
  abi_clamp_ok BoolClamp w = (word_lsr w 1 = 0w)
End

(* ===== Head offsets in a tuple encoding ===== *)

(* Bytes an element takes in the head of a tuple encoding: an offset word
   for a dynamic element, its encoding for a static one. *)
Definition abi_head_size_def:
  abi_head_size t v = if is_dynamic t then 32n else LENGTH (enc t v)
End

(* The heads of a tuple encoding come first, in order. *)
Theorem enc_tuple_heads:
  !ts vs hl tl rhds rtls.
    LENGTH ts = LENGTH vs ==>
    ?hs rest.
      enc_tuple hl tl ts vs rhds rtls = FLAT (REVERSE rhds) ++ FLAT hs ++ rest /\
      LENGTH hs = LENGTH ts /\
      !j. j < LENGTH ts ==>
          LENGTH (EL j hs) = abi_head_size (EL j ts) (EL j vs) /\
          (~is_dynamic (EL j ts) ==> EL j hs = enc (EL j ts) (EL j vs))
Proof
  Induct
  >- (Cases >> simp[enc_def, REV_REVERSE_LEM, FLAT_APPEND] >>
      rpt gen_tac >> qexistsl [`[]`, `FLAT (REVERSE rtls)`] >> simp[]) >>
  gen_tac >> Cases >> simp[] >> rpt gen_tac >> strip_tac >>
  simp[Once enc_def] >>
  qmatch_goalsub_abbrev_tac `enc_tuple hl tl1 ts t (hd1::rhds) (tl2::rtls)` >>
  first_x_assum (qspecl_then [`t`, `hl`, `tl1`, `hd1::rhds`, `tl2::rtls`]
                   mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`hd1::hs`, `rest`] >> simp[] >>
  Cases >> simp[Abbr `hd1`, abi_head_size_def] >> rw[]
QED

(* A static element's encoding sits at its head offset. *)
Theorem enc_tuple_static_head:
  !ts vs i.
    LENGTH ts = LENGTH vs /\ i < LENGTH ts /\ ~is_dynamic (EL i ts) ==>
    TAKE (LENGTH (enc (EL i ts) (EL i vs)))
      (DROP (SUM (MAP2 abi_head_size (TAKE i ts) (TAKE i vs)))
         (enc (Tuple ts) (ListV vs))) =
    enc (EL i ts) (EL i vs)
Proof
  rpt strip_tac >>
  qspecl_then [`ts`, `vs`, `head_lengths ts 0`, `0`, `[]`, `[]`] mp_tac
    enc_tuple_heads >>
  simp[] >> strip_tac >>
  `FLAT hs = FLAT (TAKE i hs) ++ FLAT (DROP i hs)` by
    metis_tac[TAKE_DROP, FLAT_APPEND] >>
  `FLAT (DROP i hs) = EL i hs ++ FLAT (DROP (i + 1) hs)` by
    (qspecl_then [`hs`, `i`] mp_tac DROP_EL_CONS >> impl_tac >- simp[] >>
     disch_then SUBST1_TAC >> REWRITE_TAC [FLAT]) >>
  `SUM (MAP2 abi_head_size (TAKE i ts) (TAKE i vs)) =
   LENGTH (FLAT (TAKE i hs))` by
    (simp[LENGTH_FLAT] >> AP_TERM_TAC >> irule LIST_EQ >>
     simp[EL_MAP, EL_MAP2, EL_TAKE]) >>
  `EL i hs = enc (EL i ts) (EL i vs)` by simp[] >>
  simp[enc_def] >>
  qpat_x_assum `enc_tuple _ _ _ _ _ _ = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `FLAT hs = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `FLAT (DROP _ _) = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `SUM _ = _` (fn th => REWRITE_TAC [th]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  qpat_x_assum `EL i hs = _` (fn th => REWRITE_TAC [GSYM th]) >>
  REWRITE_TAC [TAKE_LENGTH_APPEND]
QED

(* ===== Word values ===== *)

(* A word-typed value is in memory exactly when its word is. *)
Theorem val_in_memory_word:
  !tenv ty tv v off mem.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v ==>
    (val_in_memory tv v off mem <=>
     mem_word_at off mem = typed_val_to_w256 tv v)
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_word_type_def]) >>
      simp[evaluate_type_def] >> rw[] >> Cases_on `v` >>
      gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def]) >>
  simp[evaluate_type_def, AllCaseEqs()] >> rw[] >> Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def]
QED

(* A word-typed value's ABI encoding is its word. *)
Theorem vyper_to_abi_word_enc:
  !tenv ty tv v av.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    enc (vyper_to_abi_type tenv ty) av = word_to_bytes (typed_val_to_w256 tv v) T
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `mem = word_to_bytes (typed_val_to_w256 tv v) T` >>
  `LENGTH mem = 32` by simp[Abbr `mem`] >>
  `mem_bytes_at 0 32 mem = mem` by
    (simp[mem_bytes_at_def] >> metis_tac[TAKE_LENGTH_APPEND]) >>
  `val_in_memory tv v 0 mem` by
    (drule_all val_in_memory_word >> simp[] >> disch_then kall_tac >>
     simp[mem_word_at_def] >>
     `TAKE 32 (mem ++ REPLICATE 32 0w) = mem` by
       metis_tac[TAKE_LENGTH_APPEND] >>
     simp[Abbr `mem`]) >>
  Cases_on `ty` >> gvs[is_word_type_def]
  >- (rename1 `BaseT bt` >>
      `tv = BaseTV bt` by
        (Cases_on `bt` >> gvs[is_word_type_def, evaluate_type_def] >>
         TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
         gvs[is_word_type_def]) >>
      gvs[] >>
      `mem_bytes_at 0 32 mem = enc (vyper_base_to_abi_type bt) av` by
        (irule val_in_memory_prim_enc >> simp[] >> qexists_tac `v` >> simp[]) >>
      gvs[] >>
      Cases_on `bt` >> gvs[is_word_type_def, vyper_base_to_abi_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
      gvs[is_word_type_def, vyper_base_to_abi_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  drule val_in_memory_flag_enc >> simp[]
QED

(* ===== The calldata word ===== *)

Theorem vyper_to_abi_types_EL[local]:
  !tys i. i < LENGTH tys ==>
    LENGTH (vyper_to_abi_types tenv tys) = LENGTH tys /\
    EL i (vyper_to_abi_types tenv tys) = vyper_to_abi_type tenv (EL i tys)
Proof
  Induct >> simp[vyper_to_abi_type_def] >> Cases_on `i` >>
  simp[vyper_to_abi_type_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> Cases_on `tys` >> gvs[]
QED

(* Calldata that encodes a call holds a word argument's word at the
   argument's head offset, after the 4-byte selector. *)
Theorem calldata_encodes_word_arg:
  !tenv fname tys vals cd i tv.
    calldata_encodes tenv fname tys vals cd /\ LENGTH vals = LENGTH tys /\
    i < LENGTH tys /\ is_word_type (EL i tys) /\
    evaluate_type tenv (EL i tys) = SOME tv /\
    value_has_type tv (EL i vals) ==>
    ?avs. vyper_to_abi_list tenv tys vals = SOME avs /\
          mem_word_at
            (4 + SUM (MAP2 abi_head_size
                        (TAKE i (vyper_to_abi_types tenv tys)) (TAKE i avs)))
            cd =
          typed_val_to_w256 tv (EL i vals)
Proof
  rpt strip_tac >> gvs[calldata_encodes_def] >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  `vyper_to_abi tenv (EL i tys) (EL i vals) = SOME (EL i abi_vals)` by
    (first_x_assum irule >> decide_tac) >>
  drule_all vyper_to_abi_word_enc >> strip_tac >>
  qabbrev_tac `ats = vyper_to_abi_types tenv tys` >>
  `LENGTH ats = LENGTH tys /\ EL i ats = vyper_to_abi_type tenv (EL i tys)` by
    metis_tac[vyper_to_abi_types_EL] >>
  qabbrev_tac `e = enc (Tuple ats) (ListV abi_vals)` >>
  qabbrev_tac `k = SUM (MAP2 abi_head_size (TAKE i ats) (TAKE i abi_vals))` >>
  `TAKE 32 (DROP k e) = word_to_bytes (typed_val_to_w256 tv (EL i vals)) T` by
    (qspecl_then [`ats`, `abi_vals`, `i`] mp_tac enc_tuple_static_head >>
     impl_tac >- gvs[] >>
     asm_rewrite_tac[] >> simp[]) >>
  `32 <= LENGTH (DROP k e)` by
    (`LENGTH (TAKE 32 (DROP k e)) = 32` by simp[] >>
     pop_assum mp_tac >> rw[LENGTH_TAKE_EQ]) >>
  fs[Abbr`e`] >>
  simp[mem_word_at_def, DROP_APPEND2, function_selector_length,
       TAKE_APPEND1]
QED

(* bind_arguments succeeding types each argument. *)
Theorem bind_arguments_word_arg:
  !tenv args vals env i.
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args ==>
    LENGTH vals = LENGTH args /\
    ?tv. evaluate_type tenv (SND (EL i args)) = SOME tv /\
         value_has_type tv (EL i vals)
Proof
  rpt gen_tac >> strip_tac >>
  drule bind_arguments_length >> strip_tac >> simp[] >>
  qpat_x_assum `bind_arguments _ _ _ = _` mp_tac >>
  qpat_x_assum `i < _` mp_tac >>
  qpat_x_assum `LENGTH _ = LENGTH _` mp_tac >>
  map_every qid_spec_tac [`env`, `i`, `vals`, `args`] >>
  Induct >- simp[] >>
  Cases >> Cases >> simp[bind_arguments_def, AllCaseEqs()] >>
  rpt gen_tac >> rpt strip_tac >> gvs[] >>
  Cases_on `i` >> gvs[]
  >- (drule safe_cast_result_well_typed >> drule (CONJUNCT1 safe_cast_some_eq) >>
      simp[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* With only word arguments before i, the head offset is 32 bytes per
   argument, as the decoder steps through them. *)
Theorem abi_head_size_word_prefix:
  !tenv tys vals avs i.
    vyper_to_abi_list tenv tys vals = SOME avs /\ i <= LENGTH tys /\
    (!j. j < i ==> is_word_type (EL j tys) /\
                   ?tv. evaluate_type tenv (EL j tys) = SOME tv /\
                        value_has_type tv (EL j vals)) ==>
    SUM (MAP2 abi_head_size (TAKE i (vyper_to_abi_types tenv tys))
                            (TAKE i avs)) = 32 * i
Proof
  rpt strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  `MAP2 abi_head_size (TAKE i (vyper_to_abi_types tenv tys)) (TAKE i avs) =
   REPLICATE i 32` by
    (irule LIST_EQ >>
     simp[valueEncodingProofsTheory.vyper_to_abi_types_length, EL_MAP2, EL_TAKE, EL_REPLICATE] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >>
     `EL x (vyper_to_abi_types tenv tys) = vyper_to_abi_type tenv (EL x tys)`
       by (`x < LENGTH tys` by decide_tac >>
           metis_tac[vyper_to_abi_types_EL]) >>
     `vyper_to_abi tenv (EL x tys) (EL x vals) = SOME (EL x avs)` by
       (first_x_assum irule >> decide_tac) >>
     drule_all vyper_to_abi_word_enc >> simp[abi_head_size_def]) >>
  simp[SUM_REPLICATE]
QED

Theorem abi_embedded_static_size_word:
  !sfields ty. is_word_type ty ==> abi_embedded_static_size sfields ty = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def] >>
       TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_word_type_def])) >>
  simp[abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def]
QED

(* ===== The clamp accepts the word ===== *)

val dimindex_256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

Theorem lsr_zero_of_lt[local]:
  !(w : 'a word) n. w2n w < 2 ** n ==> w >>> n = 0w
Proof
  rpt strip_tac >>
  `w2n (w >>> n) = 0` by
    (REWRITE_TAC[w2n_lsr] >> irule LESS_DIV_EQ_ZERO >>
     first_assum ACCEPT_TAC) >>
  fs[w2n_eq_0]
QED

Theorem n2w_lsr_clamp_ok[local]:
  !m k. m <= 256 /\ k < 2 ** m ==>
        (n2w k : bytes32) >>> w2n (n2w m : bytes32) = 0w
Proof
  rpt strip_tac >>
  `w2n (n2w m : bytes32) = m` by simp[w2n_n2w, dimword_def] >>
  `2 ** m <= 2 ** 256` by (irule EXP_BASE_LEQ_MONO_IMP >> simp[]) >>
  `k < dimword (:256)` by
    (REWRITE_TAC[dimword_def, dimindex_256] >> decide_tac) >>
  irule lsr_zero_of_lt >> simp[w2n_n2w]
QED

Theorem signed_int_mod_within[local]:
  !m i. 0 < m /\ within_int_bound (Signed m) i ==> signed_int_mod m i = i
Proof
  rpt strip_tac >>
  `-&(2 ** (m - 1)) <= i /\ i < &(2 ** (m - 1))` by
    metis_tac[within_int_bound_ineq] >>
  `2 ** m = 2 * 2 ** (m - 1)` by
    (`m = SUC (m - 1)` by simp[] >> pop_assum SUBST1_TAC >> simp[EXP]) >>
  `&(2 ** m) = 2 * &(2 ** (m - 1)) : int` by
    asm_rewrite_tac[GSYM integerTheory.INT_MUL] >>
  `0 < &(2 ** (m - 1)) : int` by simp[] >>
  qabbrev_tac `H = &(2 ** (m - 1)) : int` >>
  simp[signed_int_mod_def, LET_THM] >>
  Cases_on `0 <= i`
  >- (`i % (2 * H) = i` by (irule integerTheory.INT_LESS_MOD >> intLib.ARITH_TAC) >>
      rw[] >> intLib.ARITH_TAC) >>
  `i % (2 * H) = i + 2 * H` by
    (irule integerTheory.INT_MOD_UNIQUE >> qexists_tac `-1` >>
     rw[] >> intLib.ARITH_TAC) >>
  rw[] >> intLib.ARITH_TAC
QED

Theorem int_clamp_signed_ok[local]:
  !m i. 8 <= m /\ m < 256 /\ m MOD 8 = 0 /\ within_int_bound (Signed m) i ==>
        sign_extend (n2w (m DIV 8 - 1)) (i2w i : bytes32) = i2w i
Proof
  rpt strip_tac >>
  `m = m DIV 8 * 8` by
    (`0 < 8n` by simp[] >> drule DIVISION >>
     disch_then (qspec_then `m` mp_tac) >> simp[]) >>
  qabbrev_tac `d = m DIV 8` >>
  `d - 1 <= 30 /\ 8 * (d - 1 + 1) = m` by decide_tac >>
  qpat_x_assum `m = _` kall_tac >>
  `signed_int_mod m i = i` by (irule signed_int_mod_within >> simp[]) >>
  qspecl_then [`d - 1`, `i`] mp_tac i2w_signed_int_mod_sign_extend >>
  impl_tac >- decide_tac >>
  disch_then (SUBST1_TAC o SYM) >> asm_rewrite_tac[]
QED

Theorem address_clamp_ok[local]:
  !bs. LENGTH bs = 20 ==>
       (word_of_bytes_be (PAD_LEFT 0w 32 bs) : bytes32) >>>
         w2n (n2w 160 : bytes32) = 0w
Proof
  rpt strip_tac >>
  `(word_of_bytes_be (PAD_LEFT 0w 32 bs) : bytes32) =
     w2w (word_of_bytes_be bs : 160 word)` by
    (qspec_then `bs` mp_tac
       (w2w_word_of_bytes_be_pad_left
          |> INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]) >>
     simp[dividesTheory.compute_divides]) >>
  pop_assum SUBST1_TAC >>
  irule lsr_zero_of_lt >>
  assume_tac (INST_TYPE [alpha |-> ``:160``] w2n_lt) >>
  fs[w2n_w2w, w2n_n2w, dimword_def]
QED

Theorem bytesM_clamp_ok[local]:
  !bs. LENGTH bs < 32 ==>
       word_lsl (word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32)
                (w2n (n2w (LENGTH bs * 8) : bytes32)) = 0w
Proof
  rpt strip_tac >>
  `w2n (n2w (LENGTH bs * 8) : bytes32) = LENGTH bs * 8` by
    simp[w2n_n2w, dimword_def] >>
  `(word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32) =
     n2w (256 ** (32 - LENGTH bs) * num_of_bytes (REVERSE bs))` by
    (simp[cv_stdTheory.word_of_bytes_be_eq_num_of_bytes,
          dividesTheory.compute_divides, be_bytes_thm, PAD_RIGHT,
          GSYM REPLICATE_GENLIST, TAKE_APPEND1, TAKE_LENGTH_TOO_LONG,
          REVERSE_APPEND,
          num_of_bytes_APPEND]) >>
  `256 ** (32 - LENGTH bs) * 2 ** (LENGTH bs * 8) = dimword (:256)` by
    (`256 ** (32 - LENGTH bs) = 2 ** (8 * (32 - LENGTH bs))` by
       simp[EXP_EXP_MULT] >>
     `8 * (32 - LENGTH bs) + LENGTH bs * 8 = 256` by decide_tac >>
     asm_rewrite_tac[GSYM EXP_ADD, dimword_def, dimindex_256]) >>
  `256 ** (32 - LENGTH bs) * num_of_bytes (REVERSE bs) *
     2 ** (LENGTH bs * 8) =
   num_of_bytes (REVERSE bs) * dimword (:256)` by
    (qpat_x_assum `_ = dimword _` (SUBST1_TAC o SYM) >>
     CONV_TAC (AC_CONV (MULT_ASSOC, MULT_COMM))) >>
  `~(dimindex (:256) - 1 < LENGTH bs * 8)` by simp[] >>
  asm_rewrite_tac[word_lsl_n2w] >>
  ONCE_REWRITE_TAC[GSYM n2w_mod] >>
  simp[MOD_EQ_0]
QED

(* A well-typed word argument passes the clamp the compiler picks for its
   type.  Two hypotheses tie the compiler's view to the source:
   - signed integer widths are multiples of 8: Vyper has only int8 ...
     int256, and the clamp sign-extends from byte bits DIV 8 - 1;
     evaluate_type does not rule other widths out yet;
   - a flag's member count in the compile env is the source's (the same
     clause exprSimHyps uses). *)
Theorem word_arg_clamp_ok:
  !tenv sfields cenv ty tv v.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\
    (!m. ty = BaseT (IntT m) ==> m MOD 8 = 0) /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_clamp_ok
      (case type_to_abi_dec_info sfields cenv ty of
         DecPrimWord c => c
       | _ => NoClamp)
      (typed_val_to_w256 tv v)
Proof
  rpt strip_tac >> Cases_on `ty` >> gvs[is_word_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def]) >>
  gvs[evaluate_type_def, type_to_abi_dec_info_def, type_to_abi_clamp_def,
      AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  rw[abi_clamp_ok_def]
  >~ [`PAD_LEFT`] >- (qspec_then `l` mp_tac address_clamp_ok >> simp[])
  >~ [`PAD_RIGHT`] >- (qspec_then `l` mp_tac bytesM_clamp_ok >> simp[])
  >~ [`Signed 168`]
  >- (qspecl_then [`168`, `i`] mp_tac int_clamp_signed_ok >> simp[])
  >~ [`sign_extend`]
  >- (`8 <= n` by
        (spose_not_then assume_tac >> `n < 8` by decide_tac >>
         gvs[LESS_MOD]) >>
      qspecl_then [`n`, `i`] mp_tac int_clamp_signed_ok >> simp[])
  >~ [`Num i`]
  >- (`(i2w i : bytes32) = n2w (Num i)` by
        (`~(i < 0)` by intLib.ARITH_TAC >>
         simp[integer_wordTheory.i2w_def]) >>
      qspecl_then [`n`, `Num i`] mp_tac n2w_lsr_clamp_ok >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`m`, `n`] mp_tac n2w_lsr_clamp_ok >> simp[]
QED

(* ===== The decode code ===== *)

(* The is_prim path of compile_decode_args for one calldata argument:
   CALLDATALOAD at off, the clamp, MSTORE to the destination.  It either
   finishes with the loaded word stored at the destination, having passed
   the clamp, or reverts because the clamp rejects it. *)
Theorem compile_decode_word_arg_phases[local]:
  !cenv name is_dyn abi_size dec off hi st st' loc dst.
  compile_decode_args cenv [(name, T, is_dyn, abi_size, dec)] off
    CALLDATALOAD hi 4 st = ((), st') /\
  FLOOKUP cenv.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst ==>
  ?src val_op st1 st2 st3.
    emit_op ADD [Lit 4w; Lit (n2w (off - 4))] st = (src, st1) /\
    emit_op CALLDATALOAD [src] st1 = (val_op, st2) /\
    compile_abi_clamp_basetype val_op
      (case dec of DecPrimWord c => c | _ => NoClamp) st2 = ((), st3) /\
    emit_void MSTORE [dst; val_op] st3 = ((), st')
Proof
  simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[]
QED

Theorem compile_abi_clamp_structure[local]:
  !cl op st st'.
  compile_abi_clamp_basetype op cl st = ((), st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  Cases >> rpt gen_tac >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def] >>
  TRY (rename1 `if signed then _ else _` >> Cases_on `signed`) >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def,
       inst_extends_def, exprLoweringPropsTheory.emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def]
QED

Theorem compile_decode_word_arg_structure[local]:
  !cenv name is_dyn abi_size dec off hi st st' loc dst.
  compile_decode_args cenv [(name, T, is_dyn, abi_size, dec)] off
    CALLDATALOAD hi 4 st = ((), st') /\
  FLOOKUP cenv.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  st.cs_next_var <= st'.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  rpt strip_tac >> drule_all compile_decode_word_arg_phases >> strip_tac >>
  drule compile_abi_clamp_structure >> strip_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_abi_clamp_basetype _ _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `EVERY _ code` >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def,
      inst_extends_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[exprLoweringPropsTheory.emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def,
       IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[is_terminator_def]
QED

Theorem decode_emit_update_frame[local]:
  !opc ops st v st' s w.
  emit_op opc ops st = (v, st') /\ fresh_vars_wrt st s /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      eval_operand v t = SOME w /\ fresh_vars_wrt st' t /\
      vars_pc_only s t /\
      (!op a. eval_operand op s = SOME a ==> eval_operand op t = SOME a) /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[] >> simp[exprLoweringPropsTheory.run_inst_seq_def, eval_operand_update_var] >>
  rpt conj_tac
  >- (irule fresh_vars_wrt_advance >> goal_assum (drule_at Any) >> simp[])
  >- simp[vars_pc_only_update_var, vars_pc_only_refl]
  >- (rpt strip_tac >> irule eval_operand_update_fresh >>
      simp[] >> qexists_tac `st` >> simp[]) >>
  rpt strip_tac >> irule lookup_var_update_not_fresh >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem decode_calldataload_frame[local]:
  !op a st v st' s.
  emit_op CALLDATALOAD [op] st = (v, st') /\
  eval_operand op s = SOME a /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      eval_operand v t = SOME (mem_word_at (w2n a) s.vs_call_ctx.cc_calldata) /\
      fresh_vars_wrt st' t /\ vars_pc_only s t /\
      (!op b. eval_operand op s = SOME b ==> eval_operand op t = SOME b) /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >> irule decode_emit_update_frame >>
  simp[] >> qexistsl [`CALLDATALOAD`, `[op]`] >>
  simp[mem_word_at_def] >> drule step_CALLDATALOAD >> simp[]
QED

Theorem decode_mstore_frame[local]:
  !s t a w. vars_pc_only s t ==>
    vars_pc_only (mstore a w s) (mstore a w t)
Proof
  rw[vars_pc_only_def, venom_state_component_equality, mstore_def] >> gvs[]
QED

Theorem decode_emit_mstore_frame[local]:
  !op1 op2 p w st st' s.
  emit_void MSTORE [op1; op2] st = ((), st') /\
  eval_operand op1 s = SOME p /\ eval_operand op2 s = SOME w /\
  fresh_vars_wrt st s ==>
  run_inst_seq (emitted_insts st st') s = OK (mstore (w2n p) w s) /\
  fresh_vars_wrt st' (mstore (w2n p) w s) /\
  (!x. lookup_var x (mstore (w2n p) w s) = lookup_var x s)
Proof
  rpt strip_tac >> drule_all emit_void_MSTORE_correct >> strip_tac >>
  gvs[lookup_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem decode_frame_compose[local]:
  !st st1 s t u.
  st.cs_next_var <= st1.cs_next_var /\
  vars_pc_only s t /\ vars_pc_only t u /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  (!x. not_fresh_at st1 x ==> lookup_var x u = lookup_var x t) ==>
  vars_pc_only s u /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[vars_pc_only_trans] >>
  `!x. not_fresh_at st x ==> not_fresh_at st1 x` by
    (rw[not_fresh_at_def] >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Theorem decode_two_tests_assert[local]:
  !opc ops test tops st a st1 b st2 st' s w z.
  emit_op opc ops st = (a, st1) /\
  emit_op test tops st1 = (b, st2) /\
  emit_void ASSERT [b] st2 = ((), st') /\ fresh_vars_wrt st s /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  step_inst_base (mk_inst st1.cs_next_id test tops
    [STRING #"%" (toString st1.cs_next_var)])
    (update_var (STRING #"%" (toString st.cs_next_var)) w s) =
    OK (update_var (STRING #"%" (toString st1.cs_next_var)) z
      (update_var (STRING #"%" (toString st.cs_next_var)) w s)) ==>
  if z <> 0w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all decode_emit_update_frame >> strip_tac >>
  `t = update_var (STRING #"%" (toString st.cs_next_var)) w s` by
    (rev_drule emitted_insts_emit_op >> strip_tac >>
     gvs[exprLoweringPropsTheory.run_inst_seq_def]) >>
  rev_drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `emit_op opc ops st = _` kall_tac >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all decode_emit_update_frame >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `run_inst_seq (emitted_insts st st2) s = OK t` by
    (irule run_emitted_compose2 >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `inst_extends st st2` by
    (rewrite_tac[inst_extends_def] >> irule emit_extends_trans >>
     qexists_tac `st1` >> simp[]) >>
  `inst_extends st2 st'` by simp[inst_extends_def] >>
  drule_all run_inst_seq_emit_extend >> disch_then SUBST1_TAC >>
  `vars_pc_only s t /\
   (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)` by
    (irule decode_frame_compose >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `z = 0w` >> gvs[]
  >- (drule_all emit_void_ASSERT_revert_full >> metis_tac[]) >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

Theorem decode_zero_test_assert[local]:
  !opc ops st a st1 b st2 st' s w.
  emit_op opc ops st = (a, st1) /\
  emit_op ISZERO [a] st1 = (b, st2) /\
  emit_void ASSERT [b] st2 = ((), st') /\ fresh_vars_wrt st s /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  if w = 0w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst st1.cs_next_id ISZERO [a]
    [STRING #"%" (toString st1.cs_next_var)])
      (update_var (STRING #"%" (toString st.cs_next_var)) w s) =
    OK (update_var (STRING #"%" (toString st1.cs_next_var))
      (if w = 0w then 1w else 0w)
      (update_var (STRING #"%" (toString st.cs_next_var)) w s))` by
    (rev_drule emitted_insts_emit_op >> strip_tac >>
     simp[step_inst_base_def, exec_pure1_def, eval_operand_update_var,
          venomExecSemanticsTheory.bool_to_word_def, mk_inst_def] >>
     Cases_on `w = 0w` >> simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  drule_all decode_two_tests_assert >>
  Cases_on `w = 0w` >> simp[]
QED

Theorem decode_unsigned_clamp[local]:
  !op bits st st' s w.
  compile_abi_int_clamp op bits F st = ((), st') /\
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  if word_lsr w (w2n (n2w bits : bytes32)) = 0w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[compile_abi_int_clamp_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `step_inst_base (mk_inst st.cs_next_id SHR [Lit (n2w bits); op]
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (word_lsr w (w2n (n2w bits : bytes32))) s)` by
    (irule step_SHR >> simp[eval_operand_def]) >>
  drule_all decode_zero_test_assert >> simp[]
QED

Theorem decode_bytes_clamp[local]:
  !op m st st' s w.
  compile_abi_bytes_clamp op m st = ((), st') /\
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  if word_lsl w (w2n (n2w (m * 8) : bytes32)) = 0w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `step_inst_base (mk_inst st.cs_next_id SHL [Lit (n2w (m * 8)); op]
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (word_lsl w (w2n (n2w (m * 8) : bytes32))) s)` by
    (irule step_SHL >> simp[eval_operand_def]) >>
  gvs[] >> drule_all decode_zero_test_assert >> simp[]
QED

Theorem decode_signed_clamp[local]:
  !op bits st st' s w.
  compile_abi_int_clamp op bits T st = ((), st') /\
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  if sign_extend (n2w (bits DIV 8 - 1)) w = w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[compile_abi_int_clamp_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt strip_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op SIGNEXTEND _ st = (canonical, st1)` >>
  qmatch_goalsub_abbrev_tac `if extended = w then _ else _` >>
  `step_inst_base (mk_inst st.cs_next_id SIGNEXTEND
    [Lit (n2w (bits DIV 8 - 1)); op]
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) extended s)` by
    (simp[Abbr `extended`] >> irule step_SIGNEXTEND >> simp[eval_operand_def]) >>
  `eval_operand op (update_var (STRING #"%" (toString st.cs_next_var)) extended s) = SOME w` by
    (irule eval_operand_update_fresh >> simp[] >> qexists_tac `st` >> simp[]) >>
  `step_inst_base (mk_inst st1.cs_next_id EQ [op; canonical]
    [STRING #"%" (toString st1.cs_next_var)])
      (update_var (STRING #"%" (toString st.cs_next_var)) extended s) =
    OK (update_var (STRING #"%" (toString st1.cs_next_var))
      (if extended = w then 1w else 0w)
      (update_var (STRING #"%" (toString st.cs_next_var)) extended s))` by
    (rev_drule emitted_insts_emit_op >> strip_tac >>
     simp[step_inst_base_def, exec_pure2_def, eval_operand_update_var, mk_inst_def] >>
     Cases_on `extended = w` >> gvs[venomExecSemanticsTheory.bool_to_word_def]) >>
  drule_all decode_two_tests_assert >> Cases_on `extended = w` >> simp[]
QED

Theorem decode_clamp_frame[local]:
  !cl op st st' s w.
  compile_abi_clamp_basetype op cl st = ((), st') /\
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  if abi_clamp_ok cl w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  Cases >> simp[compile_abi_clamp_basetype_def, abi_clamp_ok_def]
  >- (rw[comp_return_def] >> qexists_tac `s` >>
      simp[exprLoweringPropsTheory.emitted_insts_def,
           exprLoweringPropsTheory.run_inst_seq_def,
           rich_listTheory.DROP_LENGTH_NIL, vars_pc_only_refl])
  >- (rpt gen_tac >> rename1 `compile_abi_int_clamp op bits signed st = _` >>
      Cases_on `signed` >> rpt strip_tac
      >- (drule_all decode_signed_clamp >> simp[]) >>
      drule_all decode_unsigned_clamp >> simp[])
  >- (rpt strip_tac >> drule_all decode_bytes_clamp >> simp[]) >>
  rpt strip_tac >>
  `compile_abi_int_clamp op 1 F st = ((), st')` by
    simp[compile_abi_int_clamp_def] >>
  drule_all decode_unsigned_clamp >> simp[]
QED

Theorem decode_load_frame[local]:
  !off st src st1 val_op st2 s.
  emit_op ADD [Lit 4w; Lit (n2w (off - 4))] st = (src, st1) /\
  emit_op CALLDATALOAD [src] st1 = (val_op, st2) /\
  4 <= off /\ off < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st2) s = OK t /\
      eval_operand val_op t = SOME (mem_word_at off s.vs_call_ctx.cc_calldata) /\
      vars_pc_only s t /\ fresh_vars_wrt st2 t /\
      (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id ADD [Lit 4w; Lit (n2w (off - 4))]
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) (n2w off) s)` by
    (`(n2w off : bytes32) = 4w + n2w (off - 4)` by
       (rewrite_tac[word_add_n2w] >> AP_TERM_TAC >> decide_tac) >>
     pop_assum SUBST1_TAC >> irule step_ADD >> simp[eval_operand_def]) >>
  drule_all decode_emit_update_frame >> strip_tac >>
  drule_all decode_calldataload_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) t = OK u` >>
  `vars_pc_only s u /\
   (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s)` by
    (irule decode_frame_compose >> goal_assum (drule_at Any) >>
     rev_drule emitted_insts_emit_op >> simp[]) >>
  `st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1` by
    metis_tac[inst_extends_emit_op, inst_extends_def] >>
  `st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2` by
    metis_tac[inst_extends_emit_op, inst_extends_def] >>
  `run_inst_seq (emitted_insts st st2) s = OK u` by
    (irule run_emitted_compose2 >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
  qexists_tac `u` >> simp[w2n_n2w] >> metis_tac[]
QED

Theorem decode_word_arg_run[local]:
  !cenv name is_dyn abi_size dec off hi st st' loc dst s0 p.
    compile_decode_args cenv [(name, T, is_dyn, abi_size, dec)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    4 <= off /\ off < dimword (:256) /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 ==>
    (?t. run_inst_seq (emitted_insts st st') s0 = OK t /\
         vars_pc_only
           (mstore (w2n p) (mem_word_at off s0.vs_call_ctx.cc_calldata) s0) t /\
         fresh_vars_wrt st' t /\
         (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
         abi_clamp_ok (case dec of DecPrimWord c => c | _ => NoClamp)
           (mem_word_at off s0.vs_call_ctx.cc_calldata)) \/
    (?t. run_inst_seq (emitted_insts st st') s0 = Abort Revert_abort t /\
         ~abi_clamp_ok (case dec of DecPrimWord c => c | _ => NoClamp)
           (mem_word_at off s0.vs_call_ctx.cc_calldata))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_decode_word_arg_phases >> strip_tac >>
  drule_all decode_load_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st2) s0 = OK s2` >>
  drule_all decode_clamp_frame >>
  qmatch_goalsub_abbrev_tac `abi_clamp_ok cl w` >>
  Cases_on `abi_clamp_ok cl w` >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st2 st3) s2 = _` >>
  `inst_extends st st2` by
    metis_tac[inst_extends_emit_op, inst_extends_trans] >>
  drule compile_abi_clamp_structure >> strip_tac >>
  `emitted_insts st st' = emitted_insts st st2 ++
     (emitted_insts st2 st3 ++ emitted_insts st3 st')` by
    (drule inst_extends_emit_void >> strip_tac >>
     fs[inst_extends_def] >>
     `emitted_insts st2 st' = emitted_insts st2 st3 ++ emitted_insts st3 st'` by
       (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
     `st'.cs_current_insts = st2.cs_current_insts ++ emitted_insts st2 st'` by
       (irule emit_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
     `emitted_insts st st' = emitted_insts st st2 ++ emitted_insts st2 st'` by
       (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
     asm_rewrite_tac[] >> rewrite_tac[APPEND_ASSOC]) >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_assum `run_inst_seq (emitted_insts st st2) s0 = OK s2`
    (fn th => rewrite_tac[MATCH_MP exprLoweringPropsTheory.run_inst_seq_append th])
  >- (rename1 `run_inst_seq (emitted_insts st2 st3) s2 = OK s3` >>
      `eval_operand dst s3 = SOME p /\ eval_operand val_op s3 = SOME w` by
        metis_tac[] >>
      drule_all decode_emit_mstore_frame >> strip_tac >>
      qpat_assum `run_inst_seq (emitted_insts st2 st3) s2 = OK s3`
        (fn th => rewrite_tac[MATCH_MP exprLoweringPropsTheory.run_inst_seq_append th]) >>
      `vars_pc_only s0 s3 /\
       (!x. not_fresh_at st x ==> lookup_var x s3 = lookup_var x s0)` by
        (irule decode_frame_compose >> goal_assum (drule_at Any) >>
         rev_drule emitted_insts_emit_op >> strip_tac >>
         drule emitted_insts_emit_op >> strip_tac >> simp[]) >>
      simp[] >> irule decode_mstore_frame >> simp[]) >>
  `!t. run_inst_seq (emitted_insts st2 st3) s2 <> OK t` by simp[] >>
  drule exprLoweringPropsTheory.run_inst_seq_append_err >>
  disch_then (qspec_then `emitted_insts st3 st'` mp_tac) >> simp[]
QED

Theorem compile_decode_word_arg_frag:
  !cenv name is_dyn abi_size dec off hi st st' ctx loc dst s0 p.
    compile_decode_args cenv [(name, T, is_dyn, abi_size, dec)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    4 <= off /\ off < dimword (:256) /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only
             (mstore (w2n p) (mem_word_at off s0.vs_call_ctx.cc_calldata) s0) t /\
           fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
           abi_clamp_ok (case dec of DecPrimWord c => c | _ => NoClamp)
             (mem_word_at off s0.vs_call_ctx.cc_calldata))
      (\r. ?t. r = Abort Revert_abort t /\
               ~abi_clamp_ok (case dec of DecPrimWord c => c | _ => NoClamp)
                  (mem_word_at off s0.vs_call_ctx.cc_calldata))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_decode_word_arg_structure >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all decode_word_arg_run >> simp[] >> strip_tac
  >- (disj1_tac >> qexists_tac `t` >>
      gvs[vars_pc_only_inst_idx, fresh_vars_wrt_def, lookup_var_def]) >>
  disj2_tac >> qexists_tac `t` >> simp[]
QED

(* A word argument whose source value sits at its offset in the calldata
   decodes without reverting, leaving the value in memory at the
   destination.  calldata_encodes_word_arg gives the calldata premise for
   calldata that encodes the call. *)
Theorem compile_decode_word_arg_correct:
  !cenv cenv0 sfields name is_dyn abi_size off hi st st' ctx loc dst s0 p
   tenv ty tv v.
    compile_decode_args cenv
      [(name, T, is_dyn, abi_size, type_to_abi_dec_info sfields cenv0 ty)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    4 <= off /\ off < dimword (:256) /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\
    (!m. ty = BaseT (IntT m) ==> m MOD 8 = 0) /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv0.ce_flag_n_members (nsid_to_string nsid) = m) /\
    mem_word_at off s0.vs_call_ctx.cc_calldata = typed_val_to_w256 tv v ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only (mstore (w2n p) (typed_val_to_w256 tv v) s0) t /\
           fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
           val_in_memory tv v (w2n p) t.vs_memory)
      (\r. F)
Proof
  rpt strip_tac >>
  drule_all word_arg_clamp_ok >>
  disch_then (qspec_then `sfields` assume_tac) >>
  drule_all compile_decode_word_arg_frag >>
  disch_then (qspec_then `ctx` mp_tac) >>
  qpat_x_assum `mem_word_at off _ = _` (fn th => REWRITE_TAC [th]) >>
  strip_tac >> drule frag_exec_weaken >> disch_then irule >>
  rw[] >> gvs[] >>
  rename1 `vars_pc_only _ tt` >>
  `tt.vs_memory = (mstore (w2n p) (typed_val_to_w256 tv v) s0).vs_memory` by
    (qpat_x_assum `vars_pc_only _ tt`
       (mp_tac o Q.AP_TERM `venom_state_vs_memory` o
        REWRITE_RULE [vars_pc_only_def]) >>
     simp[]) >>
  drule_all val_in_memory_word >>
  disch_then (qspecl_then [`w2n p`, `tt.vs_memory`] SUBST1_TAC) >>
  qpat_x_assum `tt.vs_memory = _` SUBST1_TAC >>
  rewrite_tac[mem_word_at_eq_mload, mload_mstore_same]
QED
