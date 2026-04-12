(* Typing properties of evaluate_builtin.
 *
 * Proves: evaluate_builtin_well_typed
 *   If evaluate_builtin succeeds and the builtin is well-typed,
 *   then the result value has the declared type.
 *
 * Also proves supporting lemmas:
 *   - LENGTH_Keccak_256_w64: Keccak output has 32 bytes
 *   - num_sqrt_le: num_sqrt n <= n
 *   - modexp_bound: modexp result < modulus (when modulus > 0)
 *)

Theory vyperBuiltinTyping
Ancestors
  vyperTypeSoundnessHelpers keccak

Libs
  wordsLib

open listTheory rich_listTheory
open integerTheory intLib
open keccakTheory
open vyperTypeSoundnessHelpersTheory vyperTypingTheory
open vyperASTTheory vyperContextTheory vyperValueTheory vyperValueOperationTheory vyperMiscTheory
open vyperArithTheory byteTheory arithmeticTheory
open vfmExecutionTheory sortingTheory BasicProvers

(* Remove SIZES_CONV from simpset to prevent dimword(:256) expansion.
   Keep INDEX_CONV for dimindex evaluation (needed by LENGTH_word_to_bytes). *)
val _ = diminish_srw_ss ["sizes"]
val _ = augment_srw_ss [simpLib.std_conv_ss
  {name = "INDEX_CONV", conv = fcpLib.INDEX_CONV,
   pats = [``fcp$dimindex(:'a)``]}]

(* Tactic: fully decompose LIST_REL R vs tys when LENGTH tys is known.
   Repeatedly finds the LIST_REL assumption, cases on its second list arg,
   and simplifies with LIST_REL_CONS1 until the relation is []=[]. *)
fun decompose_list_rel_tac (asms, gl) =
  let
    fun find_list_rel [] = NONE
      | find_list_rel (a::rest) =
          (case strip_comb a of
             (r, [_, vs, tys]) =>
               if same_const r ``LIST_REL``
                  andalso is_var tys andalso not (listSyntax.is_nil tys)
               then SOME tys
               else find_list_rel rest
           | _ => find_list_rel rest)
  in
    case find_list_rel asms of
      SOME tys =>
        (Cases_on [ANTIQUOTE tys] >> gvs[LIST_REL_CONS1] >>
         TRY decompose_list_rel_tac) (asms, gl)
    | NONE => ALL_TAC (asms, gl)
  end;

(* ===== Keccak LENGTH lemma ===== *)

(* Keccak_p_24_w64 preserves length 25 *)
Theorem LENGTH_Keccak_p_24_w64[local]:
  !ws. LENGTH ws = 25 ==> LENGTH (Keccak_p_24_w64 ws) = 25
Proof
  rewrite_tac[Keccak_p_24_w64_def] >>
  qspec_tac (`iota_w64_RCz`, `rcs`) >>
  Induct >> simp[FOLDL] >> rpt strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[LENGTH_Rnd_w64]
QED

(* FOLDL with Keccak_p_24_w64 preserves length 25 *)
Theorem LENGTH_FOLDL_Keccak[local]:
  !Pis s. LENGTH s = 25 /\ EVERY (\p. LENGTH p >= 25) Pis ==>
          LENGTH (FOLDL (\Si Pi. Keccak_p_24_w64 (MAP2 $?? Si Pi)) s Pis) = 25
Proof
  Induct >> simp[FOLDL] >> rpt strip_tac >>
  first_x_assum match_mp_tac >> simp[] >>
  irule LENGTH_Keccak_p_24_w64 >> simp[LENGTH_MAP2, MIN_DEF]
QED

(* absorb_w64 returns length 25 when all chunks have length >= 25 *)
Theorem LENGTH_absorb_w64[local]:
  !Pis. EVERY (\p. LENGTH p >= 25) Pis ==>
        LENGTH (absorb_w64 Pis) = 25
Proof
  rpt strip_tac >>
  simp[absorb_w64_def] >>
  irule LENGTH_FOLDL_Keccak >>
  simp[LENGTH_REPLICATE]
QED

(* state_bools_w64 implies word list has length 25 *)
Theorem state_bools_w64_LENGTH[local]:
  state_bools_w64 bls ws ==> LENGTH ws = 25
Proof
  simp[state_bools_w64_def] >> strip_tac >> gvs[] >>
  `divides 64 1600` by (simp[dividesTheory.divides_def] >> qexists_tac `25` >> simp[]) >>
  `~NULL (MAP bool_to_bit bls)` by (Cases_on `bls` >> gvs[]) >>
  simp[LENGTH_chunks, LENGTH_MAP, bool_to_bit_def]
QED

(* LIST_REL state_bools_w64 ==> EVERY length 25 *)
Theorem LIST_REL_state_bools_w64_lengths[local]:
  !bss wss. LIST_REL state_bools_w64 bss wss ==>
            EVERY (\p. LENGTH p >= 25) wss
Proof
  Induct >> simp[LIST_REL_CONS1] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac state_bools_w64_LENGTH >> simp[]
QED

Theorem pad10s1_136_w64_every_len25[local]:
  !bs. EVERY (\p. LENGTH p >= 25)
         (pad10s1_136_w64 eight_zeros_w64 bs [])
Proof
  gen_tac >>
  mp_tac (INST [``bytes:word8 list`` |-> ``bs:word8 list``]
               pad10s1_136_w64_sponge_init) >>
  simp[LET_THM] >>
  `eight_zeros_w64 = REPLICATE (512 DIV 64) (0w:word64)`
    by EVAL_TAC >>
  pop_assum SUBST_ALL_TAC >> strip_tac >>
  irule LIST_REL_state_bools_w64_lengths >>
  qexists_tac `MAP (\Pi. Pi ++ REPLICATE 512 F)
    (chunks 1088 (bytes_to_bools bs ++
       pad10s1 1088 (LENGTH (bytes_to_bools bs))))` >>
  simp[]
QED

Theorem LENGTH_absorb_pad[local]:
  !bs. LENGTH (absorb_w64 (pad10s1_136_w64 eight_zeros_w64 bs [])) = 25
Proof
  gen_tac >> irule LENGTH_absorb_w64 >>
  simp[pad10s1_136_w64_every_len25]
QED

Theorem LENGTH_FLAT_word_to_bytes[local]:
  !ws:word64 list.
    LENGTH (FLAT (MAP (\y. word_to_bytes y F) ws)) = 8 * LENGTH ws
Proof
  Induct >> simp[LENGTH_word_to_bytes]
QED

Theorem LENGTH_Keccak_256_w64:
  !bs. LENGTH (Keccak_256_w64 bs) = 32
Proof
  gen_tac >> rewrite_tac[Keccak_256_w64_def, combinTheory.C_DEF] >>
  BETA_TAC >>
  simp[LENGTH_FLAT_word_to_bytes, LENGTH_TAKE, LENGTH_absorb_pad]
QED

(* ===== num_sqrt bound ===== *)

Theorem num_sqrt_aux_le[local]:
  !n r. 0 < r ==> num_sqrt_aux n r <= r
Proof
  ho_match_mp_tac num_sqrt_aux_ind >> rpt strip_tac >>
  once_rewrite_tac[num_sqrt_aux_def] >>
  `r <> 0` by simp[] >> simp[] >>
  Cases_on `(r + n DIV r) DIV 2 < r` >> simp[] >>
  Cases_on `(r + n DIV r) DIV 2 = 0` >- (
    once_rewrite_tac[num_sqrt_aux_def] >> simp[]) >>
  `0 < (r + n DIV r) DIV 2` by simp[] >>
  `num_sqrt_aux n ((r + n DIV r) DIV 2) <= (r + n DIV r) DIV 2`
    by (first_x_assum irule >> simp[]) >>
  simp[]
QED

Theorem num_sqrt_le:
  !n. num_sqrt n <= n
Proof
  gen_tac >> simp[num_sqrt_def] >>
  Cases_on `n = 0` >> simp[] >>
  irule num_sqrt_aux_le >> simp[]
QED

(* ===== modexp bound ===== *)

Theorem modexp_lt[local]:
  !b e m a. 0 < m ==> vfmExecution$modexp b e m a < m
Proof
  simp[modexp_exp]
QED

(* ===== evaluate_block_hash typing ===== *)

Theorem evaluate_block_hash_well_typed[local]:
  !t n v. evaluate_block_hash t n = INL v ==>
          v = BytesV (word_to_bytes_be (EL (t.block_number - 1 - n)
                        t.block_hashes))
Proof
  rw[evaluate_block_hash_def, LET_THM]
QED

(* LENGTH word_to_bytes_be for bytes32 *)
Theorem LENGTH_word_to_bytes_be_32[local]:
  LENGTH (word_to_bytes_be (w:bytes32)) = 32
Proof
  simp[word_to_bytes_be_def, LENGTH_word_to_bytes]
QED

(* ===== evaluate_concat typing ===== *)

Theorem evaluate_concat_loop_typed[local]:
  !n v1 sa ba vs v.
    evaluate_concat_loop n v1 sa ba vs = INL v ==>
    (?s. v = StringV s /\ compatible_bound (Dynamic n) (LENGTH s)) \/
    (?bs. v = BytesV bs /\ compatible_bound (Dynamic n) (LENGTH bs))
Proof
  ho_match_mp_tac evaluate_concat_loop_ind >>
  rw[evaluate_concat_loop_def, LET_THM] >>
  gvs[AllCaseEqs()]
QED

Theorem evaluate_concat_typed[local]:
  !n vs v.
    evaluate_concat n vs = INL v ==>
    (?s. v = StringV s /\ compatible_bound (Dynamic n) (LENGTH s)) \/
    (?bs. v = BytesV bs /\ compatible_bound (Dynamic n) (LENGTH bs))
Proof
  rw[evaluate_concat_def, AllCaseEqs()] >>
  imp_res_tac evaluate_concat_loop_typed >> metis_tac[]
QED

(* ===== evaluate_slice typing ===== *)

Theorem evaluate_slice_typed[local]:
  !v1 v2 v3 n v.
    evaluate_slice v1 v2 v3 n = INL v ==>
    (?s. v = StringV s /\ compatible_bound (Dynamic n) (LENGTH s)) \/
    (?bs. v = BytesV bs /\ compatible_bound (Dynamic n) (LENGTH bs))
Proof
  rw[evaluate_slice_def, AllCaseEqs(), LET_THM] >>
  simp[LENGTH_TAKE]
QED

(* ===== evaluate_as_wei_value typing ===== *)

Theorem evaluate_as_wei_value_typed[local]:
  !dn v rv.
    evaluate_as_wei_value dn v = INL rv ==>
    ?i. rv = IntV i /\ within_int_bound (Unsigned 256) i
Proof
  rw[evaluate_as_wei_value_def, LET_THM, AllCaseEqs()] >>
  Cases_on `v` >> gvs[] >>
  simp[within_int_bound_def]
QED

(* ===== evaluate_ecrecover typing ===== *)

Theorem evaluate_ecrecover_typed[local]:
  !vs v. evaluate_ecrecover vs = INL v ==> ?w. v = AddressV w
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = INL _` mp_tac >>
  Cases_on `vs` >> simp[evaluate_ecrecover_def] >>
  Cases_on `h` >> simp[evaluate_ecrecover_def] >>
  Cases_on `t` >> simp[evaluate_ecrecover_def] >>
  Cases_on `t'` >> simp[evaluate_ecrecover_def] >>
  Cases_on `t` >> simp[evaluate_ecrecover_def] >>
  Cases_on `t'` >> simp[evaluate_ecrecover_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* ===== evaluate_ecadd/ecmul typing ===== *)

(* SORTED for enumerate_static_array *)
Theorem SORTED_MAP_FST_enumerate_static_array[local]:
  !vs d n. SORTED $< (MAP FST (enumerate_static_array d n vs))
Proof
  Induct >> simp[enumerate_static_array_def, LET_THM] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  assume_tac arithmeticTheory.transitive_LESS >>
  simp[SORTED_EQ] >> rpt strip_tac >>
  gvs[MEM_MAP] >>
  rename1 `MEM kv (enumerate_static_array _ _ _)` >>
  Cases_on `kv` >> gvs[MEM_enumerate_static_array_iff]
QED

(* bn254p is positive and < 2^256 *)
Theorem bn254p_pos[local]: 0 < bn254$bn254p
Proof
  EVAL_TAC
QED

Theorem bn254p_lt_2_256[local]: bn254$bn254p < 2 ** 256
Proof
  EVAL_TAC
QED

(* Field operations: fmul and fadd always < bn254p *)
Theorem fmul_bounded[local]:
  !x y. bn254$fmul x y < bn254$bn254p
Proof
  simp[bn254Theory.fmul_def, MOD_LESS, bn254p_pos]
QED

Theorem fadd_bounded[local]:
  !x y. bn254$fadd x y < bn254$bn254p
Proof
  simp[bn254Theory.fadd_def, MOD_LESS, bn254p_pos]
QED

Theorem fsub_bounded[local]:
  !x y. x < bn254$bn254p /\ y < bn254$bn254p ==>
         bn254$fsub x y < bn254$bn254p
Proof
  rpt strip_tac >> simp[bn254Theory.fsub_def] >>
  IF_CASES_TAC >> simp[MOD_LESS, bn254p_pos]
QED

(* Predicate: all components of a projective point are < bn254p *)
Definition fp_bounded_def:
  fp_bounded (x:num, y:num, z:num) <=> x < bn254$bn254p /\ y < bn254$bn254p /\ z < bn254$bn254p
End

(* add preserves boundedness *)
Theorem add_bounded[local]:
  !p1 p2. fp_bounded (bn254$add p1 p2)
Proof
  rpt gen_tac >> PairCases_on `p1` >> PairCases_on `p2` >>
  simp[fp_bounded_def, bn254Theory.add_def, LET_THM] >>
  `!a b. a < bn254$bn254p /\ b < bn254$bn254p ==>
         bn254$fsub a b < bn254$bn254p` by simp[fsub_bounded] >>
  simp[fmul_bounded, fadd_bounded]
QED

(* dbl preserves boundedness *)
Theorem dbl_bounded[local]:
  !p. fp_bounded (bn254$dbl p)
Proof
  gen_tac >> PairCases_on `p` >>
  simp[fp_bounded_def, bn254Theory.dbl_def, LET_THM] >>
  `!a b. a < bn254$bn254p /\ b < bn254$bn254p ==>
         bn254$fsub a b < bn254$bn254p` by simp[fsub_bounded] >>
  simp[fmul_bounded, fadd_bounded]
QED

(* mul_loop preserves boundedness *)
Theorem mul_loop_bounded[local]:
  !a p n. fp_bounded a ==> fp_bounded (bn254$mul_loop a p n)
Proof
  ho_match_mp_tac bn254Theory.mul_loop_ind >> rpt strip_tac >>
  once_rewrite_tac[bn254Theory.mul_loop_def] >>
  IF_CASES_TAC >> simp[LET_THM] >>
  first_x_assum irule >>
  simp[dbl_bounded] >> IF_CASES_TAC >> simp[add_bounded]
QED

(* zero is bounded *)
Theorem zero_bounded[local]: fp_bounded bn254$zero
Proof
  EVAL_TAC
QED

(* mul output is bounded when input is bounded *)
Theorem mul_bounded[local]:
  !p n. fp_bounded p ==> fp_bounded (bn254$mul p n)
Proof
  rpt strip_tac >> simp[bn254Theory.mul_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[zero_bounded, mul_loop_bounded]
QED

(* fromAffine on bounded coords gives bounded point *)
Theorem fromAffine_bounded[local]:
  !x y. x < bn254$bn254p /\ y < bn254$bn254p ==>
    fp_bounded (bn254$fromAffine (x, y))
Proof
  rpt strip_tac >> simp[bn254Theory.fromAffine_def, LET_THM] >>
  IF_CASES_TAC >> simp[zero_bounded, fp_bounded_def, bn254p_pos]
QED

(* toAffine on bounded input gives coords < bn254p *)
Theorem toAffine_bounded[local]:
  !p. fp_bounded p ==>
    FST (bn254$toAffine p) < bn254$bn254p /\
    SND (bn254$toAffine p) < bn254$bn254p
Proof
  rpt strip_tac >> PairCases_on `p` >> gvs[fp_bounded_def] >>
  simp[bn254Theory.toAffine_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[fmul_bounded]
QED

(* Helper: < bn254p implies < 2^256 *)
Theorem lt_bn254p_lt_2_256[local]:
  !n. n < bn254$bn254p ==> n < 2 ** 256
Proof
  rpt strip_tac >> irule LESS_TRANS >> qexists `bn254$bn254p` >>
  rewrite_tac[bn254p_lt_2_256] >> simp[]
QED

(* addAffine output coordinates < 2^256 *)
Theorem addAffine_bounded[local]:
  !a b. FST (bn254$addAffine a b) < 2 ** 256 /\
        SND (bn254$addAffine a b) < 2 ** 256
Proof
  rpt gen_tac >>
  `fp_bounded (bn254$add (bn254$fromAffine a) (bn254$fromAffine b))`
    by simp[add_bounded] >>
  `FST (bn254$toAffine (bn254$add (bn254$fromAffine a) (bn254$fromAffine b))) < bn254$bn254p /\
   SND (bn254$toAffine (bn254$add (bn254$fromAffine a) (bn254$fromAffine b))) < bn254$bn254p`
    by (irule toAffine_bounded >> simp[]) >>
  rewrite_tac[bn254Theory.addAffine_def] >>
  conj_tac >> irule lt_bn254p_lt_2_256 >> simp[]
QED

(* mulAffine output coordinates < 2^256 when input coords < bn254p *)
Theorem mulAffine_bounded[local]:
  !a n. FST a < bn254$bn254p /\ SND a < bn254$bn254p ==>
        FST (bn254$mulAffine a n) < 2 ** 256 /\
        SND (bn254$mulAffine a n) < 2 ** 256
Proof
  rpt gen_tac >> PairCases_on `a` >> strip_tac >>
  `fp_bounded (bn254$fromAffine (a0, a1))` by simp[fromAffine_bounded] >>
  `fp_bounded (bn254$mul (bn254$fromAffine (a0, a1)) n)` by simp[mul_bounded] >>
  `FST (bn254$toAffine (bn254$mul (bn254$fromAffine (a0, a1)) n)) < bn254$bn254p /\
   SND (bn254$toAffine (bn254$mul (bn254$fromAffine (a0, a1)) n)) < bn254$bn254p`
    by (irule toAffine_bounded >> simp[]) >>
  rewrite_tac[bn254Theory.mulAffine_def] >>
  conj_tac >> irule lt_bn254p_lt_2_256 >> simp[]
QED

(* mk_ec_result is well-typed when coords < 2^256 *)
Theorem mk_ec_result_well_typed[local]:
  !p. FST p < 2 ** 256 /\ SND p < 2 ** 256 ==>
    value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
                   (mk_ec_result p)
Proof
  Cases >> rpt strip_tac >>
  rewrite_tac[mk_ec_result_def, make_array_value_def] >>
  once_rewrite_tac[value_has_type_def] >>
  conj_tac >- simp[SORTED_MAP_FST_enumerate_static_array] >>
  irule sparse_has_type_enumerate >>
  fs[default_value_def, value_has_type_def]
QED

(* ecadd success implies well-typed result *)
Theorem evaluate_ecadd_well_typed[local]:
  !vs v. evaluate_ecadd vs = INL v ==>
    value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v
Proof
  rpt strip_tac >> qpat_x_assum `_ = INL _` mp_tac >>
  Cases_on `vs` >> simp[evaluate_ecadd_def] >>
  Cases_on `t` >> simp[evaluate_ecadd_def] >>
  Cases_on `t'` >> simp[evaluate_ecadd_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[]
  (* NONE case: ecadd returns NONE => mk_ec_result (0,0) *)
  >- (irule mk_ec_result_well_typed >> simp[])
  (* SOME case: ecadd returns SOME r => mk_ec_result r *)
  >> gvs[ecadd_def, AllCaseEqs()] >>
     irule mk_ec_result_well_typed >>
     simp[addAffine_bounded]
QED

(* ecmul success implies well-typed result *)
Theorem evaluate_ecmul_well_typed[local]:
  !vs v. evaluate_ecmul vs = INL v ==>
    value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v
Proof
  rpt strip_tac >> qpat_x_assum `_ = INL _` mp_tac >>
  Cases_on `vs` >> simp[evaluate_ecmul_def] >>
  Cases_on `t` >> simp[evaluate_ecmul_def] >>
  Cases_on `h'` >> simp[evaluate_ecmul_def] >>
  Cases_on `t'` >> simp[evaluate_ecmul_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[]
  (* NONE case *)
  >- (irule mk_ec_result_well_typed >> simp[])
  (* SOME case: ecmul checks validAffine, then returns mulAffine result *)
  >> gvs[ecmul_def, AllCaseEqs()] >>
     irule mk_ec_result_well_typed >>
     irule mulAffine_bounded >>
     fs[bn254Theory.validAffine_def]
QED

(* ===== Helper: within_int_bound / value_has_type bridge ===== *)

Theorem within_int_bound_vht_unsigned[local]:
  !m i. within_int_bound (Unsigned m) i /\ m <= 256 ==>
        value_has_type (BaseTV (UintT m)) (IntV i)
Proof
  rw[within_int_bound_def, value_has_type_def]
QED

Theorem within_int_bound_vht_signed[local]:
  !m i. within_int_bound (Signed m) i /\ m <= 256 ==>
        value_has_type (BaseTV (IntT m)) (IntV i)
Proof
  rw[within_int_bound_def, value_has_type_def]
QED

(* ===== Main theorem ===== *)

(* Helper for the Bop case: connects type_to_int_bound with evaluate_type *)
Theorem type_to_int_bound_evaluate_type[local]:
  !tenv ty leaf_tv.
    evaluate_type tenv ty = SOME leaf_tv ==>
    (!m. leaf_tv = BaseTV (UintT m) ==>
      (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) =
        Unsigned m) /\
    (!m. leaf_tv = BaseTV (IntT m) ==>
      (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) =
        Signed m)
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp_tac (srw_ss()) [evaluate_type_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[type_to_int_bound_def]
QED

(* evaluate_type for BaseT: only for valid base types. Used as rewrite. *)
Theorem evaluate_type_BaseT_BoolT[local,simp]:
  evaluate_type tenv (BaseT BoolT) = SOME (BaseTV BoolT)
Proof simp[evaluate_type_def]
QED

Theorem evaluate_type_BaseT_DecimalT[local,simp]:
  evaluate_type tenv (BaseT DecimalT) = SOME (BaseTV DecimalT)
Proof simp[evaluate_type_def]
QED

Theorem evaluate_type_BaseT_AddressT[local,simp]:
  evaluate_type tenv (BaseT AddressT) = SOME (BaseTV AddressT)
Proof simp[evaluate_type_def]
QED

(* value_has_type simplification helpers — include ALL conditions *)
Theorem vht_BytesV_Fixed[local]:
  value_has_type (BaseTV (BytesT (Fixed n))) (BytesV bs) <=>
  LENGTH bs = n
Proof
  simp[value_has_type_def]
QED

Theorem vht_BytesV_Dynamic[local]:
  value_has_type (BaseTV (BytesT (Dynamic n))) (BytesV bs) <=>
  compatible_bound (Dynamic n) (LENGTH bs)
Proof
  simp[value_has_type_def, compatible_bound_def]
QED

Theorem vht_StringV[local]:
  value_has_type (BaseTV (StringT n)) (StringV str) <=>
  compatible_bound (Dynamic n) (STRLEN str)
Proof
  simp[value_has_type_def, compatible_bound_def]
QED

Theorem vht_IntV_UintT[local]:
  value_has_type (BaseTV (UintT m)) (IntV i) <=>
  0 <= i /\ Num i < 2 ** m
Proof
  simp[value_has_type_def]
QED

(* Floor/Ceil: decimal division stays within int256 bounds *)
Theorem floor_decimal_in_int256_bounds[local]:
  within_int_bound (Signed 168) i ==>
  -(&(2 ** 255)) <= i / 10000000000 /\
  i / 10000000000 < &(2 ** 255)
Proof
  rw[within_int_bound_def] >>
  `10000000000:int <> 0` by intLib.ARITH_TAC >>
  drule INT_DIVISION >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

Theorem ceil_decimal_in_int256_bounds[local]:
  within_int_bound (Signed 168) i ==>
  -(&(2 ** 255)) <= (i + 9999999999) / 10000000000 /\
  (i + 9999999999) / 10000000000 < &(2 ** 255)
Proof
  rw[within_int_bound_def] >>
  `10000000000:int <> 0` by intLib.ARITH_TAC >>
  drule INT_DIVISION >>
  disch_then (qspec_then `i + 9999999999` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

(* bounded_int_op success gives within_int_bound *)
Theorem bounded_int_op_INL[local]:
  !u r v. bounded_int_op u r = INL v ==>
          v = IntV r /\ within_int_bound u r
Proof
  rw[bounded_int_op_def, AllCaseEqs()]
QED

(* bounded_decimal_op success gives within_int_bound (Signed 168) *)
Theorem bounded_decimal_op_INL[local]:
  !i v. bounded_decimal_op i = INL v ==>
        v = DecimalV i /\ within_int_bound (Signed 168) i
Proof
  rw[bounded_decimal_op_def, AllCaseEqs()]
QED

(* Any well-typed IntV with well-formed type has Num i < 2^256 *)
Theorem int_type_Num_bound[local]:
  !tyv i. value_has_type tyv (IntV i) /\ well_formed_type_value tyv ==>
          Num i < 2 ** 256
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `_ < bound` >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[value_has_type_inv] >> strip_tac >> gvs[well_formed_type_value_def]
  >- (irule LESS_LESS_EQ_TRANS >> qexists `2 ** n` >>
      unabbrev_all_tac >> simp[] >>
      irule (iffRL EXP_BASE_LE_MONO) >> simp[])
  >> Cases_on `n = 0` >- (unabbrev_all_tac >> gvs[within_int_bound_def])
  >> gvs[within_int_bound_def, LET_THM, Num_neg] >>
     Cases_on `i < 0` >> gvs[] >>
     irule LESS_EQ_LESS_TRANS >>
     qexists `2 ** (n - 1)` >>
     unabbrev_all_tac >> simp[]
QED

(* Uint2Str: toString of any well-typed integer has at most 78 characters *)
Theorem uint2str_strlen_bound[local]:
  !tyv i. value_has_type tyv (IntV i) /\ well_formed_type_value tyv ==>
          STRLEN (toString (Num i)) <= 78
Proof
  rpt strip_tac >>
  imp_res_tac int_type_Num_bound >>
  qmatch_asmsub_abbrev_tac `Num i < bound` >>
  simp[ASCIInumbersTheory.LENGTH_num_to_dec_string] >>
  Cases_on `i = 0` >> gvs[] >>
  `0 < Num i` by intLib.ARITH_TAC >>
  `Num i <= bound - 1` by decide_tac >>
  `LOG 10 (Num i) <= LOG 10 (bound - 1)` by
    (irule logrootTheory.LOG_LE_MONO >> simp[]) >>
  `LOG 10 (bound - 1) = 77` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  decide_tac
QED

(* Comparison binops always return BoolV *)
Theorem evaluate_binop_comparison[local]:
  !u tv bop a v result.
    (bop = Eq \/ bop = NotEq \/ bop = Lt \/ bop = LtE \/
     bop = Gt \/ bop = GtE \/ bop = In \/ bop = NotIn) /\
    evaluate_binop u tv bop a v = INL result ==>
    ?b. result = BoolV b
Proof
  rpt strip_tac >>
  gvs[evaluate_binop_def, AllCaseEqs(), LET_THM, binop_negate_def] >>
  Cases_on `v` >> gvs[AllCaseEqs(), binop_negate_def] >>
  Cases_on `a` >> gvs[AllCaseEqs(), binop_negate_def]
QED

(* ===== Main theorem: evaluate_builtin_well_typed ===== *)

(* Helper: low-m-bits mask is n2w(2^m - 1) *)
Theorem low_mask_eq[local]:
  !m. m <= 256 ==>
    ~(~(0w:bytes32) << m) = n2w (2 ** m - 1)
Proof
  rpt strip_tac >>
  rewrite_tac[wordsTheory.WORD_NOT_0, wordsTheory.LSL_UINT_MAX,
              wordsTheory.word_1comp_n2w] >>
  AP_TERM_TAC >>
  rewrite_tac[wordsTheory.dimword_def] >>
  `dimindex(:256) = 256` by EVAL_TAC >>
  asm_rewrite_tac[] >>
  `2 ** m <= 2 ** 256` by (irule (iffRL EXP_BASE_LE_MONO) >> simp[]) >>
  `(2 ** 256 - 2 ** m) MOD 2 ** 256 = 2 ** 256 - 2 ** m` by simp[LESS_MOD] >>
  asm_rewrite_tac[] >> decide_tac
QED

(* Helper: w2n(w && n2w(2^m - 1)) = w2n w MOD 2^m *)
Theorem w2n_and_mask_mod[local]:
  !m (w:bytes32). w2n (w && n2w (2 ** m - 1)) = w2n w MOD 2 ** m
Proof
  rpt strip_tac >>
  (* Rewrite only the first arg of && from w to n2w(w2n w) *)
  CONV_TAC (LHS_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
    (REWR_CONV (GSYM wordsTheory.n2w_w2n)))))) >>
  rewrite_tac[wordsTheory.WORD_AND_EXP_SUB1, wordsTheory.w2n_n2w] >>
  (* Goal: (w2n w MOD 2^m) MOD dimword(:256) = w2n w MOD 2^m *)
  irule LESS_MOD >>
  irule LESS_EQ_LESS_TRANS >>
  qexists `w2n w` >>
  simp[MOD_LESS_EQ, wordsTheory.w2n_lt]
QED

(* Helper: AND with low-m-bits mask produces value < 2^m *)
Theorem w2n_and_low_mask_lt[local]:
  !m (w:bytes32). m <= 256 ==>
    w2n (w && ~(~0w << m)) < 2 ** m
Proof
  rpt strip_tac >>
  imp_res_tac low_mask_eq >> pop_assum (fn th => rewrite_tac[th]) >>
  simp[w2n_and_mask_mod, MOD_LESS]
QED

(* For BaseT types, evaluate_type always gives BaseTV (when IS_SOME) *)
Theorem evaluate_type_BaseT[local]:
  !tenv bt. IS_SOME (evaluate_type tenv (BaseT bt)) ==>
            evaluate_type tenv (BaseT bt) = SOME (BaseTV bt)
Proof
  rpt strip_tac >> Cases_on `bt` >>
  gvs[evaluate_type_def, LET_THM, AllCaseEqs()] >>
  rpt (FULL_CASE_TAC >> gvs[])
QED

(* evaluate_concat_loop preserves value kind *)
Theorem evaluate_concat_loop_string_typed[local]:
  !n v sa ba vs r.
    evaluate_concat_loop n (StringV v) sa ba vs = INL r ==>
    ?s. r = StringV s /\ compatible_bound (Dynamic n) (LENGTH s)
Proof
  Induct_on `vs` >>
  rw[evaluate_concat_loop_def, LET_THM, AllCaseEqs()] >>
  Cases_on `h` >> gvs[evaluate_concat_loop_def] >>
  first_x_assum drule >> simp[]
QED

Theorem evaluate_concat_loop_bytes_typed[local]:
  !n v sa ba vs r.
    evaluate_concat_loop n (BytesV v) sa ba vs = INL r ==>
    ?bs. r = BytesV bs /\ compatible_bound (Dynamic n) (LENGTH bs)
Proof
  Induct_on `vs` >>
  rw[evaluate_concat_loop_def, LET_THM, AllCaseEqs()] >>
  Cases_on `h` >> gvs[evaluate_concat_loop_def] >>
  first_x_assum drule >> simp[]
QED

(* If all types are BytesT and LIST_REL vht holds, all values are BytesV *)
Theorem list_rel_bytes_all_bytesv[local]:
  !vs tys tenv.
    LIST_REL (\v t. ?tyv. evaluate_type tenv t = SOME tyv /\
                          value_has_type tyv v) vs tys /\
    EVERY (\t. ?bd. t = BaseT (BytesT bd)) tys ==>
    EVERY (\v. ?bs. v = BytesV bs) vs
Proof
  Induct >> rw[LIST_REL_CONS1] >> gvs[] >>
  first_x_assum drule >> (impl_tac >- simp[]) >> simp[] >>
  Cases_on `bd` >>
  gvs[evaluate_type_def, LET_THM, AllCaseEqs()] >>
  Cases_on `h` >> gvs[value_has_type_def]
QED

Theorem list_rel_string_all_stringv[local]:
  !vs tys tenv.
    LIST_REL (\v t. ?tyv. evaluate_type tenv t = SOME tyv /\
                          value_has_type tyv v) vs tys /\
    EVERY (\t. ?m. t = BaseT (StringT m)) tys ==>
    EVERY (\v. ?s. v = StringV s) vs
Proof
  Induct >> rw[LIST_REL_CONS1] >> gvs[] >>
  first_x_assum drule >> (impl_tac >- simp[]) >> simp[] >>
  gvs[evaluate_type_def, LET_THM, AllCaseEqs()] >>
  Cases_on `h` >> gvs[value_has_type_def]
QED

(* Forward-chain forms for evaluate_binop theorems *)
val ebpv = REWRITE_RULE [GSYM AND_IMP_INTRO] evaluate_binop_preserves_vht;
val ebspv_shl = evaluate_binop_shift_preserves_vht
  |> Q.SPECL [`u`,`tv2`,`ShL`]
  |> SIMP_RULE (srw_ss()) []
  |> REWRITE_RULE [GSYM AND_IMP_INTRO];
val ebspv_shr = evaluate_binop_shift_preserves_vht
  |> Q.SPECL [`u`,`tv2`,`ShR`]
  |> SIMP_RULE (srw_ss()) []
  |> REWRITE_RULE [GSYM AND_IMP_INTRO];

(* Tactic to close a single Bop subgoal after Cases_on b + gvs *)
val bop_close_tac = fn (asms, gl) =>
  let
    val tv = case strip_comb gl of (_, [tv, _]) => tv | _ => raise Fail "bop"
  in (
    (* Comparisons: result is always BoolV *)
    TRY (imp_res_tac evaluate_binop_comparison >>
         gvs[value_has_type_def] >> NO_TAC) >>
    (* Establish well_formed_type_value (from evaluate_type or concrete) *)
    TRY (imp_res_tac (cj 1 evaluate_type_well_formed)) >>
    TRY (`well_formed_type_value ^tv` by
      simp[well_formed_type_value_def]) >>
    (* Shifts *)
    TRY (qpat_x_assum `evaluate_binop _ _ _ _ _ = _` (fn eb =>
      mp_tac (MATCH_MP ebspv_shl eb)) >>
      disch_then (fn th => first_assum (mp_tac o MATCH_MP th)) >>
      disch_then (fn th => first_assum (mp_tac o MATCH_MP th)) >>
      simp[] >> NO_TAC) >>
    TRY (qpat_x_assum `evaluate_binop _ _ _ _ _ = _` (fn eb =>
      mp_tac (MATCH_MP ebspv_shr eb)) >>
      disch_then (fn th => first_assum (mp_tac o MATCH_MP th)) >>
      disch_then (fn th => first_assum (mp_tac o MATCH_MP th)) >>
      simp[] >> NO_TAC) >>
    (* General (non-comparison, non-shift) *)
    qpat_x_assum `evaluate_binop _ _ _ _ _ = _` (fn eb =>
      mp_tac (MATCH_MP ebpv eb)) >>
    disch_then (fn th => first_assum (mp_tac o MATCH_MP th)) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[]
  ) (asms, gl) end;

Theorem evaluate_builtin_well_typed:
  !cx acc ty bt vs v arg_tys.
    evaluate_builtin cx acc ty bt vs = INL v /\
    well_typed_builtin_app ty bt arg_tys /\
    context_well_typed cx /\
    LIST_REL (\v t. ?tyv. evaluate_type (get_tenv cx) t = SOME tyv /\
                          value_has_type tyv v) vs arg_tys /\
    IS_SOME (evaluate_type (get_tenv cx) ty) ==>
    ?tyv. evaluate_type (get_tenv cx) ty = SOME tyv /\ value_has_type tyv v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bt` >> gvs[]
  >- suspend "Len"
  >- suspend "Not"
  >- suspend "Neg"
  >- suspend "Abs"
  >- suspend "Keccak256"
  >- suspend "Sha256"
  >- suspend "AsWeiValue"
  >- suspend "Concat"
  >- suspend "Slice"
  >- suspend "Uint2Str"
  >- suspend "MakeArray"
  >- suspend "Ceil"
  >- suspend "Floor"
  >- suspend "AddMod"
  >- suspend "MulMod"
  >- suspend "Bop"
  >- suspend "BlockHash"
  >- suspend "BlobHash"
  >- suspend "Env"
  >- suspend "Acc"
  >- suspend "Isqrt"
  >- suspend "MethodId"
  >- suspend "ECRecover"
  >- suspend "ECAdd"
  >- suspend "ECMul"
  >> suspend "PowMod256"
QED

(* === Resume blocks === *)

Resume evaluate_builtin_well_typed[Len]:
  gvs[evaluate_builtin_def]
QED

Resume evaluate_builtin_well_typed[Not]:
  gvs[well_typed_builtin_app_def] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >>
  gvs[evaluate_builtin_def, AllCaseEqs()] >>
  Cases_on `t'` >>
  gvs[is_bool_type_def, is_int_type_def, is_flag_type_def,
      type_to_int_bound_def, evaluate_type_def, AllCaseEqs()] >>
  fs[value_has_type_def] >>
  TRY intLib.ARITH_TAC >>
  rewrite_tac[wordsTheory.WORD_NEG_1, GSYM wordsTheory.WORD_NOT_0] >>
  imp_res_tac w2n_and_low_mask_lt >> simp[]
QED

Resume evaluate_builtin_well_typed[Neg]:
  gvs[well_typed_builtin_app_def] >>
  Cases_on `v'` >>
  gvs[evaluate_builtin_def, AllCaseEqs()] >>
  imp_res_tac bounded_int_op_INL >>
  imp_res_tac bounded_decimal_op_INL >>
  gvs[] >>
  (* is_int_type ty: resolve ty to BaseT (UintT/IntT) *)
  TRY (Cases_on `ty` >> gvs[is_int_type_def] >>
       gvs[type_to_int_bound_def, evaluate_type_def,
           AllCaseEqs(), value_has_type_def, within_int_bound_def] >> NO_TAC) >>
  (* DecimalT case *)
  gvs[evaluate_type_def, value_has_type_def]
QED

Resume evaluate_builtin_well_typed[Abs]:
  gvs[evaluate_builtin_def]
QED

Resume evaluate_builtin_well_typed[Keccak256]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, AllCaseEqs()] >>
  gvs[vht_BytesV_Fixed, LENGTH_Keccak_256_w64]
QED

Resume evaluate_builtin_well_typed[Sha256]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, AllCaseEqs()] >>
  gvs[vht_BytesV_Fixed, word_to_bytes_be_def, LENGTH_word_to_bytes]
QED

Resume evaluate_builtin_well_typed[AsWeiValue]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >>
  gvs[evaluate_builtin_def, evaluate_as_wei_value_def,
      AllCaseEqs(), LET_THM] >>
  gvs[value_has_type_def, within_int_bound_def]
QED

Resume evaluate_builtin_well_typed[Concat]:
  gvs[well_typed_builtin_app_def, evaluate_builtin_def]
  >- ((* BytesT case *)
      drule_all list_rel_bytes_all_bytesv >> strip_tac >>
      imp_res_tac evaluate_type_BaseT >> gvs[] >>
      `2 <= LENGTH vs` by (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
      Cases_on `vs` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      gvs[EVERY_DEF, evaluate_concat_def, init_concat_output_def] >>
      imp_res_tac evaluate_concat_loop_bytes_typed >>
      gvs[vht_BytesV_Dynamic])
  >> ((* StringT case *)
      drule_all list_rel_string_all_stringv >> strip_tac >>
      imp_res_tac evaluate_type_BaseT >> gvs[] >>
      `2 <= LENGTH vs` by (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
      Cases_on `vs` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      gvs[EVERY_DEF, evaluate_concat_def, init_concat_output_def] >>
      imp_res_tac evaluate_concat_loop_string_typed >>
      gvs[vht_StringV])
QED

Resume evaluate_builtin_well_typed[Slice]:
  gvs[well_typed_builtin_app_def] >>
  imp_res_tac evaluate_type_BaseT >> gvs[] >>
  decompose_list_rel_tac >>
  TRY (Cases_on `bd`) >>
  gvs[evaluate_type_def, LET_THM, AllCaseEqs()] >>
  rename1 `evaluate_builtin _ _ _ _ [fv; _; _]` >>
  Cases_on `fv` >> gvs[value_has_type_def] >>
  gvs[evaluate_builtin_def, evaluate_slice_def, AllCaseEqs(), LET_THM] >>
  simp[vht_BytesV_Dynamic, vht_StringV, LENGTH_TAKE]
QED

Resume evaluate_builtin_well_typed[Uint2Str]:
  gvs[well_typed_builtin_app_def] >>
  imp_res_tac evaluate_type_BaseT >> gvs[] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, AllCaseEqs()] >>
  `well_formed_type_value tyv` by
    (imp_res_tac evaluate_type_well_formed >> gvs[]) >>
  imp_res_tac uint2str_strlen_bound >>
  gvs[vht_StringV, compatible_bound_def]
QED

Resume evaluate_builtin_well_typed[MakeArray]:
  gvs[well_typed_builtin_app_def]
QED

Resume evaluate_builtin_well_typed[Ceil]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, AllCaseEqs()] >>
  imp_res_tac bounded_int_op_INL >>
  gvs[value_has_type_def, within_int_bound_def] >>
  imp_res_tac ceil_decimal_in_int256_bounds >> intLib.ARITH_TAC
QED

Resume evaluate_builtin_well_typed[Floor]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, AllCaseEqs()] >>
  imp_res_tac bounded_int_op_INL >>
  gvs[value_has_type_def, within_int_bound_def] >>
  imp_res_tac floor_decimal_in_int256_bounds >> intLib.ARITH_TAC
QED

(* Helper: bound implies UintT well-typedness — NO simpset, so 2^k stays symbolic *)
Theorem vht_uint_bound[local]:
  !k m. m < 2 ** k /\ k <= 256 ==>
        value_has_type (BaseTV (UintT k)) (IntV (&m))
Proof
  rewrite_tac[vht_IntV_UintT, integerTheory.NUM_OF_INT, integerTheory.INT_POS] >>
  rpt strip_tac >> asm_rewrite_tac[]
QED

(* Extract Num bound from value_has_type — NO simpset *)
Theorem vht_uint_Num_bound[local]:
  !k i. value_has_type (BaseTV (UintT k)) (IntV i) ==> Num i < 2 ** k
Proof
  rewrite_tac[vht_IntV_UintT] >> rpt strip_tac
QED

(* Fold literal 2^256 back to symbolic — for goals where evaluate_builtin_def expanded it *)
val fold_2_256 = GSYM (EVAL ``2n ** 256``);

(* EC operations return ArrayTV (BaseTV (UintT 256)) (Fixed 2).
   The evaluate_type for this checks type_slot_size < dimword (:256). *)
Theorem ec_array_type_slot_size_ok[local]:
  0 < type_slot_size (BaseTV (UintT 256)) /\
  type_slot_size (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) < dimword (:256)
Proof
  rewrite_tac[type_slot_size_def, wordsTheory.dimword_def] >>
  `dimindex (:256) = 256` by EVAL_TAC >> asm_rewrite_tac[] >>
  `4n <= 2 ** 256` suffices_by DECIDE_TAC >>
  `4n = 2 ** 2` by EVAL_TAC >> pop_assum SUBST1_TAC >>
  irule bitTheory.TWOEXP_MONO2 >> DECIDE_TAC
QED

Resume evaluate_builtin_well_typed[AddMod]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  decompose_list_rel_tac >> gvs[evaluate_type_def] >>
  rename1 `evaluate_builtin _ _ _ _ [a1; a2; a3]` >>
  Cases_on `a1` >> Cases_on `a2` >> Cases_on `a3` >>
  gvs[evaluate_builtin_def, AllCaseEqs()] >>
  irule vht_uint_bound >>
  conj_tac >- (irule LESS_TRANS >> qexists `Num i''` >>
    conj_tac >- (irule MOD_LESS >> imp_res_tac ratTheory.NUM_NZERO >> simp[]) >>
    irule vht_uint_Num_bound >> first_assum ACCEPT_TAC) >>
  DECIDE_TAC
QED

Resume evaluate_builtin_well_typed[MulMod]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  decompose_list_rel_tac >> gvs[evaluate_type_def] >>
  rename1 `evaluate_builtin _ _ _ _ [a1; a2; a3]` >>
  Cases_on `a1` >> Cases_on `a2` >> Cases_on `a3` >>
  gvs[evaluate_builtin_def, AllCaseEqs()] >>
  irule vht_uint_bound >>
  conj_tac >- (irule LESS_TRANS >> qexists `Num i''` >>
    conj_tac >- (irule MOD_LESS >> imp_res_tac ratTheory.NUM_NZERO >> simp[]) >>
    irule vht_uint_Num_bound >> first_assum ACCEPT_TAC) >>
  DECIDE_TAC
QED

Resume evaluate_builtin_well_typed[Bop]:
  gvs[well_typed_builtin_app_def] >>
  decompose_list_rel_tac >>
  gvs[evaluate_builtin_def, LET_THM] >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv` by
    (Cases_on `evaluate_type (get_tenv cx) ty` >> gvs[]) >>
  gvs[] >>
  drule type_to_int_bound_evaluate_type >> strip_tac >>
  Cases_on `b` >> gvs[well_typed_binop_def] >> bop_close_tac
QED

Resume evaluate_builtin_well_typed[BlockHash]:
  gvs[well_typed_builtin_app_def, LIST_REL_CONS1, evaluate_type_def] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, AllCaseEqs()] >>
  imp_res_tac evaluate_block_hash_well_typed >>
  gvs[vht_BytesV_Fixed, LENGTH_word_to_bytes_be_32]
QED

Resume evaluate_builtin_well_typed[BlobHash]:
  gvs[well_typed_builtin_app_def, LIST_REL_CONS1, evaluate_type_def] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, evaluate_blob_hash_def, AllCaseEqs()] >>
  gvs[vht_BytesV_Fixed, LENGTH_word_to_bytes_be_32]
QED

Resume evaluate_builtin_well_typed[Env]:
  gvs[well_typed_builtin_app_def, LIST_REL_CONS1] >>
  rename1 `Env ei` >> Cases_on `ei` >>
  gvs[evaluate_builtin_def, AllCaseEqs(), env_item_type_def,
      evaluate_type_def, value_has_type_def, context_well_typed_def] >>
  imp_res_tac evaluate_block_hash_well_typed >>
  gvs[vht_BytesV_Fixed, LENGTH_word_to_bytes_be_32]
QED

Resume evaluate_builtin_well_typed[Acc]:
  gvs[well_typed_builtin_app_def]
QED

Resume evaluate_builtin_well_typed[Isqrt]:
  gvs[well_typed_builtin_app_def, LIST_REL_CONS1, evaluate_type_def] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, AllCaseEqs()] >>
  irule vht_uint_bound >>
  (conj_tac >- (irule LESS_EQ_LESS_TRANS >> qexists `Num i` >>
    (conj_tac >- (irule vht_uint_Num_bound >> first_assum ACCEPT_TAC)) >>
    simp[num_sqrt_le])) >>
  DECIDE_TAC
QED

Resume evaluate_builtin_well_typed[MethodId]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  rename1 `evaluate_builtin _ _ _ _ [av]` >>
  Cases_on `av` >> gvs[evaluate_builtin_def, AllCaseEqs()] >>
  gvs[vht_BytesV_Fixed] >>
  simp[LENGTH_TAKE, LENGTH_Keccak_256_w64]
QED

Resume evaluate_builtin_well_typed[ECRecover]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  decompose_list_rel_tac >>
  gvs[evaluate_builtin_def, AllCaseEqs()] >>
  imp_res_tac evaluate_ecrecover_typed >>
  gvs[value_has_type_def]
QED

Resume evaluate_builtin_well_typed[ECAdd]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  decompose_list_rel_tac >>
  gvs[evaluate_builtin_def, AllCaseEqs()] >>
  imp_res_tac evaluate_ecadd_well_typed >>
  assume_tac ec_array_type_slot_size_ok >> gvs[]
QED

Resume evaluate_builtin_well_typed[ECMul]:
  gvs[well_typed_builtin_app_def, evaluate_type_def] >>
  decompose_list_rel_tac >>
  gvs[evaluate_builtin_def, AllCaseEqs()] >>
  imp_res_tac evaluate_ecmul_well_typed >>
  assume_tac ec_array_type_slot_size_ok >> gvs[]
QED

Resume evaluate_builtin_well_typed[PowMod256]:
  gvs[well_typed_builtin_app_def, LIST_REL_CONS1, evaluate_type_def] >>
  rename1 `evaluate_builtin _ _ _ _ [a1; a2]` >>
  Cases_on `a1` >> Cases_on `a2` >>
  gvs[evaluate_builtin_def, AllCaseEqs()] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV fold_2_256)) >>
  irule vht_uint_bound >>
  conj_tac >- (irule modexp_lt >> rewrite_tac[bitTheory.ZERO_LT_TWOEXP]) >>
  DECIDE_TAC
QED

Finalise evaluate_builtin_well_typed

val _ = export_theory();
