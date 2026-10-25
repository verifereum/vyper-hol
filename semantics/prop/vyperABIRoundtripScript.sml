(*
 * Roundtrip theorems for the Vyper <-> ABI value conversions.
 *
 * TOP-LEVEL:
 *   abi_to_vyper_vyper_to_abi   — abi_to_vyper then vyper_to_abi is the identity
 *   vyper_to_abi_default_value  — encoding of default values
 *)

Theory vyperABIRoundtrip
Ancestors
  contractABI vyperAST vyperValue vyperMisc vyperNsidFmap
  arithmetic byte combin divides
  finite_map list option pair rich_list string words vyperABI
Libs
  wordsLib dep_rewrite

(* ===== Roundtrip Theorems ===== *)

(* Helper: abi_to_vyper_list in terms of OPT_MMAP *)
Theorem abi_to_vyper_list_OPT_MMAP:
  ∀ts vs. abi_to_vyper_list env ts vs =
    if LENGTH ts = LENGTH vs then
      OPT_MMAP (UNCURRY (abi_to_vyper env)) (ZIP (ts, vs))
    else NONE
Proof
  Induct \\ rw[abi_to_vyper_def]
  \\ Cases_on `vs` \\ gvs[abi_to_vyper_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

(* Bytes encoding roundtrip: n2w o ORD o CHR o w2n = id for word8 *)
Theorem bytes_encode_decode_roundtrip:
  ∀bs:word8 list. MAP ((n2w:num->word8) o ORD o CHR o w2n) bs = bs
Proof
  Induct \\ simp[]
  \\ rw[]
  \\ ASSUME_TAC (Q.SPEC `h` (INST_TYPE [``:α`` |-> ``:8``] w2n_lt))
  \\ gvs[dimword_8, ORD_CHR]
QED

Theorem bytes_encode_decode_roundtrip':
  ∀bs:word8 list. MAP (n2w o ORD) (MAP (CHR o w2n) bs) = bs
Proof
  rw[MAP_MAP_o, o_DEF]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ rw[GSYM o_DEF, bytes_encode_decode_roundtrip]
QED

(* ===== Helper Lemmas for Roundtrip Theorems ===== *)

Theorem within_int_bound_Unsigned_dimword:
  within_int_bound (Unsigned n) (&m) ⇒ m < 2 ** n
Proof
  rw[within_int_bound_def]
QED

Theorem vyper_to_abi_list_OPT_MMAP:
  !ts vs. vyper_to_abi_list env ts vs =
  if LENGTH ts = LENGTH vs then
    OPT_MMAP (UNCURRY (vyper_to_abi env)) (ZIP (ts,vs))
  else NONE
Proof
  Induct \\ rw[vyper_to_abi_def]
  \\ Cases_on `vs` \\ gvs[vyper_to_abi_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

Theorem vyper_to_abi_same_OPT_MMAP:
  !vs. vyper_to_abi_same env t vs =
    OPT_MMAP (vyper_to_abi env t) vs
Proof
  Induct \\ rw[vyper_to_abi_def]
  \\ Cases_on `vs` \\ gvs[vyper_to_abi_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

(* Helper 2: vyper_to_abi_same equals vyper_to_abi_list with REPLICATE *)
Theorem vyper_to_abi_same_REPLICATE:
  ∀env t vs avs.
    vyper_to_abi_list env (REPLICATE (LENGTH vs) t) vs = SOME avs ⇒
    vyper_to_abi_same env t vs = SOME avs
Proof
  rw[vyper_to_abi_list_OPT_MMAP, vyper_to_abi_same_OPT_MMAP]
  \\ pop_assum $ SUBST1_TAC o SYM
  \\ Induct_on `vs` \\ rw[]
QED

(* Helper 4: Default value inverse - if decoding gives default, input was default encoding *)
Theorem abi_to_vyper_default_value_inv_mutual:
  (∀env t av v. abi_to_vyper env t av = SOME v ⇒
                ∀tv. evaluate_type env t = SOME tv ⇒
                     v = default_value tv ⇒ av = default_to_abi tv) ∧
  (∀env ts avs vs. abi_to_vyper_list env ts avs = SOME vs ⇒
                   ∀tvs. OPT_MMAP (evaluate_type env) ts = SOME tvs ⇒
                         vs = MAP default_value tvs ⇒ avs = MAP default_to_abi tvs)
Proof
  ho_match_mp_tac abi_to_vyper_ind
  \\ rw[]
  \\ gvs[evaluate_type_def, abi_to_vyper_def, default_value_def, default_to_abi_def,
         check_IntV_def, AllCaseEqs(), within_int_bound_def, compatible_bound_def,
         make_array_value_def, default_value_tuple_MAP, ETA_AX, NULL_EQ,
         default_value_struct_MAP, evaluate_types_OPT_MMAP,
         default_to_abi_list_MAP, default_to_abi_fields_MAP]
  >- (
    first_x_assum(mp_tac o Q.AP_TERM`word_of_bytes T (0w:address)`)
    \\ DEP_REWRITE_TAC[word_of_bytes_word_to_bytes]
    \\ rw[divides_def] )
  \\ TRY (
    rename1`BytesT bd`
    \\ Cases_on `bd` \\ gvs[default_value_def, default_to_abi_def] )
  \\ TRY (
    Cases_on `b`
    \\ gvs[evaluate_type_def, abi_to_vyper_def, default_value_def,
           default_to_abi_def, check_IntV_def, AllCaseEqs(),
           within_int_bound_def, compatible_bound_def,
           make_array_value_def, default_value_tuple_MAP, ETA_AX, NULL_EQ,
           default_value_struct_MAP, evaluate_types_OPT_MMAP,
           OPT_MMAP_SOME_IFF, abi_to_vyper_list_OPT_MMAP, ZIP_EQ_NIL]
    \\ first_x_assum irule
    \\ rw[LIST_EQ_REWRITE, EL_MAP, EL_REPLICATE, EL_ZIP]
    \\ gvs[NIL_NO_MEM, FORALL_PROD, MEM_enumerate_static_array_iff]
    \\ first_x_assum(qspec_then`x`mp_tac) \\ rw[EL_MAP, EL_ZIP, EL_REPLICATE])
 \\ gvs[OPT_MMAP_SOME_IFF, ZIP_MAP, abi_to_vyper_list_OPT_MMAP]
 \\ gvs[MAP_MAP_o, o_DEF]
 \\ gvs[LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
QED

(* Original single-type version with partial proof *)
Theorem abi_to_vyper_default_value_inv:
  ∀env t tv av.
    evaluate_type env t = SOME tv ∧
    abi_to_vyper env t av = SOME (default_value tv) ⇒
    av = default_to_abi tv
Proof
  metis_tac[abi_to_vyper_default_value_inv_mutual]
QED

(* Helper: vyper_to_abi_sparse only depends on ALOOKUP for indices < n *)
Theorem vyper_to_abi_sparse_ALOOKUP_cong:
  ∀n env t tv sparse1 sparse2.
    (∀i. i < n ⇒ ALOOKUP sparse1 i = ALOOKUP sparse2 i) ⇒
    vyper_to_abi_sparse env t tv n sparse1 = vyper_to_abi_sparse env t tv n sparse2
Proof
  Induct_on `n` \\ rw[vyper_to_abi_def]
  \\ simp[Once vyper_to_abi_def]
  \\ `vyper_to_abi_sparse env t tv n sparse1 = vyper_to_abi_sparse env t tv n sparse2`
      by (first_x_assum irule \\ rw[])
  \\ `ALOOKUP sparse1 n = ALOOKUP sparse2 n` by gvs[]
  \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum SUBST_ALL_TAC
  \\ rw[]
QED

(* Corollary: vyper_to_abi_sparse for full vs' = for TAKE n vs' *)
Theorem vyper_to_abi_sparse_TAKE:
  ∀n env t tv d vs'. n ≤ LENGTH vs' ⇒
    vyper_to_abi_sparse env t tv n (enumerate_static_array d 0 vs') =
    vyper_to_abi_sparse env t tv n (enumerate_static_array d 0 (TAKE n vs'))
Proof
  rw[]
  \\ irule vyper_to_abi_sparse_ALOOKUP_cong
  \\ rw[]
  \\ irule enumerate_ALOOKUP_TAKE
  \\ gvs[]
QED

(* Helper 5: vyper_to_abi_sparse reconstruction *)
Theorem vyper_to_abi_sparse_correct:
  ∀env t tv n vs' vs.
    LENGTH vs' = n ∧
    LENGTH vs = n ∧
    evaluate_type env t = SOME tv ∧
    (∀i. i < n ⇒ abi_to_vyper env t (EL i vs) = SOME (EL i vs')) ∧
    (∀i. i < n ⇒ vyper_to_abi env t (EL i vs') = SOME (EL i vs)) ⇒
    vyper_to_abi_sparse env t tv n (enumerate_static_array (default_value tv) 0 vs') = SOME vs
Proof
  Induct_on `n`
  (* Base case *)
  >- (rw[vyper_to_abi_def] \\ gvs[LENGTH_EQ_NUM_compute])
  (* Inductive case *)
  \\ rw[]
  \\ simp[Once vyper_to_abi_def, CaseEq"option"]
  (* Rewrite recursive call using TAKE lemma *)
  \\ `vyper_to_abi_sparse env t tv n (enumerate_static_array (default_value tv) 0 vs') =
      vyper_to_abi_sparse env t tv n (enumerate_static_array (default_value tv) 0 (TAKE n vs'))`
      by (irule vyper_to_abi_sparse_TAKE \\ gvs[])
  \\ pop_assum SUBST_ALL_TAC
  (* Apply IH *)
  \\ `vyper_to_abi_sparse env t tv n (enumerate_static_array (default_value tv) 0 (TAKE n vs')) =
      SOME (TAKE n vs)` by (first_x_assum irule \\ rw[LENGTH_TAKE, EL_TAKE])
  (* Witness: TAKE n vs *)
  \\ qexists_tac `TAKE n vs` \\ gvs[]
  (* ALOOKUP at index n *)
  \\ `ALOOKUP (enumerate_static_array (default_value tv) 0 vs') n =
      if EL n vs' = default_value tv then NONE else SOME (EL n vs')` by (
       `ALOOKUP (enumerate_static_array (default_value tv) 0 vs') (0 + n) =
        if EL n vs' = default_value tv then NONE else SOME (EL n vs')` suffices_by gvs[]
       \\ irule enumerate_static_array_ALOOKUP \\ gvs[])
  (* Case split *)
  \\ Cases_on `EL n vs' = default_value tv`
  (* Case 1: EL n vs' = default_value tv - need abi_to_vyper_default_value_inv *)
  >- (disj1_tac \\ gvs[]
      \\ `abi_to_vyper env t (EL n vs) = SOME (default_value tv)` by gvs[]
      \\ `EL n vs = default_to_abi tv` by (
          irule abi_to_vyper_default_value_inv \\ qexists_tac `env` \\ qexists_tac `t` \\ gvs[])
      \\ `TAKE n vs ++ [EL n vs] = vs` suffices_by gvs[]
      \\ irule TAKE_SNOC_EL \\ gvs[])
  (* Case 2: EL n vs' ≠ default_value tv - use vyper_to_abi directly *)
  \\ disj2_tac
  \\ qexists_tac `EL n vs'`
  \\ conj_tac >- gvs[]
  \\ qexists_tac `EL n vs`
  \\ conj_tac >- gvs[]
  \\ irule TAKE_SNOC_EL \\ gvs[]
QED

(* Helper 6: Element-wise correspondence from list operations *)
Theorem abi_to_vyper_list_EL:
  ∀env ts avs vs.
    abi_to_vyper_list env ts avs = SOME vs ⇒
    LENGTH ts = LENGTH avs ∧
    LENGTH vs = LENGTH avs ∧
    (∀i. i < LENGTH avs ⇒ abi_to_vyper env (EL i ts) (EL i avs) = SOME (EL i vs))
Proof
  rw[abi_to_vyper_list_OPT_MMAP]
  \\ gvs[OPT_MMAP_SOME_IFF]
  \\ rw[EL_MAP, EL_ZIP]
  \\ gvs[EVERY_MEM, MEM_ZIP, MEM_MAP, PULL_EXISTS, IS_SOME_EXISTS]
  \\ res_tac \\ gvs[]
QED

Theorem vyper_to_abi_list_EL:
  ∀env ts vs avs.
    vyper_to_abi_list env ts vs = SOME avs ⇒
    LENGTH ts = LENGTH vs ∧
    LENGTH avs = LENGTH vs ∧
    (∀i. i < LENGTH vs ⇒ vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs))
Proof
  rw[vyper_to_abi_list_OPT_MMAP]
  \\ gvs[OPT_MMAP_SOME_IFF]
  \\ rw[EL_MAP, EL_ZIP]
  \\ gvs[EVERY_MEM, MEM_ZIP, MEM_MAP, PULL_EXISTS, IS_SOME_EXISTS]
  \\ res_tac \\ gvs[]
QED

(* ===== Encoding default values ===== *)

(* Helper: sparse encoding with empty sparse list fills all slots with defaults.
   Simple induction on n. *)
Theorem vyper_to_abi_sparse_empty:
  ∀n env t tv. vyper_to_abi_sparse env t tv n [] = SOME (REPLICATE n (default_to_abi tv))
Proof
  Induct \\ rw[vyper_to_abi_def]
  \\ rw[LIST_EQ_REWRITE, EL_APPEND_EQN]
  \\ rw[EL_REPLICATE]
  \\ Cases_on `x` \\ gvs[EL_REPLICATE]
  \\ rw[iffRL SUB_EQ_0]
QED

(* Main theorem: encoding default_value gives the same result as default_to_abi.
   This justifies that default_to_abi is not a separate concept - it's just
   a shortcut that avoids creating intermediate Vyper values. *)
Theorem vyper_to_abi_default_value:
  (∀env t tv. evaluate_type env t = SOME tv ⇒
              vyper_to_abi env t (default_value tv) = SOME (default_to_abi tv)) ∧
  (∀env ts acc tvs. evaluate_types env ts acc = SOME tvs ⇒
    vyper_to_abi_list env ts (MAP default_value (DROP (LENGTH acc) tvs)) =
      SOME (MAP default_to_abi (DROP (LENGTH acc) tvs)))
Proof
  ho_match_mp_tac evaluate_type_ind
  (* BaseT bt: direct computation, AddressT needs word_of_bytes_word_to_bytes *)
  \\ conj_tac >- (
    rw[evaluate_type_def]
    \\ gvs[CaseEq"base_type", vyper_to_abi_base_def, default_value_def,
           default_to_abi_def, CaseEq"bound", word_of_bytes_be_def] \\
    DEP_REWRITE_TAC[word_of_bytes_word_to_bytes] \\
    rw[divides_def] )
  (* TupleT ts: use IH on list, default_value_tuple_MAP *)
  \\ conj_tac >- (
    rw[evaluate_type_def, vyper_to_abi_def, CaseEq"option"] \\ gvs[]
    \\ gvs[vyper_to_abi_def, default_value_def, default_to_abi_def,
          default_to_abi_list_MAP]
    \\ rw[default_value_tuple_MAP, vyper_to_abi_def, ETA_AX] )
  (* ArrayT t bd: Dynamic is trivial, Fixed uses vyper_to_abi_sparse_empty *)
  \\ conj_tac >- (
    Cases_on `bd` \\ rw[evaluate_type_def, CaseEq"option"]
    \\ gvs[default_to_abi_def, default_value_def]
    \\ rw[vyper_to_abi_sparse_empty] )
  (* StructT id: use IH on field types, default_value_struct_MAP *)
  \\ conj_tac >- (
    rw[evaluate_type_def, CaseEq"type_args", CaseEq"option"]
    \\ gvs[default_value_def, default_to_abi_def, default_value_struct_MAP,
          default_to_abi_fields_MAP]
    \\ gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF]
    \\ gvs[MAP_ZIP, ZIP_MAP, MAP_MAP_o, o_DEF] )
  (* FlagT id: direct computation *)
  \\ conj_tac >- (
    rw[evaluate_type_def, CaseEq"option", CaseEq"type_args"]
    \\ gvs[default_value_def, default_to_abi_def] )
  (* NoneT: direct computation *)
  (* evaluate_types [] acc: trivial *)
  (* evaluate_types (t::ts) acc: list induction using single-type IH *)
  \\ rw[evaluate_type_def, CaseEq"option"]
  \\ gvs[default_value_def, default_to_abi_def, DROP_LENGTH_TOO_LONG]
  \\ gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF, DROP_APPEND, iffRL SUB_EQ_0]
  \\ gvs[DROP_LENGTH_TOO_LONG]
QED

(* ===== Main Roundtrip Theorem: abi_to_vyper then vyper_to_abi ===== *)

(* Helper for word8 bounds *)
val w2n_lt_256 = REWRITE_RULE [EVAL ``dimword (:8)``]
  (INST_TYPE [``:'a`` |-> ``:8``] w2n_lt);

Theorem abi_to_vyper_vyper_to_abi:
  (∀env ty av v. abi_to_vyper env ty av = SOME v ⇒ vyper_to_abi env ty v = SOME av) ∧
  (∀env tys avs vs. abi_to_vyper_list env tys avs = SOME vs ⇒ vyper_to_abi_list env tys vs = SOME avs)
Proof
  ho_match_mp_tac abi_to_vyper_ind \\ rw[]
  \\ gvs[abi_to_vyper_def, vyper_to_abi_def, vyper_to_abi_base_def,
         check_IntV_def, AllCaseEqs(),
         integerTheory.NUM_OF_INT, bytes_encode_decode_roundtrip', NULL_EQ]
  (* AddressT: need word roundtrip *)
  >- (drule within_int_bound_Unsigned_dimword
      \\ rw[word_of_bytes_be_def]
      \\ DEP_REWRITE_TAC[word_of_bytes_word_to_bytes]
      \\ gvs[dimword_def, divides_def])
  (* StringT: need MAP for CHR/ORD roundtrip on word8 list *)
  >- (gvs[n2w_o_ORD_def, MAP_MAP_o, o_DEF, ORD_CHR_RWT, w2n_lt_256, n2w_w2n])
  (* ArrayT: Fixed and Dynamic cases - case split on the bound *)
  >- (gvs[AllCaseEqs(), vyper_to_abi_def]
      \\ Cases_on `b`
      \\ gvs[make_array_value_def]
      (* Fixed case: need vyper_to_abi_sparse reconstruction *)
      >- (drule abi_to_vyper_list_EL \\ rw[]
          \\ gvs[compatible_bound_def]
          \\ `vyper_to_abi_sparse env t tv (LENGTH avs)
                (enumerate_static_array (default_value tv) 0 vs') = SOME avs`
             suffices_by rw[]
          \\ irule vyper_to_abi_sparse_correct
          \\ drule vyper_to_abi_list_EL \\ rw[]
          \\ gvs[EL_REPLICATE])
      (* Dynamic case: need vyper_to_abi_same from vyper_to_abi_list *)
      >- (drule abi_to_vyper_list_EL \\ rw[]
          \\ gvs[vyper_to_abi_def]
          \\ `vyper_to_abi_same env t vs' = SOME avs` suffices_by rw[]
          \\ irule vyper_to_abi_same_REPLICATE
          \\ gvs[]))
  (* StructT: need MAP SND (ZIP ...) = vs' *)
  >- (drule abi_to_vyper_list_EL \\ rw[]
      \\ gvs[MAP_ZIP])
QED
