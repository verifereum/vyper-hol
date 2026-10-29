(*
 * Entry argument decoding: static complex arguments (#639)
 *
 * TOP-LEVEL:
 *   abi_dec_plan — what a decode info must be for a static type, as
 *     abi_enc_plan is for encoding
 *   abi_dec_plan_value — for a value of the type, a plan is static, its
 *     clamps accept the value's encoding wherever it sits, and memory
 *     holding the encoding holds the value (the converse of
 *     val_in_memory_static_abi)
 *   compile_abi_decode_static_buf_correct — compile_abi_decode_to_buf from
 *     calldata holding a static value's encoding leaves the value in
 *     memory at the destination, without reverting
 *   calldata_encodes_static_arg — calldata that encodes a call holds a
 *     static argument's encoding at the argument's head offset
 *   compile_decode_static_arg_correct — the static, non-word path of
 *     compile_decode_args (tuples, structs, static arrays): the argument
 *     ends in memory at its ALLOCA (val_in_memory)
 *   type_to_abi_dec_info_word_plan — a word type's decode info is a plan
 *   type_to_abi_dec_info_word_tuple_plan,
 *   type_to_abi_dec_info_word_sarray_plan — so is that of a tuple of word
 *     types and of a static array of a word type (abi_dec_plan is not
 *     vacuous for the infos the compiler builds)
 *
 * Helpers: dec_value, decs_value, sparse_val and their lemmas.
 *
 * Not here: that type_to_abi_dec_info builds plans for every static
 * complex type (structs, nested aggregates), and that the decoder's head
 * offsets (abi_embedded_static_size) match the ABI's for them.  Both
 * need the compile env's struct metadata and sizes (ce_struct_fields,
 * type_memory_bytes, abi_embedded_static_size) to agree with the type
 * environment, as the encoder's plans do (abi_enc_plan).  For a word
 * type the plan follows from word_arg_clamp_ok
 * (type_to_abi_dec_info_word_plan).
 *)
Theory entryDecodeStaticProps
Ancestors
  arithmetic list rich_list words sorting alist
  abiDecodeStaticProps entryDecodeProps entryDispatchProps moduleLoweringProps
  valueEncodingProofs valueEncodingProps valueEncoding
  vyperABI vyperABIRoundtrip vyperTyping vyperTypeDefaults vyperTypeABI
  vyperValue vfmTypes
  compileEnv exprLowering moduleLowering selectorDispatch
  emitHelperProps fragExec venomState
Libs
  wordsLib

(* ===== Decode plans ===== *)

(* abi_dec_plan env ty info: info decodes a static value of type ty in type
   environment env.  A word's clamp accepts every value of its type; an
   aggregate's elements are its components in order (a struct's typed in
   env \\ nsid, as vyper_to_abi_type does), each taking its memory size in
   the ABI head; a static array repeats its element's plan.  Dynamic types
   have no plan here. *)
Inductive abi_dec_plan:
[~prim:]
  is_word_type ty /\
  (!tv v. evaluate_type env ty = SOME tv /\ value_has_type tv v ==>
          abi_clamp_ok c (typed_val_to_w256 tv v)) ==>
  abi_dec_plan env ty (DecPrimWord c)
[~tuple:]
  abi_dec_plans env ts elems ==>
  abi_dec_plan env (TupleT ts) (DecComplex F elems)
[~sarray:]
  evaluate_type env t = SOME tv /\ abi_dec_plan env t ei ==>
  abi_dec_plan env (ArrayT t (Fixed n))
    (DecComplex F
       (REPLICATE n (ei, type_memory_size tv, type_memory_size tv)))
[~struct:]
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_dec_plans (env \\ nsid) (MAP SND args) elems ==>
  abi_dec_plan env (StructT nsid) (DecComplex F elems)
[~nil:]
  abi_dec_plans env [] []
[~cons:]
  evaluate_type env t = SOME tv /\ abi_dec_plan env t ei /\
  abi_dec_plans env ts elems ==>
  abi_dec_plans env (t::ts)
    ((ei, type_memory_size tv, type_memory_size tv) :: elems)
End

(* A word type's decode info is a plan, under word_arg_clamp_ok's
   premises. *)
Theorem type_to_abi_dec_info_word_plan:
  !tenv sfields cenv ty.
    is_word_type ty /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_dec_plan tenv ty (type_to_abi_dec_info sfields cenv ty)
Proof
  rpt strip_tac >>
  `?c. type_to_abi_dec_info sfields cenv ty = DecPrimWord c` by
    (Cases_on `ty` >> gvs[is_word_type_def, type_to_abi_dec_info_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_word_type_def, type_to_abi_dec_info_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_word_type_def, type_to_abi_dec_info_def]) >>
  simp[] >> irule abi_dec_plan_prim >> rw[] >>
  drule_all word_arg_clamp_ok >>
  disch_then (qspec_then `sfields` mp_tac) >> simp[]
QED

(* ===== What a plan decodes ===== *)

(* The facts abi_dec_plan_value gives for a value v of type tv with ABI
   value av, decoded by info. *)
Definition dec_value_def:
  dec_value env ty tv v av info <=>
    ~is_dynamic (vyper_to_abi_type env ty) /\
    LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv /\
    static_dec info (type_memory_size tv) /\
    (!cd off. mem_bytes_at off (type_memory_size tv) cd =
              enc (vyper_to_abi_type env ty) av ==> dec_ok info cd off) /\
    (!off mem. mem_bytes_at off (type_memory_size tv) mem =
               enc (vyper_to_abi_type env ty) av ==>
               val_in_memory tv v off mem)
End

Definition decs_value_def:
  decs_value env ts tvs vs avs elems <=>
    LENGTH avs = LENGTH ts /\
    EVERY is_static (vyper_to_abi_types env ts) /\
    LENGTH (FLAT (MAP2 enc (vyper_to_abi_types env ts) avs)) =
      SUM (MAP type_memory_size tvs) /\
    static_decs elems (SUM (MAP type_memory_size tvs)) /\
    (!cd off. mem_bytes_at off (SUM (MAP type_memory_size tvs)) cd =
              FLAT (MAP2 enc (vyper_to_abi_types env ts) avs) ==>
              decs_ok elems cd off) /\
    (!off mem. mem_bytes_at off (SUM (MAP type_memory_size tvs)) mem =
               FLAT (MAP2 enc (vyper_to_abi_types env ts) avs) ==>
               tuple_in_memory vs tvs off mem)
End

Theorem word_type_memory_size:
  !env ty tv.
    is_word_type ty /\ evaluate_type env ty = SOME tv ==>
    type_memory_size tv = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def]
  >~ [`FlagT`] >- simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS,
                       type_memory_size_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, evaluate_type_def, type_memory_size_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, evaluate_type_def, type_memory_size_def]
QED

Theorem mem_bytes_at_word_eq:
  !off mem (w : bytes32).
    mem_bytes_at off 32 mem = word_to_bytes w T <=> mem_word_at off mem = w
Proof
  rw[mem_bytes_at_word] >> eq_tac >> rw[] >>
  pop_assum (mp_tac o Q.AP_TERM `word_of_bytes T (0w : bytes32)`) >>
  simp[word_to_bytes_word_of_bytes_256]
QED

Theorem mem_bytes_at_split_eq:
  !off m n mem x y.
    LENGTH x = m /\ mem_bytes_at off (m + n) mem = x ++ y ==>
    mem_bytes_at off m mem = x /\ mem_bytes_at (off + m) n mem = y
Proof
  rpt gen_tac >> strip_tac >> fs[mem_bytes_at_split_padded] >>
  `LENGTH (mem_bytes_at off m mem) = LENGTH x` by simp[] >>
  metis_tac[APPEND_11_LENGTH]
QED

Theorem word_dec_value:
  !env ty tv v av c.
    is_word_type ty /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    abi_clamp_ok c (typed_val_to_w256 tv v) ==>
    dec_value env ty tv v av (DecPrimWord c)
Proof
  rpt strip_tac >> drule_all vyper_to_abi_word_enc >> strip_tac >>
  drule_all word_type_memory_size >> strip_tac >>
  simp[dec_value_def, dec_ok_def, static_dec_prim, mem_bytes_at_word_eq,
       venomMemPropsTheory.dimindex_256] >>
  metis_tac[val_in_memory_word]
QED

(* ===== Plans of word aggregates ===== *)

Theorem word_type_dec_sizes:
  !sfields cenv ty.
    is_word_type ty ==>
    ~is_abi_dynamic sfields ty /\ abi_embedded_static_size sfields ty = 32 /\
    type_memory_bytes cenv ty = 32
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[is_word_type_def, is_abi_dynamic_def, type_memory_bytes_def,
       abi_embedded_static_size_word] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, is_abi_dynamic_def, type_memory_bytes_def,
       abi_embedded_static_size_word] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, is_abi_dynamic_def, type_memory_bytes_def,
       abi_embedded_static_size_word]
QED

Theorem type_to_abi_dec_info_word_plans:
  !tenv sfields cenv ts.
    EVERY (\t. is_word_type t /\ IS_SOME (evaluate_type tenv t)) ts /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_dec_plans tenv ts
      (MAP (\t. (type_to_abi_dec_info sfields cenv t,
                 abi_embedded_static_size cenv.ce_struct_fields t,
                 type_memory_bytes cenv t)) ts)
Proof
  rpt gen_tac >> Induct_on `ts` >> simp[abi_dec_plan_nil] >>
  rpt strip_tac >> rename1 `is_word_type h` >>
  `?tv. evaluate_type tenv h = SOME tv` by
    (Cases_on `evaluate_type tenv h` >> fs[]) >>
  drule_all word_type_memory_size >> strip_tac >>
  qspecl_then [`cenv.ce_struct_fields`, `cenv`, `h`] mp_tac
    word_type_dec_sizes >>
  simp[] >> strip_tac >>
  `abi_dec_plans tenv (h::ts)
     ((type_to_abi_dec_info sfields cenv h, type_memory_size tv,
       type_memory_size tv) ::
      MAP (\t. (type_to_abi_dec_info sfields cenv t,
                abi_embedded_static_size cenv.ce_struct_fields t,
                type_memory_bytes cenv t)) ts)` suffices_by simp[] >>
  irule abi_dec_plan_cons >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (irule type_to_abi_dec_info_word_plan >> rpt conj_tac >>
      first_assum ACCEPT_TAC) >>
  first_x_assum irule >> simp[]
QED

(* Non-vacuity: the decode info type_to_abi_dec_info builds for a tuple of
   word types is a plan. *)
Theorem type_to_abi_dec_info_word_tuple_plan:
  !tenv sfields cenv ts.
    EVERY (\t. is_word_type t /\ IS_SOME (evaluate_type tenv t)) ts /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_dec_plan tenv (TupleT ts)
      (type_to_abi_dec_info sfields cenv (TupleT ts))
Proof
  rpt strip_tac >>
  `~EXISTS (is_abi_dynamic cenv.ce_struct_fields) ts` by
    (fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[word_type_dec_sizes]) >>
  simp[Once type_to_abi_dec_info_def] >> irule abi_dec_plan_tuple >>
  irule type_to_abi_dec_info_word_plans >> simp[]
QED

(* Non-vacuity: so is the decode info of a static array of a word type. *)
Theorem type_to_abi_dec_info_word_sarray_plan:
  !tenv sfields cenv t n.
    is_word_type t /\ IS_SOME (evaluate_type tenv t) /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_dec_plan tenv (ArrayT t (Fixed n))
      (type_to_abi_dec_info sfields cenv (ArrayT t (Fixed n)))
Proof
  rpt strip_tac >>
  `?tv. evaluate_type tenv t = SOME tv` by
    (Cases_on `evaluate_type tenv t` >> fs[]) >>
  drule_all word_type_memory_size >> strip_tac >>
  qspecl_then [`cenv.ce_struct_fields`, `cenv`, `t`] mp_tac
    word_type_dec_sizes >>
  simp[Once type_to_abi_dec_info_def, GSYM REPLICATE_GENLIST] >>
  strip_tac >>
  `abi_dec_plan tenv (ArrayT t (Fixed n))
     (DecComplex F (REPLICATE n (type_to_abi_dec_info sfields cenv t,
                                 type_memory_size tv, type_memory_size tv)))`
    suffices_by simp[] >>
  irule abi_dec_plan_sarray >> conj_tac
  >- first_assum ACCEPT_TAC >>
  irule type_to_abi_dec_info_word_plan >> rpt conj_tac >>
  first_assum ACCEPT_TAC
QED

(* ===== Tuples, structs and static arrays ===== *)

Theorem decs_value_nil:
  !env. decs_value env [] [] [] [] []
Proof
  simp[decs_value_def, static_dec_nil, dec_ok_def, val_in_memory_def]
QED

Theorem decs_value_cons:
  !env t tv v av ei ts tvs vs avs elems.
    dec_value env t tv v av ei /\ decs_value env ts tvs vs avs elems ==>
    decs_value env (t::ts) (tv::tvs) (v::vs) (av::avs)
      ((ei, type_memory_size tv, type_memory_size tv)::elems)
Proof
  rpt gen_tac >> simp[dec_value_def, decs_value_def] >> strip_tac >>
  `static_decs ((ei, type_memory_size tv, type_memory_size tv)::elems)
     (type_memory_size tv + SUM (MAP type_memory_size tvs))` by
    (irule static_dec_cons >> simp[]) >>
  `!mem off.
     mem_bytes_at off (type_memory_size tv + SUM (MAP type_memory_size tvs))
       mem =
     enc (vyper_to_abi_type env t) av ++
     FLAT (MAP2 enc (vyper_to_abi_types env ts) avs) ==>
     mem_bytes_at off (type_memory_size tv) mem =
       enc (vyper_to_abi_type env t) av /\
     mem_bytes_at (off + type_memory_size tv) (SUM (MAP type_memory_size tvs))
       mem = FLAT (MAP2 enc (vyper_to_abi_types env ts) avs)` by
    (rpt gen_tac >> strip_tac >> irule mem_bytes_at_split_eq >> simp[]) >>
  fs[dec_ok_def, val_in_memory_def] >> metis_tac[]
QED

Theorem decs_value_tuple:
  !env ts tvs vs avs elems.
    decs_value env ts tvs vs avs elems ==>
    dec_value env (TupleT ts) (TupleTV tvs) (ArrayV (TupleV vs)) (ListV avs)
      (DecComplex F elems)
Proof
  rw[decs_value_def, dec_value_def, any_dynamic_every_static,
     type_memory_size_def, type_memory_size_list_sum, dec_ok_def,
     val_in_memory_def] >>
  `LENGTH (vyper_to_abi_types env ts) = LENGTH avs` by
    simp[vyper_to_abi_types_length] >>
  gvs[enc_tuple_static_acc, static_dec_complex]
QED

Theorem decs_value_struct:
  !env nsid args tvs fields avs elems.
    FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
    decs_value (env \\ nsid) (MAP SND args) tvs (MAP SND fields) avs elems ==>
    dec_value env (StructT nsid) (StructTV (ZIP (MAP FST args, tvs)))
      (StructV fields) (ListV avs) (DecComplex F elems)
Proof
  rw[decs_value_def, dec_value_def, any_dynamic_every_static,
     type_memory_size_def, type_memory_size_fields_sum, dec_ok_def,
     val_in_memory_def, fields_in_memory_tuple] >>
  `LENGTH (vyper_to_abi_types (env \\ nsid) (MAP SND args)) = LENGTH avs` by
    simp[vyper_to_abi_types_length] >>
  `MAP (type_memory_size o SND) (ZIP (MAP FST args, tvs)) =
   MAP type_memory_size tvs` by simp[GSYM MAP_MAP_o, MAP_ZIP] >>
  gvs[enc_tuple_static_acc, static_dec_complex, MAP_ZIP]
QED

(* The element at index i of a sparse static array. *)
Definition sparse_val_def:
  sparse_val tv kvs (i : num) =
    case ALOOKUP kvs i of SOME v => v | NONE => default_value tv
End

Theorem vyper_to_abi_sparse_EL:
  !m env t tv sparse xs.
    vyper_to_abi_sparse env t tv m sparse = SOME xs /\
    evaluate_type env t = SOME tv ==>
    LENGTH xs = m /\
    !i. i < m ==>
        vyper_to_abi env t (sparse_val tv sparse i) = SOME (EL i xs)
Proof
  Induct >> simp[Once vyper_to_abi_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule_all >> strip_tac >>
  simp[] >> rpt strip_tac >>
  `i < m \/ i = m` by decide_tac >>
  gvs[EL_APPEND1, EL_APPEND2, sparse_val_def] >>
  metis_tac[cj 1 vyper_to_abi_default_value]
QED

Theorem sparse_val_has_type:
  !env t tv n sparse i.
    sparse_has_type tv n sparse /\ evaluate_type env t = SOME tv ==>
    value_has_type tv (sparse_val tv sparse i)
Proof
  rw[sparse_val_def] >> CASE_TAC
  >- metis_tac[default_value_has_type_thm] >>
  metis_tac[sparse_has_type_lookup]
QED

Theorem sorted_alookup_mem:
  !kvs k (v : value).
    SORTED $< (MAP FST kvs) /\ MEM (k, v) kvs ==> ALOOKUP kvs k = SOME v
Proof
  rpt strip_tac >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[] >>
  irule SORTED_ALL_DISTINCT >> qexists_tac `$<` >>
  simp[relationTheory.irreflexive_def, relationTheory.transitive_def]
QED

Theorem kvs_in_memory_intro:
  !kvs off tv mem.
    (!k v. MEM (k, v) kvs ==>
           val_in_memory tv v (off + k * type_memory_size tv) mem) ==>
    kvs_in_memory kvs off tv mem
Proof
  Induct >> simp[val_in_memory_def] >> Cases >>
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem tuple_in_memory_replicate:
  !vs tv off mem i.
    tuple_in_memory vs (REPLICATE (LENGTH vs) tv) off mem /\ i < LENGTH vs ==>
    val_in_memory tv (EL i vs) (off + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[] >>
  first_x_assum drule_all >> simp[MULT_CLAUSES]
QED

Theorem vyper_to_abi_types_REPLICATE:
  !n env t.
    vyper_to_abi_types env (REPLICATE n t) =
    REPLICATE n (vyper_to_abi_type env t)
Proof
  Induct >> simp[vyper_to_abi_type_def]
QED

Theorem decs_value_replicate:
  !avs env t tv ei vs.
    LENGTH vs = LENGTH avs /\
    (!i. i < LENGTH avs ==> dec_value env t tv (EL i vs) (EL i avs) ei) ==>
    decs_value env (REPLICATE (LENGTH avs) t) (REPLICATE (LENGTH avs) tv)
      vs avs
      (REPLICATE (LENGTH avs) (ei, type_memory_size tv, type_memory_size tv))
Proof
  Induct >> rpt gen_tac >> Cases_on `vs` >> simp[decs_value_nil] >>
  strip_tac >> irule decs_value_cons >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem decs_value_sarray:
  !env t tv n sparse avs ei.
    (!i. i < n ==> dec_value env t tv (sparse_val tv sparse i) (EL i avs) ei) /\
    dec_value env t tv (default_value tv) (default_to_abi tv) ei /\
    LENGTH avs = n /\ SORTED $< (MAP FST sparse) /\
    sparse_has_type tv n sparse ==>
    dec_value env (ArrayT t (Fixed n)) (ArrayTV tv (Fixed n))
      (ArrayV (SArrayV sparse)) (ListV avs)
      (DecComplex F
         (REPLICATE n (ei, type_memory_size tv, type_memory_size tv)))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`avs`, `env`, `t`, `tv`, `ei`,
               `GENLIST (sparse_val tv sparse) n`] mp_tac decs_value_replicate >>
  impl_tac >- (gvs[] >> decide_tac) >>
  qpat_x_assum `dec_value _ _ _ (default_value _) _ _` mp_tac >>
  rw[decs_value_def, dec_value_def, vyper_to_abi_types_REPLICATE,
     map_replicate, SUM_REPLICATE, type_memory_size_def, dec_ok_def,
     static_dec_complex] >>
  gvs[enc_tuple_static_acc, EVERY_REPLICATE] >>
  `!i. i < LENGTH avs ==>
       val_in_memory tv (sparse_val tv sparse i)
         (off + i * type_memory_size tv) mem` by
    (rpt strip_tac >>
     qspecl_then [`GENLIST (sparse_val tv sparse) (LENGTH avs)`, `tv`, `off`,
                  `mem`, `i`] mp_tac tuple_in_memory_replicate >>
     simp[]) >>
  simp[val_in_memory_def] >> conj_tac
  >- (irule kvs_in_memory_intro >> rpt strip_tac >>
      drule sparse_has_type_all_less >>
      simp[EVERY_MEM, pairTheory.FORALL_PROD] >> disch_then drule >> strip_tac >>
      `ALOOKUP sparse k = SOME v` by metis_tac[sorted_alookup_mem] >>
      first_x_assum drule >> simp[sparse_val_def]) >>
  rpt strip_tac >> first_x_assum drule >> simp[sparse_val_def]
QED

(* ===== Plans decode values ===== *)

val inv_plan_tac =
  qpat_x_assum `abi_dec_plan _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_dec_plan_cases]);

val inv_plans_tac =
  qpat_x_assum `abi_dec_plans _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_dec_plan_cases]);

Theorem abi_dec_plan_value:
  (!env ty. !tv v av info.
     abi_dec_plan env ty info /\ evaluate_type env ty = SOME tv /\
     value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
     dec_value env ty tv v av info) /\
  (!env ts. !tvs vs avs elems.
     abi_dec_plans env ts elems /\ OPT_MMAP (evaluate_type env) ts = SOME tvs /\
     values_have_types tvs vs /\ vyper_to_abi_list env ts vs = SOME avs ==>
     decs_value env ts tvs vs avs elems)
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >> rpt conj_tac
  >- (rpt strip_tac >> inv_plan_tac >> gvs[] >> irule word_dec_value >> simp[])
  >- suspend "tuple"
  >- (rpt strip_tac >> inv_plan_tac >> gvs[is_word_type_def])
  >- suspend "array"
  >- suspend "struct"
  >- (rpt strip_tac >> inv_plan_tac >> gvs[] >> irule word_dec_value >> simp[])
  >- (rpt strip_tac >> inv_plan_tac >> gvs[is_word_type_def])
  >- (rpt strip_tac >> inv_plans_tac >> gvs[] >>
      Cases_on `vs` >> gvs[value_has_type_def, vyper_to_abi_def] >>
      simp[decs_value_nil])
  >> suspend "cons"
QED

Resume abi_dec_plan_value[tuple]:
  rpt strip_tac >> inv_plan_tac >> gvs[is_word_type_def] >>
  Cases_on `v` >>
  gvs[evaluate_type_def, vyper_to_abi_def, AllCaseEqs()] >>
  Cases_on `a` >>
  gvs[value_has_type_def, vyper_to_abi_def, evaluate_types_OPT_MMAP,
      AllCaseEqs()] >>
  irule decs_value_tuple >> first_x_assum irule >> simp[]
QED

Resume abi_dec_plan_value[array]:
  rpt strip_tac >> inv_plan_tac >> gvs[is_word_type_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `a` >> gvs[value_has_type_def, vyper_to_abi_def, AllCaseEqs()] >>
  drule_all vyper_to_abi_sparse_EL >> strip_tac >>
  irule decs_value_sarray >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[sparse_val_has_type, default_value_has_type_thm,
            cj 1 vyper_to_abi_default_value]
QED

Resume abi_dec_plan_value[struct]:
  rpt strip_tac >> inv_plan_tac >> gvs[is_word_type_def] >>
  Cases_on `v` >>
  gvs[evaluate_type_def, vyper_to_abi_def, AllCaseEqs()] >>
  gvs[evaluate_types_OPT_MMAP, value_has_type_def] >>
  drule struct_has_type_values_have_types >> strip_tac >>
  drule OPT_MMAP_LENGTH >> strip_tac >>
  irule decs_value_struct >> gvs[MAP_ZIP] >>
  first_x_assum irule >> gvs[MAP_ZIP]
QED

Resume abi_dec_plan_value[cons]:
  rpt strip_tac >> inv_plans_tac >> gvs[] >>
  Cases_on `vs` >>
  gvs[OPT_MMAP_def, vyper_to_abi_def, value_has_type_def, AllCaseEqs()] >>
  irule decs_value_cons >> simp[]
QED

Finalise abi_dec_plan_value

(* ===== Decoding a static value ===== *)

(* Calldata holding a static value's encoding at a decodes to the value in
   memory at p, without reverting. *)
Theorem compile_abi_decode_static_buf_correct:
  !env ty tv v av info dst src st st' ctx s0 p a.
    abi_dec_plan env ty info /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
      ((), st') /\
    eval_operand dst s0 = SOME p /\ eval_operand src s0 = SOME a /\
    fresh_vars_wrt st s0 /\
    w2n p + type_memory_size tv < dimword (:256) /\
    w2n a + type_memory_size tv < dimword (:256) /\
    mem_bytes_at (w2n a) (type_memory_size tv) s0.vs_call_ctx.cc_calldata =
      enc (vyper_to_abi_type env ty) av ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\ val_in_memory tv v (w2n p) t.vs_memory)
      (\r. F)
Proof
  rpt strip_tac >>
  drule_all (cj 1 abi_dec_plan_value) >> simp[dec_value_def] >> strip_tac >>
  drule_all compile_abi_decode_static_buf_frag >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  drule frag_exec_weaken >> disch_then irule >> rw[] >> gvs[]
QED

(* ===== Static arguments ===== *)

(* Calldata that encodes a call holds a static argument's encoding at the
   argument's head offset, after the 4-byte selector. *)
Theorem calldata_encodes_static_arg:
  !tenv fname tys vals cd i.
    calldata_encodes tenv fname tys vals cd /\ LENGTH vals = LENGTH tys /\
    i < LENGTH tys /\ ~is_dynamic (vyper_to_abi_type tenv (EL i tys)) ==>
    ?avs. vyper_to_abi_list tenv tys vals = SOME avs /\
          vyper_to_abi tenv (EL i tys) (EL i vals) = SOME (EL i avs) /\
          mem_bytes_at
            (4 + SUM (MAP2 abi_head_size
                        (TAKE i (vyper_to_abi_types tenv tys)) (TAKE i avs)))
            (LENGTH (enc (vyper_to_abi_type tenv (EL i tys)) (EL i avs))) cd =
          enc (vyper_to_abi_type tenv (EL i tys)) (EL i avs)
Proof
  rpt strip_tac >> gvs[calldata_encodes_def] >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  `vyper_to_abi tenv (EL i tys) (EL i vals) = SOME (EL i abi_vals)` by
    (first_x_assum irule >> decide_tac) >>
  simp[] >>
  qabbrev_tac `ats = vyper_to_abi_types tenv tys` >>
  `LENGTH ats = LENGTH tys /\ EL i ats = vyper_to_abi_type tenv (EL i tys)` by
    metis_tac[vyper_to_abi_types_EL] >>
  qabbrev_tac `e = enc (Tuple ats) (ListV abi_vals)` >>
  qabbrev_tac `k = SUM (MAP2 abi_head_size (TAKE i ats) (TAKE i abi_vals))` >>
  qabbrev_tac `ei = enc (vyper_to_abi_type tenv (EL i tys)) (EL i abi_vals)` >>
  `TAKE (LENGTH ei) (DROP k e) = ei` by
    (qspecl_then [`ats`, `abi_vals`, `i`] mp_tac enc_tuple_static_head >>
     impl_tac >- gvs[] >> gvs[Abbr `ei`]) >>
  `LENGTH ei <= LENGTH (DROP k e)` by
    (`LENGTH (TAKE (LENGTH ei) (DROP k e)) = LENGTH ei` by simp[] >>
     pop_assum mp_tac >> rw[LENGTH_TAKE_EQ]) >>
  fs[Abbr `e`] >>
  simp[mem_bytes_at_def, DROP_APPEND2, function_selector_length,
       TAKE_APPEND1]
QED

(* The static, non-word path of compile_decode_args for one calldata
   argument: the head pointer, then compile_abi_decode_to_buf. *)
Theorem compile_decode_static_arg_phases:
  !cenv name abi_size info off hi st st' loc dst.
    compile_decode_args cenv [(name, F, F, abi_size, info)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst ==>
    ?src st1.
      emit_op ADD [Lit 4w; Lit (n2w (off - 4))] st = (src, st1) /\
      compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st1 =
        ((), st')
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[oneTheory.one]
QED

Theorem decode_head_ptr_run:
  !off st src st1 s.
    emit_op ADD [Lit 4w; Lit (n2w (off - 4))] st = (src, st1) /\
    4 <= off /\ fresh_vars_wrt st s ==>
    ?t. run_inst_seq (emitted_insts st st1) s = OK t /\
        eval_operand src t = SOME (n2w off) /\
        fresh_vars_wrt st1 t /\ vars_pc_only s t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >> irule decode_emit_update_frame >> simp[] >>
  qexistsl [`ADD`, `[Lit 4w; Lit (n2w (off - 4))]`] >> simp[] >>
  `(n2w off : bytes32) = 4w + n2w (off - 4)` by
    (rewrite_tac[word_add_n2w] >> AP_TERM_TAC >> decide_tac) >>
  pop_assum SUBST1_TAC >> irule step_ADD >> simp[eval_operand_def]
QED

(* A static argument whose encoding sits at off in the calldata decodes
   without reverting, leaving the value in memory at the destination.
   For calldata that encodes the call, calldata_encodes_static_arg gives
   the encoding at the ABI head offset; that it is the decoder's off is
   the head-offset agreement this file leaves out (see the header). *)
Theorem compile_decode_static_arg_correct:
  !cenv name abi_size info off hi st st' ctx loc dst s0 p tenv ty tv v av.
    compile_decode_args cenv [(name, F, F, abi_size, info)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    4 <= off /\ off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) /\
    abi_dec_plan tenv ty info /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av /\
    mem_bytes_at off (type_memory_size tv) s0.vs_call_ctx.cc_calldata =
      enc (vyper_to_abi_type tenv ty) av ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\ val_in_memory tv v (w2n p) t.vs_memory)
      (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_decode_static_arg_phases >> strip_tac >>
  drule_all decode_head_ptr_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) s0 = OK t1` >>
  `eval_operand dst t1 = SOME p` by metis_tac[] >>
  `t1.vs_call_ctx = s0.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
  `w2n (n2w off : bytes32) = off` by (fs[] >> decide_tac) >>
  drule_all (cj 1 abi_dec_plan_value) >> simp[dec_value_def] >> strip_tac >>
  `dec_straight st st1` by metis_tac[dec_straight_emit_add] >>
  `dec_straight st1 st'` by
    (drule (cj 1 static_dec_straight) >> disch_then drule >> simp[]) >>
  `dec_straight st st'` by metis_tac[dec_straight_trans] >>
  drule (cj 1 decode_static_buf_run) >>
  disch_then (qspecl_then [`dst`, `src`, `st1`, `st'`, `t1`, `p`, `n2w off`]
                mp_tac) >>
  impl_tac >- (gvs[] >> decide_tac) >>
  `dec_ok info s0.vs_call_ctx.cc_calldata off` by metis_tac[] >>
  simp[dec_run_def] >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s0 = OK t` by
    (`inst_extends st st1 /\ inst_extends st1 st'` by fs[dec_straight_def] >>
     metis_tac[run_inst_seq_emit_extend]) >>
  `dec_frame st (w2n p) (type_memory_size tv) s0 t` by
    (irule dec_frame_trans >>
     qexistsl [`0`, `type_memory_size tv`, `w2n p`, `w2n p`, `st1`, `t1`] >>
     fs[dec_straight_def] >> irule dec_frame_of_vars >> simp[]) >>
  `val_in_memory tv v (w2n p) t.vs_memory` by metis_tac[] >>
  irule frag_exec_run_inst_seq >>
  fs[dec_straight_def, inst_extends_def, IS_PREFIX_APPEND] >>
  simp[dec_frame_inst_idx] >> fs[fresh_vars_wrt_def]
QED
