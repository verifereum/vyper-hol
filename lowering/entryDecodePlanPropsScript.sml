(*
 * Entry argument decoding: the compiler's decode plans and head offsets
 * (#639)
 *
 * The decode info build_positional_arg puts in a positional argument
 * (type_to_abi_dec_info) is an abi_dec_plan for every static assignable
 * type, and the decoder's head offsets (the running sum of
 * abi_embedded_static_size that compile_register_positional_args steps by)
 * are the ABI's (abi_head_size), whatever the earlier arguments' types.
 * Both need the compile env to agree with the type environment
 * (dec_cenv_agrees), as the encoder's plans do (retAbiPlanProps).
 *
 * TOP-LEVEL:
 *   int_byte_widths — every signed integer type in a type value is a whole
 *     number of bytes wide
 *   dec_cenv_agrees — the compile env's struct fields, memory sizes and
 *     flag member counts are the type environment's
 *   type_to_abi_dec_info_plan — type_to_abi_dec_info builds a plan for a
 *     static assignable type
 *   decode_head_offset — the decoder's head offset is the ABI's
 *   compile_decode_static_arg_calldata — a static non-word argument of
 *     calldata that encodes the call decodes to the source value at its
 *     ALLOCA
 *   compile_decode_word_arg_calldata — the same for a word argument
 *   make_struct_fields_map_dec_cenv_agrees — dec_cenv_agrees holds of an
 *     env with the compiler's struct map, given the flag counts
 *   package_external_fn_dec_cenv_agrees — package_external_fn's positional
 *     arguments are build_positional_args at an env where dec_cenv_agrees
 *     holds
 *
 * Helpers: static_length_memory_size, vyper_to_abi_static_enc_length,
 *   abi_dec_plans_map, abi_head_size_embedded, build_flag_info_n_members.
 *)
Theory entryDecodePlanProps
Ancestors
  arithmetic list rich_list finite_map
  entryDecodeStaticProps entryDecodeProps retAbiPlanProps structFieldsProps
  valueEncodingProofs valueEncoding
  vyperABI vyperABIRoundtrip vyperTyping vyperValue vyperTypeSystem
  vyperMisc vyperTypeABI contractABI
  compileEnv compileVyper exprLowering moduleLowering selectorDispatch
  fragExec

(* ===== Hypotheses ===== *)

(* Every signed integer type inside a type value is a whole number of bytes
   wide, as Vyper's int8 ... int256 are.  The decoder's clamp for intN
   sign-extends from byte N DIV 8 - 1, so it accepts every intN value only
   for those widths.  evaluate_type admits only such widths
   (evaluate_type_int_byte_widths in entryStateRel). *)
Definition int_byte_widths_def:
  int_byte_widths (BaseTV (IntT m)) = (m MOD 8 = 0) /\
  int_byte_widths (TupleTV tvs) = EVERY int_byte_widths tvs /\
  int_byte_widths (ArrayTV tv _) = int_byte_widths tv /\
  int_byte_widths (StructTV fields) = EVERY (int_byte_widths o SND) fields /\
  int_byte_widths _ = T
End

(* The compile env agrees with the type environment tenv: its struct map
   has tenv's structs with their field types (make_struct_fields_map, see
   structFieldsProps), every struct is the main module's (so
   nsid_to_string tells them apart), type_memory_bytes is the memory size
   of the evaluated type, and a flag's member count is tenv's. *)
Definition dec_cenv_agrees_def:
  dec_cenv_agrees cenv tenv <=>
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
    (!t tv. evaluate_type tenv t = SOME tv ==>
            type_memory_bytes cenv t = type_memory_size tv) /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m)
End

(* ===== Sizes of static types ===== *)

Theorem static_length_memory_size:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv /\
     ~is_dynamic (vyper_to_abi_type tenv ty) ==>
     static_length (vyper_to_abi_type tenv ty) = type_memory_size tv) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs /\
     ~any_dynamic (vyper_to_abi_types tenv ts) ==>
     static_length (Tuple (vyper_to_abi_types tenv ts)) +
       SUM (MAP type_memory_size acc) = SUM (MAP type_memory_size tvs))
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
      drule OPT_MMAP_LENGTH >> strip_tac >>
      simp[type_memory_size_def, type_memory_size_fields_sum,
           GSYM MAP_MAP_o, MAP_ZIP])
  >~ [`TupleT ts`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      simp[type_memory_size_def, type_memory_size_list_sum])
  >~ [`ArrayT t bd`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `bd` >> gvs[type_memory_size_def])
  >~ [`BaseT bt`]
  >- (rpt strip_tac >> Cases_on `bt` >>
      gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs(),
                           type_memory_size_def])
  >~ [`evaluate_types tenv [] acc`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, MAP_REVERSE, SUM_REVERSE])
  >~ [`evaluate_types tenv (t::ts) acc`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule_all >> strip_tac >>
      first_x_assum drule_all >> strip_tac >> fs[] >> decide_tac) >>
  rpt strip_tac >> gvs[evaluate_type_def, type_memory_size_def]
QED

Theorem length_flat_map2_replicate[local]:
  !xs t k.
    (!i. i < LENGTH xs ==> LENGTH (enc t (EL i xs)) = k) ==>
    LENGTH (FLAT (MAP2 enc (REPLICATE (LENGTH xs) t) xs)) = LENGTH xs * k
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `LENGTH (enc t h) = k` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH (FLAT (MAP2 enc (REPLICATE (LENGTH xs) t) xs)) = LENGTH xs * k` by
    (first_x_assum irule >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  simp[MULT_CLAUSES]
QED

Theorem length_word_to_bytes_256[local,simp]:
  LENGTH (word_to_bytes (w:bytes32) T) = 32
Proof
  simp[byteTheory.LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

(* A static value's ABI encoding takes its memory size. *)
Theorem vyper_to_abi_static_enc_length:
  (!env ty. !tv v av.
     evaluate_type env ty = SOME tv /\
     ~is_dynamic (vyper_to_abi_type env ty) /\
     value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
     LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv) /\
  (!env ts. !tvs vs avs.
     OPT_MMAP (evaluate_type env) ts = SOME tvs /\
     EVERY is_static (vyper_to_abi_types env ts) /\
     values_have_types tvs vs /\ vyper_to_abi_list env ts vs = SOME avs ==>
     LENGTH avs = LENGTH ts /\
     LENGTH (FLAT (MAP2 enc (vyper_to_abi_types env ts) avs)) =
       SUM (MAP type_memory_size tvs))
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >> rpt conj_tac
  >- suspend "base"
  >- suspend "tuple"
  >- (rpt strip_tac >> gvs[])
  >- suspend "array"
  >- suspend "struct"
  >- (rpt strip_tac >>
      rename1 `FlagT nsid` >> `is_word_type (FlagT nsid)` by simp[is_word_type_def] >>
      drule_all vyper_to_abi_word_enc >> strip_tac >>
      drule_all word_type_memory_size >> simp[])
  >- (rpt strip_tac >> gvs[evaluate_type_def, type_memory_size_def] >>
      simp[REV_DEF])
  >- (rpt strip_tac >> Cases_on `vs` >> gvs[OPT_MMAP_def, value_has_type_def])
  >> suspend "cons"
QED

Resume vyper_to_abi_static_enc_length[base]:
  rpt strip_tac >> rename1 `BaseT bt` >>
  `is_word_type (BaseT bt)` by
    (Cases_on `bt` >> gvs[is_word_type_def, evaluate_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_word_type_def, evaluate_type_def]) >>
  drule_all vyper_to_abi_word_enc >> strip_tac >>
  drule_all word_type_memory_size >> simp[]
QED

Resume vyper_to_abi_static_enc_length[tuple]:
  rpt strip_tac >> Cases_on `v` >>
  gvs[evaluate_type_def, vyper_to_abi_def, AllCaseEqs()] >>
  Cases_on `a` >>
  gvs[value_has_type_def, vyper_to_abi_def, evaluate_types_OPT_MMAP,
      AllCaseEqs(), any_dynamic_every_static] >>
  first_x_assum drule_all >> strip_tac >>
  `LENGTH (vyper_to_abi_types env ts) = LENGTH avs` by
    simp[vyper_to_abi_types_length] >>
  simp[enc_tuple_static_acc, type_memory_size_def, type_memory_size_list_sum]
QED

Resume vyper_to_abi_static_enc_length[array]:
  rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `a` >> gvs[value_has_type_def, vyper_to_abi_def, AllCaseEqs()] >>
  drule_all vyper_to_abi_sparse_EL >> strip_tac >>
  rename1 `vyper_to_abi_sparse env t tv' n sparse = SOME xs` >>
  `EVERY is_static (REPLICATE (LENGTH xs) (vyper_to_abi_type env t))` by
    simp[EVERY_REPLICATE] >>
  simp[enc_tuple_static_acc, type_memory_size_def] >>
  `LENGTH (FLAT (MAP2 enc (REPLICATE (LENGTH xs) (vyper_to_abi_type env t))
                   xs)) = LENGTH xs * type_memory_size tv'`
    suffices_by simp[] >>
  irule length_flat_map2_replicate >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  qexists_tac `sparse_val tv' sparse i` >> simp[] >>
  metis_tac[sparse_val_has_type]
QED

Resume vyper_to_abi_static_enc_length[struct]:
  rpt strip_tac >> Cases_on `v` >>
  gvs[evaluate_type_def, vyper_to_abi_def, AllCaseEqs()] >>
  gvs[evaluate_types_OPT_MMAP, value_has_type_def, any_dynamic_every_static] >>
  drule struct_has_type_values_have_types >> strip_tac >>
  drule OPT_MMAP_LENGTH >> strip_tac >>
  gvs[MAP_ZIP] >>
  first_x_assum drule_all >> strip_tac >>
  `LENGTH (vyper_to_abi_types (env \\ nsid) (MAP SND args)) = LENGTH avs` by
    simp[vyper_to_abi_types_length] >>
  `MAP (type_memory_size o SND) (ZIP (MAP FST args, tvs)) =
   MAP type_memory_size tvs` by simp[GSYM MAP_MAP_o, MAP_ZIP] >>
  simp[enc_tuple_static_acc, type_memory_size_def,
       type_memory_size_fields_sum]
QED

Resume vyper_to_abi_static_enc_length[cons]:
  rpt strip_tac >> Cases_on `vs` >>
  gvs[OPT_MMAP_def, vyper_to_abi_def, value_has_type_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Finalise vyper_to_abi_static_enc_length

(* ===== Plans ===== *)

Theorem vyper_to_abi_types_MAP[local]:
  !env ts. vyper_to_abi_types env ts = MAP (vyper_to_abi_type env) ts
Proof
  gen_tac >> Induct >> simp[]
QED

Theorem OPT_MMAP_MEM[local]:
  !ts tvs t. OPT_MMAP f ts = SOME tvs /\ MEM t ts ==>
             ?tv. f t = SOME tv /\ MEM tv tvs
Proof
  Induct >> simp[OPT_MMAP_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem EVERY_SND_ZIP[local]:
  !l1 l2. LENGTH l1 = LENGTH l2 ==>
          (EVERY (P o SND) (ZIP (l1, l2)) <=> EVERY P l2)
Proof
  Induct >> Cases_on `l2` >> simp[]
QED

Theorem map_field_types[local]:
  !fields. MAP (\(fn, fty, sz). g fty) fields = MAP g (MAP (FST o SND) fields)
Proof
  Induct >> simp[pairTheory.FORALL_PROD]
QED

Theorem dec_cenv_agrees_struct_keys[local]:
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 ==>
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE)
Proof
  rw[dec_cenv_agrees_def, SUBMAP_FLOOKUP_EQN] >> metis_tac[]
QED

Theorem dec_cenv_agrees_flags[local]:
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 ==>
  (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
            cenv.ce_flag_n_members (nsid_to_string nsid) = m)
Proof
  rw[dec_cenv_agrees_def, SUBMAP_FLOOKUP_EQN] >> metis_tac[]
QED

(* What a plan element needs of a static component type. *)
Theorem dec_cenv_agrees_elem[local]:
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
  evaluate_type tenv t = SOME tv /\ ~is_dynamic (vyper_to_abi_type tenv t) ==>
  ~is_abi_dynamic cenv.ce_struct_fields t /\
  abi_embedded_static_size cenv.ce_struct_fields t = type_memory_size tv /\
  type_memory_bytes cenv t = type_memory_size tv
Proof
  rw[dec_cenv_agrees_def] >> drule_all abi_elem_props >> strip_tac >>
  gvs[] >> metis_tac[static_length_memory_size]
QED

Theorem abi_dec_plans_map:
  !tenv tenv0 cenv f ts.
    tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
    (!t. MEM t ts ==>
         IS_SOME (evaluate_type tenv t) /\
         ~is_dynamic (vyper_to_abi_type tenv t) /\
         abi_dec_plan tenv t (f t)) ==>
    ~EXISTS (is_abi_dynamic cenv.ce_struct_fields) ts /\
    abi_dec_plans tenv ts
      (MAP (\t. (f t, abi_embedded_static_size cenv.ce_struct_fields t,
                 type_memory_bytes cenv t)) ts)
Proof
  ntac 4 gen_tac >> Induct >- simp[abi_dec_plan_nil] >>
  gen_tac >> strip_tac >>
  `?tv. evaluate_type tenv h = SOME tv`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS]) >>
  `~is_dynamic (vyper_to_abi_type tenv h) /\ abi_dec_plan tenv h (f h)`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  drule_all dec_cenv_agrees_elem >> strip_tac >>
  `~EXISTS (is_abi_dynamic cenv.ce_struct_fields) ts /\
   abi_dec_plans tenv ts
     (MAP (\t. (f t, abi_embedded_static_size cenv.ce_struct_fields t,
                type_memory_bytes cenv t)) ts)`
    by (last_x_assum irule >> simp[] >> rpt strip_tac >>
        first_x_assum (qspec_then `t` mp_tac) >> simp[]) >>
  simp[] >> conj_tac >- fs[EVERY_MEM, EXISTS_MEM] >>
  irule abi_dec_plan_cons >> simp[]
QED

(* The StructT case of type_to_abi_dec_info_plan, given each field's plan
   (the induction hypothesis). *)
Theorem type_to_abi_dec_info_plan_struct[local]:
  FLOOKUP tenv nsid = SOME (StructArgs args) /\
  EVERY (assignable_type (tenv \\ nsid) o SND) args /\
  (!x. MEM x args ==>
     assignable_type (tenv \\ nsid) (SND x) ==>
     !(sf' : (string, (string # type # num) list) fmap) cenv tenv1 tv.
       tenv \\ nsid SUBMAP tenv1 /\ dec_cenv_agrees cenv tenv1 /\
       sfields_tenv_consistent sf' (tenv \\ nsid) /\
       evaluate_type (tenv \\ nsid) (SND x) = SOME tv /\ int_byte_widths tv /\
       ~is_dynamic (vyper_to_abi_type (tenv \\ nsid) (SND x)) ==>
       abi_dec_plan (tenv \\ nsid) (SND x)
         (type_to_abi_dec_info sf' cenv (SND x))) /\
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap)
    tenv /\
  evaluate_type tenv (StructT nsid) = SOME tv /\ int_byte_widths tv /\
  ~is_dynamic (vyper_to_abi_type tenv (StructT nsid)) ==>
  abi_dec_plan tenv (StructT nsid) (type_to_abi_dec_info sf cenv (StructT nsid))
Proof
  strip_tac >>
  drule_then (drule_then assume_tac) dec_cenv_agrees_struct_keys >>
  drule_all sfields_tenv_consistent_domsub >> strip_tac >>
  `?fields. FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
            MAP (FST o SND) fields = MAP SND args`
    by (qpat_x_assum `sfields_tenv_consistent sf tenv` mp_tac >>
        simp[sfields_tenv_consistent_def] >> strip_tac >>
        first_x_assum drule >> strip_tac >> simp[]) >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP,
      int_byte_widths_def, any_dynamic_every_static] >>
  rename1 `OPT_MMAP _ _ = SOME ftvs` >>
  drule OPT_MMAP_LENGTH >> strip_tac >>
  `EVERY int_byte_widths ftvs` by gvs[EVERY_SND_ZIP, ETA_AX] >>
  `tenv \\ nsid SUBMAP tenv0` by
    (irule SUBMAP_TRANS >> qexists_tac `tenv` >> simp[]) >>
  simp[Once type_to_abi_dec_info_def, map_field_types] >>
  qspecl_then [`tenv \\ nsid`, `tenv0`, `cenv`,
               `type_to_abi_dec_info (sf \\ nsid_to_string nsid) cenv`,
               `MAP SND args`] mp_tac abi_dec_plans_map >>
  impl_tac
  >- (conj_tac >- simp[] >> conj_tac >- simp[] >>
      gen_tac >> strip_tac >>
      drule_all OPT_MMAP_MEM >> strip_tac >>
      rename1 `evaluate_type (tenv \\ nsid) t = SOME ftv` >>
      `?y. t = SND y /\ MEM y args` by (fs[MEM_MAP] >> metis_tac[]) >>
      gvs[] >>
      `int_byte_widths ftv` by metis_tac[EVERY_MEM] >>
      `is_static (vyper_to_abi_type (tenv \\ nsid) (SND y))` by
        (qpat_x_assum `EVERY is_static _` mp_tac >>
         simp[vyper_to_abi_types_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
         disch_then irule >> simp[]) >>
      `assignable_type (tenv \\ nsid) (SND y)` by
        (qpat_x_assum `EVERY (assignable_type _ o SND) _` mp_tac >>
         simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
      simp[] >>
      last_x_assum (qspec_then `y` mp_tac) >> simp[] >>
      disch_then irule >> simp[] >> qexists_tac `tenv0` >> simp[]) >>
  strip_tac >> simp[] >> irule abi_dec_plan_struct >> simp[]
QED

(* The TupleT case of type_to_abi_dec_info_plan, given each component's
   plan (the induction hypothesis). *)
Theorem type_to_abi_dec_info_plan_tuple[local]:
  (!ty. MEM ty tys ==>
     assignable_type tenv ty ==>
     !(sf : (string, (string # type # num) list) fmap) cenv tenv0 tv.
       tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
       sfields_tenv_consistent sf tenv /\
       evaluate_type tenv ty = SOME tv /\ int_byte_widths tv /\
       ~is_dynamic (vyper_to_abi_type tenv ty) ==>
       abi_dec_plan tenv ty (type_to_abi_dec_info sf cenv ty)) /\
  assignable_type tenv (TupleT tys) /\
  tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap)
    tenv /\
  evaluate_type tenv (TupleT tys) = SOME tv /\ int_byte_widths tv /\
  ~is_dynamic (vyper_to_abi_type tenv (TupleT tys)) ==>
  abi_dec_plan tenv (TupleT tys) (type_to_abi_dec_info sf cenv (TupleT tys))
Proof
  strip_tac >>
  gvs[assignable_type_def, evaluate_type_def, AllCaseEqs(),
      evaluate_types_OPT_MMAP, int_byte_widths_def,
      any_dynamic_every_static] >>
  simp[Once type_to_abi_dec_info_def] >>
  qspecl_then [`tenv`, `tenv0`, `cenv`, `type_to_abi_dec_info sf cenv`,
               `tys`] mp_tac abi_dec_plans_map >>
  impl_tac
  >- (conj_tac >- simp[] >> conj_tac >- simp[] >>
      gen_tac >> strip_tac >>
      drule_all OPT_MMAP_MEM >> strip_tac >>
      rename1 `evaluate_type tenv t = SOME etv` >>
      `int_byte_widths etv` by metis_tac[EVERY_MEM] >>
      `is_static (vyper_to_abi_type tenv t)` by
        (qpat_x_assum `EVERY is_static _` mp_tac >>
         simp[vyper_to_abi_types_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
         disch_then irule >> simp[]) >>
      `assignable_type tenv t` by metis_tac[EVERY_MEM] >>
      simp[] >>
      qpat_x_assum `!ty. MEM ty tys ==> _` (qspec_then `t` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >>
      qexists_tac `tenv0` >> simp[]) >>
  strip_tac >> simp[] >> irule abi_dec_plan_tuple >> simp[]
QED

(* type_to_abi_dec_info builds a plan for a static assignable type.  sf is
   the struct map the recursion has narrowed to tenv's structs; sizes and
   flags come from the whole compile env, which agrees with tenv0. *)
Theorem type_to_abi_dec_info_plan:
  !tenv ty.
    assignable_type tenv ty ==>
    !(sf : (string, (string # type # num) list) fmap) cenv tenv0 tv.
      tenv SUBMAP tenv0 /\ dec_cenv_agrees cenv tenv0 /\
      sfields_tenv_consistent sf tenv /\
      evaluate_type tenv ty = SOME tv /\ int_byte_widths tv /\
      ~is_dynamic (vyper_to_abi_type tenv ty) ==>
      abi_dec_plan tenv ty (type_to_abi_dec_info sf cenv ty)
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      `?args. FLOOKUP tenv nsid = SOME (StructArgs args)`
        by (qpat_x_assum `assignable_type _ _` mp_tac >>
            simp[assignable_type_def] >> rpt BasicProvers.TOP_CASE_TAC >>
            simp[]) >>
      drule_at (Pos hd) type_to_abi_dec_info_plan_struct >>
      disch_then irule >>
      qpat_x_assum `assignable_type _ _` mp_tac >>
      simp[assignable_type_def] >> strip_tac >>
      rpt conj_tac
      >- (rpt strip_tac >>
          first_x_assum (qspecl_then [`StructArgs args`, `args`, `x`, `SND x`]
                           mp_tac) >>
          simp[] >> disch_then irule >> simp[] >>
          qexists_tac `tenv1` >> simp[])
      >- fs[EVERY_MEM] >>
      qexists_tac `tenv0` >> simp[])
  >~ [`TupleT tys`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      drule_all type_to_abi_dec_info_plan_tuple >> simp[])
  >~ [`ArrayT elem bd`]
  >- (rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
      gvs[assignable_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `bd` >> gvs[int_byte_widths_def] >>
      rename1 `evaluate_type tenv elem = SOME etv` >>
      `abi_dec_plan tenv elem (type_to_abi_dec_info sf cenv elem)` by
        (first_x_assum irule >> simp[] >> qexists_tac `tenv0` >> simp[]) >>
      drule_all dec_cenv_agrees_elem >> strip_tac >>
      simp[Once type_to_abi_dec_info_def, GSYM REPLICATE_GENLIST] >>
      irule abi_dec_plan_sarray >> simp[])
  >~ [`BaseT bt`]
  >- (rpt strip_tac >>
      `is_word_type (BaseT bt)` by
        (Cases_on `bt` >> gvs[is_word_type_def, evaluate_type_def] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[is_word_type_def, evaluate_type_def]) >>
      irule type_to_abi_dec_info_word_plan >> simp[] >>
      drule_then (drule_then assume_tac) dec_cenv_agrees_flags >> simp[] >>
      rpt strip_tac >> gvs[evaluate_type_def, int_byte_widths_def])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> irule type_to_abi_dec_info_word_plan >>
      simp[is_word_type_def] >>
      drule_then (drule_then assume_tac) dec_cenv_agrees_flags >> simp[]) >>
  simp[assignable_type_def]
QED

(* ===== Head offsets ===== *)

(* An argument takes as many bytes in the ABI head as the decoder steps
   over for it. *)
Theorem abi_head_size_embedded:
  !cenv tenv t tv v av.
    dec_cenv_agrees cenv tenv /\ evaluate_type tenv t = SOME tv /\
    value_has_type tv v /\ vyper_to_abi tenv t v = SOME av ==>
    abi_head_size (vyper_to_abi_type tenv t) av =
    abi_embedded_static_size cenv.ce_struct_fields t
Proof
  rpt strip_tac >> fs[dec_cenv_agrees_def] >>
  `tenv SUBMAP tenv` by simp[] >>
  drule_all abi_elem_props >> strip_tac >>
  simp[abi_head_size_def] >> IF_CASES_TAC >> simp[] >>
  drule_all (cj 1 vyper_to_abi_static_enc_length) >> simp[] >>
  metis_tac[static_length_memory_size]
QED

(* The decoder's head offset for argument i (abi_embedded_static_size
   summed over the earlier arguments, as compile_register_positional_args
   steps) is the ABI's, whatever the earlier arguments' types. *)
Theorem decode_head_offset:
  !cenv tenv tys vals avs i.
    dec_cenv_agrees cenv tenv /\
    vyper_to_abi_list tenv tys vals = SOME avs /\ i <= LENGTH tys /\
    (!j. j < i ==> ?tv. evaluate_type tenv (EL j tys) = SOME tv /\
                        value_has_type tv (EL j vals)) ==>
    SUM (MAP2 abi_head_size (TAKE i (vyper_to_abi_types tenv tys))
                            (TAKE i avs)) =
    SUM (MAP (abi_embedded_static_size cenv.ce_struct_fields) (TAKE i tys))
Proof
  rpt strip_tac >> drule vyper_to_abi_list_EL >> strip_tac >>
  AP_TERM_TAC >> irule LIST_EQ >>
  simp[vyper_to_abi_types_length, EL_MAP2, EL_MAP, EL_TAKE] >>
  rpt strip_tac >>
  `x < LENGTH tys /\ x < LENGTH vals` by decide_tac >>
  `EL x (vyper_to_abi_types tenv tys) = vyper_to_abi_type tenv (EL x tys)`
    by metis_tac[vyper_to_abi_types_EL] >>
  `vyper_to_abi tenv (EL x tys) (EL x vals) = SOME (EL x avs)` by simp[] >>
  qpat_x_assum `!j. j < i ==> _` (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >>
  irule abi_head_size_embedded >> simp[] >> metis_tac[]
QED

(* ===== Arguments of calldata that encodes the call ===== *)

Theorem map_embedded_take[local]:
  MAP (abi_embedded_static_size sf o SND) (TAKE i args) =
  MAP (abi_embedded_static_size sf) (TAKE i (MAP SND args))
Proof
  simp[MAP_TAKE, MAP_MAP_o]
QED

(* The ABI head offset of argument i is the decoder's off. *)
Theorem calldata_head_offset[local]:
  dec_cenv_agrees cenv0 tenv /\
  vyper_to_abi_list tenv (MAP SND args) vals = SOME avs /\
  i < LENGTH args /\
  (!j. j < i ==> ?tv. evaluate_type tenv (SND (EL j args)) = SOME tv /\
                      value_has_type tv (EL j vals)) ==>
  4 + SUM (MAP2 abi_head_size (TAKE i (vyper_to_abi_types tenv (MAP SND args)))
                              (TAKE i avs)) =
  4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
               (TAKE i args))
Proof
  strip_tac >> simp[map_embedded_take] >>
  irule decode_head_offset >> simp[EL_MAP] >> metis_tac[]
QED

(* A static argument other than a word, of calldata that encodes the call,
   decodes without reverting to the source value in memory at its ALLOCA.
   off is where compile_register_positional_args decodes argument i from:
   4 plus the abi sizes build_positional_arg gives the earlier arguments.
   The earlier arguments may be of any (well-typed) type. *)
Theorem compile_decode_static_arg_calldata:
  !cenv cenv0 tenv fname args vals i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    calldata_encodes tenv fname (MAP SND args) vals
      s0.vs_call_ctx.cc_calldata /\
    LENGTH vals = LENGTH args /\ i < LENGTH args /\
    (!j. j < i ==> ?tv. evaluate_type tenv (SND (EL j args)) = SOME tv /\
                        value_has_type tv (EL j vals)) /\
    assignable_type tenv (SND (EL i args)) /\
    ~is_word_type (SND (EL i args)) /\
    ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    value_has_type tv (EL i vals) /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\
           val_in_memory tv (EL i vals) (w2n p) t.vs_memory)
      (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `EL i args` >> rename1 `EL i args = (name, ty)` >> gvs[] >>
  `EL i (MAP SND args) = ty` by simp[EL_MAP] >>
  qspecl_then [`tenv`, `fname`, `MAP SND args`, `vals`,
               `s0.vs_call_ctx.cc_calldata`, `i`] mp_tac
    calldata_encodes_static_arg >>
  simp[] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_static_enc_length) >> strip_tac >>
  `tenv SUBMAP tenv` by simp[] >>
  drule_all dec_cenv_agrees_elem >> strip_tac >>
  `abi_dec_plan tenv ty
     (type_to_abi_dec_info cenv0.ce_struct_fields cenv0 ty)` by
    (irule type_to_abi_dec_info_plan >> fs[dec_cenv_agrees_def] >>
     qexists_tac `tenv` >> fs[dec_cenv_agrees_def]) >>
  drule_all calldata_head_offset >> strip_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  simp[build_positional_arg_def] >> strip_tac >>
  qspecl_then [`cenv`, `name`,
               `abi_embedded_static_size cenv0.ce_struct_fields ty`,
               `type_to_abi_dec_info cenv0.ce_struct_fields cenv0 ty`,
               `4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o
                             SND) (TAKE i args))`,
               `hi`, `st`, `st'`, `ctx`, `loc`, `dst`, `s0`, `p`,
               `tenv`, `ty`, `tv`, `EL i vals`, `EL i avs`] mp_tac
    compile_decode_static_arg_correct >>
  impl_tac >- gvs[] >> simp[]
QED

(* The same for a word argument (#739's compile_decode_word_arg_correct,
   at the head offset of calldata that encodes the call). *)
Theorem compile_decode_word_arg_calldata:
  !cenv cenv0 tenv fname args vals i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    calldata_encodes tenv fname (MAP SND args) vals
      s0.vs_call_ctx.cc_calldata /\
    LENGTH vals = LENGTH args /\ i < LENGTH args /\
    (!j. j < i ==> ?tv. evaluate_type tenv (SND (EL j args)) = SOME tv /\
                        value_has_type tv (EL j vals)) /\
    is_word_type (SND (EL i args)) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    value_has_type tv (EL i vals) /\
    off < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only (mstore (w2n p) (typed_val_to_w256 tv (EL i vals)) s0)
             t /\
           fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
           val_in_memory tv (EL i vals) (w2n p) t.vs_memory)
      (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `EL i args` >> rename1 `EL i args = (name, ty)` >> gvs[] >>
  `EL i (MAP SND args) = ty` by simp[EL_MAP] >>
  qspecl_then [`tenv`, `fname`, `MAP SND args`, `vals`,
               `s0.vs_call_ctx.cc_calldata`, `i`, `tv`] mp_tac
    calldata_encodes_word_arg >>
  simp[] >> strip_tac >>
  drule_all calldata_head_offset >> strip_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  simp[build_positional_arg_def] >> strip_tac >>
  qspecl_then [`cenv`, `cenv0`, `cenv0.ce_struct_fields`, `name`,
               `is_abi_dynamic cenv0.ce_struct_fields ty`,
               `abi_embedded_static_size cenv0.ce_struct_fields ty`,
               `4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o
                             SND) (TAKE i args))`,
               `hi`, `st`, `st'`, `ctx`, `loc`, `dst`, `s0`, `p`,
               `tenv`, `ty`, `tv`, `EL i vals`] mp_tac
    compile_decode_word_arg_correct >>
  impl_tac >> simp[] >>
  gvs[dec_cenv_agrees_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, int_byte_widths_def]
QED

(* ===== The compiler's env ===== *)

(* dec_cenv_agrees holds of an env whose struct map is the compiler's
   (build_compile_env's), for a contract whose type keys are distinct,
   given the flag member counts (see exprSimHyps on why
   build_compile_env's counts need not be the source's). *)
Theorem make_struct_fields_map_dec_cenv_agrees:
  !tops cenv.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    (!nsid m. FLOOKUP (type_env tops) nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    dec_cenv_agrees cenv (type_env tops)
Proof
  rpt strip_tac >>
  `struct_args_unique tops`
    by (irule typedCopyProducerTheory.distinct_type_keys_struct_args_unique >>
        simp[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (type_env tops)`
    by simp[make_struct_fields_map_consistent] >>
  `!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE`
    by (rw[vyperContextTheory.type_env_def] >>
        drule type_env_for_module_struct_mem >> rw[] >> simp[]) >>
  `!t tv. evaluate_type (type_env tops) t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv`
    by (rpt strip_tac >> drule_all make_struct_fields_map_memory_size >>
        simp[]) >>
  simp[dec_cenv_agrees_def]
QED

(* build_flag_info's member counts are type_env's, for distinct keys. *)
Theorem build_flag_info_other[local]:
  !tops fmid fnm id.
    ~MEM (NONE, id)
       (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ==>
    SND (build_flag_info tops fmid fnm) id = fnm id
Proof
  Induct >> simp[build_flag_info_def] >> Cases >>
  rw[build_flag_info_def, vyperTypeContractTheory.type_def_keys_toplevel_def]
QED

Theorem build_flag_info_n_members[local]:
  !tops fmid fnm nsid m.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    FLOOKUP (type_env_for_module NONE tops) nsid = SOME (FlagArgs m) ==>
    SND (build_flag_info tops fmid fnm) (nsid_to_string nsid) = m
Proof
  Induct >> simp[vyperContextTheory.type_env_for_module_def] >> Cases >>
  simp[vyperContextTheory.type_env_for_module_def, build_flag_info_def,
       vyperTypeContractTheory.type_def_keys_toplevel_def, FLOOKUP_UPDATE,
       ALL_DISTINCT_APPEND] >>
  rw[] >> gvs[nsid_to_string_def, build_flag_info_other] >>
  first_x_assum irule >> simp[]
QED

Theorem build_compile_env_ce_flag_n_members[local]:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_flag_n_members = SND (build_flag_info tops (K (K 0)) (K 0))
Proof
  rpt strip_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* package_external_fn decodes its positional arguments with the decode
   infos of build_positional_args, at an env that agrees with the
   contract's type environment. *)
Theorem package_external_fn_dec_cenv_agrees:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret body
   lbl cenv pos_args rest.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    package_external_fn tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, body) =
      (lbl, cenv, pos_args, rest) ==>
    pos_args = build_positional_args cenv fargs /\
    dec_cenv_agrees cenv (type_env tops)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[package_external_fn_def] >>
  irule make_struct_fields_map_dec_cenv_agrees >>
  rw[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
     build_compile_env_ce_struct_fields, build_compile_env_ce_flag_n_members] >>
  gvs[vyperContextTheory.type_env_def] >>
  irule build_flag_info_n_members >> simp[]
QED
