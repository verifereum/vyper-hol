(*
 * Whitelist removal: the S1 lemmas behind supported_word_type /
 * supported_scalar_type at flag types.  Flags are 256-bit words in the
 * lowering (is_word_type (FlagT _) = T, type_rank (FlagT _) = 1), so each
 * consumer of the two clauses holds with the clause widened to
 * `supported_word_type ty \/ ?n. ty = FlagT n` (likewise for
 * supported_scalar_type), and the nested-type metadata chain holds for any
 * leaf predicate that excludes aggregates.
 *
 * Survey: theorems outside lowering/supported/ whose statement has
 * supported_word_type or supported_scalar_type, directly or as the leaf of
 * supported_nested_type / supported_place_type / supported_value_type.
 *
 * Flag instance proved here:
 *   typedCopyMetadata:127 supported_word_type_is_word
 *       -> word_or_flag_is_word
 *   exprOpenCopies:207 supported_copy_types_store_path
 *       -> copy_types_store_path_flag
 *   exprOpenDispatch:30 compile_dispatch_bop_open (supported_binop rows 32,37)
 *       -> compile_dispatch_bop_open_flag
 *   retAbiPlanProps:537 supported_scalar_type_assignable
 *       -> scalar_or_flag_assignable
 *   retAbiPlanProps:526 supported_word_type_assignable
 *       -> word_or_flag_assignable: needs well_formed_type at a flag
 *          (FlagT of an undeclared flag is not well formed); its consumer
 *          supported_return_type_assignable has that premise.
 *   bodySimStmtCases:997,1018 storage_scalar_fit_equal, storage_scalars_fit_equal
 *       ([local]) -> storage_scalar_fit_equal_flag, storage_scalars_fit_equal_flag
 *   typedCopyMetadata:243 nested_metadata_fields,
 *     :262 nested_metadata_agrees_fields,
 *     :278 nested_type_rank_metadata_invariant,
 *     :317 nested_metadata_agrees_delete_unreachable,
 *     :331 nested_fields_rank, :361 nested_copy_metadata_acyclic,
 *     :403 make_struct_fields_map_acyclic (struct fields with flag leaves,
 *     rows 14, 15, 104)
 *       -> the *_leaf versions below, for any leaf that excludes aggregates,
 *          and flag_struct_fields_map_acyclic for the flag leaf.
 *
 * Already general (no supported_* premise, flags included):
 *   exprSimOperators: compile_bop_word_case (word_value_type includes
 *     is_flag_type; rows 32, 37), compile_not_case (row 45),
 *     compile_ifexp_case / compile_ifexp_aggregate_case (rows 20, 97);
 *   exprSimFlagWord: compile_flag_member_case_sim (row 5);
 *   open lemmas: compile_dispatch_not_open, compile_invert_open,
 *     compile_ifexp_open, compile_flag_member_open (whitelistExprOpen);
 *   whitelistCheckerTypes: well_formed_fixed_bytes_word,
 *     well_formed_base_scalar (about BaseT only).
 *   The syntactic lemmas over supported_expr (supported_pure_scopes_mutual,
 *   supported_pure_main_calls, supported_pure_forms_int_calls,
 *   supported_pure_shape) never name the type predicates in their proofs.
 *
 * Not this piece:
 *   - log family (bodySimLog:62,75 and stmtSimLog*, 69 theorems): event field
 *     ABI encoding (EventDecl header clause), not the word representation;
 *   - supportedExprs:124 supported_external_call_contract: external-call
 *     argument ABI types;
 *   - memoryLocalRhsProps:180,247 (supported_tuple_type): tuple ABI encoding;
 *   - typedCopyMetadata:135 supported_value_type_shallow_metadata: no
 *     consumer;
 *   - bodySimStmtCases:1029 storage_value_fit_equal ([local]): storage-value
 *     typing; its scalar leaves are storage_scalar_fit_equal_flag above;
 *   - lowering/supported/* consumer contracts (supportedTypes:164-193,
 *     supportedTypeProps): statements about the whitelist itself.
 *)
Theory whitelistFlags
Ancestors
  typedCopyMetadata typedCopyDomain compileVyper exprOpenPrimitives exprLowering
  compileEnv venomInst
  supportedExprForms supportedTypes supportedDecls vyperTypeSystem vyperValue vyperAST
  finite_map list pair combin arithmetic pred_set

(* ===== Flags as words ===== *)

Theorem word_or_flag_is_word:
  supported_word_type ty \/ (?n. ty = FlagT n) ==> is_word_type ty
Proof
  rw[] >> simp[is_word_type_def, supported_word_type_is_word]
QED

Theorem copy_types_store_path_flag:
  !dst src.
    supported_copy_types dst src \/
    ((supported_word_type dst \/ ?n. dst = FlagT n) /\
     (supported_word_type src \/ ?n. src = FlagT n)) ==>
    is_word_type dst \/ is_bytestring_type dst \/ dst = src
Proof
  rpt gen_tac >> strip_tac
  >- (pop_assum mp_tac >> simp[supported_copy_types_def] >> strip_tac
      >- simp[]
      >- metis_tac[supported_word_type_is_word] >>
      Cases_on `dst` >> Cases_on `src` >>
      gvs[AllCaseEqs(), is_bytestring_type_def] >>
      rename1 `is_word_type (BaseT dst_base) \/ _ \/ dst_base = src_base` >>
      Cases_on `dst_base` >> Cases_on `src_base` >>
      gvs[AllCaseEqs(), is_bytestring_type_def] >>
      rename1 `is_word_type (BaseT (BytesT dst_bound)) \/ _ \/
               dst_bound = src_bound` >>
      Cases_on `dst_bound` >> Cases_on `src_bound` >>
      gvs[is_bytestring_type_def]) >>
  metis_tac[word_or_flag_is_word]
QED

(* ===== Binary operators on flags keep the block open (rows 32, 37) ===== *)

Theorem compile_dispatch_bop_open_flag:
  !cfn cenv rty ty op a b sa vv sb.
    (supported_binop op (expr_type a) (expr_type b)
       (supported_integer_literal a) (supported_nonnegative_literal b) \/
     ((op = And \/ op = Or \/ op = XOr \/ op = Eq \/ op = NotEq) /\
      ?n. expr_type a = FlagT n)) /\
    compile_builtin_dispatch_body cfn cenv rty ty (Bop op) [a;b] sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN ASSUME_TAC) >>
  `op <> In /\ op <> NotIn /\ op <> ExpMod` by
    (Cases_on `op` >> gvs[supported_binop_def]) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> IF_CASES_TAC
  >- (simp[pairTheory.UNCURRY] >> IF_CASES_TAC >>
      simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  rpt (pairarg_tac >> simp[]) >>
  simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule compile_binop_open >> simp[] >> disch_then drule >> simp[]
QED

(* ===== Assignability ===== *)

Theorem word_or_flag_assignable:
  !tenv ty.
    supported_word_type ty \/ (?n. ty = FlagT n) /\ well_formed_type tenv ty ==>
    assignable_type tenv ty
Proof
  rw[] >> simp[assignable_type_def] >>
  Cases_on `ty` >> gvs[supported_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[supported_word_type_def, assignable_type_def, well_formed_type_def,
      evaluate_type_def, supported_int_width_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[supported_word_type_def, evaluate_type_def]
QED

Theorem scalar_or_flag_assignable:
  !tenv ty.
    (supported_scalar_type ty \/ ?n. ty = FlagT n) /\
    well_formed_type tenv ty ==>
    assignable_type tenv ty
Proof
  rw[supported_scalar_type_def] >> TRY (metis_tac[word_or_flag_assignable]) >>
  Cases_on `ty` >> gvs[supported_string_type_def, assignable_type_def]
QED

(* ===== Storage type fit ===== *)

(* A flag fits only itself: arg_type_fits falls through to equality. *)
Theorem storage_scalar_fit_equal_flag:
  !tops fuel t u.
    (supported_scalar_type t \/ ?n. t = FlagT n) /\
    supported_nested_type supported_full_word_type fuel tops u /\
    arg_type_fits t u ==> t = u
Proof
  rpt gen_tac >> Cases_on `?n. t = FlagT n`
  >- (gvs[] >> Cases_on `u` >> simp[arg_type_fits_def]) >>
  pop_assum mp_tac >> simp[] >> strip_tac >>
  Cases_on `t` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
  rename1 `supported_word_type (BaseT bt)` >> Cases_on `u` >>
  simp[arg_type_fits_def] >>
  rename1 `arg_type_fits _ (BaseT ub)` >>
  Cases_on `bt` >> Cases_on `ub` >>
  simp[supported_word_type_def, supported_string_type_def,
       arg_type_fits_def, Once supported_nested_type_def,
       supported_full_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  gvs[arg_type_fits_def, supported_word_type_def, supported_string_type_def]
QED

Theorem storage_scalars_fit_equal_flag:
  !ts us tops fuel.
    EVERY (\t. supported_scalar_type t \/ ?n. t = FlagT n) ts /\
    EVERY (supported_nested_type supported_full_word_type fuel tops) us /\
    arg_types_fit ts us ==> ts = us
Proof
  Induct >> Cases_on `us` >> simp[arg_type_fits_def] >>
  rpt strip_tac >> simp[] >> metis_tac[storage_scalar_fit_equal_flag]
QED

(* ===== Nested place types: struct metadata for any non-aggregate leaf =====

   The typedCopyMetadata chain proves acyclicity for the leaf
   supported_scalar_type; it only uses that a leaf is never an array, tuple
   or struct.  These are the same theorems for any such leaf, so they cover
   both supported_scalar_type and its flag extension. *)

Theorem nonagg_leaf_nested_struct[local]:
  (!t. leaf t ==> (!e b. t <> ArrayT e b) /\ (!ts. t <> TupleT ts) /\
                  (!id. t <> StructT id)) ==>
  (supported_nested_type leaf fuel tops (StructT id) <=>
   fuel <> 0 /\
   case supported_struct_fields tops id of
     NONE => F
   | SOME fields =>
       ~NULL fields /\
       EVERY (supported_nested_type leaf (fuel - 1) tops o SND) fields) /\
  (supported_nested_type leaf fuel tops (ArrayT elem bd) <=>
   (case bd of Fixed n => 0 < n | Dynamic n => T) /\
   supported_nested_type leaf fuel tops elem) /\
  (supported_nested_type leaf fuel tops (TupleT tys) <=>
   ~NULL tys /\ EVERY (supported_nested_type leaf fuel tops) tys)
Proof
  strip_tac >> rpt conj_tac >>
  simp[Once supported_nested_type_def] >>
  `~leaf (StructT id) /\ ~leaf (ArrayT elem bd) /\ ~leaf (TupleT tys)` by
    metis_tac[] >>
  simp[] >> TRY (Cases_on `bd` >> simp[]) >> rw[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem nested_metadata_fields_leaf:
  (!t. leaf t ==> (!e b. t <> ArrayT e b) /\ (!ts. t <> TupleT ts) /\
                  (!id. t <> StructT id)) /\
  struct_metadata_types_match tops sf /\
  supported_nested_type leaf fuel tops (StructT nsid) ==>
  0 < fuel /\
  EVERY (supported_nested_type leaf (fuel - 1) tops o FST o SND)
    (get_struct_fields sf (nsid_to_string nsid))
Proof
  strip_tac >> drule nonagg_leaf_nested_struct >>
  disch_then (fn th => fs[th]) >>
  Cases_on `nsid` >> rename1 `(modid,name)` >> Cases_on `modid` >>
  gvs[supported_struct_fields_other_module, nsid_to_string_def] >>
  Cases_on `supported_struct_fields tops (NONE,name)` >> gvs[] >>
  simp[get_struct_fields_def] >>
  Cases_on `FLOOKUP sf name` >> simp[] >>
  fs[struct_metadata_types_match_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[GSYM EVERY_MAP, MAP_MAP_o, o_DEF]
QED

Theorem nested_metadata_agrees_fields_leaf:
  (!t. leaf t ==> (!e b. t <> ArrayT e b) /\ (!ts. t <> TupleT ts) /\
                  (!id. t <> StructT id)) /\
  (!n name. n <= fuel /\
            supported_nested_type leaf n tops (StructT (NONE,name)) ==>
            FLOOKUP sub name = FLOOKUP sf name) /\
  supported_nested_type leaf fuel tops (StructT nsid) ==>
  get_struct_fields sub (nsid_to_string nsid) =
  get_struct_fields sf (nsid_to_string nsid)
Proof
  strip_tac >>
  Cases_on `nsid` >> rename1 `(modid,name)` >> Cases_on `modid`
  >- (simp[nsid_to_string_def, get_struct_fields_def] >>
      first_x_assum (qspecl_then [`fuel`, `name`] mp_tac) >> simp[]) >>
  drule nonagg_leaf_nested_struct >> disch_then (fn th => fs[th]) >>
  gvs[supported_struct_fields_other_module]
QED

Theorem nested_type_rank_metadata_invariant_leaf:
  !sf ty sub fuel tops leaf.
    (!t. leaf t ==> (!e b. t <> ArrayT e b) /\ (!ts. t <> TupleT ts) /\
                    (!id. t <> StructT id)) /\
    struct_metadata_types_match tops sf /\
    struct_metadata_types_match tops sub /\
    supported_nested_type leaf fuel tops ty /\
    (!n name. n <= fuel /\
              supported_nested_type leaf n tops (StructT (NONE,name)) ==>
              FLOOKUP sub name = FLOOKUP sf name) ==>
    type_rank sub ty = type_rank sf ty
Proof
  recInduct type_rank_ind >> rpt conj_tac
  >- simp[type_rank_def]
  >- (rpt strip_tac >> rename1 `ArrayT elem bd` >>
      qpat_x_assum `supported_nested_type _ _ _ (ArrayT _ _)` mp_tac >>
      drule nonagg_leaf_nested_struct >> disch_then (fn th => simp[th]) >>
      strip_tac >> simp[type_rank_def] >>
      first_x_assum irule >> qexistsl_tac [`fuel`, `leaf`, `tops`] >>
      simp[] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `supported_nested_type _ _ _ (TupleT _)` mp_tac >>
      drule nonagg_leaf_nested_struct >> disch_then (fn th => simp[th]) >>
      strip_tac >> simp[type_rank_def] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >>
      qexistsl_tac [`fuel`, `leaf`, `tops`] >> fs[EVERY_MEM] >> metis_tac[])
  >- (rpt strip_tac >>
      `0 < fuel /\
       EVERY (supported_nested_type leaf (fuel - 1) tops o FST o SND)
         (get_struct_fields sf (nsid_to_string nsid))` by
        (irule nested_metadata_fields_leaf >> simp[]) >>
      `get_struct_fields sub (nsid_to_string nsid) =
       get_struct_fields sf (nsid_to_string nsid)` by
        (irule nested_metadata_agrees_fields_leaf >> simp[] >>
         qexistsl_tac [`fuel`, `leaf`, `tops`] >> simp[] >>
         first_assum ACCEPT_TAC) >>
      simp[type_rank_def] >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
      rpt strip_tac >> qmatch_goalsub_rename_tac `FST (SND triple)` >>
      first_x_assum irule >> simp[] >>
      conj_tac >- (qexists_tac `triple` >> simp[]) >>
      qexistsl_tac [`fuel - 1`, `leaf`, `tops`] >>
      simp[struct_metadata_types_match_delete] >>
      fs[EVERY_MEM] >> rw[DOMSUB_FLOOKUP_THM] >>
      first_x_assum irule >> qexists_tac `n` >> simp[])
  >- simp[type_rank_def]
  >> simp[type_rank_def]
QED

Theorem nested_fields_rank_leaf:
  !fuel tops sf name fields leaf.
    (!t. leaf t ==> (!e b. t <> ArrayT e b) /\ (!ts. t <> TupleT ts) /\
                    (!id. t <> StructT id)) /\
    struct_metadata_types_match tops sf /\
    FLOOKUP sf name = SOME fields /\
    EVERY (supported_nested_type leaf fuel tops o FST o SND) fields ==>
    SUM (MAP (type_rank sf o FST o SND) fields) <
    type_rank sf (StructT (NONE,name))
Proof
  completeInduct_on `fuel` >> rpt strip_tac >>
  Cases_on `?n. n <= fuel /\
    supported_nested_type leaf n tops (StructT (NONE,name))`
  >- (pop_assum strip_assume_tac >>
      `0 < n /\
       EVERY (supported_nested_type leaf (n - 1) tops o FST o SND)
         (get_struct_fields sf (nsid_to_string (NONE,name)))` by
        (irule nested_metadata_fields_leaf >> simp[]) >>
      first_x_assum irule >> simp[] >>
      qexistsl_tac [`leaf`, `n - 1`, `tops`] >>
      gvs[get_struct_fields_def, nsid_to_string_def]) >>
  `MAP (type_rank (sf \\ name) o FST o SND) fields =
   MAP (type_rank sf o FST o SND) fields` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     irule nested_type_rank_metadata_invariant_leaf >>
     qexistsl_tac [`fuel`, `leaf`, `tops`] >>
     simp[struct_metadata_types_match_delete, DOMSUB_FLOOKUP_THM] >>
     fs[EVERY_MEM] >> rw[] >> metis_tac[]) >>
  simp[type_rank_def, nsid_to_string_def, get_struct_fields_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> gvs[]
QED

Theorem nested_copy_metadata_acyclic_leaf:
  (!t. leaf t ==> (!e b. t <> ArrayT e b) /\ (!ts. t <> TupleT ts) /\
                  (!id. t <> StructT id)) /\
  struct_metadata_types_match tops sf /\
  FEVERY (λ(name,fields).
    EVERY (supported_nested_type leaf fuel tops o FST o SND) fields) sf ==>
  acyclic_struct_metadata sf
Proof
  rw[acyclic_struct_metadata_def, FEVERY_DEF] >>
  irule nested_fields_rank_leaf >> simp[FLOOKUP_DEF] >>
  qexistsl_tac [`fuel`, `leaf`, `tops`] >> simp[]
QED

(* make_struct_fields_map_acyclic with the struct-field clause of
   supported_declaration_headers stated for any non-aggregate leaf. *)
Theorem struct_fields_map_acyclic_leaf:
  (!t. leaf t ==> (!e b. t <> ArrayT e b) /\ (!ts. t <> TupleT ts) /\
                  (!id. t <> StructT id)) /\
  struct_args_unique tops /\
  (!name fields. MEM (StructDecl name fields) tops ==>
     EVERY (supported_nested_type leaf (LENGTH tops) tops o SND) fields) ==>
  acyclic_struct_metadata (make_struct_fields_map tops)
Proof
  strip_tac >> irule nested_copy_metadata_acyclic_leaf >>
  qexistsl_tac [`LENGTH tops`, `leaf`, `tops`] >>
  simp[make_struct_fields_map_types_match] >>
  simp[make_struct_fields_map_def] >> irule built_struct_fields_every >>
  simp[FEVERY_FEMPTY] >> metis_tac[]
QED

(* The flag leaf: struct fields whose place types have flag leaves. *)
Theorem flag_struct_fields_map_acyclic:
  struct_args_unique tops /\
  (!name fields. MEM (StructDecl name fields) tops ==>
     EVERY (supported_nested_type
              (\t. supported_scalar_type t \/ ?n. t = FlagT n)
              (LENGTH tops) tops o SND) fields) ==>
  acyclic_struct_metadata (make_struct_fields_map tops)
Proof
  strip_tac >> irule struct_fields_map_acyclic_leaf >> simp[] >>
  qexists_tac `\t. supported_scalar_type t \/ ?n. t = FlagT n` >>
  conj_tac >- fs[] >>
  Cases >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def]
QED
