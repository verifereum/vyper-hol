(* Whitelist removal: the type and expression-form clauses of the compiler
   whitelist (supportedTypes, supportedExprForms) that the source type checker
   already discharges.  Each theorem takes the checker fact as premise and
   concludes the whitelist clause as written there.  Where the checker rules
   out only part of a clause, the conclusion is the clause or the residual
   forms the checker still admits (the forms other whitelist rows cover), so
   a simulation case can split on it. *)
Theory whitelistCheckerTypes
Ancestors
  supportedExprForms supportedTypes vyperTypeSystem vyperContext vyperValue
  vyperAST vyperMisc exprLowering placeTypingProps abiCallerStructSize
  alist finite_map list pred_set pair arithmetic

Theorem IS_SOME_COND[local]:
  IS_SOME (if b then SOME x else NONE) <=> b
Proof
  Cases_on `b` >> simp[]
QED

(* ===== Well-formed types ===== *)

(* Row 1: integer widths. *)
Theorem well_formed_int_width:
  (well_formed_type tenv (BaseT (UintT n)) ==> supported_int_width n) /\
  (well_formed_type tenv (BaseT (IntT n)) ==> supported_int_width n)
Proof
  rw[well_formed_type_def, evaluate_type_def, supported_int_width_def,
     IS_SOME_COND] >>
  CCONTR_TAC >> `n < 8` by decide_tac >> gvs[LESS_MOD]
QED

Theorem well_formed_integer_type:
  well_formed_type tenv ty /\ is_int_type ty ==> supported_integer_type ty
Proof
  Cases_on `ty` >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_integer_type_def] >> metis_tac[well_formed_int_width]
QED

Theorem well_formed_numeric_type:
  well_formed_type tenv ty /\ is_numeric_type ty ==> supported_numeric_type ty
Proof
  rw[supported_numeric_type_def] >>
  metis_tac[well_formed_integer_type, is_numeric_type_def]
QED

(* Row 3: bytesM has M <= 32; bytes0 (row 2) and bytes20 (row 4) remain. *)
Theorem well_formed_fixed_bytes_word:
  well_formed_type tenv (BaseT (BytesT (Fixed n))) ==>
  supported_word_type (BaseT (BytesT (Fixed n))) \/ n = 0 \/ n = 20
Proof
  rw[well_formed_type_def, evaluate_type_def, supported_word_type_def,
     IS_SOME_COND] >> decide_tac
QED

(* A well-formed base type is a whitelisted scalar, bytes0 or bytes20. *)
Theorem well_formed_base_scalar:
  well_formed_type tenv (BaseT bt) ==>
  supported_scalar_type (BaseT bt) \/
  bt = BytesT (Fixed 0) \/ bt = BytesT (Fixed 20)
Proof
  rw[] >> Cases_on `bt` >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
  imp_res_tac well_formed_int_width >> simp[] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[supported_string_type_def] >>
  imp_res_tac well_formed_fixed_bytes_word >>
  gvs[supported_word_type_def]
QED

(* Rows 12 and 18: fixed arrays are non-empty. *)
Theorem well_formed_fixed_array_nonempty:
  well_formed_type tenv (ArrayT elem (Fixed n)) ==> 0 < n
Proof
  simp[well_formed_type_def, evaluate_type_def] >>
  Cases_on `evaluate_type tenv elem` >> simp[IS_SOME_COND]
QED

(* Row 25: map keys are never decimals or aggregates; bytesM keys other
   than bytes32 (row 23) and flag keys (row 24) remain. *)
Theorem well_formed_hashmap_key_supported:
  well_formed_vtype tenv (HashMapT kt vt) ==>
  supported_hashmap_key_type kt \/
  (?m. kt = BaseT (BytesT (Fixed m)) /\ m <> 32) \/ (?id. kt = FlagT id)
Proof
  rw[well_formed_vtype_def] >> imp_res_tac well_formed_int_width >>
  Cases_on `kt` >> gvs[hashmap_key_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[hashmap_key_type_def, supported_hashmap_key_type_def,
      supported_integer_type_def, supported_string_type_def] >>
  imp_res_tac well_formed_int_width >> simp[] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[supported_string_type_def]
QED

(* Row 28: unsigned and signed operand widths. *)
Theorem well_formed_unsigned_signed:
  (well_formed_type tenv ty /\ is_uint_type ty ==> supported_unsigned_type ty) /\
  (well_formed_type tenv (BaseT (IntT n)) ==>
   supported_signed_type (BaseT (IntT n)))
Proof
  rw[] >> simp[supported_unsigned_type_def, supported_signed_type_def] >>
  metis_tac[well_formed_int_width]
QED

(* ===== Struct declarations ===== *)

(* The checker's type environment resolves a struct exactly where the
   whitelist does: first declaration of the name, main module only. *)
Theorem type_env_struct_fields:
  !tops id args.
    FLOOKUP (type_env tops) id = SOME (StructArgs args) ==>
    supported_struct_fields tops id = SOME args
Proof
  simp[type_env_def] >> Induct >>
  simp[type_env_for_module_def, FORALL_PROD] >> Cases >>
  rw[type_env_for_module_def, FLOOKUP_UPDATE, supported_struct_fields_def] >>
  first_x_assum drule >> Cases_on `p_1` >>
  gvs[supported_struct_fields_other_module]
QED

Theorem type_env_card_le:
  !tops. CARD (FDOM (type_env_for_module src tops)) <= LENGTH tops
Proof
  Induct >> simp[type_env_for_module_def] >> Cases >>
  simp[type_env_for_module_def, FDOM_FUPDATE, CARD_INSERT] >> rw[] >> fs[]
QED

Theorem type_size_mem_tuple[local]:
  !tys t. MEM t tys ==> type_size t < type_size (TupleT tys)
Proof
  Induct >> rw[type_size_def, list_size_def] >> res_tac >>
  fs[type_size_def, list_size_def]
QED

(* Beyond the declaration count, the expansion fuel of supported_nested_type
   no longer matters for a well-formed type. *)
Theorem supported_nested_type_fuel_irrelevant:
  !n tenv ty fuel fuel' leaf tops.
    CARD (FDOM tenv) = n /\ well_formed_type tenv ty /\
    n <= fuel /\ fuel <= fuel' /\
    (!id args. FLOOKUP tenv id = SOME (StructArgs args) ==>
               supported_struct_fields tops id = SOME args) ==>
    (supported_nested_type leaf fuel' tops ty <=>
     supported_nested_type leaf fuel tops ty)
Proof
  completeInduct_on `n` >> gen_tac >>
  measureInduct_on `type_size ty` >> rpt strip_tac >> gvs[] >>
  Cases_on `ty`
  >~ [`ArrayT elem bd`]
  >- (`well_formed_type tenv elem`
        by (fs[well_formed_type_def] >>
            Cases_on `evaluate_type tenv elem` >>
            qpat_x_assum `IS_SOME _` mp_tac >>
            simp[Once evaluate_type_def]) >>
      first_x_assum (qspec_then `elem` mp_tac) >> simp[type_size_def] >>
      disch_then (qspecl_then [`fuel`, `fuel'`, `leaf`, `tops`] mp_tac) >>
      impl_tac >- gvs[] >> strip_tac >>
      ONCE_REWRITE_TAC[supported_nested_type_def] >>
      Cases_on `bd` >> simp[])
  >~ [`TupleT tys`]
  >- (`EVERY (well_formed_type tenv) tys`
        by (qpat_x_assum `well_formed_type _ _` mp_tac >>
            simp[well_formed_type_def, Once evaluate_type_def] >>
            Cases_on `evaluate_types tenv tys []` >> simp[] >>
            gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF, EVERY_MEM,
                MEM_MAP, PULL_EXISTS, well_formed_type_def]) >>
      `!t. MEM t tys ==>
           (supported_nested_type leaf fuel' tops t <=>
            supported_nested_type leaf fuel tops t)`
        by (rw[] >> first_x_assum (qspec_then `t` mp_tac) >>
            simp[type_size_mem_tuple] >>
            disch_then (qspecl_then [`fuel`, `fuel'`, `leaf`, `tops`] mp_tac) >>
            impl_tac >- gvs[EVERY_MEM] >> simp[]) >>
      ONCE_REWRITE_TAC[supported_nested_type_def] >> gvs[EVERY_MEM])
  >~ [`StructT id`]
  >- (`?args. FLOOKUP tenv id = SOME (StructArgs args) /\
              EVERY (well_formed_type (tenv \\ id)) (MAP SND args)`
        by (qpat_x_assum `well_formed_type _ _` mp_tac >>
            simp[well_formed_type_def, Once evaluate_type_def] >>
            Cases_on `FLOOKUP tenv id` >> simp[] >>
            rename1 `SOME ta` >> Cases_on `ta` >> simp[] >>
            rename1 `StructArgs args` >>
            Cases_on `evaluate_types (tenv \\ id) (MAP SND args) []` >>
            simp[] >>
            gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF, EVERY_MEM,
                MEM_MAP, PULL_EXISTS, well_formed_type_def]) >>
      `supported_struct_fields tops id = SOME args` by metis_tac[] >>
      `id IN FDOM tenv` by gvs[flookup_thm] >>
      `0 < CARD (FDOM tenv)`
        by (spose_not_then assume_tac >>
            `CARD (FDOM tenv) = 0` by decide_tac >>
            gvs[CARD_EQ_0, FDOM_FINITE]) >>
      `CARD (FDOM (tenv \\ id)) = CARD (FDOM tenv) - 1`
        by simp[FDOM_DOMSUB, CARD_DELETE, FDOM_FINITE] >>
      `fuel <> 0 /\ fuel' <> 0` by decide_tac >>
      `!p. MEM p args ==>
           (supported_nested_type leaf (fuel' - 1) tops (SND p) <=>
            supported_nested_type leaf (fuel - 1) tops (SND p))`
        by (rw[] >>
            last_x_assum (qspec_then `CARD (FDOM (tenv \\ id))` mp_tac) >>
            impl_tac >- decide_tac >>
            disch_then (qspecl_then [`tenv \\ id`, `SND p`, `fuel - 1`,
                                     `fuel' - 1`, `leaf`, `tops`] mp_tac) >>
            impl_tac
            >- (gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, DOMSUB_FLOOKUP_THM] >>
                rw[] >> metis_tac[]) >>
            simp[]) >>
      ONCE_REWRITE_TAC[supported_nested_type_def] >>
      qpat_x_assum `supported_struct_fields _ _ = _` (fn th => simp[th]) >>
      gvs[EVERY_MEM])
  >> ONCE_REWRITE_TAC[supported_nested_type_def] >> simp[]
QED

(* Row 13: the declaration count LENGTH tops, the fuel of
   supported_place_type and supported_storage_type, is never exhausted for a
   type the checker accepts: more fuel changes nothing. *)
Theorem supported_nested_type_type_env_fuel:
  well_formed_type (type_env tops) ty /\ LENGTH tops <= fuel ==>
  (supported_nested_type leaf fuel tops ty <=>
   supported_nested_type leaf (LENGTH tops) tops ty)
Proof
  strip_tac >> irule supported_nested_type_fuel_irrelevant >>
  simp[type_env_struct_fields] >>
  qexists `type_env tops` >> simp[type_env_struct_fields] >>
  metis_tac[type_env_card_le, type_env_def]
QED

(* ===== Copies ===== *)

(* Row 21: the checker types literal elements and struct fields exactly, and
   an exact copy is whitelisted. *)
Theorem supported_copy_types_refl:
  supported_copy_types ty ty
Proof
  simp[supported_copy_types_def]
QED

(* The copy-types conjunct of supported_stmt's AnnAssign clause: the checker
   lets the right-hand side's type widen to the declared type. *)
Theorem type_stmt_annassign_copy_types:
  !env ret_ty id typ e env'.
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' ==>
    supported_copy_types typ (expr_type e) \/ arg_type_fits (expr_type e) typ
Proof
  rpt strip_tac >> gvs[type_stmt_def, AllCaseEqs(), type_widens_to_def] >>
  metis_tac[supported_copy_types_refl]
QED

(* ===== Binary operators ===== *)

Theorem int_literal_value_supported:
  IS_SOME (int_literal_value e) <=> supported_integer_literal e
Proof
  Cases_on `e` >> simp[int_literal_value_def, supported_integer_literal_def] >>
  rename1 `Literal _ l` >> Cases_on `l` >>
  simp[int_literal_value_def, supported_integer_literal_def]
QED

Theorem nonneg_int_literal_supported:
  nonneg_int_literal e <=> supported_nonnegative_literal e
Proof
  Cases_on `e` >>
  simp[nonneg_int_literal_def, int_literal_value_def,
       supported_nonnegative_literal_def] >>
  rename1 `Literal _ l` >> Cases_on `l` >>
  simp[int_literal_value_def, supported_nonnegative_literal_def]
QED

(* Row 29. *)
Theorem well_typed_binop_arith_supported:
  well_typed_binop ty op t1 t2 /\ well_formed_type tenv t1 /\
  (op = Add \/ op = Sub \/ op = Mul \/ op = Div \/ op = Mod) ==>
  supported_binop op t1 t2 lb ne
Proof
  rw[] >> gvs[well_typed_binop_def, supported_binop_def] >>
  metis_tac[well_formed_numeric_type, is_numeric_type_def]
QED

(* Row 30. *)
Theorem well_typed_binop_exp_supported:
  well_typed_binop ty (Exp) (expr_type a) (expr_type b) /\
  well_formed_type tenv (expr_type a) /\
  builtin_operands_ok (Bop Exp) [a; b] ==>
  supported_binop Exp (expr_type a) (expr_type b)
    (supported_integer_literal a) (supported_nonnegative_literal b)
Proof
  rw[well_typed_binop_def, builtin_operands_ok_def, supported_binop_def,
     int_literal_value_supported, nonneg_int_literal_supported] >>
  metis_tac[well_formed_integer_type]
QED

(* Row 31. *)
Theorem well_typed_binop_unsafe_supported:
  well_typed_binop ty op t1 t2 /\ well_formed_type tenv t1 /\
  (op = UnsafeAdd \/ op = UnsafeSub \/ op = UnsafeMul \/ op = UnsafeDiv) ==>
  supported_binop op t1 t2 lb ne
Proof
  rw[] >> gvs[well_typed_binop_def, supported_binop_def] >>
  metis_tac[well_formed_integer_type]
QED

(* Rows 34 and 35 (narrow): shifts take an integer, << only a 256-bit one;
   a non-negative literal amount of signed type (row 33) remains. *)
Theorem well_typed_binop_shift_supported:
  well_typed_binop ty op (expr_type a) (expr_type b) /\
  well_formed_type tenv (expr_type a) /\ well_formed_type tenv (expr_type b) /\
  builtin_operands_ok (Bop op) [a; b] /\ (op = ShL \/ op = ShR) ==>
  supported_binop op (expr_type a) (expr_type b) lb ne \/
  (supported_nonnegative_literal b /\ ~is_uint_type (expr_type b))
Proof
  rpt strip_tac >>
  `is_int_type (expr_type a)` by gvs[well_typed_binop_def] >>
  `supported_integer_type (expr_type a)`
    by metis_tac[well_formed_integer_type] >>
  `is_uint_type (expr_type b) ==> supported_unsigned_type (expr_type b)`
    by metis_tac[well_formed_unsigned_signed] >>
  gvs[well_typed_binop_def, supported_binop_def, builtin_operands_ok_def,
      shift_amount_ok_def, nonneg_int_literal_supported] >>
  metis_tac[]
QED

(* Row 38: == and != never take aggregates; bytestrings (row 36), flags
   (row 37), bytes0 (row 2) and bytes20 (row 4) remain. *)
Theorem well_typed_binop_eq_supported:
  well_typed_binop ty op t1 t2 /\ well_formed_type tenv t1 /\
  (op = Eq \/ op = NotEq) ==>
  supported_binop op t1 t2 lb ne \/ supported_string_type t1 \/
  (?id. t1 = FlagT id) \/
  t1 = BaseT (BytesT (Fixed 0)) \/ t1 = BaseT (BytesT (Fixed 20))
Proof
  rw[] >> Cases_on `t1` >> gvs[well_typed_binop_def, supported_binop_def] >>
  drule well_formed_base_scalar >> rw[supported_scalar_type_def] >> simp[]
QED

(* Row 39. *)
Theorem well_typed_binop_compare_supported:
  well_typed_binop ty op t1 t2 /\ well_formed_type tenv t1 /\
  (op = Lt \/ op = LtE \/ op = Gt \/ op = GtE \/ op = Min \/ op = Max) ==>
  supported_binop op t1 t2 lb ne
Proof
  rw[] >> gvs[well_typed_binop_def, supported_binop_def] >>
  metis_tac[well_formed_numeric_type, is_numeric_type_def]
QED

(* Row 40. *)
Theorem well_typed_binop_not_expmod:
  ~well_typed_binop ty ExpMod t1 t2
Proof
  simp[well_typed_binop_def]
QED

(* ===== Builtins ===== *)

(* Row 44: the checker fixes the arity of every builtin the whitelist
   matches by shape. *)
Theorem well_typed_builtin_app_arity:
  well_typed_builtin_app ty blt ts ==>
  case blt of
    Bop _ => LENGTH ts = 2
  | Not => LENGTH ts = 1
  | Neg => LENGTH ts = 1
  | Abs => LENGTH ts = 1
  | AsWeiValue _ => LENGTH ts = 1
  | AddMod => LENGTH ts = 3
  | MulMod => LENGTH ts = 3
  | PowMod256 => LENGTH ts = 2
  | Env _ => LENGTH ts = 0
  | Acc _ => LENGTH ts = 1
  | BlockHash => LENGTH ts = 1
  | BlobHash => LENGTH ts = 1
  | ECRecover => LENGTH ts = 4
  | ECAdd => LENGTH ts = 2
  | ECMul => LENGTH ts = 2
  | Uint2Str _ => LENGTH ts = 1
  | CalldataSlice _ => LENGTH ts = 1
  | _ => T
Proof
  Cases_on `blt` >> rw[well_typed_builtin_app_def] >> simp[]
QED

(* Row 42 (copies and shape): a literal is typed at a tuple of its element
   types or at an array of their common type, so supported_literal_elements
   reduces to the element-type parts. *)
Theorem well_typed_make_array_literal_elements:
  well_typed_builtin_app ty (MakeArray eo bd) (MAP expr_type es) ==>
  (supported_literal_elements tops ty es <=>
   supported_place_type tops ty /\
   (!tys. ty = TupleT tys ==> supported_tuple_type ty))
Proof
  Cases_on `eo` >> rw[well_typed_builtin_app_def] >>
  simp[supported_literal_elements_def]
  >- (`LIST_REL supported_copy_types (MAP expr_type es) (MAP expr_type es)`
        by (irule EVERY2_refl >> simp[supported_copy_types_refl]) >>
      simp[])
  >> gvs[EVERY_MAP, EVERY_MEM] >> eq_tac >> rw[] >> res_tac >>
  gvs[supported_copy_types_refl]
QED

(* Row 43 (copies): a struct literal lists the declared fields in order at
   their declared types, so supported_struct_elements reduces to the place
   type.  Field names are distinct by check_contract_struct_fields_distinct
   (with abi_caller_type_env_struct). *)
Theorem well_typed_struct_lit_elements:
  well_typed_expr env (StructLit ty nsid kes) /\
  env.type_defs = type_env tops /\ ALL_DISTINCT (MAP FST kes) ==>
  (supported_struct_elements tops ty kes <=> supported_place_type tops ty)
Proof
  rw[well_typed_expr_def] >>
  `FLOOKUP (type_env tops) nsid = SOME (StructArgs args)` by fs[] >>
  drule type_env_struct_fields >> strip_tac >>
  `!n. n < LENGTH kes ==>
       ALOOKUP args (FST (EL n kes)) = SOME (expr_type (SND (EL n kes)))`
    by (rw[] >>
        `LENGTH args = LENGTH kes` by metis_tac[LENGTH_MAP] >>
        `ALL_DISTINCT (MAP FST args)` by metis_tac[] >>
        `EL n (MAP FST kes) = EL n (MAP FST args) /\
         EL n (MAP (expr_type o SND) kes) = EL n (MAP SND args)`
          by metis_tac[] >>
        gvs[EL_MAP] >> metis_tac[ALOOKUP_ALL_DISTINCT_EL]) >>
  `EVERY (\(name,e). case ALOOKUP args name of
                       SOME dst => supported_copy_types dst (expr_type e)
                     | NONE => F) kes`
    by (simp[EVERY_EL] >> rw[] >> first_x_assum drule >>
        Cases_on `EL n kes` >> simp[supported_copy_types_refl]) >>
  simp[supported_struct_elements_def] >>
  qpat_x_assum `supported_struct_fields _ _ = _` (fn th => simp[th]) >>
  qpat_x_assum `EVERY _ kes` (fn th => simp[th])
QED

(* Row 46. *)
Theorem well_typed_neg_supported:
  well_typed_builtin_app ty Neg ts /\ well_formed_type tenv ty ==>
  supported_signed_type ty \/ ty = BaseT DecimalT
Proof
  rw[well_typed_builtin_app_def] >> Cases_on `ty` >> gvs[] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[] >>
  metis_tac[well_formed_unsigned_signed]
QED

(* Row 47. *)
Theorem well_typed_abs_supported:
  well_typed_builtin_app ty Abs ts ==> ty = BaseT (IntT 256)
Proof
  rw[well_typed_builtin_app_def]
QED

(* Row 48. *)
Theorem well_typed_as_wei_value_supported:
  well_typed_builtin_app ty (AsWeiValue d) [t] /\ well_formed_type tenv t ==>
  supported_unsigned_type t
Proof
  rw[well_typed_builtin_app_def] >> simp[supported_unsigned_type_def] >>
  metis_tac[well_formed_int_width]
QED

(* Row 49. *)
Theorem well_typed_mod_arith_supported:
  well_typed_builtin_app ty blt (MAP expr_type es) /\
  (blt = AddMod \/ blt = MulMod \/ blt = PowMod256) ==>
  EVERY (supported_unsigned_type o expr_type) es
Proof
  `!ts. well_typed_builtin_app ty blt ts /\
        (blt = AddMod \/ blt = MulMod \/ blt = PowMod256) ==>
        EVERY supported_unsigned_type ts`
    suffices_by (rw[] >> res_tac >> fs[EVERY_MAP, combinTheory.o_DEF]) >>
  rw[EVERY_MEM] >> gvs[well_typed_builtin_app_def, EVERY_MEM] >>
  res_tac >> gvs[supported_unsigned_type_def, supported_int_width_def]
QED

(* Row 52. *)
Theorem well_typed_make_array_type:
  well_typed_builtin_app ty (MakeArray (SOME elem) bnd) ts ==>
  ty = ArrayT elem bnd
Proof
  rw[well_typed_builtin_app_def]
QED

(* Row 53. *)
Theorem well_typed_uint2str_supported:
  well_typed_builtin_app ty (Uint2Str n) [t] /\ well_formed_type tenv t ==>
  supported_unsigned_type t
Proof
  rw[well_typed_builtin_app_def] >> simp[supported_unsigned_type_def] >>
  metis_tac[well_formed_int_width]
QED

(* ===== Type builtins ===== *)

(* Row 63: the checker fixes the arity of every type builtin the whitelist
   matches by shape; abi_encode with several arguments (row 71) remains. *)
Theorem well_typed_type_builtin_args_arity:
  well_typed_type_builtin_args tb target ts ==>
  case tb of
    Empty => ts = []
  | MaxValue => ts = []
  | MinValue => ts = []
  | Epsilon => ts = []
  | Convert => LENGTH ts = 1
  | AbiDecode _ => LENGTH ts = 1
  | AbiEncode _ _ => ts <> []
  | Extract32 => LENGTH ts = 2
Proof
  Cases_on `tb` >> rw[well_typed_type_builtin_args_def]
QED

(* Row 64. *)
Theorem well_typed_empty_target:
  type_builtin_result_ok tenv Empty ty target ts ==> ty = target
Proof
  simp[type_builtin_result_ok_def]
QED

(* Row 66. *)
Theorem well_typed_max_min_value_supported:
  type_builtin_result_ok tenv tb ty target ts /\
  well_typed_type_builtin_args tb target ts /\ well_formed_type tenv ty /\
  (tb = MaxValue \/ tb = MinValue) ==>
  ty = target /\ supported_numeric_type ty
Proof
  rw[] >> gvs[type_builtin_result_ok_def, well_typed_type_builtin_args_def] >>
  metis_tac[well_formed_numeric_type, is_numeric_type_def]
QED

(* Row 67. *)
Theorem well_typed_epsilon_supported:
  type_builtin_result_ok tenv Epsilon ty target ts /\
  well_typed_type_builtin_args Epsilon target ts ==>
  ty = target /\ ty = BaseT DecimalT
Proof
  rw[type_builtin_result_ok_def, well_typed_type_builtin_args_def]
QED

(* Row 68. *)
Theorem well_typed_convert_supported:
  type_builtin_result_ok tenv Convert ty target [t] /\
  well_typed_type_builtin_args Convert target [t] ==>
  ty = target /\ valid_conversion t ty
Proof
  rw[type_builtin_result_ok_def, well_typed_type_builtin_args_def]
QED

(* Row 69. *)
Theorem well_typed_abi_encode_method_id:
  well_typed_type_builtin_args (AbiEncode ensure (SOME mid)) target ts ==>
  LENGTH mid = 4
Proof
  rw[well_typed_type_builtin_args_def]
QED

(* Row 74. *)
Theorem well_typed_abi_decode_target:
  type_builtin_result_ok tenv (AbiDecode unwrap) ty target ts ==> ty = target
Proof
  rw[type_builtin_result_ok_def]
QED

(* Row 77: abi_decode reads a Bytes[n] value, never a bytesM. *)
Theorem well_typed_abi_decode_source:
  well_typed_type_builtin_args (AbiDecode unwrap) target ts ==>
  ?n. ts = [BaseT (BytesT (Dynamic n))]
Proof
  rw[well_typed_type_builtin_args_def] >>
  Cases_on `ts` >> gvs[] >> Cases_on `t` >> gvs[]
QED

(* ===== Places ===== *)

(* Row 90: a subscripted base is an array, a tuple, or a map place, never a
   scalar.  Relating this to supported_place_info's ValPT needs the lowering's
   map table (build_hashmap_info) to agree with the checker's map places. *)
Theorem well_typed_subscript_base:
  well_typed_expr env (Subscript ty e1 e2) ==>
  (?elem bd. expr_type e1 = ArrayT elem bd) \/
  (?tys. expr_type e1 = TupleT tys) \/
  (?kt vt. type_place_expr env e1 = SOME (HashMapT kt vt))
Proof
  rw[well_typed_expr_def]
  >- (Cases_on `expr_type e1` >> gvs[subscript_type_ok_def])
  >> Cases_on `vt` >> gvs[subscript_vtype_def]
  >> rename1 `Type t` >> Cases_on `t` >> gvs[subscript_vtype_def] >>
  drule type_place_expr_annotation >> simp[]
QED

(* Row 92: .field is checked against the struct the checker resolved, which
   is the one the whitelist resolves. *)
Theorem well_typed_attribute_field_place:
  attribute_type_ok (type_env tops) ty fid rty ==>
  supported_field_place tops ty fid
Proof
  Cases_on `ty` >>
  simp[attribute_type_ok_def, attribute_type_def, supported_field_place_def,
       AllCaseEqs()] >>
  rw[] >> drule type_env_struct_fields >> rw[] >>
  drule ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED
