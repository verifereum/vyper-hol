(* Two word-store facts of `self.x = e` for a storage or transient x, kept
   apart from stmtSimAssignStorage so that consumers need neither its
   statement-simulation ancestors nor its finite-storage port. *)
Theory stmtSimAssignStorageFacts
Ancestors
  exprLowering compileEnv valueEncoding valueEncodingProofs
  vyperStorage vyperTyping vyperValue

(* A value of a word type encodes, in one slot, as the word typed_val_to_w256
   gives it. *)
Theorem encode_value_word_typed:
  !tenv t tv v.
    is_word_type t /\ evaluate_type tenv t = SOME tv /\
    value_has_type tv v ==>
    encode_value tv v = SOME [(0, typed_val_to_w256 tv v)]
Proof
  rpt gen_tac >> strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, encode_value_def, encode_base_to_slot_def,
      typed_val_to_w256_def, val_to_w256_def, word_of_bytes_be_pad_right,
      bool_to_slot_def]
QED

(* A storage or transient variable's target pointer is its slot, and no
   code. *)
Theorem compile_get_target_ptr_toplevel:
  !cenv nsid tr slot st.
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE ==>
    compile_get_target_ptr compile_expr cenv (TopLevelNameTarget nsid) st =
      ((Lit slot, SOME (if tr then LocTransient else LocStorage),
        OPTION_MAP ValPT (cenv.ce_module_var_type nsid)), st)
Proof
  Cases_on `tr` >> simp[compile_get_target_ptr_def, comp_return_def]
QED
