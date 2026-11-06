(* TOP-LEVEL: source sparse-array conversion uses the actual complete element
   list, including default values. Static ABI lists encode by concatenation.
   Helpers: optional mapping over a final element and accumulator flattening. *)
Theory sourceAbiArray
Ancestors
  vyperABI vyperABIRoundtrip vyperValueOperation vyperValue vyperMisc contractABI
  list rich_list option alist arithmetic

Theorem OPT_MMAP_SNOC:
  !xs f x.
    OPT_MMAP f (SNOC x xs) =
      (case OPT_MMAP f xs of NONE => NONE | SOME ys =>
         case f x of NONE => NONE | SOME y => SOME (SNOC y ys))
Proof
  Induct_on `xs` >- simp[OPT_MMAP_def, OPTION_BIND_eq_case] >> rpt gen_tac >>
  rename1 `OPT_MMAP f (SNOC x (head::rest))` >>
  Cases_on `f head` >> Cases_on `OPT_MMAP f rest` >> Cases_on `f x` >>
  simp[OPT_MMAP_def, OPTION_BIND_eq_case]
QED

Theorem vyper_to_abi_sparse_GENLIST:
  !n env t tv sparse.
    evaluate_type env t = SOME tv ==>
    vyper_to_abi_sparse env t tv n sparse =
      OPT_MMAP (vyper_to_abi env t)
        (GENLIST (\i. case ALOOKUP sparse i of
           NONE => default_value tv | SOME v => v) n)
Proof
  Induct_on `n` >- simp[Once vyper_to_abi_def, OPT_MMAP_def] >>
  rpt gen_tac >> DISCH_TAC >>
  `vyper_to_abi env t (default_value tv) = SOME (default_to_abi tv)` by
    (drule (CONJUNCT1 vyper_to_abi_default_value) >> simp[]) >>
  Cases_on `ALOOKUP sparse n` >>
  simp[Once vyper_to_abi_def, GENLIST, OPT_MMAP_SNOC] >> simp[SNOC_APPEND]
QED

Theorem vyper_to_abi_sparse_elements:
  !env t tv n sparse.
    evaluate_type env t = SOME tv ==>
    vyper_to_abi_sparse env t tv n sparse =
      vyper_to_abi_same env t
        (array_elements (ArrayTV tv (Fixed n)) (SArrayV sparse))
Proof
  simp[vyper_to_abi_same_OPT_MMAP, array_elements_def, vyper_to_abi_sparse_GENLIST]
QED

Theorem vyper_to_abi_same_EL:
  !env t vs avs.
    vyper_to_abi_same env t vs = SOME avs ==>
    LENGTH avs = LENGTH vs /\
    (!i. i < LENGTH vs ==> vyper_to_abi env t (EL i vs) = SOME (EL i avs))
Proof
  simp[vyper_to_abi_same_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
  rpt strip_tac >> gvs[EVERY_EL, EL_MAP, IS_SOME_EXISTS] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> fs[]
QED

Theorem enc_tuple_static_acc:
  !ts vs hl tl hds tls.
    ~any_dynamic ts ==>
    enc_tuple hl tl ts vs hds tls =
      FLAT (REVERSE hds) ++ FLAT (MAP2 enc ts vs) ++ FLAT (REVERSE tls)
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  simp[Once enc_def, is_dynamic_def, REV_REVERSE_LEM, FLAT_APPEND, APPEND_ASSOC]
QED

Theorem enc_tuple_static_values:
  !ts vs.
    ~any_dynamic ts ==>
    enc (Tuple ts) (ListV vs) = FLAT (MAP2 enc ts vs)
Proof
  rpt strip_tac >> simp[Once enc_def, enc_tuple_static_acc]
QED

Theorem enc_tuple_static_cons:
  !ty ts v vs.
    ~is_dynamic ty /\ ~any_dynamic ts ==>
    enc (Tuple (ty::ts)) (ListV (v::vs)) =
      enc ty v ++ enc (Tuple ts) (ListV vs)
Proof
  rpt strip_tac >> simp[enc_tuple_static_values]
QED

Theorem enc_array_static_values:
  !bound elem_type vs.
    ~is_dynamic elem_type ==>
    enc (Array (SOME bound) elem_type) (ListV vs) = FLAT (MAP (enc elem_type) vs)
Proof
  rpt strip_tac >>
  simp[Once enc_def, enc_tuple_static_acc, any_dynamic_EXISTS, EXISTS_MEM] >>
  qid_spec_tac `vs` >> Induct >> simp[]
QED

Theorem enc_dynamic_array_static_values:
  !elem_type vs.
    ~is_dynamic elem_type ==>
    enc (Array NONE elem_type) (ListV vs) =
      enc_number (Uint 256) (NumV (LENGTH vs)) ++ FLAT (MAP (enc elem_type) vs)
Proof
  rpt strip_tac >>
  simp[Once enc_def, enc_tuple_static_acc, any_dynamic_EXISTS, EXISTS_MEM] >>
  AP_TERM_TAC >> qid_spec_tac `vs` >> Induct >> simp[]
QED
