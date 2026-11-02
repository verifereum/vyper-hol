(* Meaningful immutable bytes agree with the canonical encoder. Only unused
   bytestring capacity and inactive dynamic-array elements are padding.
   Omitted fixed-array elements still have their source default values. *)
Theory immutableValue
Ancestors
  immutableEncoding valueEncoding vyperValue integer_word list alist
Libs wordsLib intLib

Definition immutable_mask_fit_def:
  immutable_mask_fit n (mask:bool list) = TAKE n (mask ++ REPLICATE n F)
End

Theorem immutable_mask_fit_length[simp]:
  !n mask. LENGTH (immutable_mask_fit n mask) = n
Proof
  simp[immutable_mask_fit_def]
QED

Definition immutable_value_mask_def:
  immutable_value_mask (BaseTV bt) v =
    immutable_mask_fit (type_memory_size (BaseTV bt))
      (case (bt,v) of
         (StringT _, StringV text) => REPLICATE (32 + LENGTH text) T
       | (BytesT (Dynamic _), BytesV bs) => REPLICATE (32 + LENGTH bs) T
       | _ => REPLICATE 32 T) /\
  immutable_value_mask (FlagTV _) v = REPLICATE 32 T /\
  immutable_value_mask NoneTV v = [] /\
  immutable_value_mask (TupleTV tvs) v =
    immutable_mask_fit (type_memory_size (TupleTV tvs))
      (case v of ArrayV (TupleV vs) => immutable_tuple_mask tvs vs | _ => []) /\
  immutable_value_mask (StructTV fields) v =
    immutable_mask_fit (type_memory_size (StructTV fields))
      (case v of StructV vs => immutable_fields_mask fields vs | _ => []) /\
  immutable_value_mask (ArrayTV tv bound) v =
    immutable_mask_fit (type_memory_size (ArrayTV tv bound))
      (case (bound,v) of
         (Fixed n, ArrayV (SArrayV kvs)) =>
           FLAT (GENLIST (\i. immutable_value_mask tv
             (case ALOOKUP kvs i of NONE => default_value tv | SOME x => x)) n)
       | (Dynamic _, ArrayV (DynArrayV vs)) =>
           REPLICATE 32 T ++ FLAT (MAP (immutable_value_mask tv) vs)
       | _ => []) /\
  immutable_tuple_mask [] vs = [] /\
  immutable_tuple_mask (tv::tvs) vs =
    (case vs of
       [] => immutable_value_mask tv (default_value tv) ++ immutable_tuple_mask tvs []
     | v::rest => immutable_value_mask tv v ++ immutable_tuple_mask tvs rest) /\
  immutable_fields_mask [] vs = [] /\
  immutable_fields_mask ((name,tv)::fields) vs =
    (case vs of
       [] => immutable_value_mask tv (default_value tv) ++ immutable_fields_mask fields []
     | (id,v)::rest => immutable_value_mask tv v ++ immutable_fields_mask fields rest)
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (tv,v) => type_value_size tv
    | INR (INL (tvs,vs)) => list_size type_value_size tvs
    | INR (INR (fields,vs)) =>
        list_size (pair_size (\x. 0) type_value_size) fields)` >>
  rw[] >> Induct_on `fields` >> rw[] >> Cases_on `h` >> rw[]
End

Theorem immutable_value_mask_length[simp]:
  !tv v. LENGTH (immutable_value_mask tv v) = type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `tv` >>
  simp[Once immutable_value_mask_def, type_memory_size_def]
QED

(* Admissibility is a separate source-typing obligation. This predicate checks
   byte agreement, including semantic defaults omitted from a sparse array. *)
Definition immutable_value_bytes_rel_def:
  immutable_value_bytes_rel tv v (bytes:word8 list) <=>
    LENGTH bytes = type_memory_size tv /\
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (immutable_value_mask tv v,
            ZIP (bytes, encode_immutable_value tv v)))
End

Theorem immutable_mask_same_bytes:
  !mask bytes. LENGTH mask = LENGTH bytes ==>
    EVERY (\(used,(actual,expected)). used ==> actual = expected)
      (ZIP (mask, ZIP (bytes,bytes)))
Proof
  Induct >> rpt gen_tac >> Cases_on `bytes` >> simp[]
QED

Theorem immutable_value_bytes_encoded[simp]:
  !tv v. immutable_value_bytes_rel tv v (encode_immutable_value tv v)
Proof
  rpt gen_tac >> simp[immutable_value_bytes_rel_def] >>
  irule immutable_mask_same_bytes >> simp[]
QED

Theorem immutable_value_bytes_slice:
  TAKE (type_memory_size tv) (DROP off mem) = encode_immutable_value tv v ==>
  immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) mem)
Proof
  strip_tac >>
  `LENGTH (TAKE (type_memory_size tv) (DROP off mem)) = type_memory_size tv` by
    asm_rewrite_tac[encode_immutable_value_length] >>
  `type_memory_size tv <= LENGTH (DROP off mem)` by
    (qpat_x_assum `LENGTH (TAKE _ _) = _`
       (mp_tac o REWRITE_RULE [LENGTH_TAKE_EQ]) >> rw[] >> decide_tac) >>
  simp[mem_bytes_at_def, TAKE_APPEND1]
QED

val immutable_value_probe_conv = computeLib.CBV_CONV
  (computeLib.add_thms [i2w_pos, i2w_def]
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))));

Theorem immutable_string_padding_allowed:
  immutable_value_bytes_rel (BaseTV (StringT 40)) (StringV "a")
    (REPLICATE 31 0w ++ [1w;97w] ++ REPLICATE 62 0w ++ [1w])
Proof
  CONV_TAC immutable_value_probe_conv
QED

Theorem immutable_sparse_defaults_checked:
  ~immutable_value_bytes_rel (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
    (ArrayV (SArrayV [])) (REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w)
Proof
  CONV_TAC immutable_value_probe_conv
QED

Theorem immutable_dynamic_capacity_padding_allowed:
  immutable_value_bytes_rel (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
    (ArrayV (DynArrayV [IntV 7]))
    (REPLICATE 31 0w ++ [1w] ++ REPLICATE 31 0w ++ [7w] ++
      REPLICATE 31 0w ++ [1w])
Proof
  CONV_TAC immutable_value_probe_conv
QED

Theorem immutable_sparse_string_padding_allowed:
  immutable_value_bytes_rel (ArrayTV (BaseTV (StringT 40)) (Fixed 1))
    (ArrayV (SArrayV [])) (REPLICATE 95 0w ++ [1w])
Proof
  CONV_TAC immutable_value_probe_conv
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed immutable byte relation: " ^ name)
  end) (DB.thms "immutableValue");
