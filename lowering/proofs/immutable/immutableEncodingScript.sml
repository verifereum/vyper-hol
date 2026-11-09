Theory immutableEncoding
Ancestors
  valueEncoding

(* Total capacity fitting. Padding is deliberately canonical zero padding;
   semantic memory correspondence alone does not imply this exact encoding. *)
Definition immutable_fit_def:
  immutable_fit n (bs:word8 list) = TAKE n (bs ++ REPLICATE n 0w)
End

Theorem immutable_fit_length[simp]:
  LENGTH (immutable_fit n bs) = n
Proof
  simp[immutable_fit_def]
QED

Definition immutable_word_bytes_def:
  immutable_word_bytes (w:bytes32) = word_to_bytes w T
End

Definition encode_immutable_value_def:
  encode_immutable_value (BaseTV bt) v =
    immutable_fit (type_memory_size (BaseTV bt))
      (case (bt,v) of
         (StringT n, StringV s) =>
           immutable_word_bytes (n2w (LENGTH s)) ++ MAP (n2w o ORD) s
       | (BytesT (Dynamic n), BytesV bs) =>
           immutable_word_bytes (n2w (LENGTH bs)) ++ bs
       | _ => immutable_word_bytes (typed_val_to_w256 (BaseTV bt) v)) /\
  encode_immutable_value (FlagTV k) v =
    immutable_fit 32 (immutable_word_bytes (typed_val_to_w256 (FlagTV k) v)) /\
  encode_immutable_value NoneTV v = [] /\
  encode_immutable_value (TupleTV tvs) v =
    immutable_fit (type_memory_size (TupleTV tvs))
      (case v of ArrayV (TupleV vs) => encode_immutable_tuple tvs vs | _ => []) /\
  encode_immutable_value (StructTV fields) v =
    immutable_fit (type_memory_size (StructTV fields))
      (case v of StructV vs => encode_immutable_fields fields vs | _ => []) /\
  encode_immutable_value (ArrayTV tv bound) v =
    immutable_fit (type_memory_size (ArrayTV tv bound))
      (case (bound,v) of
         (Fixed n, ArrayV (SArrayV kvs)) =>
           FLAT (GENLIST (\i. case ALOOKUP kvs i of
             NONE => REPLICATE (type_memory_size tv) 0w
           | SOME x => encode_immutable_value tv x) n)
       | (Dynamic n, ArrayV (DynArrayV vs)) =>
           immutable_word_bytes (n2w (LENGTH vs)) ++
           FLAT (MAP (encode_immutable_value tv) vs)
       | _ => []) /\
  encode_immutable_tuple [] vs = [] /\
  encode_immutable_tuple (tv::tvs) vs =
    (case vs of [] => REPLICATE (type_memory_size_list (tv::tvs)) 0w
     | v::rest => encode_immutable_value tv v ++ encode_immutable_tuple tvs rest) /\
  encode_immutable_fields [] vs = [] /\
  encode_immutable_fields ((name,tv)::fields) vs =
    (case vs of [] => REPLICATE (type_memory_size_fields ((name,tv)::fields)) 0w
     | (id,v)::rest => encode_immutable_value tv v ++ encode_immutable_fields fields rest)
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (tv,v) => type_value_size tv
    | INR (INL (tvs,vs)) => list_size type_value_size tvs
    | INR (INR (fields,vs)) =>
        list_size (pair_size (\x. 0) type_value_size) fields)` >>
  rw[] >> Induct_on `fields` >> rw[] >> Cases_on `h` >> rw[]
End

Theorem encode_immutable_value_length[simp]:
  LENGTH (encode_immutable_value tv v) = type_memory_size tv
Proof
  Cases_on `tv` >> simp[Once encode_immutable_value_def, type_memory_size_def]
QED

(* Structural admissibility is stronger than val_wf: in particular sparse
   keys are unique, and heterogeneous layouts have exactly matching shapes. *)
Definition immutable_value_admissible_def:
  immutable_value_admissible (BaseTV bt) v =
    (case (bt,v) of
       (BoolT, BoolV b) => T
     | (UintT n, IntV i) => T
     | (IntT n, IntV i) => T
     | (DecimalT, DecimalV i) => T
     | (AddressT, BytesV bs) => LENGTH bs = 20
     | (BytesT (Fixed n), BytesV bs) => LENGTH bs = n /\ n <= 32
     | (BytesT (Dynamic n), BytesV bs) => LENGTH bs <= n
     | (StringT n, StringV s) => LENGTH s <= n
     | _ => F) /\
  immutable_value_admissible (FlagTV k) v =
    (case v of FlagV n => T | _ => F) /\
  immutable_value_admissible NoneTV v = (v = NoneV) /\
  immutable_value_admissible (TupleTV tvs) v =
    (case v of ArrayV (TupleV vs) => immutable_tuple_admissible tvs vs | _ => F) /\
  immutable_value_admissible (StructTV fields) v =
    (case v of StructV vs => immutable_fields_admissible fields vs | _ => F) /\
  immutable_value_admissible (ArrayTV tv bound) v =
    (case (bound,v) of
       (Fixed n, ArrayV (SArrayV kvs)) =>
         ALL_DISTINCT (MAP FST kvs) /\
         EVERY (\(i,x). i < n /\ immutable_value_admissible tv x) kvs
     | (Dynamic n, ArrayV (DynArrayV vs)) =>
         LENGTH vs <= n /\ EVERY (immutable_value_admissible tv) vs
     | _ => F) /\
  immutable_tuple_admissible [] vs = (vs = []) /\
  immutable_tuple_admissible (tv::tvs) vs =
    (case vs of [] => F | v::rest =>
       immutable_value_admissible tv v /\ immutable_tuple_admissible tvs rest) /\
  immutable_fields_admissible [] vs = (vs = []) /\
  immutable_fields_admissible ((name,tv)::fields) vs =
    (case vs of [] => F | (id,v)::rest =>
       id = name /\ immutable_value_admissible tv v /\
       immutable_fields_admissible fields rest)
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (tv,v) => type_value_size tv
    | INR (INL (tvs,vs)) => list_size type_value_size tvs
    | INR (INR (fields,vs)) =>
        list_size (pair_size (\x. 0) type_value_size) fields)` >>
  rw[] >> Induct_on `fields` >> rw[] >> Cases_on `h` >> rw[]
End

Theorem immutable_encoding_word_probe:
  encode_immutable_value (BaseTV (UintT 256)) (IntV 42) =
    REPLICATE 31 0w ++ [42w]
Proof
  simp[immutable_word_bytes_def, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV intLib.REDUCE_CONV) >>
  CONV_TAC wordsLib.WORD_EVAL_CONV
QED

Theorem immutable_encoding_string_probe:
  encode_immutable_value (BaseTV (StringT 40)) (StringV "a") =
    REPLICATE 31 0w ++ [1w; 97w] ++ REPLICATE 63 0w /\
  immutable_value_admissible (BaseTV (StringT 40)) (StringV "a") /\
  encode_immutable_value (BaseTV (StringT 40)) (StringV "") = REPLICATE 96 0w
Proof
  simp[immutable_word_bytes_def, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV intLib.REDUCE_CONV) >>
  CONV_TAC wordsLib.WORD_EVAL_CONV
QED

Theorem immutable_encoding_sparse_probe:
  encode_immutable_value (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(1,IntV 7)])) =
      REPLICATE 63 0w ++ [7w] ++ REPLICATE 32 0w /\
  immutable_value_admissible (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(1,IntV 7)])) /\
  ~immutable_value_admissible (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(1,IntV 7); (1,IntV 8)]))
Proof
  simp[immutable_word_bytes_def, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV intLib.REDUCE_CONV) >>
  CONV_TAC wordsLib.WORD_EVAL_CONV
QED

Theorem immutable_encoding_aggregate_probe:
  encode_immutable_value
    (StructTV [("a", BaseTV (UintT 256));
               ("b", TupleTV [ArrayTV (BaseTV (UintT 256)) (Dynamic 2)])])
    (StructV [("a", IntV 9);
              ("b", ArrayV (TupleV [ArrayV (DynArrayV [IntV 5])]))]) =
    REPLICATE 31 0w ++ [9w] ++ REPLICATE 31 0w ++ [1w] ++
    REPLICATE 31 0w ++ [5w] ++ REPLICATE 32 0w /\
  immutable_value_admissible
    (StructTV [("a", BaseTV (UintT 256));
               ("b", TupleTV [ArrayTV (BaseTV (UintT 256)) (Dynamic 2)])])
    (StructV [("a", IntV 9);
              ("b", ArrayV (TupleV [ArrayV (DynArrayV [IntV 5])]))])
Proof
  simp[immutable_word_bytes_def, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV intLib.REDUCE_CONV) >>
  CONV_TAC wordsLib.WORD_EVAL_CONV
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_ENCODING_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed immutable encoding theorem: " ^ name)
  end) (DB.thms "immutableEncoding");
