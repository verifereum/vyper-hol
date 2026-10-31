(* EVAL sanity checks of the place evaluator: memory paths, pops, delayed
   reads and storage writes, and small programs through eval_stmt. *)
Theory vyperPlaceSanityTest
Ancestors
  finite_map vyperValue vyperValueOperation vyperState vyperInterpreter
Libs
  wordsLib intLib monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem place_delayed_pop_read:
  read_memory_path
    <|assignable := T; type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV []);
      popped := [([ValueSubscript (IntV 0)],IntV 5)]|>
    [ValueSubscript (IntV 0)] = INL (IntV 5)
Proof
  EVAL_TAC >> simp[]
QED

Theorem place_nested_pop_read:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      entry = <|assignable := T; type := tv; value := ArrayV (DynArrayV []);
        popped := [([ValueSubscript (IntV 0)],ArrayV (DynArrayV [IntV 1]));
                   ([ValueSubscript (IntV 0); ValueSubscript (IntV 1)],IntV 2)]|>
  in read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (IntV 1) /\
     read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 1)] = INL (IntV 2)
Proof
  EVAL_TAC >> simp[subscript_type_def] >> EVAL_TAC
QED

Theorem place_fixed_extension_oob:
  !cx st. extend_storage_place cx F 0w (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
    (ValueSubscript (IntV 1)) st =
    (INR (Error (RuntimeError "array fixed oob")),st)
Proof
  EVAL_TAC >> simp[]
QED

Theorem place_pop_then_delayed_read:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV [IntV 5]); popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in FST ((do
      pop_place cx (MemoryPlace "d" []);
      read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)])
    od) st) = INL (IntV 5)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem place_nested_pop_sequence:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      value := ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1; IntV 2])]);
      popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in FST ((do
      pop_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]);
      pop_place cx (MemoryPlace "d" []);
      a <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]);
      b <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0); ValueSubscript (IntV 0)]);
      c <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0); ValueSubscript (IntV 1)]);
      return (a,b,c)
    od) st) = INL (ArrayV (DynArrayV [IntV 1]),IntV 1,IntV 2)
Proof
  rpt (CHANGED_TAC (EVAL_TAC >>
    simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY,
         subscript_type_def, return_def]))
QED

Theorem place_repeated_pop_sequence:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV [IntV 1; IntV 2]); popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in FST ((do
      pop_place cx (MemoryPlace "d" []);
      pop_place cx (MemoryPlace "d" []);
      a <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]);
      b <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 1)]);
      return (a,b)
    od) st) = INL (IntV 1,IntV 2)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[return_def]
QED

Theorem place_memory_write_reset:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV [IntV 1]);
      popped := [([ValueSubscript (IntV 1)],IntV 2)]|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in FST ((do
      write_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]) (IntV 7);
      a <- read_place cx (MemoryPlace "d" [ValueSubscript (IntV 0)]);
      sc <- get_scopes;
      return (a, OPTION_MAP (\e. e.popped) (lookup_scopes "d" sc))
    od) st) = INL (IntV 7,SOME [])
Proof
  rpt (CHANGED_TAC (EVAL_TAC >>
    simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY, return_def]))
QED

Theorem place_storage_raw_write:
  !cx.
  FST ((do
      write_place cx (StoragePlace T 7w (BaseTV (UintT 256))) (IntV 10);
      read_place cx (StoragePlace T 7w (BaseTV (UintT 256)))
    od) empty_state) = INL (IntV 10)
Proof
  EVAL_TAC >> simp[]
QED

Theorem place_memory_extension_bounds:
  !cx.
  let entry = <|assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV [IntV 5]); popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("d",entry)]
  in extend_place cx (PlaceR (MemoryPlace "d" []))
       (ValueSubscript (IntV 0)) st =
       (INL (PlaceR (MemoryPlace "d" [ValueSubscript (IntV 0)])),st) /\
     ISL (FST (extend_place cx (PlaceR (MemoryPlace "d" []))
       (ValueSubscript (IntV 1)) st)) = F
Proof
  rpt (CHANGED_TAC (EVAL_TAC >>
    simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY, return_def]))
QED

Theorem place_struct_fixed_path:
  !cx.
  let entry = <|assignable := T;
      type := StructTV [("a",ArrayTV (BaseTV (UintT 256)) (Fixed 2))];
      value := StructV [("a",ArrayV (DynArrayV [IntV 3; IntV 4]))]; popped := []|>;
      st = empty_state with scopes := [FEMPTY |+ ("s",entry)]
  in FST ((do
      pv <- extend_place cx
        (PlaceR (MemoryPlace "s" [])) (AttrSubscript "a");
      pv' <- extend_place cx pv (ValueSubscript (IntV 1));
      read_result cx pv'
    od) st) = INL (IntV 4)
Proof
  rpt (CHANGED_TAC (EVAL_TAC >>
    simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY,
         subscript_type_def, return_def]))
QED

(* Small checked memory programs exercise the place evaluator independently of
   contract deployment. The surrounding machine state is deliberately arbitrary. *)
Definition place_probe_state_def:
  place_probe_state st = st with scopes :=
    [FEMPTY |+ ("d", <|assignable := T;
       type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
       value := ArrayV (DynArrayV [IntV 5]); popped := []|>)
     |+ ("i", <|assignable := T; type := BaseTV (UintT 256);
                 value := IntV 0; popped := []|>)
     |+ ("a", <|assignable := T;
       type := ArrayTV (BaseTV (UintT 256)) (Dynamic 6);
       value := ArrayV (DynArrayV (REPLICATE 6 (IntV 0))); popped := []|>)]
End

Theorem eval_expr_literal_probe:
  eval_expr cx (Literal (BaseT (UintT 256)) (IntL 7)) st =
    (INL (Value (IntV 7)), st)
Proof
  simp[evaluate_def, evaluate_literal_def, return_def, bind_def]
QED

(* ABI captures are arbitrary in these probes. Split their write-through guards
   without restricting the surrounding machine state. *)
val PLACE_PROBE_EVAL_TAC =
  rpt (CHANGED_TAC (EVAL_TAC >> simp[integerTheory.INT_LE_REFL])
       ORELSE IF_CASES_TAC);

Theorem assign_pop_bounds_probe:
  FST (eval_stmt cx
    (Assign (BaseTarget (SubscriptTarget (NameTarget "d")
       (Literal (BaseT (UintT 256)) (IntL 0))))
       (Pop (BaseT (UintT 256)) (NameTarget "d")))
    (place_probe_state st)) =
    INR (Error (RuntimeError "evaluate_subscripts array_index"))
Proof
  PLACE_PROBE_EVAL_TAC
QED

Theorem augassign_pop_stale_probe:
  case eval_stmt cx
    (AugAssign (BaseT (UintT 256))
      (SubscriptTarget (NameTarget "d")
        (Literal (BaseT (UintT 256)) (IntL 0))) Add
      (Pop (BaseT (UintT 256)) (NameTarget "d")))
    (place_probe_state st) of
    (INL (),st') => lookup_scopes_val "d" st'.scopes =
                      SOME (ArrayV (DynArrayV []))
  | _ => F
Proof
  PLACE_PROBE_EVAL_TAC
QED

Theorem assign_delayed_pop_read_probe:
  case eval_stmt cx
    (Assign (BaseTarget (SubscriptTarget (NameTarget "a")
       (Pop (BaseT (UintT 256)) (NameTarget "d"))))
      (Subscript (BaseT (UintT 256))
        (Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "d")
        (Literal (BaseT (UintT 256)) (IntL 0))))
    (place_probe_state st) of
    (INL (),st') => lookup_scopes_val "a" st'.scopes =
      SOME (ArrayV (DynArrayV [IntV 0; IntV 0; IntV 0; IntV 0; IntV 0; IntV 5]))
  | _ => F
Proof
  PLACE_PROBE_EVAL_TAC
QED

Theorem nested_tuple_order_probe:
  case assign_tuple_targets cx
    (TupleTarget [TupleTarget [BaseTarget (NameTarget "i")];
      BaseTarget (SubscriptTarget (NameTarget "a")
        (Name (BaseT (UintT 256)) "i"))])
    (ArrayV (TupleV [ArrayV (TupleV [IntV 5]); IntV 9]))
    (place_probe_state st) of
    (INL (),st') => lookup_scopes_val "a" st'.scopes =
      SOME (ArrayV (DynArrayV [IntV 0; IntV 0; IntV 0; IntV 0; IntV 0; IntV 9]))
  | _ => F
Proof
  PLACE_PROBE_EVAL_TAC
QED

Theorem eager_nested_bounds_probe:
  SND (eval_expr cx
    (Subscript (BaseT (UintT 256))
      (Subscript (BaseT (UintT 256))
        (Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "d")
        (Literal (BaseT (UintT 256)) (IntL 9)))
      (Pop (BaseT (UintT 256)) (NameTarget "d")))
    (place_probe_state st)) = place_probe_state st
Proof
  EVAL_TAC
QED

Theorem eval_target_place_nested_mapping_probe:
  lookup_global cx NONE "m" st =
    (INL (HashMapRef F slot (BaseT (UintT 256))
      (HashMapT (BaseT (UintT 256)) (Type (BaseT (UintT 256))))), st) ==>
  eval_target_place cx
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
        (Literal (BaseT (UintT 256)) (IntL 1)))
      (Literal (BaseT (UintT 256)) (IntL 2))) st =
    (INL (StoragePlace F
      (hashmap_slot (hashmap_slot slot (encode_hashmap_key (BaseT (UintT 256)) (IntV 1)))
        (encode_hashmap_key (BaseT (UintT 256)) (IntV 2))) (BaseTV (UintT 256))), st)
Proof
  strip_tac >> simp[evaluate_def, bind_def, return_def, evaluate_literal_def,
    read_result_def, extend_place_nested_mapping,
    extend_place_def, lift_option_type_def, evaluate_type_def, get_place_def]
QED

(* Keep the evaluator and the checked place-order probes kernel-closed. *)
val () = List.app (fn (_,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then () else raise Fail "interpreter has admitted dependencies"
  end) (DB.thms "vyperInterpreter" @ DB.thms "vyperPlaceSanityTest");
