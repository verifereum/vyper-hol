(* TOP-LEVEL: memory_value_rel describes complete typed memory layouts.
   Fixed-array holes contain the element type's default value; dynamic
   arrays constrain live elements and leave unused capacity unrestricted.
   Helpers: exact field and tuple layouts. *)
Theory memoryValueDefs
Ancestors
  valueEncoding vyperValue list alist arithmetic pair

Definition memory_value_rel_def:
  memory_value_rel (BaseTV bt) v offset mem =
    val_in_memory (BaseTV bt) v offset mem /\
  memory_value_rel (FlagTV count) v offset mem =
    val_in_memory (FlagTV count) v offset mem /\
  memory_value_rel NoneTV NoneV offset mem = T /\
  memory_value_rel (ArrayTV elem_tv (Fixed count)) (ArrayV (SArrayV sparse)) offset mem =
    (!i. i < count ==>
      memory_value_rel elem_tv
        (case ALOOKUP sparse i of NONE => default_value elem_tv | SOME v => v)
        (offset + i * type_memory_size elem_tv) mem) /\
  memory_value_rel (ArrayTV elem_tv (Dynamic bound)) (ArrayV (DynArrayV vs)) offset mem =
    (mem_word_at offset mem = n2w (LENGTH vs) /\
     !i. i < LENGTH vs ==>
       memory_value_rel elem_tv (EL i vs) (offset + 32 + i * type_memory_size elem_tv) mem) /\
  memory_value_rel (StructTV tvs) (StructV fields) offset mem =
    memory_fields_rel tvs fields offset mem /\
  memory_value_rel (TupleTV tvs) (ArrayV (TupleV vs)) offset mem =
    memory_tuple_rel tvs vs offset mem /\
  memory_value_rel _ _ offset mem = F /\
  memory_fields_rel [] [] offset mem = T /\
  memory_fields_rel ((name,tv)::tvs) ((value_name,v)::vs) offset mem =
    (value_name = name /\ memory_value_rel tv v offset mem /\
     memory_fields_rel tvs vs (offset + type_memory_size tv) mem) /\
  memory_fields_rel _ _ offset mem = F /\
  memory_tuple_rel [] [] offset mem = T /\
  memory_tuple_rel (tv::tvs) (v::vs) offset mem =
    (memory_value_rel tv v offset mem /\
     memory_tuple_rel tvs vs (offset + type_memory_size tv) mem) /\
  memory_tuple_rel _ _ offset mem = F
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (tv,_,_,_) => 2 * type_value_size tv + 1
    | INR (INL (tvs,_,_,_)) => 2 * type_value_size (StructTV tvs)
    | INR (INR (tvs,_,_,_)) => 2 * type_value_size (TupleTV tvs))` >>
  simp[type_value_size_def]
End

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete memory definition: " ^ name)
  end) (DB.thms "memoryValueDefs")
