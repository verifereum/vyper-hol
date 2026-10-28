(* Physical layout keys for comparing aggregate copy layouts. Bounds on
   bytes/string payloads affect their rounded footprint, not the length word.
   Struct and flag identities remain explicit; metadata is not traversed.
   TOP-LEVEL: memory_layout_key, memory_layout_bytes, tuple_memory_layout_eq.
   KEY LEMMA: memory_layout_key_bytes. *)
Theory memoryLayoutDefs
Ancestors compileEnv vyperAST list arithmetic combin pair

Datatype:
  memory_layout =
    BaseLayout base_type
  | BytesLayout num
  | StringLayout num
  | ArrayLayout memory_layout bound
  | TupleLayout (memory_layout list)
  | StructLayout nsid
  | FlagLayout nsid
  | EmptyLayout
End

Definition memory_layout_key_def:
  memory_layout_key (BaseT (BytesT (Dynamic n))) =
    BytesLayout ((n + 31) DIV 32) /\
  memory_layout_key (BaseT (StringT n)) =
    StringLayout ((n + 31) DIV 32) /\
  memory_layout_key (BaseT bt) = BaseLayout bt /\
  memory_layout_key (ArrayT ty (Fixed n)) =
    ArrayLayout (memory_layout_key ty) (Fixed n) /\
  memory_layout_key (ArrayT ty (Dynamic n)) =
    ArrayLayout (memory_layout_key ty) (Dynamic n) /\
  memory_layout_key (TupleT tys) = TupleLayout (MAP memory_layout_key tys) /\
  memory_layout_key (StructT id) = StructLayout id /\
  memory_layout_key (FlagT id) = FlagLayout id /\
  memory_layout_key NoneT = EmptyLayout
Termination
  WF_REL_TAC `measure type_size`
End

Definition memory_layout_bytes_def:
  memory_layout_bytes cenv (BaseLayout bt) = 32 /\
  memory_layout_bytes cenv (BytesLayout words) = 32 + words * 32 /\
  memory_layout_bytes cenv (StringLayout words) = 32 + words * 32 /\
  memory_layout_bytes cenv (ArrayLayout elem (Fixed n)) =
    n * memory_layout_bytes cenv elem /\
  memory_layout_bytes cenv (ArrayLayout elem (Dynamic n)) =
    32 + n * memory_layout_bytes cenv elem /\
  memory_layout_bytes cenv (TupleLayout elems) =
    SUM (MAP (memory_layout_bytes cenv) elems) /\
  memory_layout_bytes cenv (StructLayout id) =
    SUM (MAP (SND o SND)
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string id))) /\
  memory_layout_bytes cenv (FlagLayout id) = 32 /\
  memory_layout_bytes cenv EmptyLayout = 0
Termination
  WF_REL_TAC `measure (memory_layout_size o SND)`
End

Theorem memory_layout_key_bytes:
  !ty cenv. memory_layout_bytes cenv (memory_layout_key ty) =
            type_memory_bytes cenv ty
Proof
  ho_match_mp_tac memory_layout_key_ind >> rpt strip_tac >>
  simp[memory_layout_key_def, memory_layout_bytes_def, type_memory_bytes_def,
       MAP_MAP_o, o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[]
QED

(* Pinned Vyper permits a bulk copy for tuple types whose bounds differ.
   Check the entire field layout, including offsets, before using that path. *)
Definition tuple_memory_layout_eq_def:
  tuple_memory_layout_eq (TupleT dst) (TupleT src) =
    (MAP memory_layout_key dst = MAP memory_layout_key src) /\
  tuple_memory_layout_eq _ _ = F
End

Theorem tuple_memory_layout_eq_bytes:
  tuple_memory_layout_eq dst src ==>
  type_memory_bytes cenv dst = type_memory_bytes cenv src
Proof
  Cases_on `dst` >> Cases_on `src` >>
  simp[tuple_memory_layout_eq_def] >> strip_tac >>
  rewrite_tac[GSYM memory_layout_key_bytes] >>
  simp[memory_layout_key_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem memory_layout_keys_member_bytes:
  MAP memory_layout_key dst = MAP memory_layout_key src ==>
  MAP (type_memory_bytes cenv) dst = MAP (type_memory_bytes cenv) src
Proof
  disch_then (mp_tac o AP_TERM ``MAP (memory_layout_bytes cenv)``) >>
  simp[MAP_MAP_o, o_DEF, memory_layout_key_bytes] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem tuple_memory_layout_eq_offsets:
  tuple_memory_layout_eq (TupleT dst) (TupleT src) ==>
  !n. SUM (MAP (type_memory_bytes cenv) (TAKE n dst)) =
      SUM (MAP (type_memory_bytes cenv) (TAKE n src))
Proof
  simp[tuple_memory_layout_eq_def] >> strip_tac >> gen_tac >>
  drule memory_layout_keys_member_bytes >>
  disch_then (qspec_then `cenv`
    (mp_tac o AP_TERM ``\sizes:num list. SUM (TAKE n sizes)``)) >>
  simp[MAP_TAKE]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed memory layout theorem: " ^ name)
  end) (DB.thms "memoryLayoutDefs")
