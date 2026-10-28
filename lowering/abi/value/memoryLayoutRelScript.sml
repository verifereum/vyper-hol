(* TOP-LEVEL: memory_layout_rel compares complete physical value layouts,
   including strides and the defaults used for sparse array holes.
   Helpers lift matching layouts through arrays and tuples. *)
Theory memoryLayoutRel
Ancestors
  memoryValueDefs valueEncoding vyperValue list words arithmetic

Definition memory_layout_rel_def:
  memory_layout_rel ftv atv <=>
    type_memory_size ftv = type_memory_size atv /\
    default_value ftv = default_value atv /\
    !v offset mem. memory_value_rel ftv v offset mem = memory_value_rel atv v offset mem
End

Definition memory_layouts_rel_def:
  memory_layouts_rel ftvs atvs <=>
    type_memory_size_list ftvs = type_memory_size_list atvs /\
    MAP default_value ftvs = MAP default_value atvs /\
    !vs offset mem. memory_tuple_rel ftvs vs offset mem = memory_tuple_rel atvs vs offset mem
End

Theorem memory_layout_rel_refl[simp]:
  !tv. memory_layout_rel tv tv
Proof
  simp[memory_layout_rel_def]
QED

Theorem memory_layout_rel_sym:
  !ftv atv. memory_layout_rel ftv atv ==> memory_layout_rel atv ftv
Proof
  simp[memory_layout_rel_def, EQ_SYM_EQ]
QED

Theorem memory_layout_rel_value:
  !ftv atv v offset mem.
    memory_layout_rel ftv atv /\ memory_value_rel atv v offset mem ==>
    memory_value_rel ftv v offset mem
Proof
  simp[memory_layout_rel_def]
QED

Theorem memory_layout_rel_array:
  !ftv atv array_bound.
    memory_layout_rel ftv atv ==>
    memory_layout_rel (ArrayTV ftv array_bound) (ArrayTV atv array_bound)
Proof
  rpt gen_tac >> rewrite_tac[memory_layout_rel_def] >> strip_tac >>
  Cases_on `array_bound` >> simp[type_memory_size_def, default_value_def] >>
  rpt gen_tac >> Cases_on `v` >> simp[memory_value_rel_def] >>
  rename1 `ArrayV elems` >> Cases_on `elems` >> simp[memory_value_rel_def]
QED

Theorem memory_layouts_rel_nil[simp]:
  memory_layouts_rel [] []
Proof
  simp[memory_layouts_rel_def, type_memory_size_def]
QED

Theorem memory_layouts_rel_cons:
  !ftv atv ftvs atvs.
    memory_layout_rel ftv atv /\ memory_layouts_rel ftvs atvs ==>
    memory_layouts_rel (ftv::ftvs) (atv::atvs)
Proof
  rpt gen_tac >> rewrite_tac[memory_layout_rel_def, memory_layouts_rel_def] >> strip_tac >>
  simp[type_memory_size_def] >> rpt gen_tac >> Cases_on `vs` >> simp[memory_value_rel_def]
QED

Theorem memory_layout_rel_tuple:
  !ftvs atvs. memory_layouts_rel ftvs atvs ==>
    memory_layout_rel (TupleTV ftvs) (TupleTV atvs)
Proof
  rpt gen_tac >> rewrite_tac[memory_layout_rel_def, memory_layouts_rel_def] >> strip_tac >>
  simp[type_memory_size_def, default_value_def, default_value_tuple_MAP] >>
  rpt gen_tac >> Cases_on `v` >> simp[memory_value_rel_def] >>
  rename1 `ArrayV elems` >> Cases_on `elems` >> simp[memory_value_rel_def]
QED

Theorem memory_layout_rel_bytestring:
  (!n m. (n + 31) DIV 32 = (m + 31) DIV 32 ==>
    memory_layout_rel (BaseTV (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic m)))) /\
  (!n m. (n + 31) DIV 32 = (m + 31) DIV 32 ==>
    memory_layout_rel (BaseTV (StringT n)) (BaseTV (StringT m)))
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[memory_layout_rel_def, type_memory_size_def, vfmConstantsTheory.word_size_def,
    default_value_def] >> rpt gen_tac >> Cases_on `v` >>
  simp[memory_value_rel_def, val_in_memory_def, LET_THM] >>
  rename1 `ArrayV elems` >> Cases_on `elems` >> simp[val_in_memory_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete memory-layout relation theorem: " ^ name)
  end) (DB.thms "memoryLayoutRel")
