(* TOP-LEVEL: every recursive source field supplies its child's complete
   memory encoding. Array loop indices select the exact source stride and
   ABI head metadata, including when children themselves contain arrays. *)
Theory abiMemoryEncodingElements
Ancestors
  abiMemoryEncoding abiMemoryEncodingCases abiFieldLayoutDefs
  list rich_list pair arithmetic words
Libs pairLib

Theorem abi_memory_fields_flags:
  !entries src span mem fields.
    abi_memory_fields entries src span mem fields ==>
    MAP FST fields = MAP (\(_,_,_,flag). flag) entries
Proof
  Induct_on `entries` >> rpt gen_tac >>
  simp[Once abi_memory_fields_cases] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_memory_fields_element:
  !entries src span mem fields i.
    abi_memory_fields entries src span mem fields /\ i < LENGTH entries ==>
    let (info,abi_sz,mem_sz,is_dyn) = EL i entries in
      FST (EL i fields) = is_dyn /\
      abi_sz = (if is_dyn then 32 else LENGTH (SND (EL i fields))) /\
      abi_memory_encoding info
        (src + SUM (MAP (\(_,_,slot_size,_). slot_size) (TAKE i entries)))
        mem_sz mem (SND (EL i fields))
Proof
  Induct_on `entries` >- simp[] >> rpt gen_tac >>
  simp[Once abi_memory_fields_cases] >> rpt strip_tac >> gvs[] >>
  rename1 `abi_memory_encoding child_info src child_span mem child_payload` >>
  rename1 `abi_memory_fields entries _ _ mem remaining` >> Cases_on `i`
  >- simp[] >> rename1 `SUC index < SUC (LENGTH entries)` >>
  first_x_assum (qspecl_then
    [`src + child_span`, `span - child_span`, `mem`, `remaining`, `index`] mp_tac) >>
  impl_tac >- simp[] >>
  simp_tac bool_ss [EL, TL, TAKE, MAP, SUM, ADD_ASSOC, UNCURRY_DEF]
QED

Theorem abi_replicate_prefix:
  !n m x. TAKE n (REPLICATE m x) = REPLICATE (MIN n m) x
Proof
  simp_tac bool_ss [REPLICATE_GENLIST, TAKE_GENLIST]
QED

Theorem abi_memory_array_element:
  !info abi_sz mem_sz is_dyn src span mem fields i.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,abi_sz,mem_sz,is_dyn))
      src span mem fields /\ i < LENGTH fields ==>
    FST (EL i fields) = is_dyn /\
    abi_sz = (if is_dyn then 32 else LENGTH (SND (EL i fields))) /\
    abi_memory_encoding info (src + i * mem_sz) mem_sz mem (SND (EL i fields))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`REPLICATE (LENGTH fields) (info,abi_sz,mem_sz,is_dyn)`,
    `src`, `span`, `mem`, `fields`, `i`] mp_tac abi_memory_fields_element >>
  impl_tac >- simp[] >>
  simp[EL_REPLICATE, abi_replicate_prefix, MIN_DEF]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI source elements: " ^ name)
  end) (DB.thms "abiMemoryEncodingElements")
