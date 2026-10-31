(* Typed values move with their observed memory window; unused capacity bytes
   need not have a canonical encoding. *)
Theory valueMemoryTransport
Ancestors
  valueEncoding valueEncodingProofs list rich_list arithmetic

Theorem mem_word_at_drop:
  mem_word_at off (DROP base_off mem) = mem_word_at (base_off + off) mem
Proof
  `off + base_off = base_off + off` by decide_tac >>
  simp[mem_word_at_def, DROP_DROP_T]
QED

Theorem mem_bytes_at_drop:
  mem_bytes_at off n (DROP base_off mem) = mem_bytes_at (base_off + off) n mem
Proof
  `off + base_off = base_off + off` by decide_tac >>
  simp[mem_bytes_at_def, DROP_DROP_T]
QED

Theorem memory_value_drop:
  (!tv v off mem. !base_off.
    val_in_memory tv v off (DROP base_off mem) =
    val_in_memory tv v (base_off + off) mem) /\
  (!fields tvs off mem. !base_off.
    fields_in_memory fields tvs off (DROP base_off mem) =
    fields_in_memory fields tvs (base_off + off) mem) /\
  (!vs off tv mem. !base_off.
    elems_in_memory vs off tv (DROP base_off mem) =
    elems_in_memory vs (base_off + off) tv mem) /\
  (!kvs off tv mem. !base_off.
    kvs_in_memory kvs off tv (DROP base_off mem) =
    kvs_in_memory kvs (base_off + off) tv mem) /\
  (!vs tvs off mem. !base_off.
    tuple_in_memory vs tvs off (DROP base_off mem) =
    tuple_in_memory vs tvs (base_off + off) mem)
Proof
  ho_match_mp_tac val_in_memory_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  asm_rewrite_tac[val_in_memory_def, GSYM ADD_ASSOC,
    mem_word_at_drop, mem_bytes_at_drop, LET_THM] >>
  FIRST [Cases_on `tv` >> gvs[] >> NO_TAC, pairarg_tac >> gvs[]]
QED

Theorem val_in_memory_drop:
  val_in_memory tv v 0 (DROP base_off mem) = val_in_memory tv v base_off mem
Proof
  mp_tac (CONJUNCT1 memory_value_drop) >>
  disch_then (qspecl_then [`tv`, `v`, `0`, `mem`, `base_off`] mp_tac) >> simp[]
QED

Theorem val_in_memory_transport:
  val_in_memory tv v src mem /\ val_wf tv v /\
  mem_bytes_at src (type_memory_size tv) mem =
    mem_bytes_at dst (type_memory_size tv) mem' ==>
  val_in_memory tv v dst mem'
Proof
  strip_tac >>
  qspecl_then [`tv`, `v`, `0`, `DROP src mem`, `DROP dst mem'`] mp_tac
    (CONJUNCT1 val_in_memory_mem_agree_proof) >>
  simp[val_in_memory_drop, mem_bytes_at_drop]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed value memory transport: " ^ name)
  end) (DB.thms "valueMemoryTransport");
