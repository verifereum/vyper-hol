(* TOP-LEVEL: arbitrary recursive ABI source encodings survive changes
   outside their source window. Capacities can grow without changing bytes.
   Helpers: the header and suffix observations of a bounded source window. *)
Theory abiMemoryEncodingFrame
Ancestors
  abiMemoryEncoding valueEncodingProofs valueEncoding list arithmetic words

Theorem abi_memory_encoding_capacity:
  (!info src span mem payload.
    abi_memory_encoding info src span mem payload ==>
    !larger. span <= larger ==> abi_memory_encoding info src larger mem payload) /\
  (!entries src span mem fields.
    abi_memory_fields entries src span mem fields ==>
    !larger. span <= larger ==> abi_memory_fields entries src larger mem fields)
Proof
  ho_match_mp_tac abi_memory_encoding_strongind >> rpt strip_tac
  >| [irule abi_memory_encoding_word >> decide_tac,
      irule abi_memory_encoding_copy >> decide_tac,
      irule abi_memory_encoding_bytes >> simp[] >> decide_tac,
      irule abi_memory_encoding_complex >> first_x_assum irule >> simp[],
      irule abi_memory_encoding_array >> simp[] >>
        first_x_assum irule >> decide_tac,
      irule abi_memory_encoding_fields_nil,
      irule abi_memory_encoding_fields_cons >> simp[] >>
        first_x_assum irule >> decide_tac]
QED

Theorem abi_memory_window_header:
  !src span mem mem'.
    32 <= span /\ mem_bytes_at src span mem = mem_bytes_at src span mem' ==>
    mem_word_at src mem' = mem_word_at src mem
Proof
  rpt strip_tac >> drule mem_bytes_at_agree_window >> strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem abi_memory_window_part:
  !src span delta len mem mem'.
    delta + len <= span /\
    mem_bytes_at src span mem = mem_bytes_at src span mem' ==>
    mem_bytes_at (src + delta) len mem' = mem_bytes_at (src + delta) len mem
Proof
  rpt strip_tac >> drule mem_bytes_at_agree_window >> strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem abi_memory_window_suffix:
  !src span delta mem mem'.
    delta <= span /\ mem_bytes_at src span mem = mem_bytes_at src span mem' ==>
    mem_bytes_at (src + delta) (span - delta) mem' =
      mem_bytes_at (src + delta) (span - delta) mem
Proof
  rpt strip_tac >> irule abi_memory_window_part >> qexists_tac `span` >>
  simp[]
QED

Theorem abi_memory_window_prefix:
  !src span len mem mem'.
    len <= span /\ mem_bytes_at src span mem = mem_bytes_at src span mem' ==>
    mem_bytes_at src len mem' = mem_bytes_at src len mem
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`src`, `span`, `0`, `len`, `mem`, `mem'`]
    abi_memory_window_part) >> simp[]
QED

Theorem abi_memory_encoding_frame:
  (!info src span mem payload.
    abi_memory_encoding info src span mem payload ==>
    !mem'. mem_bytes_at src span mem = mem_bytes_at src span mem' ==>
      abi_memory_encoding info src span mem' payload) /\
  (!entries src span mem fields.
    abi_memory_fields entries src span mem fields ==>
    !mem'. mem_bytes_at src span mem = mem_bytes_at src span mem' ==>
      abi_memory_fields entries src span mem' fields)
Proof
  ho_match_mp_tac abi_memory_encoding_strongind >> rpt strip_tac
  >| [drule_all abi_memory_window_header >>
        disch_then (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
        irule abi_memory_encoding_word >> simp[],
      drule_all abi_memory_window_prefix >>
        disch_then (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
        irule abi_memory_encoding_copy >> simp[],
      `32 <= span` by decide_tac >>
        drule_all abi_memory_window_header >> DISCH_TAC >>
        drule_all abi_memory_window_part >> DISCH_TAC >>
        irule abi_memory_encoding_bytes >> simp[],
      irule abi_memory_encoding_complex >> first_x_assum irule >> simp[],
      drule_all abi_memory_window_header >> DISCH_TAC >>
        drule_all abi_memory_window_suffix >> DISCH_TAC >>
        irule abi_memory_encoding_array >> simp[] >> first_x_assum irule >> simp[],
      irule abi_memory_encoding_fields_nil,
      drule_all abi_memory_window_prefix >> DISCH_TAC >>
        drule_all abi_memory_window_suffix >> DISCH_TAC >>
        irule abi_memory_encoding_fields_cons >> simp[] >>
        conj_tac >> first_x_assum irule >> simp[]]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI source memory frame: " ^ name)
  end) (DB.thms "abiMemoryEncodingFrame")
