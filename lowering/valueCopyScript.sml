(*
 * Copying a value held in memory (#638)
 *
 * val_in_memory lays a value out relative to its address, so the bytes of
 * its footprint, copied anywhere, hold the value there.  The internal call
 * copies values this way: the caller stages a memory-passed argument in a
 * buffer of its own, and the callee copies a memory return into the
 * caller's buffer.
 *
 * TOP-LEVEL:
 *   val_in_memory_drop     — val_in_memory at k + off of mem is
 *                            val_in_memory at off of DROP k mem
 *   val_in_memory_relocate — a value's footprint bytes (val_footprint,
 *                            exprSim), copied to another address, hold the
 *                            value there
 *   mcopy_val_in_memory    — MCOPY of at least the footprint does that
 *   mem_bytes_at_mcopy_disjoint — and leaves the bytes outside its
 *                            destination alone
 *)

Theory valueCopy
Ancestors
  list rich_list arithmetic
  valueEncoding valueEncodingProps valueEncodingProofs exprSim
  venomState venomExecSemantics venomMemProps

Theorem mem_word_at_drop:
  !k off mem. mem_word_at (k + off) mem = mem_word_at off (DROP k mem)
Proof
  simp[mem_word_at_def, DROP_DROP_T]
QED

Theorem mem_bytes_at_drop:
  !k off len mem.
    mem_bytes_at (k + off) len mem = mem_bytes_at off len (DROP k mem)
Proof
  simp[mem_bytes_at_def, DROP_DROP_T]
QED

val drop_rws = [val_in_memory_def, LET_THM, GSYM mem_word_at_drop,
                GSYM mem_bytes_at_drop, AC ADD_ASSOC ADD_COMM];

Theorem val_in_memory_drop:
  (!ty v off mem k.
     val_in_memory ty v (k + off) mem <=>
     val_in_memory ty v off (DROP k mem)) /\
  (!fields field_tvs off mem k.
     fields_in_memory fields field_tvs (k + off) mem <=>
     fields_in_memory fields field_tvs off (DROP k mem)) /\
  (!vs off tv mem k.
     elems_in_memory vs (k + off) tv mem <=>
     elems_in_memory vs off tv (DROP k mem)) /\
  (!(kvs : (num # value) list) off tv mem k.
     kvs_in_memory kvs (k + off) tv mem <=>
     kvs_in_memory kvs off tv (DROP k mem)) /\
  (!vs tvs off mem k.
     tuple_in_memory vs tvs (k + off) mem <=>
     tuple_in_memory vs tvs off (DROP k mem))
Proof
  ho_match_mp_tac val_in_memory_ind >> rpt conj_tac >> rpt strip_tac
  >~ [`val_in_memory ty (StructV fields)`] >- (Cases_on `ty` >> fs drop_rws)
  >~ [`val_in_memory ty (ArrayV (DynArrayV vs))`]
  >- (Cases_on `ty` >> fs drop_rws)
  >~ [`val_in_memory ty (ArrayV (SArrayV kvs))`]
  >- (Cases_on `ty` >> fs drop_rws)
  >~ [`val_in_memory ty (ArrayV (TupleV vs))`]
  >- (Cases_on `ty` >> fs drop_rws)
  >~ [`fields_in_memory ((name,v)::rest) field_tvs`]
  >- (Cases_on `field_tvs` >- fs drop_rws >> PairCases_on `h` >> fs drop_rws)
  >~ [`tuple_in_memory (v::vs) tvs`] >- (Cases_on `tvs` >> fs drop_rws) >>
  fs drop_rws
QED

(* The footprint bytes of a value, wherever they are copied, hold it. *)
Theorem val_in_memory_relocate:
  !tv v a b len mem mem'.
    val_in_memory tv v a mem /\ val_wf tv v /\ val_footprint tv v <= len /\
    mem_bytes_at b len mem' = mem_bytes_at a len mem ==>
    val_in_memory tv v b mem'
Proof
  rpt strip_tac >>
  `val_in_memory tv v 0 (DROP a mem)` by
    metis_tac[CONJUNCT1 val_in_memory_drop, ADD_CLAUSES] >>
  `mem_bytes_at 0 len (DROP b mem') = mem_bytes_at 0 len (DROP a mem)` by
    metis_tac[mem_bytes_at_drop, ADD_CLAUSES] >>
  drule mem_bytes_at_agree_window >> strip_tac >>
  first_x_assum (qspecl_then [`0`, `val_footprint tv v`] mp_tac) >>
  simp[] >> strip_tac >>
  `val_in_memory tv v 0 (DROP b mem')` by
    (irule val_in_memory_footprint_agree >> simp[] >> metis_tac[]) >>
  metis_tac[CONJUNCT1 val_in_memory_drop, ADD_CLAUSES]
QED

Theorem mcopy_val_in_memory:
  !tv v dst src n s.
    val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n ==>
    val_in_memory tv v dst (mcopy dst src n s).vs_memory
Proof
  rpt strip_tac >> match_mp_tac val_in_memory_relocate >>
  qexistsl_tac [`src`, `n`, `s.vs_memory`] >>
  simp[mem_bytes_at_def, mcopy_padded_read]
QED

Theorem mem_bytes_at_write_disjoint:
  !a len d bytes s.
    a + len <= d \/ d + LENGTH bytes <= a ==>
    mem_bytes_at a len (write_memory_with_expansion d bytes s).vs_memory =
    mem_bytes_at a len s.vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[write_memory_with_expansion_def, LET_THM] >>
  Cases_on `0 < d + LENGTH bytes - LENGTH s.vs_memory` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `TAKE d exp` >>
      `d + LENGTH bytes <= LENGTH exp` by simp[Abbr `exp`] >>
      `mem_bytes_at a len
         (TAKE d exp ++ bytes ++ DROP (d + LENGTH bytes) exp) =
       mem_bytes_at a len exp` by
        (simp[mem_bytes_at_def] >> irule take_drop_splice_disjoint >>
         simp[]) >>
      simp[Abbr `exp`, mem_bytes_at_append_zero]) >>
  `d + LENGTH bytes <= LENGTH s.vs_memory` by simp[] >>
  simp[mem_bytes_at_def] >> irule take_drop_splice_disjoint >> simp[]
QED

Theorem mem_bytes_at_mcopy_disjoint:
  !a len dst src n s.
    a + len <= dst \/ dst + n <= a ==>
    mem_bytes_at a len (mcopy dst src n s).vs_memory =
    mem_bytes_at a len s.vs_memory
Proof
  rpt strip_tac >> simp[mcopy_def, LET_THM] >>
  irule mem_bytes_at_write_disjoint >> simp[LENGTH_TAKE_EQ]
QED
