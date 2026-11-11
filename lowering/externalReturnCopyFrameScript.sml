(* Task-owned destination frame for footprint-sensitive return copies. *)
Theory externalReturnCopyFrame
Ancestors
  externalReturnCopyBase externalReturnFootprint valueEncoding valueEncodingProps
  valueEncodingProofs venomState compileEnv loweringPosts arithmetic
  exprSimBufferEmpty

Definition return_copy_memory_frame_def:
  return_copy_memory_frame off len mem mem' <=>
    (!a n. a + n <= off \/ off + len <= a ==>
      mem_bytes_at a n mem' = mem_bytes_at a n mem) /\
    LENGTH mem <= LENGTH mem'
End

Definition return_copy_frame_def:
  return_copy_frame sa off len s t <=>
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    return_copy_memory_frame off len s.vs_memory t.vs_memory
End

Theorem return_copy_memory_frame_refl[simp]:
  return_copy_memory_frame off len mem mem
Proof
  simp[return_copy_memory_frame_def]
QED

Theorem return_copy_memory_frame_trans:
  return_copy_memory_frame off len mem1 mem2 /\
  return_copy_memory_frame off len mem2 mem3 ==>
  return_copy_memory_frame off len mem1 mem3
Proof
  rw[return_copy_memory_frame_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem return_copy_memory_frame_subinterval:
  off <= child /\ child + clen <= off + len /\
  return_copy_memory_frame child clen mem mem' ==>
  return_copy_memory_frame off len mem mem'
Proof
  rw[return_copy_memory_frame_def] >>
  `a + n <= child \/ child + clen <= a` by decide_tac >> metis_tac[]
QED

Theorem return_copy_frame_refl[simp]:
  return_copy_frame sa off len s s
Proof
  simp[return_copy_frame_def]
QED

Theorem return_copy_frame_trans:
  return_copy_frame sa off len s t /\ return_copy_frame sa off len t u ==>
  return_copy_frame sa off len s u
Proof
  rw[return_copy_frame_def]
  >- gvs[venom_state_component_equality] >>
  metis_tac[return_copy_memory_frame_trans]
QED

Theorem return_copy_frame_subinterval:
  off <= child /\ child + clen <= off + len /\
  return_copy_frame sa child clen s t ==>
  return_copy_frame sa off len s t
Proof
  rw[return_copy_frame_def] >>
  irule return_copy_memory_frame_subinterval >>
  qexistsl_tac [`child`, `clen`] >> simp[]
QED

Theorem return_aggregate_footprint:
  (!bs. v <> BytesV bs) /\ (!str. v <> StringV str) ==>
  val_footprint tv v = type_memory_size tv
Proof
  Cases_on `v` >> simp[val_footprint_def]
QED

Theorem return_footprint_cases[local]:
  !tv v.
    (?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
    (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
    val_footprint tv v = type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[] >>
  rename1 `BytesT sz` >> Cases_on `sz` >> simp[]
QED

Theorem return_memory_footprint_agree:
  val_in_memory tv v off mem /\ val_wf tv v /\
  mem_bytes_at off (val_footprint tv v) mem =
    mem_bytes_at off (val_footprint tv v) mem' ==>
  val_in_memory tv v off mem'
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_footprint tv v = type_memory_size tv` by
    metis_tac[return_footprint_cases]
  >- (gvs[val_footprint_def, val_in_memory_def] >>
      drule mem_bytes_at_agree_window >> strip_tac >>
      `mem_word_at off mem' = mem_word_at off mem` by
        (qpat_x_assum `!off2. _ ==> mem_word_at _ _ = _` irule >> simp[]) >>
      `mem_bytes_at (off + 32) (LENGTH bs) mem' =
       mem_bytes_at (off + 32) (LENGTH bs) mem` by
        (qpat_x_assum `!off2 len2. _ ==> mem_bytes_at _ _ _ = _` irule >>
         simp[]) >> simp[])
  >- (gvs[val_footprint_def, val_in_memory_def] >>
      drule mem_bytes_at_agree_window >> strip_tac >>
      `mem_word_at off mem' = mem_word_at off mem` by
        (qpat_x_assum `!off2. _ ==> mem_word_at _ _ = _` irule >> simp[]) >>
      `mem_bytes_at (off + 32) (LENGTH str) mem' =
       mem_bytes_at (off + 32) (LENGTH str) mem` by
        (qpat_x_assum `!off2 len2. _ ==> mem_bytes_at _ _ _ = _` irule >>
         simp[]) >> simp[]) >>
  gvs[] >> irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[]
QED

Theorem return_copy_preserves_source:
  return_copy_frame sa dst dlen s t /\
  val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
  (src + val_footprint tv v <= dst \/ dst + dlen <= src) ==>
  val_in_memory tv v src t.vs_memory
Proof
  rw[return_copy_frame_def, return_copy_memory_frame_def] >>
  irule return_memory_footprint_agree >> simp[] >>
  qexists_tac `s.vs_memory` >> simp[]
QED

Theorem return_zero_layout_memory_all[local]:
  (!tv v. val_wf tv v ==> type_memory_size tv = 0 ==>
    !off mem. val_in_memory tv v off mem) /\
  (!fs tvs. fields_val_wf fs tvs ==> type_memory_size_fields tvs = 0 ==>
    !off mem. fields_in_memory fs tvs off mem) /\
  (!vs tv. elems_val_wf vs tv ==> type_memory_size tv = 0 ==>
    !off mem. elems_in_memory vs off tv mem) /\
  (!kvs tv n. kvs_val_wf kvs tv n ==>
    n * type_memory_size tv = 0 ==>
    !off mem. kvs_in_memory kvs off tv mem) /\
  (!vs tvs. tuple_val_wf vs tvs ==> type_memory_size_list tvs = 0 ==>
    !off mem. tuple_in_memory vs tvs off mem)
Proof
  ho_match_mp_tac val_wf_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[val_wf_def, val_in_memory_def, type_memory_size_def]
  >- (Cases_on `tv` >> simp[type_memory_size_def] >>
      rename1 `BaseTV bt` >> Cases_on `bt` >> simp[type_memory_size_def] >>
      rename1 `BytesT sz` >> Cases_on `sz` >> simp[type_memory_size_def])
  >- (Cases_on `tv` >> simp[type_memory_size_def])
  >- (Cases_on `tv` >> simp[type_memory_size_def] >>
      rename1 `ArrayTV et bd` >> Cases_on `bd` >> simp[type_memory_size_def])
  >- (Cases_on `tv` >> simp[type_memory_size_def] >>
      rename1 `ArrayTV et bd` >> Cases_on `bd` >> simp[type_memory_size_def] >>
      rpt strip_tac >> gvs[] >>
      irule default_memory_zero_bytes >> simp[mem_bytes_at_def])
  >- (Cases_on `tv` >> simp[type_memory_size_def])
  >- (Cases_on `tvs` >> simp[type_memory_size_def] >>
      PairCases_on `h` >> simp[type_memory_size_def] >> metis_tac[])
  >> Cases_on `tvs` >> simp[type_memory_size_def] >> metis_tac[]
QED

Theorem return_zero_layout_memory_address:
  val_wf tv v /\ type_memory_size tv = 0 ==>
  (val_in_memory tv v src mem <=> val_in_memory tv v dst mem')
Proof
  metis_tac[return_zero_layout_memory_all]
QED

(* A zero-layout source has no ownership or address bound obligation. *)
Definition return_copy_entry_def:
  return_copy_entry cenv ctx tenv dty sty dtv stv v <=>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      evaluate_type tenv dty = SOME dtv /\
      evaluate_type tenv sty = SOME stv /\
      type_widens_to tenv sty dty /\
      value_has_type stv v /\ value_has_type dtv v /\
      val_wf stv v /\ val_wf dtv v /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (type_memory_size stv <> 0 ==>
        w2n sw + type_memory_size stv < dimword (:256) /\
        (w2n sw + type_memory_size stv <= w2n dw \/
         w2n dw + type_memory_size dtv <= w2n sw)) ==>
      frag_exec ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
             return_copy_frame sa (w2n dw) (type_memory_size dtv) s t)
        (\r. F)
End
