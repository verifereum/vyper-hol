(* Counted indexed prefixes specialize to both dense and sparse arrays. *)
Theory externalReturnCopyLayout
Ancestors
  typedMemoryCopy
  externalReturnCopyArrays externalReturnCopyTransport externalReturnCopyArrayLoop
  externalReturnCopyFrame valueEncoding valueEncodingProps valueEncodingProofs
  vyperTypeSystem vyperTyping vyperValue vyperAST list alist arithmetic words

Theorem return_copy_prefix_frame:
  typed_copy_index_prefix f tv off N k mem /\
  (!i. i < k ==> val_wf tv (f i)) /\
  typed_copy_frame (off + k * type_memory_size tv) len mem mem' ==>
  typed_copy_index_prefix f tv off N k mem'
Proof
  rw[typed_copy_index_prefix_def] >>
  irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[] >>
  `off + i * type_memory_size tv + type_memory_size tv <=
     off + k * type_memory_size tv` by
    metis_tac[return_copy_array_child_window] >>
  gvs[typed_copy_frame_def]
QED

Theorem return_copy_elems_prefix_complete:
  typed_copy_index_prefix (\i. EL i vs) tv off (LENGTH vs) (LENGTH vs) mem ==>
  elems_in_memory vs off tv mem
Proof
  simp[typed_copy_index_prefix_def, return_copy_elems_indexed]
QED

Theorem return_copy_sparse_prefix_complete:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  typed_copy_index_prefix
    (\i. case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    tv off n n mem ==>
  val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) off mem
Proof
  rw[typed_copy_index_prefix_def] >>
  irule return_copy_sarray_indexed >> simp[]
QED

Theorem return_copy_elems_prefix_frame:
  typed_copy_index_prefix (\i. EL i vs) tv off (LENGTH vs) k mem /\
  elems_val_wf vs tv /\
  typed_copy_frame (off + k * type_memory_size tv) len mem mem' ==>
  typed_copy_index_prefix (\i. EL i vs) tv off (LENGTH vs) k mem'
Proof
  strip_tac >> irule return_copy_prefix_frame >> conj_tac
  >- (gvs[typed_copy_index_prefix_def, return_copy_elems_wf_indexed] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`len`, `mem`] >> simp[]
QED

Theorem return_copy_sparse_prefix_frame:
  typed_copy_index_prefix
    (\i. case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    tv off n k mem /\ kvs_val_wf kvs tv n /\
  typed_copy_frame (off + k * type_memory_size tv) len mem mem' ==>
  typed_copy_index_prefix
    (\i. case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
    tv off n k mem'
Proof
  strip_tac >> irule return_copy_prefix_frame >> conj_tac
  >- metis_tac[return_copy_sparse_lookup_wf] >>
  qexistsl_tac [`len`, `mem`] >> simp[]
QED

Theorem return_copy_array_count_bound:
  evaluate_type tenv (ArrayT elem bd) = SOME tv ==>
  bound_length bd < dimword (:256)
Proof
  rw[evaluate_type_def, AllCaseEqs()] >> Cases_on `bd` >>
  gvs[type_slot_size_def, bound_length_def] >>
  `n <= n * type_slot_size tv'` by
    (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >>
  decide_tac
QED
