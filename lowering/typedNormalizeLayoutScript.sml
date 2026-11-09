(* Child representation boundary for recursive return normalization.
   Dense and sparse homogeneous projections already exist as
   exprSimAggregateEncoding.elems_in_memory_EL and
   valueEncodingProofs.kvs_in_memory_lookup.  Capacity arithmetic is
   abiEncoderInput.abi_encoder_prefix_sum_bound and
   abi_encoder_array_slot_bound; do not duplicate those interfaces here. *)
Theory typedNormalizeLayout
Ancestors
  valueEncoding exprSimAggregateEncoding valueEncodingProofs abiEncoderInput
  list arithmetic

Theorem tuple_in_memory_EL:
  !vs tvs b mem i.
    tuple_in_memory vs tvs b mem /\ LENGTH vs = LENGTH tvs /\
    i < LENGTH vs ==>
    val_in_memory (EL i tvs) (EL i vs)
      (b + SUM (MAP type_memory_size (TAKE i tvs))) mem
Proof
  Induct_on `vs` >- simp[] >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  Cases_on `i` >>
  simp[valueEncodingDefsTheory.val_in_memory_def] >>
  rpt strip_tac >> first_x_assum drule_all >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED
