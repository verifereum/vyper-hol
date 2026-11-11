(* Robust prefix/suffix composition for independently laid out fields. *)
Theory bodyPtrTypedCopyFields
Ancestors
  bodyPtrTypedCopyBoundary assignBasePtrFieldsCompose assignBasePtrFieldOffsets
  typedCopyTuplePtr typedCopyLayoutPtr bodyPtrSubscriptMemoryRebuild
  abiEncoderInput typedMemoryCopy typedCopyRobustTransportPtr
  valueEncodingProps valueEncodingDefs exprSimProps list rich_list arithmetic
  pred_set

(* A write to field k preserves the completed destination prefix.  This
   boundary uses semantic sizes; sum_map_take_pointwise transports compiler
   offsets to these sums without identifying source and destination strides. *)
Theorem typed_fields_robust_prefix_frame:
  !tvs vs k addr tn tf mem mem'.
    LENGTH vs = LENGTH tvs /\ k < LENGTH tvs /\
    (!i. i < k ==> val_wf (EL i tvs) (EL i vs)) /\
    (!i. ~(addr + SUM (MAP type_memory_size (TAKE k tvs)) <= i /\
      i < addr + SUM (MAP type_memory_size (TAKE k tvs)) +
        type_memory_size (EL k tvs)) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN tf <=> i IN tn)) /\
    (!j. j < k ==> !m. mem_agree_outside tn mem m ==>
      val_in_memory (EL j tvs) (EL j vs)
        (addr + SUM (MAP type_memory_size (TAKE j tvs))) m) ==>
    !j. j < k ==> !m. mem_agree_outside tf mem' m ==>
      val_in_memory (EL j tvs) (EL j vs)
        (addr + SUM (MAP type_memory_size (TAKE j tvs))) m
Proof
  rpt strip_tac >>
  `SUM (MAP type_memory_size (TAKE j tvs)) + type_memory_size (EL j tvs) <=
    SUM (MAP type_memory_size (TAKE k tvs))` by
    (irule sum_take_element_before >> simp[]) >>
  irule robust_representation_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`addr + SUM (MAP type_memory_size (TAKE k tvs))`,
    `mem`, `mem'`, `type_memory_size (EL k tvs)`, `tn`, `tf`] >>
  simp[] >> metis_tac[]
QED
