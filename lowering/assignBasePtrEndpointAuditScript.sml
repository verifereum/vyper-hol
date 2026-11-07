(* Endpoint extent probes only: these do NOT refute the frozen assignment
   theorem. A represented footprint and a compiler read capacity differ. *)
Theory assignBasePtrEndpointAudit
Ancestors loweringPosts valueEncoding words arithmetic vyperValue vyperAST

Theorem assign_base_footprint_last_start:
  !base footprint n.
    base + footprint < dimword (:256) /\
    32*(n-1) <= footprint ==>
    base + 32*(n-1) < dimword (:256)
Proof
  rpt strip_tac >> decide_tac
QED

(* expr_val_at_bound bounds the 33 live bytes, whereas a Bytes[64] source
   type asks the bulk branch to load starts 0,32,64. The post does not say
   that the fresh allocation covers the whole declared capacity. *)
Theorem assign_base_bytes_footprint_extent_gap:
  val_footprint (BaseTV (BytesT (Dynamic 64))) (BytesV [0w]) = 33 /\
  type_memory_size (BaseTV (BytesT (Dynamic 64))) = 96 /\
  w2n (n2w (dimword (:256)-34):bytes32) +
    val_footprint (BaseTV (BytesT (Dynamic 64))) (BytesV [0w]) < dimword (:256) /\
  ~(w2n (n2w (dimword (:256)-34):bytes32) +
    32*((96 DIV 32)-1) < dimword (:256))
Proof
  simp[dimword_def, w2n_n2w] >> EVAL_TAC
QED
