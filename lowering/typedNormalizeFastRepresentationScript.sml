(* One-layer fast-copy lifting. Element and default transport remain explicit. *)
Theory typedNormalizeFastRepresentation
Ancestors
  valueEncoding valueEncodingDefs vyperValue

Theorem elems_in_memory_type_transport:
  !vs s d b mem.
    type_memory_size s = type_memory_size d /\
    (!v p. val_in_memory s v p mem ==> val_in_memory d v p mem) /\
    elems_in_memory vs b s mem ==>
    elems_in_memory vs b d mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem kvs_in_memory_type_transport[local]:
  !kvs s d b mem.
    type_memory_size s = type_memory_size d /\
    (!v p. val_in_memory s v p mem ==> val_in_memory d v p mem) /\
    kvs_in_memory kvs b s mem ==>
    kvs_in_memory kvs b d mem
Proof
  Induct >- simp[val_in_memory_def] >> PairCases >>
  simp[val_in_memory_def] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem sparse_array_in_memory_type_transport:
  !kvs s d n b mem.
    type_memory_size s = type_memory_size d /\
    (!v p. val_in_memory s v p mem ==> val_in_memory d v p mem) /\
    (!p. val_in_memory s (default_value s) p mem ==>
         val_in_memory d (default_value d) p mem) /\
    val_in_memory (ArrayTV s (Fixed n)) (ArrayV (SArrayV kvs)) b mem ==>
    val_in_memory (ArrayTV d (Fixed n)) (ArrayV (SArrayV kvs)) b mem
Proof
  simp[val_in_memory_def] >> rpt strip_tac
  >- (irule kvs_in_memory_type_transport >> metis_tac[]) >>
  metis_tac[]
QED

Theorem dynarray_in_memory_capacity_irrelevant:
  !tv n m vs b mem.
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) b mem <=>
    val_in_memory (ArrayTV tv (Dynamic m)) (ArrayV (DynArrayV vs)) b mem
Proof
  simp[val_in_memory_def]
QED
