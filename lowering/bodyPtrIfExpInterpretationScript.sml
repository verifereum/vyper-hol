Theory bodyPtrIfExpInterpretation
Ancestors
  bodyPtrIfExpRuntimeLayout bodyPtrIfExpDefaults valueEncoding

Theorem ifexp_elems_in_memory_transport:
  !stv dtv mem.
    type_memory_size stv = type_memory_size dtv /\
    (!v off. val_in_memory stv v off mem ==> val_in_memory dtv v off mem) ==>
    !vs off. elems_in_memory vs off stv mem ==> elems_in_memory vs off dtv mem
Proof
  rpt gen_tac >> strip_tac >> Induct >>
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem ifexp_kvs_in_memory_transport:
  !stv dtv mem.
    type_memory_size stv = type_memory_size dtv /\
    (!v off. val_in_memory stv v off mem ==> val_in_memory dtv v off mem) ==>
    !vs off. kvs_in_memory vs off stv mem ==> kvs_in_memory vs off dtv mem
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- simp[val_in_memory_def] >>
  Cases_on `h` >> simp[val_in_memory_def] >> metis_tac[]
QED
