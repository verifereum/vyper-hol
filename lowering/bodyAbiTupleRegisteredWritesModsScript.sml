(* Sequence the two actual registered footprints, with a taint frame on
   bytes outside their combined footprint. *)
Theory bodyAbiTupleRegisteredWritesMods
Ancestors
  abiEncoderWindowContract abiEncoderRegisteredEffect ptrDiscipline venomState
  finite_map pred_set list pair

Theorem abi_tuple_registered_writes_sequence_mods:
  abi_encoder_registered_effect left ls u z /\
  abi_encoder_registered_effect right rs z q /\
  (!i. EVERY (\(b,n). i < b \/ b+n <= i) ls /\
       (!id b n. id IN left /\ FLOOKUP z.vs_allocas id = SOME (b,n) ==>
                 i < b \/ b+n <= i) /\
       i IN tz.t_mem ==> i IN tu.t_mem) /\
  (!i. EVERY (\(b,n). i < b \/ b+n <= i) rs /\
       (!id b n. id IN right /\ FLOOKUP q.vs_allocas id = SOME (b,n) ==>
                 i < b \/ b+n <= i) /\
       i IN tq.t_mem ==> i IN tz.t_mem) ==>
  abi_encoder_registered_effect (left UNION right) (ls ++ rs) u q /\
  (!i. EVERY (\(b,n). i < b \/ b+n <= i) (ls ++ rs) /\
       (!id b n. id IN (left UNION right) /\ FLOOKUP q.vs_allocas id = SOME (b,n) ==>
                 i < b \/ b+n <= i) /\
       i IN tq.t_mem ==> i IN tu.t_mem)
Proof
  strip_tac >> conj_tac
  >- (irule abi_encoder_window_effect_sequence >>
      qexistsl_tac [`left`,`ls`,`right`,`rs`,`z`] >> simp[EVERY_APPEND]) >>
  simp[EVERY_APPEND, IN_UNION] >> rpt strip_tac >>
  `i IN tz.t_mem` by
    (qpat_assum `!i. _ /\ _ /\ i IN tq.t_mem ==> _`
       (qspec_then `i` irule) >> simp[] >> metis_tac[]) >>
  qpat_assum `!i. _ /\ _ /\ i IN tz.t_mem ==> _` (qspec_then `i` irule) >>
  simp[] >> rpt strip_tac >>
  `FLOOKUP q.vs_allocas id = SOME (b,n)` by
    (irule abi_encoder_registered_effect_allocated >> metis_tac[]) >>
  metis_tac[]
QED
