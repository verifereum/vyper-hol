(* A captured composite in an old, separated allocation survives target effects.
   Operand preservation is already exported by tuplePlaceSnapshot. *)
Theory assignEffectfulIndexSnapshotFrame
Ancestors
  tuplePlaceSnapshot valueEncodingProps

Theorem assign_effectful_target_snapshot_value:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) /\
  val_in_memory tv v b s0.vs_memory /\ val_wf tv v /\
  type_memory_size tv <= sz ==>
  val_in_memory tv v b s.vs_memory
Proof
  strip_tac >>
  drule_all tuple_place_target_allocation >> strip_tac >>
  irule val_in_memory_mem_agree >>
  metis_tac[]
QED
