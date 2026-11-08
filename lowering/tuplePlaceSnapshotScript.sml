(* Boundary probes for a tuple snapshot across place evaluation. *)
Theory tuplePlaceSnapshot
Ancestors
  loweringPosts valueEncodingProps valueEncodingProofs
  venomExecSemantics venomState compileEnv placeMemoryCopyEffect

Theorem tuple_place_target_frame:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s ==>
  wb_frame cenv es es' sa s0 s
Proof
  simp[target_post_def, wb_frame_def] >> metis_tac[]
QED

Theorem tuple_place_target_operand:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!lbl. op <> Label lbl) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def] >>
  simp[target_post_def] >> metis_tac[]
QED

Theorem tuple_place_target_allocation:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) ==>
  mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  simp[target_post_def] >> metis_tac[]
QED

(* The unchanged-entry clause includes dynamic-array length words. *)
Theorem tuple_place_target_unchanged_local:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s /\
  local_region cenv es.scopes s0 n b sz /\
  lookup_scopes n es'.scopes = lookup_scopes n es.scopes ==>
  mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  simp[target_post_def, locals_kept_def] >> metis_tac[]
QED

(* A typed-copy effect, unlike stmt_state_rel alone, protects a snapshot.
   This applies to dynamic length words and zero-sized types as well. *)
Theorem tuple_place_copy_snapshot:
  typed_copy_effect ctx func sa sb s t d n /\
  val_in_memory tv v b s.vs_memory /\ val_wf tv v /\
  (b + type_memory_size tv <= d \/ d + n <= b) ==>
  val_in_memory tv v b t.vs_memory
Proof
  strip_tac >> irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[] >>
  sym_tac >> irule typed_copy_effect_bytes >> metis_tac[]
QED
