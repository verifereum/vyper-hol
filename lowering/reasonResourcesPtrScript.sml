(* Resource boundaries for the shared raise/assert reason encoder. *)
Theory reasonResourcesPtr
Ancestors
  representationCleanPtr bodyPtrDefs exprSimProps valueEncoding vfmConstants
  words list loweringPosts venomState compileEnv allocLimits arithmetic venomMemProps

Theorem reason_string_head_clean:
  !cx ty str op G tn s tv w.
    ptr_mem_ok cx ty (StringV str) op G tn s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w ==>
    !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv (StringV str) (w2n w) mem` by
    metis_tac[ptr_mem_ok_def] >>
  drule robust_val_in_memory_string_clean >> simp[]
QED

Theorem reason_string_source_covers:
  !cx ty str op G tn s n w.
    ptr_mem_ok cx ty (StringV str) op G tn s /\
    op_taint tn op = {} /\
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT n)) /\
    eval_operand op s = SOME w ==>
    ?p. op = Var p /\
        ptr_covers G tn p s (32 + 32 * word_size (LENGTH str))
Proof
  rpt gen_tac >> strip_tac >>
  fs[ptr_mem_ok_def, val_footprint_def, val_store_size_def] >>
  gvs[] >> simp[ptr_covers_def] >>
  qexists_tac `w` >> gvs[eval_operand_def]
QED

(* The rounded copy always reads the head, including for an empty reason. *)
Theorem reason_string_copy_boundary_tests:
  MAP (\n. 32 + 32 * word_size n) [0;31;32;33] = [32;64;64;96]
Proof
  EVAL_TAC
QED

Theorem reason_string_length_word:
  !cx ty str op G tn s tv w.
    ptr_mem_ok cx ty (StringV str) op G tn s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w ==>
    mem_word_at (w2n w) s.vs_memory = n2w (LENGTH str)
Proof
  rpt gen_tac >> strip_tac >>
  `val_in_memory tv (StringV str) (w2n w) s.vs_memory` by
    (fs[ptr_mem_ok_def] >>
     first_x_assum irule >> simp[mem_agree_outside_def]) >>
  gvs[val_in_memory_def]
QED

Theorem reason_string_capacity_bounds:
  !str n.
    val_wf (BaseTV (StringT n)) (StringV str) ==>
    LENGTH str <= 32 * word_size (LENGTH str) /\
    32 + 32 * word_size (LENGTH str) <=
      type_memory_size (BaseTV (StringT n))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- simp[le_word_size_mul] >>
  drule val_store_size_le >> simp[val_store_size_def]
QED

(* Offsets are relative to the outer Error(string) buffer.  In particular
   the zero store at tail+rounded ends exactly at the minimal capacity. *)
Theorem reason_encoder_range_bounds:
  !n rounded capacity.
    n <= rounded /\ 32 + rounded <= capacity ==>
    32 + n <= capacity /\
    64 + rounded + 32 <= 64 + capacity /\
    64 + (32 + n) <= 64 + capacity /\
    28 + (4 + (32 + (32 + rounded))) <= 64 + capacity
Proof
  decide_tac
QED

Theorem reason_encoder_nonwrapping_bounds:
  !n rounded capacity.
    n <= rounded /\ 32 + rounded <= capacity /\
    64 + capacity < dimword (:256) ==>
    n + 31 < dimword (:256) /\
    32 + rounded < dimword (:256) /\
    4 + (32 + (32 + rounded)) < dimword (:256)
Proof
  decide_tac
QED

Theorem reason_string_type_capacity:
  !cenv n str.
    val_wf (BaseTV (StringT n)) (StringV str) ==>
    32 + 32 * word_size (LENGTH str) <=
      type_memory_bytes cenv (BaseT (StringT n))
Proof
  rpt gen_tac >> strip_tac >>
  drule val_store_size_le >>
  simp_tac (srw_ss()) [val_store_size_def, type_memory_size_def,
       type_memory_bytes_def, word_size_def] >> decide_tac
QED

Theorem reason_encoder_allocation_limit:
  !cenv n.
    type_alloc_ok cenv (BaseT (StringT n)) ==>
    64 + type_memory_bytes cenv (BaseT (StringT n)) < dimword (:256)
Proof
  `dimword (:256) = 2 ** 256` by simp[dimword_def] >>
  simp[type_alloc_ok_def, is_word_type_def] >> decide_tac
QED
