(* Typed constructor immutable copy retaining the counted endpoint frame. *)
Theory bodyMemSnapshotCodeCtor
Ancestors
  exprSimMemUnwrap exprSimCopy valueEncodingProps fragGasPathMem
  loweringPosts exprLoweringProps compileEnv context venomState

Theorem snapshot_ctor_copy_typed_mem:
  compile_imm_copy_to_memory T imm src dst (type_slot_size tv) 0 sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region) /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv < dimword (:256) /\
  w2n a + type_memory_size tv <= s.vs_alloca_next /\
  w2n a + type_memory_size tv < dimword (:256) /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  regions_disjoint (w2n a) (type_memory_size tv)
    (w2n d) (type_memory_size tv) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    copy_static z = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n d \/ w2n d + type_memory_size tv <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n d) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv
Proof
  strip_tac >>
  `w2n d + 0 + 32 * type_slot_size tv <= s.vs_alloca_next /\
   w2n d + 0 + 32 * type_slot_size tv < dimword (:256) /\
   w2n a + 0 + 32 * type_slot_size tv <= s.vs_alloca_next /\
   w2n a + 0 + 32 * type_slot_size tv < dimword (:256)` by
    gvs[type_memory_size_slots] >>
  drule_all ctor_code_copy_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all copy_ctor_contents >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
